%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:31 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 268 expanded)
%              Number of leaves         :   38 ( 121 expanded)
%              Depth                    :   17
%              Number of atoms          :  307 (2159 expanded)
%              Number of equality atoms :    6 (  98 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_239,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_74,axiom,(
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

tff(f_186,axiom,(
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
                     => ( m1_pre_topc(C,D)
                       => ! [F] :
                            ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(B)))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ! [H] :
                                    ( m1_subset_1(H,u1_struct_0(C))
                                   => ( ( v3_pre_topc(F,B)
                                        & r2_hidden(G,F)
                                        & r1_tarski(F,u1_struct_0(C))
                                        & G = H )
                                     => ( r1_tmap_1(D,A,E,G)
                                      <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_129,axiom,(
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

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_52,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_30,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_32,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_78,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_87,plain,(
    ! [B_525,A_526] :
      ( l1_pre_topc(B_525)
      | ~ m1_pre_topc(B_525,A_526)
      | ~ l1_pre_topc(A_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_87])).

tff(c_99,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_90])).

tff(c_10,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_22,plain,(
    ! [B_19,A_17] :
      ( m1_subset_1(u1_struct_0(B_19),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_123,plain,(
    ! [B_537,A_538] :
      ( v3_pre_topc(u1_struct_0(B_537),A_538)
      | ~ v1_tsep_1(B_537,A_538)
      | ~ m1_subset_1(u1_struct_0(B_537),k1_zfmisc_1(u1_struct_0(A_538)))
      | ~ m1_pre_topc(B_537,A_538)
      | ~ l1_pre_topc(A_538)
      | ~ v2_pre_topc(A_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_127,plain,(
    ! [B_19,A_17] :
      ( v3_pre_topc(u1_struct_0(B_19),A_17)
      | ~ v1_tsep_1(B_19,A_17)
      | ~ v2_pre_topc(A_17)
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_22,c_123])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_68,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_77,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_68])).

tff(c_116,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_44,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_74,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_74])).

tff(c_115,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_141,plain,(
    ! [D_555,B_554,F_553,E_556,C_552,H_551,A_550] :
      ( r1_tmap_1(D_555,A_550,E_556,H_551)
      | ~ r1_tmap_1(C_552,A_550,k3_tmap_1(B_554,A_550,D_555,C_552,E_556),H_551)
      | ~ r1_tarski(F_553,u1_struct_0(C_552))
      | ~ r2_hidden(H_551,F_553)
      | ~ v3_pre_topc(F_553,B_554)
      | ~ m1_subset_1(H_551,u1_struct_0(C_552))
      | ~ m1_subset_1(H_551,u1_struct_0(D_555))
      | ~ m1_subset_1(F_553,k1_zfmisc_1(u1_struct_0(B_554)))
      | ~ m1_pre_topc(C_552,D_555)
      | ~ m1_subset_1(E_556,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_555),u1_struct_0(A_550))))
      | ~ v1_funct_2(E_556,u1_struct_0(D_555),u1_struct_0(A_550))
      | ~ v1_funct_1(E_556)
      | ~ m1_pre_topc(D_555,B_554)
      | v2_struct_0(D_555)
      | ~ m1_pre_topc(C_552,B_554)
      | v2_struct_0(C_552)
      | ~ l1_pre_topc(B_554)
      | ~ v2_pre_topc(B_554)
      | v2_struct_0(B_554)
      | ~ l1_pre_topc(A_550)
      | ~ v2_pre_topc(A_550)
      | v2_struct_0(A_550) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_145,plain,(
    ! [F_553] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
      | ~ r1_tarski(F_553,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_553)
      | ~ v3_pre_topc(F_553,'#skF_2')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_553,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_115,c_141])).

tff(c_152,plain,(
    ! [F_553] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
      | ~ r1_tarski(F_553,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_553)
      | ~ v3_pre_topc(F_553,'#skF_2')
      | ~ m1_subset_1(F_553,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_52,c_48,c_46,c_44,c_42,c_36,c_34,c_78,c_145])).

tff(c_154,plain,(
    ! [F_557] :
      ( ~ r1_tarski(F_557,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_557)
      | ~ v3_pre_topc(F_557,'#skF_2')
      | ~ m1_subset_1(F_557,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_54,c_50,c_116,c_152])).

tff(c_158,plain,(
    ! [B_19] :
      ( ~ r1_tarski(u1_struct_0(B_19),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_19))
      | ~ v3_pre_topc(u1_struct_0(B_19),'#skF_2')
      | ~ m1_pre_topc(B_19,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_154])).

tff(c_162,plain,(
    ! [B_558] :
      ( ~ r1_tarski(u1_struct_0(B_558),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_558))
      | ~ v3_pre_topc(u1_struct_0(B_558),'#skF_2')
      | ~ m1_pre_topc(B_558,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_158])).

tff(c_166,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_162])).

tff(c_169,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_166])).

tff(c_170,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_173,plain,
    ( ~ v1_tsep_1('#skF_3','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_127,c_170])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_58,c_40,c_173])).

tff(c_178,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_188,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_178])).

tff(c_191,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_188])).

tff(c_14,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_194,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_191,c_14])).

tff(c_197,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_194])).

tff(c_200,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_197])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_200])).

tff(c_205,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_115])).

tff(c_208,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_228,plain,(
    ! [E_572,G_571,D_568,A_569,C_567,B_570] :
      ( r1_tmap_1(D_568,B_570,k3_tmap_1(A_569,B_570,C_567,D_568,E_572),G_571)
      | ~ r1_tmap_1(C_567,B_570,E_572,G_571)
      | ~ m1_pre_topc(D_568,C_567)
      | ~ m1_subset_1(G_571,u1_struct_0(D_568))
      | ~ m1_subset_1(G_571,u1_struct_0(C_567))
      | ~ m1_subset_1(E_572,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_567),u1_struct_0(B_570))))
      | ~ v1_funct_2(E_572,u1_struct_0(C_567),u1_struct_0(B_570))
      | ~ v1_funct_1(E_572)
      | ~ m1_pre_topc(D_568,A_569)
      | v2_struct_0(D_568)
      | ~ m1_pre_topc(C_567,A_569)
      | v2_struct_0(C_567)
      | ~ l1_pre_topc(B_570)
      | ~ v2_pre_topc(B_570)
      | v2_struct_0(B_570)
      | ~ l1_pre_topc(A_569)
      | ~ v2_pre_topc(A_569)
      | v2_struct_0(A_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_230,plain,(
    ! [D_568,A_569,G_571] :
      ( r1_tmap_1(D_568,'#skF_1',k3_tmap_1(A_569,'#skF_1','#skF_4',D_568,'#skF_5'),G_571)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_571)
      | ~ m1_pre_topc(D_568,'#skF_4')
      | ~ m1_subset_1(G_571,u1_struct_0(D_568))
      | ~ m1_subset_1(G_571,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_568,A_569)
      | v2_struct_0(D_568)
      | ~ m1_pre_topc('#skF_4',A_569)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_569)
      | ~ v2_pre_topc(A_569)
      | v2_struct_0(A_569) ) ),
    inference(resolution,[status(thm)],[c_42,c_228])).

tff(c_233,plain,(
    ! [D_568,A_569,G_571] :
      ( r1_tmap_1(D_568,'#skF_1',k3_tmap_1(A_569,'#skF_1','#skF_4',D_568,'#skF_5'),G_571)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_571)
      | ~ m1_pre_topc(D_568,'#skF_4')
      | ~ m1_subset_1(G_571,u1_struct_0(D_568))
      | ~ m1_subset_1(G_571,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_568,A_569)
      | v2_struct_0(D_568)
      | ~ m1_pre_topc('#skF_4',A_569)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_569)
      | ~ v2_pre_topc(A_569)
      | v2_struct_0(A_569) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_46,c_44,c_230])).

tff(c_235,plain,(
    ! [D_573,A_574,G_575] :
      ( r1_tmap_1(D_573,'#skF_1',k3_tmap_1(A_574,'#skF_1','#skF_4',D_573,'#skF_5'),G_575)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_575)
      | ~ m1_pre_topc(D_573,'#skF_4')
      | ~ m1_subset_1(G_575,u1_struct_0(D_573))
      | ~ m1_subset_1(G_575,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_573,A_574)
      | v2_struct_0(D_573)
      | ~ m1_pre_topc('#skF_4',A_574)
      | ~ l1_pre_topc(A_574)
      | ~ v2_pre_topc(A_574)
      | v2_struct_0(A_574) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_50,c_233])).

tff(c_209,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_238,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_235,c_209])).

tff(c_241,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_48,c_52,c_34,c_78,c_36,c_208,c_238])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.44  
% 2.63/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.44  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.63/1.44  
% 2.63/1.44  %Foreground sorts:
% 2.63/1.44  
% 2.63/1.44  
% 2.63/1.44  %Background operators:
% 2.63/1.44  
% 2.63/1.44  
% 2.63/1.44  %Foreground operators:
% 2.63/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.63/1.44  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.63/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.63/1.44  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.63/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.44  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.63/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.63/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.63/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.63/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.63/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.63/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.63/1.44  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 2.63/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.63/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.63/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.63/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.44  
% 3.04/1.46  tff(f_239, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_tmap_1)).
% 3.04/1.46  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.04/1.46  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.04/1.46  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.04/1.46  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.04/1.46  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.04/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.04/1.46  tff(f_186, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 3.04/1.46  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.04/1.46  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.04/1.46  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_52, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_34, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_30, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_32, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_78, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 3.04/1.46  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_87, plain, (![B_525, A_526]: (l1_pre_topc(B_525) | ~m1_pre_topc(B_525, A_526) | ~l1_pre_topc(A_526))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.04/1.46  tff(c_90, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_87])).
% 3.04/1.46  tff(c_99, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_90])).
% 3.04/1.46  tff(c_10, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.04/1.46  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.04/1.46  tff(c_40, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_22, plain, (![B_19, A_17]: (m1_subset_1(u1_struct_0(B_19), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.04/1.46  tff(c_123, plain, (![B_537, A_538]: (v3_pre_topc(u1_struct_0(B_537), A_538) | ~v1_tsep_1(B_537, A_538) | ~m1_subset_1(u1_struct_0(B_537), k1_zfmisc_1(u1_struct_0(A_538))) | ~m1_pre_topc(B_537, A_538) | ~l1_pre_topc(A_538) | ~v2_pre_topc(A_538))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.04/1.46  tff(c_127, plain, (![B_19, A_17]: (v3_pre_topc(u1_struct_0(B_19), A_17) | ~v1_tsep_1(B_19, A_17) | ~v2_pre_topc(A_17) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_22, c_123])).
% 3.04/1.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.04/1.46  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_68, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_77, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_68])).
% 3.04/1.46  tff(c_116, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_77])).
% 3.04/1.46  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_44, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_74, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.04/1.46  tff(c_76, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_74])).
% 3.04/1.46  tff(c_115, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_76])).
% 3.04/1.47  tff(c_141, plain, (![D_555, B_554, F_553, E_556, C_552, H_551, A_550]: (r1_tmap_1(D_555, A_550, E_556, H_551) | ~r1_tmap_1(C_552, A_550, k3_tmap_1(B_554, A_550, D_555, C_552, E_556), H_551) | ~r1_tarski(F_553, u1_struct_0(C_552)) | ~r2_hidden(H_551, F_553) | ~v3_pre_topc(F_553, B_554) | ~m1_subset_1(H_551, u1_struct_0(C_552)) | ~m1_subset_1(H_551, u1_struct_0(D_555)) | ~m1_subset_1(F_553, k1_zfmisc_1(u1_struct_0(B_554))) | ~m1_pre_topc(C_552, D_555) | ~m1_subset_1(E_556, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_555), u1_struct_0(A_550)))) | ~v1_funct_2(E_556, u1_struct_0(D_555), u1_struct_0(A_550)) | ~v1_funct_1(E_556) | ~m1_pre_topc(D_555, B_554) | v2_struct_0(D_555) | ~m1_pre_topc(C_552, B_554) | v2_struct_0(C_552) | ~l1_pre_topc(B_554) | ~v2_pre_topc(B_554) | v2_struct_0(B_554) | ~l1_pre_topc(A_550) | ~v2_pre_topc(A_550) | v2_struct_0(A_550))), inference(cnfTransformation, [status(thm)], [f_186])).
% 3.04/1.47  tff(c_145, plain, (![F_553]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~r1_tarski(F_553, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_553) | ~v3_pre_topc(F_553, '#skF_2') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_553, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_115, c_141])).
% 3.04/1.47  tff(c_152, plain, (![F_553]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~r1_tarski(F_553, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_553) | ~v3_pre_topc(F_553, '#skF_2') | ~m1_subset_1(F_553, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_52, c_48, c_46, c_44, c_42, c_36, c_34, c_78, c_145])).
% 3.04/1.47  tff(c_154, plain, (![F_557]: (~r1_tarski(F_557, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_557) | ~v3_pre_topc(F_557, '#skF_2') | ~m1_subset_1(F_557, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_54, c_50, c_116, c_152])).
% 3.04/1.47  tff(c_158, plain, (![B_19]: (~r1_tarski(u1_struct_0(B_19), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_19)) | ~v3_pre_topc(u1_struct_0(B_19), '#skF_2') | ~m1_pre_topc(B_19, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_154])).
% 3.04/1.47  tff(c_162, plain, (![B_558]: (~r1_tarski(u1_struct_0(B_558), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_558)) | ~v3_pre_topc(u1_struct_0(B_558), '#skF_2') | ~m1_pre_topc(B_558, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_158])).
% 3.04/1.47  tff(c_166, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_162])).
% 3.04/1.47  tff(c_169, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_166])).
% 3.04/1.47  tff(c_170, plain, (~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_169])).
% 3.04/1.47  tff(c_173, plain, (~v1_tsep_1('#skF_3', '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_127, c_170])).
% 3.04/1.47  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_58, c_40, c_173])).
% 3.04/1.47  tff(c_178, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_169])).
% 3.04/1.47  tff(c_188, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_178])).
% 3.04/1.47  tff(c_191, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_188])).
% 3.04/1.47  tff(c_14, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.04/1.47  tff(c_194, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_191, c_14])).
% 3.04/1.47  tff(c_197, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_194])).
% 3.04/1.47  tff(c_200, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_197])).
% 3.04/1.47  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_200])).
% 3.04/1.47  tff(c_205, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_77])).
% 3.04/1.47  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_115])).
% 3.04/1.47  tff(c_208, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_76])).
% 3.04/1.47  tff(c_228, plain, (![E_572, G_571, D_568, A_569, C_567, B_570]: (r1_tmap_1(D_568, B_570, k3_tmap_1(A_569, B_570, C_567, D_568, E_572), G_571) | ~r1_tmap_1(C_567, B_570, E_572, G_571) | ~m1_pre_topc(D_568, C_567) | ~m1_subset_1(G_571, u1_struct_0(D_568)) | ~m1_subset_1(G_571, u1_struct_0(C_567)) | ~m1_subset_1(E_572, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_567), u1_struct_0(B_570)))) | ~v1_funct_2(E_572, u1_struct_0(C_567), u1_struct_0(B_570)) | ~v1_funct_1(E_572) | ~m1_pre_topc(D_568, A_569) | v2_struct_0(D_568) | ~m1_pre_topc(C_567, A_569) | v2_struct_0(C_567) | ~l1_pre_topc(B_570) | ~v2_pre_topc(B_570) | v2_struct_0(B_570) | ~l1_pre_topc(A_569) | ~v2_pre_topc(A_569) | v2_struct_0(A_569))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.04/1.47  tff(c_230, plain, (![D_568, A_569, G_571]: (r1_tmap_1(D_568, '#skF_1', k3_tmap_1(A_569, '#skF_1', '#skF_4', D_568, '#skF_5'), G_571) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_571) | ~m1_pre_topc(D_568, '#skF_4') | ~m1_subset_1(G_571, u1_struct_0(D_568)) | ~m1_subset_1(G_571, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_568, A_569) | v2_struct_0(D_568) | ~m1_pre_topc('#skF_4', A_569) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_569) | ~v2_pre_topc(A_569) | v2_struct_0(A_569))), inference(resolution, [status(thm)], [c_42, c_228])).
% 3.04/1.47  tff(c_233, plain, (![D_568, A_569, G_571]: (r1_tmap_1(D_568, '#skF_1', k3_tmap_1(A_569, '#skF_1', '#skF_4', D_568, '#skF_5'), G_571) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_571) | ~m1_pre_topc(D_568, '#skF_4') | ~m1_subset_1(G_571, u1_struct_0(D_568)) | ~m1_subset_1(G_571, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_568, A_569) | v2_struct_0(D_568) | ~m1_pre_topc('#skF_4', A_569) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_569) | ~v2_pre_topc(A_569) | v2_struct_0(A_569))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_46, c_44, c_230])).
% 3.04/1.47  tff(c_235, plain, (![D_573, A_574, G_575]: (r1_tmap_1(D_573, '#skF_1', k3_tmap_1(A_574, '#skF_1', '#skF_4', D_573, '#skF_5'), G_575) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_575) | ~m1_pre_topc(D_573, '#skF_4') | ~m1_subset_1(G_575, u1_struct_0(D_573)) | ~m1_subset_1(G_575, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_573, A_574) | v2_struct_0(D_573) | ~m1_pre_topc('#skF_4', A_574) | ~l1_pre_topc(A_574) | ~v2_pre_topc(A_574) | v2_struct_0(A_574))), inference(negUnitSimplification, [status(thm)], [c_66, c_50, c_233])).
% 3.04/1.47  tff(c_209, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_76])).
% 3.04/1.47  tff(c_238, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_235, c_209])).
% 3.04/1.47  tff(c_241, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_48, c_52, c_34, c_78, c_36, c_208, c_238])).
% 3.04/1.47  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_241])).
% 3.04/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.47  
% 3.04/1.47  Inference rules
% 3.04/1.47  ----------------------
% 3.04/1.47  #Ref     : 0
% 3.04/1.47  #Sup     : 24
% 3.04/1.47  #Fact    : 0
% 3.04/1.47  #Define  : 0
% 3.04/1.47  #Split   : 3
% 3.04/1.47  #Chain   : 0
% 3.04/1.47  #Close   : 0
% 3.04/1.47  
% 3.04/1.47  Ordering : KBO
% 3.04/1.47  
% 3.04/1.47  Simplification rules
% 3.04/1.47  ----------------------
% 3.04/1.47  #Subsume      : 6
% 3.04/1.47  #Demod        : 56
% 3.04/1.47  #Tautology    : 13
% 3.04/1.47  #SimpNegUnit  : 7
% 3.04/1.47  #BackRed      : 0
% 3.04/1.47  
% 3.04/1.47  #Partial instantiations: 0
% 3.04/1.47  #Strategies tried      : 1
% 3.04/1.47  
% 3.04/1.47  Timing (in seconds)
% 3.04/1.47  ----------------------
% 3.04/1.47  Preprocessing        : 0.39
% 3.04/1.47  Parsing              : 0.19
% 3.04/1.47  CNF conversion       : 0.06
% 3.04/1.47  Main loop            : 0.23
% 3.04/1.47  Inferencing          : 0.08
% 3.04/1.47  Reduction            : 0.07
% 3.04/1.47  Demodulation         : 0.05
% 3.04/1.47  BG Simplification    : 0.02
% 3.04/1.47  Subsumption          : 0.04
% 3.04/1.47  Abstraction          : 0.01
% 3.04/1.47  MUC search           : 0.00
% 3.04/1.47  Cooper               : 0.00
% 3.04/1.47  Total                : 0.65
% 3.04/1.47  Index Insertion      : 0.00
% 3.04/1.47  Index Deletion       : 0.00
% 3.04/1.47  Index Matching       : 0.00
% 3.04/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
