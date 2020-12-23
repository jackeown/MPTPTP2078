%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:41 EST 2020

% Result     : Theorem 5.48s
% Output     : CNFRefutation 5.48s
% Verified   : 
% Statistics : Number of formulae       :  151 (1130 expanded)
%              Number of leaves         :   49 ( 415 expanded)
%              Depth                    :   18
%              Number of atoms          :  317 (5285 expanded)
%              Number of equality atoms :   15 ( 594 expanded)
%              Maximal formula depth    :   29 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_245,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_196,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

tff(f_118,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_127,plain,(
    ! [B_425,A_426] :
      ( l1_pre_topc(B_425)
      | ~ m1_pre_topc(B_425,A_426)
      | ~ l1_pre_topc(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_136,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_127])).

tff(c_143,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_136])).

tff(c_18,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_104,plain,(
    ! [A_423] :
      ( u1_struct_0(A_423) = k2_struct_0(A_423)
      | ~ l1_struct_0(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_108,plain,(
    ! [A_14] :
      ( u1_struct_0(A_14) = k2_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_104])).

tff(c_151,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_143,c_108])).

tff(c_171,plain,(
    ! [A_429] :
      ( ~ v1_xboole_0(u1_struct_0(A_429))
      | ~ l1_struct_0(A_429)
      | v2_struct_0(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_174,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_171])).

tff(c_184,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_174])).

tff(c_188,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_191,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_188])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_191])).

tff(c_196,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_160,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_52])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_270,plain,(
    ! [B_436,A_437] :
      ( v2_pre_topc(B_436)
      | ~ m1_pre_topc(B_436,A_437)
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_279,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_270])).

tff(c_286,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_279])).

tff(c_30,plain,(
    ! [A_25] :
      ( v3_pre_topc(k2_struct_0(A_25),A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    ! [A_36] :
      ( m1_pre_topc(A_36,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_66,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_133,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_127])).

tff(c_140,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_133])).

tff(c_147,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_140,c_108])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_152,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_54])).

tff(c_673,plain,(
    ! [B_469,A_470] :
      ( m1_pre_topc(B_469,A_470)
      | ~ m1_pre_topc(B_469,g1_pre_topc(u1_struct_0(A_470),u1_pre_topc(A_470)))
      | ~ l1_pre_topc(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_679,plain,(
    ! [B_469] :
      ( m1_pre_topc(B_469,'#skF_3')
      | ~ m1_pre_topc(B_469,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_673])).

tff(c_693,plain,(
    ! [B_469] :
      ( m1_pre_topc(B_469,'#skF_3')
      | ~ m1_pre_topc(B_469,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_152,c_679])).

tff(c_307,plain,(
    ! [B_447,A_448] :
      ( m1_subset_1(u1_struct_0(B_447),k1_zfmisc_1(u1_struct_0(A_448)))
      | ~ m1_pre_topc(B_447,A_448)
      | ~ l1_pre_topc(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_324,plain,(
    ! [B_447] :
      ( m1_subset_1(u1_struct_0(B_447),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_447,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_307])).

tff(c_956,plain,(
    ! [B_489] :
      ( m1_subset_1(u1_struct_0(B_489),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_489,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_324])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_998,plain,(
    ! [B_493] :
      ( r1_tarski(u1_struct_0(B_493),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_493,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_956,c_8])).

tff(c_1001,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_998])).

tff(c_1012,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1001])).

tff(c_1016,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_693,c_1012])).

tff(c_1023,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1016])).

tff(c_1027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_1023])).

tff(c_1028,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1001])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_44,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_109,plain,(
    ! [A_424] :
      ( u1_struct_0(A_424) = k2_struct_0(A_424)
      | ~ l1_pre_topc(A_424) ) ),
    inference(resolution,[status(thm)],[c_18,c_104])).

tff(c_116,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_109])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_118,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_58])).

tff(c_169,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_118])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_158,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_56])).

tff(c_159,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_158])).

tff(c_318,plain,(
    ! [B_447] :
      ( m1_subset_1(u1_struct_0(B_447),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_447,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_307])).

tff(c_347,plain,(
    ! [B_449] :
      ( m1_subset_1(u1_struct_0(B_449),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_449,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_318])).

tff(c_368,plain,(
    ! [B_450] :
      ( r1_tarski(u1_struct_0(B_450),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_450,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_347,c_8])).

tff(c_374,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_368])).

tff(c_382,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_567,plain,(
    ! [A_465,B_466] :
      ( m1_pre_topc(A_465,g1_pre_topc(u1_struct_0(B_466),u1_pre_topc(B_466)))
      | ~ m1_pre_topc(A_465,B_466)
      | ~ l1_pre_topc(B_466)
      | ~ l1_pre_topc(A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_584,plain,(
    ! [A_465] :
      ( m1_pre_topc(A_465,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_465,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_465) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_567])).

tff(c_603,plain,(
    ! [A_467] :
      ( m1_pre_topc(A_467,'#skF_4')
      | ~ m1_pre_topc(A_467,'#skF_3')
      | ~ l1_pre_topc(A_467) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_152,c_584])).

tff(c_614,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_603])).

tff(c_622,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_614])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_622])).

tff(c_626,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_48,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_81,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50])).

tff(c_153,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_81])).

tff(c_46,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_82,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_1077,plain,(
    ! [D_497,F_496,E_498,C_501,A_500,B_502,H_499] :
      ( r1_tmap_1(D_497,B_502,E_498,H_499)
      | ~ r1_tmap_1(C_501,B_502,k3_tmap_1(A_500,B_502,D_497,C_501,E_498),H_499)
      | ~ m1_connsp_2(F_496,D_497,H_499)
      | ~ r1_tarski(F_496,u1_struct_0(C_501))
      | ~ m1_subset_1(H_499,u1_struct_0(C_501))
      | ~ m1_subset_1(H_499,u1_struct_0(D_497))
      | ~ m1_subset_1(F_496,k1_zfmisc_1(u1_struct_0(D_497)))
      | ~ m1_pre_topc(C_501,D_497)
      | ~ m1_subset_1(E_498,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_497),u1_struct_0(B_502))))
      | ~ v1_funct_2(E_498,u1_struct_0(D_497),u1_struct_0(B_502))
      | ~ v1_funct_1(E_498)
      | ~ m1_pre_topc(D_497,A_500)
      | v2_struct_0(D_497)
      | ~ m1_pre_topc(C_501,A_500)
      | v2_struct_0(C_501)
      | ~ l1_pre_topc(B_502)
      | ~ v2_pre_topc(B_502)
      | v2_struct_0(B_502)
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_1079,plain,(
    ! [F_496] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_496,'#skF_4','#skF_6')
      | ~ r1_tarski(F_496,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_496,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_82,c_1077])).

tff(c_1082,plain,(
    ! [F_496] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_496,'#skF_4','#skF_6')
      | ~ r1_tarski(F_496,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(F_496,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_66,c_62,c_60,c_169,c_116,c_151,c_159,c_116,c_151,c_626,c_151,c_160,c_151,c_153,c_147,c_147,c_1079])).

tff(c_1093,plain,(
    ! [F_503] :
      ( ~ m1_connsp_2(F_503,'#skF_4','#skF_6')
      | ~ r1_tarski(F_503,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(F_503,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_68,c_64,c_44,c_1082])).

tff(c_1104,plain,
    ( ~ m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_83,c_1093])).

tff(c_1109,plain,(
    ~ m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_1104])).

tff(c_977,plain,(
    ! [B_490,A_491,C_492] :
      ( m1_connsp_2(B_490,A_491,C_492)
      | ~ r2_hidden(C_492,B_490)
      | ~ v3_pre_topc(B_490,A_491)
      | ~ m1_subset_1(C_492,u1_struct_0(A_491))
      | ~ m1_subset_1(B_490,k1_zfmisc_1(u1_struct_0(A_491)))
      | ~ l1_pre_topc(A_491)
      | ~ v2_pre_topc(A_491)
      | v2_struct_0(A_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_979,plain,(
    ! [B_490,C_492] :
      ( m1_connsp_2(B_490,'#skF_4',C_492)
      | ~ r2_hidden(C_492,B_490)
      | ~ v3_pre_topc(B_490,'#skF_4')
      | ~ m1_subset_1(C_492,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_490,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_977])).

tff(c_987,plain,(
    ! [B_490,C_492] :
      ( m1_connsp_2(B_490,'#skF_4',C_492)
      | ~ r2_hidden(C_492,B_490)
      | ~ v3_pre_topc(B_490,'#skF_4')
      | ~ m1_subset_1(C_492,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_490,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_143,c_151,c_979])).

tff(c_1223,plain,(
    ! [B_520,C_521] :
      ( m1_connsp_2(B_520,'#skF_4',C_521)
      | ~ r2_hidden(C_521,B_520)
      | ~ v3_pre_topc(B_520,'#skF_4')
      | ~ m1_subset_1(C_521,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_520,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_987])).

tff(c_3447,plain,(
    ! [B_629] :
      ( m1_connsp_2(B_629,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_629)
      | ~ v3_pre_topc(B_629,'#skF_4')
      | ~ m1_subset_1(B_629,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_160,c_1223])).

tff(c_3461,plain,
    ( m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6')
    | ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_83,c_3447])).

tff(c_3470,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1109,c_3461])).

tff(c_3471,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3470])).

tff(c_3483,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_3471])).

tff(c_3487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_143,c_3483])).

tff(c_3488,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3470])).

tff(c_3492,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_3488])).

tff(c_3495,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_3492])).

tff(c_3497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_3495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.30  % Computer   : n022.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % DateTime   : Tue Dec  1 16:26:40 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.48/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.04  
% 5.48/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.04  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.48/2.04  
% 5.48/2.04  %Foreground sorts:
% 5.48/2.04  
% 5.48/2.04  
% 5.48/2.04  %Background operators:
% 5.48/2.04  
% 5.48/2.04  
% 5.48/2.04  %Foreground operators:
% 5.48/2.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.48/2.04  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.48/2.04  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.48/2.04  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.48/2.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.48/2.04  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.48/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.48/2.04  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.48/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.48/2.04  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.48/2.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.48/2.04  tff('#skF_7', type, '#skF_7': $i).
% 5.48/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.48/2.04  tff('#skF_5', type, '#skF_5': $i).
% 5.48/2.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.48/2.04  tff('#skF_6', type, '#skF_6': $i).
% 5.48/2.04  tff('#skF_2', type, '#skF_2': $i).
% 5.48/2.04  tff('#skF_3', type, '#skF_3': $i).
% 5.48/2.04  tff('#skF_1', type, '#skF_1': $i).
% 5.48/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.48/2.04  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.48/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.48/2.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.48/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.48/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.48/2.04  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.48/2.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.48/2.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.48/2.04  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.48/2.04  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.48/2.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.48/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.48/2.04  
% 5.48/2.07  tff(f_245, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 5.48/2.07  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.48/2.07  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.48/2.07  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.48/2.07  tff(f_77, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.48/2.07  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.48/2.07  tff(f_54, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.48/2.07  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.48/2.07  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.48/2.07  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 5.48/2.07  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.48/2.07  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.48/2.07  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.48/2.07  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.48/2.07  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.48/2.07  tff(f_196, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 5.48/2.07  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 5.48/2.07  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_127, plain, (![B_425, A_426]: (l1_pre_topc(B_425) | ~m1_pre_topc(B_425, A_426) | ~l1_pre_topc(A_426))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.48/2.07  tff(c_136, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_127])).
% 5.48/2.07  tff(c_143, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_136])).
% 5.48/2.07  tff(c_18, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.48/2.07  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_104, plain, (![A_423]: (u1_struct_0(A_423)=k2_struct_0(A_423) | ~l1_struct_0(A_423))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.48/2.07  tff(c_108, plain, (![A_14]: (u1_struct_0(A_14)=k2_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_18, c_104])).
% 5.48/2.07  tff(c_151, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_143, c_108])).
% 5.48/2.07  tff(c_171, plain, (![A_429]: (~v1_xboole_0(u1_struct_0(A_429)) | ~l1_struct_0(A_429) | v2_struct_0(A_429))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.48/2.07  tff(c_174, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_151, c_171])).
% 5.48/2.07  tff(c_184, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_174])).
% 5.48/2.07  tff(c_188, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_184])).
% 5.48/2.07  tff(c_191, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_188])).
% 5.48/2.07  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_191])).
% 5.48/2.07  tff(c_196, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_184])).
% 5.48/2.07  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_160, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_52])).
% 5.48/2.07  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.48/2.07  tff(c_78, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_270, plain, (![B_436, A_437]: (v2_pre_topc(B_436) | ~m1_pre_topc(B_436, A_437) | ~l1_pre_topc(A_437) | ~v2_pre_topc(A_437))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.48/2.07  tff(c_279, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_270])).
% 5.48/2.07  tff(c_286, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_279])).
% 5.48/2.07  tff(c_30, plain, (![A_25]: (v3_pre_topc(k2_struct_0(A_25), A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.48/2.07  tff(c_36, plain, (![A_36]: (m1_pre_topc(A_36, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.48/2.07  tff(c_66, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_133, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_127])).
% 5.48/2.07  tff(c_140, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_133])).
% 5.48/2.07  tff(c_147, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_140, c_108])).
% 5.48/2.07  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_152, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_147, c_54])).
% 5.48/2.07  tff(c_673, plain, (![B_469, A_470]: (m1_pre_topc(B_469, A_470) | ~m1_pre_topc(B_469, g1_pre_topc(u1_struct_0(A_470), u1_pre_topc(A_470))) | ~l1_pre_topc(A_470))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.48/2.07  tff(c_679, plain, (![B_469]: (m1_pre_topc(B_469, '#skF_3') | ~m1_pre_topc(B_469, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_673])).
% 5.48/2.07  tff(c_693, plain, (![B_469]: (m1_pre_topc(B_469, '#skF_3') | ~m1_pre_topc(B_469, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_152, c_679])).
% 5.48/2.07  tff(c_307, plain, (![B_447, A_448]: (m1_subset_1(u1_struct_0(B_447), k1_zfmisc_1(u1_struct_0(A_448))) | ~m1_pre_topc(B_447, A_448) | ~l1_pre_topc(A_448))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.48/2.07  tff(c_324, plain, (![B_447]: (m1_subset_1(u1_struct_0(B_447), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_447, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_307])).
% 5.48/2.07  tff(c_956, plain, (![B_489]: (m1_subset_1(u1_struct_0(B_489), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_489, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_324])).
% 5.48/2.07  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.48/2.07  tff(c_998, plain, (![B_493]: (r1_tarski(u1_struct_0(B_493), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_493, '#skF_3'))), inference(resolution, [status(thm)], [c_956, c_8])).
% 5.48/2.07  tff(c_1001, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_151, c_998])).
% 5.48/2.07  tff(c_1012, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1001])).
% 5.48/2.07  tff(c_1016, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_693, c_1012])).
% 5.48/2.07  tff(c_1023, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1016])).
% 5.48/2.07  tff(c_1027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_1023])).
% 5.48/2.07  tff(c_1028, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1001])).
% 5.48/2.07  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.48/2.07  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.48/2.07  tff(c_83, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 5.48/2.07  tff(c_80, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_44, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_109, plain, (![A_424]: (u1_struct_0(A_424)=k2_struct_0(A_424) | ~l1_pre_topc(A_424))), inference(resolution, [status(thm)], [c_18, c_104])).
% 5.48/2.07  tff(c_116, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_109])).
% 5.48/2.07  tff(c_58, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_118, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_58])).
% 5.48/2.07  tff(c_169, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_118])).
% 5.48/2.07  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_158, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_56])).
% 5.48/2.07  tff(c_159, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_158])).
% 5.48/2.07  tff(c_318, plain, (![B_447]: (m1_subset_1(u1_struct_0(B_447), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_447, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_307])).
% 5.48/2.07  tff(c_347, plain, (![B_449]: (m1_subset_1(u1_struct_0(B_449), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_449, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_318])).
% 5.48/2.07  tff(c_368, plain, (![B_450]: (r1_tarski(u1_struct_0(B_450), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_450, '#skF_4'))), inference(resolution, [status(thm)], [c_347, c_8])).
% 5.48/2.07  tff(c_374, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_147, c_368])).
% 5.48/2.07  tff(c_382, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_374])).
% 5.48/2.07  tff(c_567, plain, (![A_465, B_466]: (m1_pre_topc(A_465, g1_pre_topc(u1_struct_0(B_466), u1_pre_topc(B_466))) | ~m1_pre_topc(A_465, B_466) | ~l1_pre_topc(B_466) | ~l1_pre_topc(A_465))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.48/2.07  tff(c_584, plain, (![A_465]: (m1_pre_topc(A_465, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_465, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_465))), inference(superposition, [status(thm), theory('equality')], [c_147, c_567])).
% 5.48/2.07  tff(c_603, plain, (![A_467]: (m1_pre_topc(A_467, '#skF_4') | ~m1_pre_topc(A_467, '#skF_3') | ~l1_pre_topc(A_467))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_152, c_584])).
% 5.48/2.07  tff(c_614, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_603])).
% 5.48/2.07  tff(c_622, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_614])).
% 5.48/2.07  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_382, c_622])).
% 5.48/2.07  tff(c_626, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_374])).
% 5.48/2.07  tff(c_48, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_81, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50])).
% 5.48/2.07  tff(c_153, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_81])).
% 5.48/2.07  tff(c_46, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_245])).
% 5.48/2.07  tff(c_82, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 5.48/2.07  tff(c_1077, plain, (![D_497, F_496, E_498, C_501, A_500, B_502, H_499]: (r1_tmap_1(D_497, B_502, E_498, H_499) | ~r1_tmap_1(C_501, B_502, k3_tmap_1(A_500, B_502, D_497, C_501, E_498), H_499) | ~m1_connsp_2(F_496, D_497, H_499) | ~r1_tarski(F_496, u1_struct_0(C_501)) | ~m1_subset_1(H_499, u1_struct_0(C_501)) | ~m1_subset_1(H_499, u1_struct_0(D_497)) | ~m1_subset_1(F_496, k1_zfmisc_1(u1_struct_0(D_497))) | ~m1_pre_topc(C_501, D_497) | ~m1_subset_1(E_498, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_497), u1_struct_0(B_502)))) | ~v1_funct_2(E_498, u1_struct_0(D_497), u1_struct_0(B_502)) | ~v1_funct_1(E_498) | ~m1_pre_topc(D_497, A_500) | v2_struct_0(D_497) | ~m1_pre_topc(C_501, A_500) | v2_struct_0(C_501) | ~l1_pre_topc(B_502) | ~v2_pre_topc(B_502) | v2_struct_0(B_502) | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.48/2.07  tff(c_1079, plain, (![F_496]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_496, '#skF_4', '#skF_6') | ~r1_tarski(F_496, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_496, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_82, c_1077])).
% 5.48/2.07  tff(c_1082, plain, (![F_496]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_496, '#skF_4', '#skF_6') | ~r1_tarski(F_496, k2_struct_0('#skF_3')) | ~m1_subset_1(F_496, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_66, c_62, c_60, c_169, c_116, c_151, c_159, c_116, c_151, c_626, c_151, c_160, c_151, c_153, c_147, c_147, c_1079])).
% 5.48/2.07  tff(c_1093, plain, (![F_503]: (~m1_connsp_2(F_503, '#skF_4', '#skF_6') | ~r1_tarski(F_503, k2_struct_0('#skF_3')) | ~m1_subset_1(F_503, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_68, c_64, c_44, c_1082])).
% 5.48/2.07  tff(c_1104, plain, (~m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_83, c_1093])).
% 5.48/2.07  tff(c_1109, plain, (~m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_1104])).
% 5.48/2.07  tff(c_977, plain, (![B_490, A_491, C_492]: (m1_connsp_2(B_490, A_491, C_492) | ~r2_hidden(C_492, B_490) | ~v3_pre_topc(B_490, A_491) | ~m1_subset_1(C_492, u1_struct_0(A_491)) | ~m1_subset_1(B_490, k1_zfmisc_1(u1_struct_0(A_491))) | ~l1_pre_topc(A_491) | ~v2_pre_topc(A_491) | v2_struct_0(A_491))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.48/2.07  tff(c_979, plain, (![B_490, C_492]: (m1_connsp_2(B_490, '#skF_4', C_492) | ~r2_hidden(C_492, B_490) | ~v3_pre_topc(B_490, '#skF_4') | ~m1_subset_1(C_492, k2_struct_0('#skF_4')) | ~m1_subset_1(B_490, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_977])).
% 5.48/2.07  tff(c_987, plain, (![B_490, C_492]: (m1_connsp_2(B_490, '#skF_4', C_492) | ~r2_hidden(C_492, B_490) | ~v3_pre_topc(B_490, '#skF_4') | ~m1_subset_1(C_492, k2_struct_0('#skF_4')) | ~m1_subset_1(B_490, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_286, c_143, c_151, c_979])).
% 5.48/2.07  tff(c_1223, plain, (![B_520, C_521]: (m1_connsp_2(B_520, '#skF_4', C_521) | ~r2_hidden(C_521, B_520) | ~v3_pre_topc(B_520, '#skF_4') | ~m1_subset_1(C_521, k2_struct_0('#skF_4')) | ~m1_subset_1(B_520, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_987])).
% 5.48/2.07  tff(c_3447, plain, (![B_629]: (m1_connsp_2(B_629, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', B_629) | ~v3_pre_topc(B_629, '#skF_4') | ~m1_subset_1(B_629, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_160, c_1223])).
% 5.48/2.07  tff(c_3461, plain, (m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_83, c_3447])).
% 5.48/2.07  tff(c_3470, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1109, c_3461])).
% 5.48/2.07  tff(c_3471, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_3470])).
% 5.48/2.07  tff(c_3483, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_3471])).
% 5.48/2.07  tff(c_3487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_286, c_143, c_3483])).
% 5.48/2.07  tff(c_3488, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_3470])).
% 5.48/2.07  tff(c_3492, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_3488])).
% 5.48/2.07  tff(c_3495, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_3492])).
% 5.48/2.07  tff(c_3497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_3495])).
% 5.48/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.07  
% 5.48/2.07  Inference rules
% 5.48/2.07  ----------------------
% 5.48/2.07  #Ref     : 0
% 5.48/2.07  #Sup     : 693
% 5.48/2.07  #Fact    : 0
% 5.48/2.07  #Define  : 0
% 5.48/2.07  #Split   : 28
% 5.48/2.07  #Chain   : 0
% 5.48/2.07  #Close   : 0
% 5.48/2.07  
% 5.48/2.07  Ordering : KBO
% 5.48/2.07  
% 5.48/2.07  Simplification rules
% 5.48/2.07  ----------------------
% 5.48/2.07  #Subsume      : 242
% 5.48/2.07  #Demod        : 779
% 5.48/2.07  #Tautology    : 172
% 5.48/2.07  #SimpNegUnit  : 80
% 5.48/2.07  #BackRed      : 5
% 5.48/2.07  
% 5.48/2.07  #Partial instantiations: 0
% 5.48/2.07  #Strategies tried      : 1
% 5.48/2.07  
% 5.48/2.07  Timing (in seconds)
% 5.48/2.07  ----------------------
% 5.48/2.07  Preprocessing        : 0.41
% 5.48/2.07  Parsing              : 0.21
% 5.48/2.07  CNF conversion       : 0.05
% 5.48/2.07  Main loop            : 0.85
% 5.48/2.07  Inferencing          : 0.27
% 5.48/2.07  Reduction            : 0.32
% 5.48/2.07  Demodulation         : 0.22
% 5.48/2.07  BG Simplification    : 0.03
% 5.48/2.07  Subsumption          : 0.17
% 5.48/2.07  Abstraction          : 0.03
% 5.48/2.07  MUC search           : 0.00
% 5.48/2.07  Cooper               : 0.00
% 5.48/2.07  Total                : 1.32
% 5.48/2.07  Index Insertion      : 0.00
% 5.48/2.07  Index Deletion       : 0.00
% 5.48/2.07  Index Matching       : 0.00
% 5.48/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
