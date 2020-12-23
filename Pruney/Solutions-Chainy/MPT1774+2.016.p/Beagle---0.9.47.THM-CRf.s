%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:26 EST 2020

% Result     : Theorem 4.31s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 225 expanded)
%              Number of leaves         :   34 ( 101 expanded)
%              Depth                    :   11
%              Number of atoms          :  329 (1846 expanded)
%              Number of equality atoms :    6 (  77 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_255,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_169,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_197,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ( ( v3_pre_topc(C,A)
                          & r1_tarski(C,u1_struct_0(B))
                          & r1_tarski(D,C)
                          & D = E )
                       => ( v3_pre_topc(E,B)
                        <=> v3_pre_topc(D,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tsep_1)).

tff(f_112,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_28,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_79,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_32,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_80,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_30,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_97,plain,(
    ! [B_687,A_688] :
      ( l1_pre_topc(B_687)
      | ~ m1_pre_topc(B_687,A_688)
      | ~ l1_pre_topc(A_688) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_103,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_97])).

tff(c_112,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_103])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_161,plain,(
    ! [C_697,A_698,B_699] :
      ( m1_subset_1(C_697,k1_zfmisc_1(u1_struct_0(A_698)))
      | ~ m1_subset_1(C_697,k1_zfmisc_1(u1_struct_0(B_699)))
      | ~ m1_pre_topc(B_699,A_698)
      | ~ l1_pre_topc(A_698) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_183,plain,(
    ! [A_703,A_704,B_705] :
      ( m1_subset_1(A_703,k1_zfmisc_1(u1_struct_0(A_704)))
      | ~ m1_pre_topc(B_705,A_704)
      | ~ l1_pre_topc(A_704)
      | ~ r1_tarski(A_703,u1_struct_0(B_705)) ) ),
    inference(resolution,[status(thm)],[c_10,c_161])).

tff(c_191,plain,(
    ! [A_703] :
      ( m1_subset_1(A_703,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_703,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_42,c_183])).

tff(c_201,plain,(
    ! [A_703] :
      ( m1_subset_1(A_703,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_703,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_191])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_78,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_70])).

tff(c_159,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_46,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_77,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_76])).

tff(c_177,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_77])).

tff(c_725,plain,(
    ! [A_757,F_758,H_761,C_760,D_759,B_755,E_756] :
      ( r1_tmap_1(D_759,B_755,E_756,H_761)
      | ~ r1_tmap_1(C_760,B_755,k3_tmap_1(A_757,B_755,D_759,C_760,E_756),H_761)
      | ~ r1_tarski(F_758,u1_struct_0(C_760))
      | ~ r2_hidden(H_761,F_758)
      | ~ v3_pre_topc(F_758,D_759)
      | ~ m1_subset_1(H_761,u1_struct_0(C_760))
      | ~ m1_subset_1(H_761,u1_struct_0(D_759))
      | ~ m1_subset_1(F_758,k1_zfmisc_1(u1_struct_0(D_759)))
      | ~ m1_pre_topc(C_760,D_759)
      | ~ m1_subset_1(E_756,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_759),u1_struct_0(B_755))))
      | ~ v1_funct_2(E_756,u1_struct_0(D_759),u1_struct_0(B_755))
      | ~ v1_funct_1(E_756)
      | ~ m1_pre_topc(D_759,A_757)
      | v2_struct_0(D_759)
      | ~ m1_pre_topc(C_760,A_757)
      | v2_struct_0(C_760)
      | ~ l1_pre_topc(B_755)
      | ~ v2_pre_topc(B_755)
      | v2_struct_0(B_755)
      | ~ l1_pre_topc(A_757)
      | ~ v2_pre_topc(A_757)
      | v2_struct_0(A_757) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_729,plain,(
    ! [F_758] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_758,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_758)
      | ~ v3_pre_topc(F_758,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_758,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_177,c_725])).

tff(c_736,plain,(
    ! [F_758] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_758,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_758)
      | ~ v3_pre_topc(F_758,'#skF_4')
      | ~ m1_subset_1(F_758,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_66,c_64,c_54,c_50,c_48,c_46,c_44,c_42,c_79,c_36,c_729])).

tff(c_738,plain,(
    ! [F_762] :
      ( ~ r1_tarski(F_762,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_762)
      | ~ v3_pre_topc(F_762,'#skF_4')
      | ~ m1_subset_1(F_762,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_56,c_52,c_159,c_736])).

tff(c_777,plain,(
    ! [A_763] :
      ( ~ r2_hidden('#skF_8',A_763)
      | ~ v3_pre_topc(A_763,'#skF_4')
      | ~ r1_tarski(A_763,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_201,c_738])).

tff(c_800,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_777])).

tff(c_822,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_800])).

tff(c_214,plain,(
    ! [A_708] :
      ( m1_subset_1(A_708,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_708,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_191])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_222,plain,(
    ! [A_709] :
      ( r1_tarski(A_709,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_709,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_214,c_8])).

tff(c_237,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_222])).

tff(c_34,plain,(
    v3_pre_topc('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_324,plain,(
    ! [E_719,B_720,A_721,C_722] :
      ( v3_pre_topc(E_719,B_720)
      | ~ v3_pre_topc(E_719,A_721)
      | ~ r1_tarski(E_719,C_722)
      | ~ r1_tarski(C_722,u1_struct_0(B_720))
      | ~ v3_pre_topc(C_722,A_721)
      | ~ m1_subset_1(E_719,k1_zfmisc_1(u1_struct_0(B_720)))
      | ~ m1_subset_1(E_719,k1_zfmisc_1(u1_struct_0(A_721)))
      | ~ m1_subset_1(C_722,k1_zfmisc_1(u1_struct_0(A_721)))
      | ~ m1_pre_topc(B_720,A_721)
      | ~ l1_pre_topc(A_721)
      | ~ v2_pre_topc(A_721) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_825,plain,(
    ! [B_764,B_765,A_766] :
      ( v3_pre_topc(B_764,B_765)
      | ~ r1_tarski(B_764,u1_struct_0(B_765))
      | ~ v3_pre_topc(B_764,A_766)
      | ~ m1_subset_1(B_764,k1_zfmisc_1(u1_struct_0(B_765)))
      | ~ m1_subset_1(B_764,k1_zfmisc_1(u1_struct_0(A_766)))
      | ~ m1_pre_topc(B_765,A_766)
      | ~ l1_pre_topc(A_766)
      | ~ v2_pre_topc(A_766) ) ),
    inference(resolution,[status(thm)],[c_6,c_324])).

tff(c_972,plain,(
    ! [A_786,B_787,A_788] :
      ( v3_pre_topc(A_786,B_787)
      | ~ v3_pre_topc(A_786,A_788)
      | ~ m1_subset_1(A_786,k1_zfmisc_1(u1_struct_0(A_788)))
      | ~ m1_pre_topc(B_787,A_788)
      | ~ l1_pre_topc(A_788)
      | ~ v2_pre_topc(A_788)
      | ~ r1_tarski(A_786,u1_struct_0(B_787)) ) ),
    inference(resolution,[status(thm)],[c_10,c_825])).

tff(c_991,plain,(
    ! [B_787] :
      ( v3_pre_topc('#skF_6',B_787)
      | ~ v3_pre_topc('#skF_6','#skF_2')
      | ~ m1_pre_topc(B_787,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski('#skF_6',u1_struct_0(B_787)) ) ),
    inference(resolution,[status(thm)],[c_40,c_972])).

tff(c_1009,plain,(
    ! [B_789] :
      ( v3_pre_topc('#skF_6',B_789)
      | ~ m1_pre_topc(B_789,'#skF_2')
      | ~ r1_tarski('#skF_6',u1_struct_0(B_789)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_34,c_991])).

tff(c_1019,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_237,c_1009])).

tff(c_1039,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1019])).

tff(c_1041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_822,c_1039])).

tff(c_1043,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1305,plain,(
    ! [D_823,E_827,G_828,A_825,B_824,C_826] :
      ( r1_tmap_1(D_823,B_824,k3_tmap_1(A_825,B_824,C_826,D_823,E_827),G_828)
      | ~ r1_tmap_1(C_826,B_824,E_827,G_828)
      | ~ m1_pre_topc(D_823,C_826)
      | ~ m1_subset_1(G_828,u1_struct_0(D_823))
      | ~ m1_subset_1(G_828,u1_struct_0(C_826))
      | ~ m1_subset_1(E_827,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_826),u1_struct_0(B_824))))
      | ~ v1_funct_2(E_827,u1_struct_0(C_826),u1_struct_0(B_824))
      | ~ v1_funct_1(E_827)
      | ~ m1_pre_topc(D_823,A_825)
      | v2_struct_0(D_823)
      | ~ m1_pre_topc(C_826,A_825)
      | v2_struct_0(C_826)
      | ~ l1_pre_topc(B_824)
      | ~ v2_pre_topc(B_824)
      | v2_struct_0(B_824)
      | ~ l1_pre_topc(A_825)
      | ~ v2_pre_topc(A_825)
      | v2_struct_0(A_825) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1307,plain,(
    ! [D_823,A_825,G_828] :
      ( r1_tmap_1(D_823,'#skF_1',k3_tmap_1(A_825,'#skF_1','#skF_4',D_823,'#skF_5'),G_828)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_828)
      | ~ m1_pre_topc(D_823,'#skF_4')
      | ~ m1_subset_1(G_828,u1_struct_0(D_823))
      | ~ m1_subset_1(G_828,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_823,A_825)
      | v2_struct_0(D_823)
      | ~ m1_pre_topc('#skF_4',A_825)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_825)
      | ~ v2_pre_topc(A_825)
      | v2_struct_0(A_825) ) ),
    inference(resolution,[status(thm)],[c_44,c_1305])).

tff(c_1313,plain,(
    ! [D_823,A_825,G_828] :
      ( r1_tmap_1(D_823,'#skF_1',k3_tmap_1(A_825,'#skF_1','#skF_4',D_823,'#skF_5'),G_828)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_828)
      | ~ m1_pre_topc(D_823,'#skF_4')
      | ~ m1_subset_1(G_828,u1_struct_0(D_823))
      | ~ m1_subset_1(G_828,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_823,A_825)
      | v2_struct_0(D_823)
      | ~ m1_pre_topc('#skF_4',A_825)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_825)
      | ~ v2_pre_topc(A_825)
      | v2_struct_0(A_825) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_46,c_1307])).

tff(c_1367,plain,(
    ! [D_834,A_835,G_836] :
      ( r1_tmap_1(D_834,'#skF_1',k3_tmap_1(A_835,'#skF_1','#skF_4',D_834,'#skF_5'),G_836)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_836)
      | ~ m1_pre_topc(D_834,'#skF_4')
      | ~ m1_subset_1(G_836,u1_struct_0(D_834))
      | ~ m1_subset_1(G_836,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_834,A_835)
      | v2_struct_0(D_834)
      | ~ m1_pre_topc('#skF_4',A_835)
      | ~ l1_pre_topc(A_835)
      | ~ v2_pre_topc(A_835)
      | v2_struct_0(A_835) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_52,c_1313])).

tff(c_1042,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1044,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_1045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1042,c_1044])).

tff(c_1047,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_1370,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1367,c_1047])).

tff(c_1373,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_54,c_79,c_36,c_42,c_1043,c_1370])).

tff(c_1375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_1373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.31/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.31/1.81  
% 4.31/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.31/1.81  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.31/1.81  
% 4.31/1.81  %Foreground sorts:
% 4.31/1.81  
% 4.31/1.81  
% 4.31/1.81  %Background operators:
% 4.31/1.81  
% 4.31/1.81  
% 4.31/1.81  %Foreground operators:
% 4.31/1.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.31/1.81  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.31/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.31/1.81  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.31/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.31/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.31/1.81  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.31/1.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.31/1.81  tff('#skF_7', type, '#skF_7': $i).
% 4.31/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.31/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.31/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.31/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.31/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.31/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.31/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.31/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.31/1.81  tff('#skF_8', type, '#skF_8': $i).
% 4.31/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.31/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.31/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.31/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.31/1.81  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.31/1.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.31/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.31/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.31/1.81  
% 4.52/1.84  tff(f_255, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tmap_1)).
% 4.52/1.84  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.52/1.84  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.52/1.84  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 4.52/1.84  tff(f_169, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.52/1.84  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.52/1.84  tff(f_197, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => ((((v3_pre_topc(C, A) & r1_tarski(C, u1_struct_0(B))) & r1_tarski(D, C)) & (D = E)) => (v3_pre_topc(E, B) <=> v3_pre_topc(D, A))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tsep_1)).
% 4.52/1.84  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.52/1.84  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_28, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_38, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_79, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 4.52/1.84  tff(c_36, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_32, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_80, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 4.52/1.84  tff(c_30, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_97, plain, (![B_687, A_688]: (l1_pre_topc(B_687) | ~m1_pre_topc(B_687, A_688) | ~l1_pre_topc(A_688))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.52/1.84  tff(c_103, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_97])).
% 4.52/1.84  tff(c_112, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_103])).
% 4.52/1.84  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.84  tff(c_161, plain, (![C_697, A_698, B_699]: (m1_subset_1(C_697, k1_zfmisc_1(u1_struct_0(A_698))) | ~m1_subset_1(C_697, k1_zfmisc_1(u1_struct_0(B_699))) | ~m1_pre_topc(B_699, A_698) | ~l1_pre_topc(A_698))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.52/1.84  tff(c_183, plain, (![A_703, A_704, B_705]: (m1_subset_1(A_703, k1_zfmisc_1(u1_struct_0(A_704))) | ~m1_pre_topc(B_705, A_704) | ~l1_pre_topc(A_704) | ~r1_tarski(A_703, u1_struct_0(B_705)))), inference(resolution, [status(thm)], [c_10, c_161])).
% 4.52/1.84  tff(c_191, plain, (![A_703]: (m1_subset_1(A_703, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_703, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_42, c_183])).
% 4.52/1.84  tff(c_201, plain, (![A_703]: (m1_subset_1(A_703, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_703, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_191])).
% 4.52/1.84  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_70, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_78, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_70])).
% 4.52/1.84  tff(c_159, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_78])).
% 4.52/1.84  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_46, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_76, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_77, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_76])).
% 4.52/1.84  tff(c_177, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_159, c_77])).
% 4.52/1.84  tff(c_725, plain, (![A_757, F_758, H_761, C_760, D_759, B_755, E_756]: (r1_tmap_1(D_759, B_755, E_756, H_761) | ~r1_tmap_1(C_760, B_755, k3_tmap_1(A_757, B_755, D_759, C_760, E_756), H_761) | ~r1_tarski(F_758, u1_struct_0(C_760)) | ~r2_hidden(H_761, F_758) | ~v3_pre_topc(F_758, D_759) | ~m1_subset_1(H_761, u1_struct_0(C_760)) | ~m1_subset_1(H_761, u1_struct_0(D_759)) | ~m1_subset_1(F_758, k1_zfmisc_1(u1_struct_0(D_759))) | ~m1_pre_topc(C_760, D_759) | ~m1_subset_1(E_756, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_759), u1_struct_0(B_755)))) | ~v1_funct_2(E_756, u1_struct_0(D_759), u1_struct_0(B_755)) | ~v1_funct_1(E_756) | ~m1_pre_topc(D_759, A_757) | v2_struct_0(D_759) | ~m1_pre_topc(C_760, A_757) | v2_struct_0(C_760) | ~l1_pre_topc(B_755) | ~v2_pre_topc(B_755) | v2_struct_0(B_755) | ~l1_pre_topc(A_757) | ~v2_pre_topc(A_757) | v2_struct_0(A_757))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.52/1.84  tff(c_729, plain, (![F_758]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(F_758, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_758) | ~v3_pre_topc(F_758, '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(F_758, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_177, c_725])).
% 4.52/1.84  tff(c_736, plain, (![F_758]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(F_758, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_758) | ~v3_pre_topc(F_758, '#skF_4') | ~m1_subset_1(F_758, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_66, c_64, c_54, c_50, c_48, c_46, c_44, c_42, c_79, c_36, c_729])).
% 4.52/1.84  tff(c_738, plain, (![F_762]: (~r1_tarski(F_762, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_762) | ~v3_pre_topc(F_762, '#skF_4') | ~m1_subset_1(F_762, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_56, c_52, c_159, c_736])).
% 4.52/1.84  tff(c_777, plain, (![A_763]: (~r2_hidden('#skF_8', A_763) | ~v3_pre_topc(A_763, '#skF_4') | ~r1_tarski(A_763, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_201, c_738])).
% 4.52/1.84  tff(c_800, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_777])).
% 4.52/1.84  tff(c_822, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_800])).
% 4.52/1.84  tff(c_214, plain, (![A_708]: (m1_subset_1(A_708, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_708, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_191])).
% 4.52/1.84  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.84  tff(c_222, plain, (![A_709]: (r1_tarski(A_709, u1_struct_0('#skF_4')) | ~r1_tarski(A_709, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_214, c_8])).
% 4.52/1.84  tff(c_237, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_222])).
% 4.52/1.84  tff(c_34, plain, (v3_pre_topc('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_255])).
% 4.52/1.84  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.52/1.84  tff(c_324, plain, (![E_719, B_720, A_721, C_722]: (v3_pre_topc(E_719, B_720) | ~v3_pre_topc(E_719, A_721) | ~r1_tarski(E_719, C_722) | ~r1_tarski(C_722, u1_struct_0(B_720)) | ~v3_pre_topc(C_722, A_721) | ~m1_subset_1(E_719, k1_zfmisc_1(u1_struct_0(B_720))) | ~m1_subset_1(E_719, k1_zfmisc_1(u1_struct_0(A_721))) | ~m1_subset_1(C_722, k1_zfmisc_1(u1_struct_0(A_721))) | ~m1_pre_topc(B_720, A_721) | ~l1_pre_topc(A_721) | ~v2_pre_topc(A_721))), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.52/1.84  tff(c_825, plain, (![B_764, B_765, A_766]: (v3_pre_topc(B_764, B_765) | ~r1_tarski(B_764, u1_struct_0(B_765)) | ~v3_pre_topc(B_764, A_766) | ~m1_subset_1(B_764, k1_zfmisc_1(u1_struct_0(B_765))) | ~m1_subset_1(B_764, k1_zfmisc_1(u1_struct_0(A_766))) | ~m1_pre_topc(B_765, A_766) | ~l1_pre_topc(A_766) | ~v2_pre_topc(A_766))), inference(resolution, [status(thm)], [c_6, c_324])).
% 4.52/1.84  tff(c_972, plain, (![A_786, B_787, A_788]: (v3_pre_topc(A_786, B_787) | ~v3_pre_topc(A_786, A_788) | ~m1_subset_1(A_786, k1_zfmisc_1(u1_struct_0(A_788))) | ~m1_pre_topc(B_787, A_788) | ~l1_pre_topc(A_788) | ~v2_pre_topc(A_788) | ~r1_tarski(A_786, u1_struct_0(B_787)))), inference(resolution, [status(thm)], [c_10, c_825])).
% 4.52/1.84  tff(c_991, plain, (![B_787]: (v3_pre_topc('#skF_6', B_787) | ~v3_pre_topc('#skF_6', '#skF_2') | ~m1_pre_topc(B_787, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski('#skF_6', u1_struct_0(B_787)))), inference(resolution, [status(thm)], [c_40, c_972])).
% 4.52/1.84  tff(c_1009, plain, (![B_789]: (v3_pre_topc('#skF_6', B_789) | ~m1_pre_topc(B_789, '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0(B_789)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_34, c_991])).
% 4.52/1.84  tff(c_1019, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_237, c_1009])).
% 4.52/1.84  tff(c_1039, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1019])).
% 4.52/1.84  tff(c_1041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_822, c_1039])).
% 4.52/1.84  tff(c_1043, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 4.52/1.84  tff(c_1305, plain, (![D_823, E_827, G_828, A_825, B_824, C_826]: (r1_tmap_1(D_823, B_824, k3_tmap_1(A_825, B_824, C_826, D_823, E_827), G_828) | ~r1_tmap_1(C_826, B_824, E_827, G_828) | ~m1_pre_topc(D_823, C_826) | ~m1_subset_1(G_828, u1_struct_0(D_823)) | ~m1_subset_1(G_828, u1_struct_0(C_826)) | ~m1_subset_1(E_827, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_826), u1_struct_0(B_824)))) | ~v1_funct_2(E_827, u1_struct_0(C_826), u1_struct_0(B_824)) | ~v1_funct_1(E_827) | ~m1_pre_topc(D_823, A_825) | v2_struct_0(D_823) | ~m1_pre_topc(C_826, A_825) | v2_struct_0(C_826) | ~l1_pre_topc(B_824) | ~v2_pre_topc(B_824) | v2_struct_0(B_824) | ~l1_pre_topc(A_825) | ~v2_pre_topc(A_825) | v2_struct_0(A_825))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.52/1.84  tff(c_1307, plain, (![D_823, A_825, G_828]: (r1_tmap_1(D_823, '#skF_1', k3_tmap_1(A_825, '#skF_1', '#skF_4', D_823, '#skF_5'), G_828) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_828) | ~m1_pre_topc(D_823, '#skF_4') | ~m1_subset_1(G_828, u1_struct_0(D_823)) | ~m1_subset_1(G_828, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_823, A_825) | v2_struct_0(D_823) | ~m1_pre_topc('#skF_4', A_825) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_825) | ~v2_pre_topc(A_825) | v2_struct_0(A_825))), inference(resolution, [status(thm)], [c_44, c_1305])).
% 4.52/1.84  tff(c_1313, plain, (![D_823, A_825, G_828]: (r1_tmap_1(D_823, '#skF_1', k3_tmap_1(A_825, '#skF_1', '#skF_4', D_823, '#skF_5'), G_828) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_828) | ~m1_pre_topc(D_823, '#skF_4') | ~m1_subset_1(G_828, u1_struct_0(D_823)) | ~m1_subset_1(G_828, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_823, A_825) | v2_struct_0(D_823) | ~m1_pre_topc('#skF_4', A_825) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_825) | ~v2_pre_topc(A_825) | v2_struct_0(A_825))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_46, c_1307])).
% 4.52/1.84  tff(c_1367, plain, (![D_834, A_835, G_836]: (r1_tmap_1(D_834, '#skF_1', k3_tmap_1(A_835, '#skF_1', '#skF_4', D_834, '#skF_5'), G_836) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_836) | ~m1_pre_topc(D_834, '#skF_4') | ~m1_subset_1(G_836, u1_struct_0(D_834)) | ~m1_subset_1(G_836, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_834, A_835) | v2_struct_0(D_834) | ~m1_pre_topc('#skF_4', A_835) | ~l1_pre_topc(A_835) | ~v2_pre_topc(A_835) | v2_struct_0(A_835))), inference(negUnitSimplification, [status(thm)], [c_68, c_52, c_1313])).
% 4.52/1.84  tff(c_1042, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 4.52/1.84  tff(c_1044, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_77])).
% 4.52/1.84  tff(c_1045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1042, c_1044])).
% 4.52/1.84  tff(c_1047, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_77])).
% 4.52/1.84  tff(c_1370, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1367, c_1047])).
% 4.52/1.84  tff(c_1373, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_54, c_79, c_36, c_42, c_1043, c_1370])).
% 4.52/1.84  tff(c_1375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_1373])).
% 4.52/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.84  
% 4.52/1.84  Inference rules
% 4.52/1.84  ----------------------
% 4.52/1.84  #Ref     : 0
% 4.52/1.84  #Sup     : 272
% 4.52/1.84  #Fact    : 0
% 4.52/1.84  #Define  : 0
% 4.52/1.84  #Split   : 12
% 4.52/1.84  #Chain   : 0
% 4.52/1.84  #Close   : 0
% 4.52/1.84  
% 4.52/1.84  Ordering : KBO
% 4.52/1.84  
% 4.52/1.84  Simplification rules
% 4.52/1.84  ----------------------
% 4.52/1.84  #Subsume      : 63
% 4.52/1.84  #Demod        : 208
% 4.52/1.84  #Tautology    : 48
% 4.52/1.84  #SimpNegUnit  : 9
% 4.52/1.84  #BackRed      : 0
% 4.52/1.84  
% 4.52/1.84  #Partial instantiations: 0
% 4.52/1.84  #Strategies tried      : 1
% 4.52/1.84  
% 4.52/1.84  Timing (in seconds)
% 4.52/1.84  ----------------------
% 4.52/1.84  Preprocessing        : 0.42
% 4.52/1.84  Parsing              : 0.22
% 4.52/1.84  CNF conversion       : 0.07
% 4.52/1.84  Main loop            : 0.55
% 4.52/1.84  Inferencing          : 0.17
% 4.52/1.84  Reduction            : 0.19
% 4.52/1.84  Demodulation         : 0.14
% 4.52/1.84  BG Simplification    : 0.03
% 4.52/1.84  Subsumption          : 0.13
% 4.52/1.84  Abstraction          : 0.02
% 4.52/1.84  MUC search           : 0.00
% 4.52/1.84  Cooper               : 0.00
% 4.52/1.84  Total                : 1.01
% 4.52/1.84  Index Insertion      : 0.00
% 4.52/1.84  Index Deletion       : 0.00
% 4.52/1.84  Index Matching       : 0.00
% 4.52/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
