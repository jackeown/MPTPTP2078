%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:26 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 253 expanded)
%              Number of leaves         :   35 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          :  348 (1864 expanded)
%              Number of equality atoms :    5 (  71 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_242,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_184,axiom,(
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

tff(f_60,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_127,axiom,(
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
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_48,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_52,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_26,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_34,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_77,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_34])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_87,plain,(
    ! [B_667,A_668] :
      ( l1_pre_topc(B_667)
      | ~ m1_pre_topc(B_667,A_668)
      | ~ l1_pre_topc(A_668) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_87])).

tff(c_102,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_93])).

tff(c_117,plain,(
    ! [A_673,B_674] :
      ( r2_hidden('#skF_1'(A_673,B_674),A_673)
      | r1_tarski(A_673,B_674) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [A_673] : r1_tarski(A_673,A_673) ),
    inference(resolution,[status(thm)],[c_117,c_4])).

tff(c_175,plain,(
    ! [B_684,A_685] :
      ( m1_subset_1(u1_struct_0(B_684),k1_zfmisc_1(u1_struct_0(A_685)))
      | ~ m1_pre_topc(B_684,A_685)
      | ~ l1_pre_topc(A_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_179,plain,(
    ! [B_684,A_685] :
      ( r1_tarski(u1_struct_0(B_684),u1_struct_0(A_685))
      | ~ m1_pre_topc(B_684,A_685)
      | ~ l1_pre_topc(A_685) ) ),
    inference(resolution,[status(thm)],[c_175,c_8])).

tff(c_28,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,(
    ! [C_676,B_677,A_678] :
      ( r2_hidden(C_676,B_677)
      | ~ r2_hidden(C_676,A_678)
      | ~ r1_tarski(A_678,B_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_233,plain,(
    ! [A_696,B_697,B_698] :
      ( r2_hidden('#skF_1'(A_696,B_697),B_698)
      | ~ r1_tarski(A_696,B_698)
      | r1_tarski(A_696,B_697) ) ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_281,plain,(
    ! [A_708,B_709,B_710,B_711] :
      ( r2_hidden('#skF_1'(A_708,B_709),B_710)
      | ~ r1_tarski(B_711,B_710)
      | ~ r1_tarski(A_708,B_711)
      | r1_tarski(A_708,B_709) ) ),
    inference(resolution,[status(thm)],[c_233,c_2])).

tff(c_297,plain,(
    ! [A_712,B_713] :
      ( r2_hidden('#skF_1'(A_712,B_713),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_712,'#skF_7')
      | r1_tarski(A_712,B_713) ) ),
    inference(resolution,[status(thm)],[c_28,c_281])).

tff(c_561,plain,(
    ! [A_749,B_750,B_751] :
      ( r2_hidden('#skF_1'(A_749,B_750),B_751)
      | ~ r1_tarski(u1_struct_0('#skF_4'),B_751)
      | ~ r1_tarski(A_749,'#skF_7')
      | r1_tarski(A_749,B_750) ) ),
    inference(resolution,[status(thm)],[c_297,c_2])).

tff(c_570,plain,(
    ! [B_752,A_753] :
      ( ~ r1_tarski(u1_struct_0('#skF_4'),B_752)
      | ~ r1_tarski(A_753,'#skF_7')
      | r1_tarski(A_753,B_752) ) ),
    inference(resolution,[status(thm)],[c_561,c_4])).

tff(c_589,plain,(
    ! [A_753,A_685] :
      ( ~ r1_tarski(A_753,'#skF_7')
      | r1_tarski(A_753,u1_struct_0(A_685))
      | ~ m1_pre_topc('#skF_4',A_685)
      | ~ l1_pre_topc(A_685) ) ),
    inference(resolution,[status(thm)],[c_179,c_570])).

tff(c_30,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_610,plain,(
    ! [A_757,A_758] :
      ( ~ r1_tarski(A_757,'#skF_7')
      | r1_tarski(A_757,u1_struct_0(A_758))
      | ~ m1_pre_topc('#skF_4',A_758)
      | ~ l1_pre_topc(A_758) ) ),
    inference(resolution,[status(thm)],[c_179,c_570])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_74,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_75,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_74])).

tff(c_115,plain,(
    r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_68,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_68])).

tff(c_159,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_76])).

tff(c_64,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_44,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_493,plain,(
    ! [F_745,H_739,C_744,A_743,B_741,D_740,E_742] :
      ( r1_tmap_1(D_740,B_741,E_742,H_739)
      | ~ r1_tmap_1(C_744,B_741,k3_tmap_1(A_743,B_741,D_740,C_744,E_742),H_739)
      | ~ r1_tarski(F_745,u1_struct_0(C_744))
      | ~ r2_hidden(H_739,F_745)
      | ~ v3_pre_topc(F_745,D_740)
      | ~ m1_subset_1(H_739,u1_struct_0(C_744))
      | ~ m1_subset_1(H_739,u1_struct_0(D_740))
      | ~ m1_subset_1(F_745,k1_zfmisc_1(u1_struct_0(D_740)))
      | ~ m1_pre_topc(C_744,D_740)
      | ~ m1_subset_1(E_742,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_740),u1_struct_0(B_741))))
      | ~ v1_funct_2(E_742,u1_struct_0(D_740),u1_struct_0(B_741))
      | ~ v1_funct_1(E_742)
      | ~ m1_pre_topc(D_740,A_743)
      | v2_struct_0(D_740)
      | ~ m1_pre_topc(C_744,A_743)
      | v2_struct_0(C_744)
      | ~ l1_pre_topc(B_741)
      | ~ v2_pre_topc(B_741)
      | v2_struct_0(B_741)
      | ~ l1_pre_topc(A_743)
      | ~ v2_pre_topc(A_743)
      | v2_struct_0(A_743) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_497,plain,(
    ! [F_745] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ r1_tarski(F_745,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_745)
      | ~ v3_pre_topc(F_745,'#skF_5')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_745,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_115,c_493])).

tff(c_504,plain,(
    ! [F_745] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ r1_tarski(F_745,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_745)
      | ~ v3_pre_topc(F_745,'#skF_5')
      | ~ m1_subset_1(F_745,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_64,c_62,c_52,c_48,c_46,c_44,c_42,c_40,c_36,c_77,c_497])).

tff(c_534,plain,(
    ! [F_747] :
      ( ~ r1_tarski(F_747,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_747)
      | ~ v3_pre_topc(F_747,'#skF_5')
      | ~ m1_subset_1(F_747,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_66,c_54,c_50,c_159,c_504])).

tff(c_546,plain,(
    ! [A_6] :
      ( ~ r1_tarski(A_6,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',A_6)
      | ~ v3_pre_topc(A_6,'#skF_5')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_10,c_534])).

tff(c_617,plain,(
    ! [A_757] :
      ( ~ r1_tarski(A_757,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',A_757)
      | ~ v3_pre_topc(A_757,'#skF_5')
      | ~ r1_tarski(A_757,'#skF_7')
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_610,c_546])).

tff(c_666,plain,(
    ! [A_760] :
      ( ~ r1_tarski(A_760,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',A_760)
      | ~ v3_pre_topc(A_760,'#skF_5')
      | ~ r1_tarski(A_760,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_40,c_617])).

tff(c_684,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | ~ v3_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_666])).

tff(c_697,plain,(
    ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_30,c_684])).

tff(c_32,plain,(
    v3_pre_topc('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_252,plain,(
    ! [D_701,C_702,A_703] :
      ( v3_pre_topc(D_701,C_702)
      | ~ m1_subset_1(D_701,k1_zfmisc_1(u1_struct_0(C_702)))
      | ~ v3_pre_topc(D_701,A_703)
      | ~ m1_pre_topc(C_702,A_703)
      | ~ m1_subset_1(D_701,k1_zfmisc_1(u1_struct_0(A_703)))
      | ~ l1_pre_topc(A_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_591,plain,(
    ! [A_754,C_755,A_756] :
      ( v3_pre_topc(A_754,C_755)
      | ~ v3_pre_topc(A_754,A_756)
      | ~ m1_pre_topc(C_755,A_756)
      | ~ m1_subset_1(A_754,k1_zfmisc_1(u1_struct_0(A_756)))
      | ~ l1_pre_topc(A_756)
      | ~ r1_tarski(A_754,u1_struct_0(C_755)) ) ),
    inference(resolution,[status(thm)],[c_10,c_252])).

tff(c_597,plain,(
    ! [A_754] :
      ( v3_pre_topc(A_754,'#skF_5')
      | ~ v3_pre_topc(A_754,'#skF_3')
      | ~ m1_subset_1(A_754,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_754,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_48,c_591])).

tff(c_911,plain,(
    ! [A_783] :
      ( v3_pre_topc(A_783,'#skF_5')
      | ~ v3_pre_topc(A_783,'#skF_3')
      | ~ m1_subset_1(A_783,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_783,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_597])).

tff(c_922,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ v3_pre_topc('#skF_7','#skF_3')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_911])).

tff(c_929,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_922])).

tff(c_930,plain,(
    ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_697,c_929])).

tff(c_958,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_589,c_930])).

tff(c_962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_40,c_122,c_958])).

tff(c_963,plain,(
    r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_1287,plain,(
    ! [C_841,D_842,E_845,B_843,G_846,A_844] :
      ( r1_tmap_1(D_842,B_843,k3_tmap_1(A_844,B_843,C_841,D_842,E_845),G_846)
      | ~ r1_tmap_1(C_841,B_843,E_845,G_846)
      | ~ m1_pre_topc(D_842,C_841)
      | ~ m1_subset_1(G_846,u1_struct_0(D_842))
      | ~ m1_subset_1(G_846,u1_struct_0(C_841))
      | ~ m1_subset_1(E_845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_841),u1_struct_0(B_843))))
      | ~ v1_funct_2(E_845,u1_struct_0(C_841),u1_struct_0(B_843))
      | ~ v1_funct_1(E_845)
      | ~ m1_pre_topc(D_842,A_844)
      | v2_struct_0(D_842)
      | ~ m1_pre_topc(C_841,A_844)
      | v2_struct_0(C_841)
      | ~ l1_pre_topc(B_843)
      | ~ v2_pre_topc(B_843)
      | v2_struct_0(B_843)
      | ~ l1_pre_topc(A_844)
      | ~ v2_pre_topc(A_844)
      | v2_struct_0(A_844) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1289,plain,(
    ! [D_842,A_844,G_846] :
      ( r1_tmap_1(D_842,'#skF_2',k3_tmap_1(A_844,'#skF_2','#skF_5',D_842,'#skF_6'),G_846)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_846)
      | ~ m1_pre_topc(D_842,'#skF_5')
      | ~ m1_subset_1(G_846,u1_struct_0(D_842))
      | ~ m1_subset_1(G_846,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_842,A_844)
      | v2_struct_0(D_842)
      | ~ m1_pre_topc('#skF_5',A_844)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_844)
      | ~ v2_pre_topc(A_844)
      | v2_struct_0(A_844) ) ),
    inference(resolution,[status(thm)],[c_42,c_1287])).

tff(c_1295,plain,(
    ! [D_842,A_844,G_846] :
      ( r1_tmap_1(D_842,'#skF_2',k3_tmap_1(A_844,'#skF_2','#skF_5',D_842,'#skF_6'),G_846)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_846)
      | ~ m1_pre_topc(D_842,'#skF_5')
      | ~ m1_subset_1(G_846,u1_struct_0(D_842))
      | ~ m1_subset_1(G_846,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_842,A_844)
      | v2_struct_0(D_842)
      | ~ m1_pre_topc('#skF_5',A_844)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_844)
      | ~ v2_pre_topc(A_844)
      | v2_struct_0(A_844) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_46,c_44,c_1289])).

tff(c_1340,plain,(
    ! [D_850,A_851,G_852] :
      ( r1_tmap_1(D_850,'#skF_2',k3_tmap_1(A_851,'#skF_2','#skF_5',D_850,'#skF_6'),G_852)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_852)
      | ~ m1_pre_topc(D_850,'#skF_5')
      | ~ m1_subset_1(G_852,u1_struct_0(D_850))
      | ~ m1_subset_1(G_852,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_850,A_851)
      | v2_struct_0(D_850)
      | ~ m1_pre_topc('#skF_5',A_851)
      | ~ l1_pre_topc(A_851)
      | ~ v2_pre_topc(A_851)
      | v2_struct_0(A_851) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_50,c_1295])).

tff(c_967,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_963,c_76])).

tff(c_1343,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1340,c_967])).

tff(c_1346,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_48,c_52,c_36,c_77,c_40,c_963,c_1343])).

tff(c_1348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_1346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:45:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.77/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.81  
% 4.77/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.81  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 4.77/1.81  
% 4.77/1.81  %Foreground sorts:
% 4.77/1.81  
% 4.77/1.81  
% 4.77/1.81  %Background operators:
% 4.77/1.81  
% 4.77/1.81  
% 4.77/1.81  %Foreground operators:
% 4.77/1.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.77/1.81  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.77/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.77/1.81  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.77/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.77/1.81  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.77/1.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.77/1.81  tff('#skF_7', type, '#skF_7': $i).
% 4.77/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.77/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.77/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.77/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.77/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.77/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.77/1.81  tff('#skF_9', type, '#skF_9': $i).
% 4.77/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.77/1.81  tff('#skF_8', type, '#skF_8': $i).
% 4.77/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.77/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.77/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/1.81  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.77/1.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.77/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.77/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.77/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.77/1.81  
% 4.97/1.84  tff(f_242, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 4.97/1.84  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.97/1.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.97/1.84  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.97/1.84  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.97/1.84  tff(f_184, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.97/1.84  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 4.97/1.84  tff(f_127, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.97/1.84  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_48, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_52, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_36, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_26, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_34, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_77, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_34])).
% 4.97/1.84  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_87, plain, (![B_667, A_668]: (l1_pre_topc(B_667) | ~m1_pre_topc(B_667, A_668) | ~l1_pre_topc(A_668))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.97/1.84  tff(c_93, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_87])).
% 4.97/1.84  tff(c_102, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_93])).
% 4.97/1.84  tff(c_117, plain, (![A_673, B_674]: (r2_hidden('#skF_1'(A_673, B_674), A_673) | r1_tarski(A_673, B_674))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.97/1.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.97/1.84  tff(c_122, plain, (![A_673]: (r1_tarski(A_673, A_673))), inference(resolution, [status(thm)], [c_117, c_4])).
% 4.97/1.84  tff(c_175, plain, (![B_684, A_685]: (m1_subset_1(u1_struct_0(B_684), k1_zfmisc_1(u1_struct_0(A_685))) | ~m1_pre_topc(B_684, A_685) | ~l1_pre_topc(A_685))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.97/1.84  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.97/1.84  tff(c_179, plain, (![B_684, A_685]: (r1_tarski(u1_struct_0(B_684), u1_struct_0(A_685)) | ~m1_pre_topc(B_684, A_685) | ~l1_pre_topc(A_685))), inference(resolution, [status(thm)], [c_175, c_8])).
% 4.97/1.84  tff(c_28, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.97/1.84  tff(c_124, plain, (![C_676, B_677, A_678]: (r2_hidden(C_676, B_677) | ~r2_hidden(C_676, A_678) | ~r1_tarski(A_678, B_677))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.97/1.84  tff(c_233, plain, (![A_696, B_697, B_698]: (r2_hidden('#skF_1'(A_696, B_697), B_698) | ~r1_tarski(A_696, B_698) | r1_tarski(A_696, B_697))), inference(resolution, [status(thm)], [c_6, c_124])).
% 4.97/1.84  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.97/1.84  tff(c_281, plain, (![A_708, B_709, B_710, B_711]: (r2_hidden('#skF_1'(A_708, B_709), B_710) | ~r1_tarski(B_711, B_710) | ~r1_tarski(A_708, B_711) | r1_tarski(A_708, B_709))), inference(resolution, [status(thm)], [c_233, c_2])).
% 4.97/1.84  tff(c_297, plain, (![A_712, B_713]: (r2_hidden('#skF_1'(A_712, B_713), u1_struct_0('#skF_4')) | ~r1_tarski(A_712, '#skF_7') | r1_tarski(A_712, B_713))), inference(resolution, [status(thm)], [c_28, c_281])).
% 4.97/1.84  tff(c_561, plain, (![A_749, B_750, B_751]: (r2_hidden('#skF_1'(A_749, B_750), B_751) | ~r1_tarski(u1_struct_0('#skF_4'), B_751) | ~r1_tarski(A_749, '#skF_7') | r1_tarski(A_749, B_750))), inference(resolution, [status(thm)], [c_297, c_2])).
% 4.97/1.84  tff(c_570, plain, (![B_752, A_753]: (~r1_tarski(u1_struct_0('#skF_4'), B_752) | ~r1_tarski(A_753, '#skF_7') | r1_tarski(A_753, B_752))), inference(resolution, [status(thm)], [c_561, c_4])).
% 4.97/1.84  tff(c_589, plain, (![A_753, A_685]: (~r1_tarski(A_753, '#skF_7') | r1_tarski(A_753, u1_struct_0(A_685)) | ~m1_pre_topc('#skF_4', A_685) | ~l1_pre_topc(A_685))), inference(resolution, [status(thm)], [c_179, c_570])).
% 4.97/1.84  tff(c_30, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_610, plain, (![A_757, A_758]: (~r1_tarski(A_757, '#skF_7') | r1_tarski(A_757, u1_struct_0(A_758)) | ~m1_pre_topc('#skF_4', A_758) | ~l1_pre_topc(A_758))), inference(resolution, [status(thm)], [c_179, c_570])).
% 4.97/1.84  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.97/1.84  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_50, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_74, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_75, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_74])).
% 4.97/1.84  tff(c_115, plain, (r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_75])).
% 4.97/1.84  tff(c_68, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_76, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_68])).
% 4.97/1.84  tff(c_159, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_76])).
% 4.97/1.84  tff(c_64, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_44, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_493, plain, (![F_745, H_739, C_744, A_743, B_741, D_740, E_742]: (r1_tmap_1(D_740, B_741, E_742, H_739) | ~r1_tmap_1(C_744, B_741, k3_tmap_1(A_743, B_741, D_740, C_744, E_742), H_739) | ~r1_tarski(F_745, u1_struct_0(C_744)) | ~r2_hidden(H_739, F_745) | ~v3_pre_topc(F_745, D_740) | ~m1_subset_1(H_739, u1_struct_0(C_744)) | ~m1_subset_1(H_739, u1_struct_0(D_740)) | ~m1_subset_1(F_745, k1_zfmisc_1(u1_struct_0(D_740))) | ~m1_pre_topc(C_744, D_740) | ~m1_subset_1(E_742, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_740), u1_struct_0(B_741)))) | ~v1_funct_2(E_742, u1_struct_0(D_740), u1_struct_0(B_741)) | ~v1_funct_1(E_742) | ~m1_pre_topc(D_740, A_743) | v2_struct_0(D_740) | ~m1_pre_topc(C_744, A_743) | v2_struct_0(C_744) | ~l1_pre_topc(B_741) | ~v2_pre_topc(B_741) | v2_struct_0(B_741) | ~l1_pre_topc(A_743) | ~v2_pre_topc(A_743) | v2_struct_0(A_743))), inference(cnfTransformation, [status(thm)], [f_184])).
% 4.97/1.84  tff(c_497, plain, (![F_745]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~r1_tarski(F_745, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_745) | ~v3_pre_topc(F_745, '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_745, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_115, c_493])).
% 4.97/1.84  tff(c_504, plain, (![F_745]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~r1_tarski(F_745, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_745) | ~v3_pre_topc(F_745, '#skF_5') | ~m1_subset_1(F_745, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_64, c_62, c_52, c_48, c_46, c_44, c_42, c_40, c_36, c_77, c_497])).
% 4.97/1.84  tff(c_534, plain, (![F_747]: (~r1_tarski(F_747, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_747) | ~v3_pre_topc(F_747, '#skF_5') | ~m1_subset_1(F_747, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_66, c_54, c_50, c_159, c_504])).
% 4.97/1.84  tff(c_546, plain, (![A_6]: (~r1_tarski(A_6, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', A_6) | ~v3_pre_topc(A_6, '#skF_5') | ~r1_tarski(A_6, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_10, c_534])).
% 4.97/1.84  tff(c_617, plain, (![A_757]: (~r1_tarski(A_757, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', A_757) | ~v3_pre_topc(A_757, '#skF_5') | ~r1_tarski(A_757, '#skF_7') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_610, c_546])).
% 4.97/1.84  tff(c_666, plain, (![A_760]: (~r1_tarski(A_760, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', A_760) | ~v3_pre_topc(A_760, '#skF_5') | ~r1_tarski(A_760, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_40, c_617])).
% 4.97/1.84  tff(c_684, plain, (~r2_hidden('#skF_8', '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_28, c_666])).
% 4.97/1.84  tff(c_697, plain, (~v3_pre_topc('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_30, c_684])).
% 4.97/1.84  tff(c_32, plain, (v3_pre_topc('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_38, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.97/1.84  tff(c_252, plain, (![D_701, C_702, A_703]: (v3_pre_topc(D_701, C_702) | ~m1_subset_1(D_701, k1_zfmisc_1(u1_struct_0(C_702))) | ~v3_pre_topc(D_701, A_703) | ~m1_pre_topc(C_702, A_703) | ~m1_subset_1(D_701, k1_zfmisc_1(u1_struct_0(A_703))) | ~l1_pre_topc(A_703))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.97/1.84  tff(c_591, plain, (![A_754, C_755, A_756]: (v3_pre_topc(A_754, C_755) | ~v3_pre_topc(A_754, A_756) | ~m1_pre_topc(C_755, A_756) | ~m1_subset_1(A_754, k1_zfmisc_1(u1_struct_0(A_756))) | ~l1_pre_topc(A_756) | ~r1_tarski(A_754, u1_struct_0(C_755)))), inference(resolution, [status(thm)], [c_10, c_252])).
% 4.97/1.84  tff(c_597, plain, (![A_754]: (v3_pre_topc(A_754, '#skF_5') | ~v3_pre_topc(A_754, '#skF_3') | ~m1_subset_1(A_754, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_754, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_48, c_591])).
% 4.97/1.84  tff(c_911, plain, (![A_783]: (v3_pre_topc(A_783, '#skF_5') | ~v3_pre_topc(A_783, '#skF_3') | ~m1_subset_1(A_783, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_783, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_597])).
% 4.97/1.84  tff(c_922, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_3') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_911])).
% 4.97/1.84  tff(c_929, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_922])).
% 4.97/1.84  tff(c_930, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_697, c_929])).
% 4.97/1.84  tff(c_958, plain, (~r1_tarski('#skF_7', '#skF_7') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_589, c_930])).
% 4.97/1.84  tff(c_962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_40, c_122, c_958])).
% 4.97/1.84  tff(c_963, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_75])).
% 4.97/1.84  tff(c_1287, plain, (![C_841, D_842, E_845, B_843, G_846, A_844]: (r1_tmap_1(D_842, B_843, k3_tmap_1(A_844, B_843, C_841, D_842, E_845), G_846) | ~r1_tmap_1(C_841, B_843, E_845, G_846) | ~m1_pre_topc(D_842, C_841) | ~m1_subset_1(G_846, u1_struct_0(D_842)) | ~m1_subset_1(G_846, u1_struct_0(C_841)) | ~m1_subset_1(E_845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_841), u1_struct_0(B_843)))) | ~v1_funct_2(E_845, u1_struct_0(C_841), u1_struct_0(B_843)) | ~v1_funct_1(E_845) | ~m1_pre_topc(D_842, A_844) | v2_struct_0(D_842) | ~m1_pre_topc(C_841, A_844) | v2_struct_0(C_841) | ~l1_pre_topc(B_843) | ~v2_pre_topc(B_843) | v2_struct_0(B_843) | ~l1_pre_topc(A_844) | ~v2_pre_topc(A_844) | v2_struct_0(A_844))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.97/1.84  tff(c_1289, plain, (![D_842, A_844, G_846]: (r1_tmap_1(D_842, '#skF_2', k3_tmap_1(A_844, '#skF_2', '#skF_5', D_842, '#skF_6'), G_846) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_846) | ~m1_pre_topc(D_842, '#skF_5') | ~m1_subset_1(G_846, u1_struct_0(D_842)) | ~m1_subset_1(G_846, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_842, A_844) | v2_struct_0(D_842) | ~m1_pre_topc('#skF_5', A_844) | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_844) | ~v2_pre_topc(A_844) | v2_struct_0(A_844))), inference(resolution, [status(thm)], [c_42, c_1287])).
% 4.97/1.84  tff(c_1295, plain, (![D_842, A_844, G_846]: (r1_tmap_1(D_842, '#skF_2', k3_tmap_1(A_844, '#skF_2', '#skF_5', D_842, '#skF_6'), G_846) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_846) | ~m1_pre_topc(D_842, '#skF_5') | ~m1_subset_1(G_846, u1_struct_0(D_842)) | ~m1_subset_1(G_846, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_842, A_844) | v2_struct_0(D_842) | ~m1_pre_topc('#skF_5', A_844) | v2_struct_0('#skF_5') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_844) | ~v2_pre_topc(A_844) | v2_struct_0(A_844))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_46, c_44, c_1289])).
% 4.97/1.84  tff(c_1340, plain, (![D_850, A_851, G_852]: (r1_tmap_1(D_850, '#skF_2', k3_tmap_1(A_851, '#skF_2', '#skF_5', D_850, '#skF_6'), G_852) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_852) | ~m1_pre_topc(D_850, '#skF_5') | ~m1_subset_1(G_852, u1_struct_0(D_850)) | ~m1_subset_1(G_852, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_850, A_851) | v2_struct_0(D_850) | ~m1_pre_topc('#skF_5', A_851) | ~l1_pre_topc(A_851) | ~v2_pre_topc(A_851) | v2_struct_0(A_851))), inference(negUnitSimplification, [status(thm)], [c_66, c_50, c_1295])).
% 4.97/1.84  tff(c_967, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_963, c_76])).
% 4.97/1.84  tff(c_1343, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1340, c_967])).
% 4.97/1.84  tff(c_1346, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_48, c_52, c_36, c_77, c_40, c_963, c_1343])).
% 4.97/1.84  tff(c_1348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_1346])).
% 4.97/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.97/1.84  
% 4.97/1.84  Inference rules
% 4.97/1.84  ----------------------
% 4.97/1.84  #Ref     : 0
% 4.97/1.84  #Sup     : 249
% 4.97/1.84  #Fact    : 0
% 4.97/1.84  #Define  : 0
% 4.97/1.84  #Split   : 10
% 4.97/1.84  #Chain   : 0
% 4.97/1.84  #Close   : 0
% 4.97/1.84  
% 4.97/1.84  Ordering : KBO
% 4.97/1.84  
% 4.97/1.84  Simplification rules
% 4.97/1.84  ----------------------
% 4.97/1.84  #Subsume      : 62
% 4.97/1.84  #Demod        : 160
% 4.97/1.84  #Tautology    : 46
% 4.97/1.84  #SimpNegUnit  : 8
% 4.97/1.84  #BackRed      : 0
% 4.97/1.84  
% 4.97/1.84  #Partial instantiations: 0
% 4.97/1.84  #Strategies tried      : 1
% 4.97/1.84  
% 4.97/1.84  Timing (in seconds)
% 4.97/1.84  ----------------------
% 5.09/1.84  Preprocessing        : 0.44
% 5.09/1.84  Parsing              : 0.22
% 5.09/1.84  CNF conversion       : 0.08
% 5.09/1.84  Main loop            : 0.58
% 5.09/1.84  Inferencing          : 0.20
% 5.09/1.84  Reduction            : 0.18
% 5.09/1.84  Demodulation         : 0.13
% 5.09/1.84  BG Simplification    : 0.03
% 5.09/1.84  Subsumption          : 0.13
% 5.09/1.85  Abstraction          : 0.02
% 5.09/1.85  MUC search           : 0.00
% 5.09/1.85  Cooper               : 0.00
% 5.09/1.85  Total                : 1.07
% 5.09/1.85  Index Insertion      : 0.00
% 5.09/1.85  Index Deletion       : 0.00
% 5.09/1.85  Index Matching       : 0.00
% 5.09/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
