%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:26 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 246 expanded)
%              Number of leaves         :   34 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  338 (1900 expanded)
%              Number of equality atoms :    5 (  72 expanded)
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

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

tff(f_53,axiom,(
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

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_93,plain,(
    ! [A_672,B_673] :
      ( ~ r2_hidden('#skF_1'(A_672,B_673),B_673)
      | r1_tarski(A_672,B_673) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_290,plain,(
    ! [B_705,C_706,A_707] :
      ( r1_tarski(u1_struct_0(B_705),u1_struct_0(C_706))
      | ~ m1_pre_topc(B_705,C_706)
      | ~ m1_pre_topc(C_706,A_707)
      | ~ m1_pre_topc(B_705,A_707)
      | ~ l1_pre_topc(A_707)
      | ~ v2_pre_topc(A_707) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_296,plain,(
    ! [B_705] :
      ( r1_tarski(u1_struct_0(B_705),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_705,'#skF_5')
      | ~ m1_pre_topc(B_705,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_290])).

tff(c_305,plain,(
    ! [B_705] :
      ( r1_tarski(u1_struct_0(B_705),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_705,'#skF_5')
      | ~ m1_pre_topc(B_705,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_296])).

tff(c_28,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_104,plain,(
    ! [C_675,B_676,A_677] :
      ( r2_hidden(C_675,B_676)
      | ~ r2_hidden(C_675,A_677)
      | ~ r1_tarski(A_677,B_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_180,plain,(
    ! [A_689,B_690,B_691] :
      ( r2_hidden('#skF_1'(A_689,B_690),B_691)
      | ~ r1_tarski(A_689,B_691)
      | r1_tarski(A_689,B_690) ) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_189,plain,(
    ! [A_692,B_693,B_694,B_695] :
      ( r2_hidden('#skF_1'(A_692,B_693),B_694)
      | ~ r1_tarski(B_695,B_694)
      | ~ r1_tarski(A_692,B_695)
      | r1_tarski(A_692,B_693) ) ),
    inference(resolution,[status(thm)],[c_180,c_2])).

tff(c_233,plain,(
    ! [A_699,B_700] :
      ( r2_hidden('#skF_1'(A_699,B_700),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_699,'#skF_7')
      | r1_tarski(A_699,B_700) ) ),
    inference(resolution,[status(thm)],[c_28,c_189])).

tff(c_526,plain,(
    ! [A_725,B_726,B_727] :
      ( r2_hidden('#skF_1'(A_725,B_726),B_727)
      | ~ r1_tarski(u1_struct_0('#skF_4'),B_727)
      | ~ r1_tarski(A_725,'#skF_7')
      | r1_tarski(A_725,B_726) ) ),
    inference(resolution,[status(thm)],[c_233,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_535,plain,(
    ! [B_728,A_729] :
      ( ~ r1_tarski(u1_struct_0('#skF_4'),B_728)
      | ~ r1_tarski(A_729,'#skF_7')
      | r1_tarski(A_729,B_728) ) ),
    inference(resolution,[status(thm)],[c_526,c_4])).

tff(c_541,plain,(
    ! [A_729] :
      ( ~ r1_tarski(A_729,'#skF_7')
      | r1_tarski(A_729,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_305,c_535])).

tff(c_559,plain,(
    ! [A_729] :
      ( ~ r1_tarski(A_729,'#skF_7')
      | r1_tarski(A_729,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_40,c_541])).

tff(c_30,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

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

tff(c_178,plain,(
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

tff(c_203,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_76])).

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

tff(c_766,plain,(
    ! [A_757,D_756,B_758,E_759,C_761,F_762,H_760] :
      ( r1_tmap_1(D_756,B_758,E_759,H_760)
      | ~ r1_tmap_1(C_761,B_758,k3_tmap_1(A_757,B_758,D_756,C_761,E_759),H_760)
      | ~ r1_tarski(F_762,u1_struct_0(C_761))
      | ~ r2_hidden(H_760,F_762)
      | ~ v3_pre_topc(F_762,D_756)
      | ~ m1_subset_1(H_760,u1_struct_0(C_761))
      | ~ m1_subset_1(H_760,u1_struct_0(D_756))
      | ~ m1_subset_1(F_762,k1_zfmisc_1(u1_struct_0(D_756)))
      | ~ m1_pre_topc(C_761,D_756)
      | ~ m1_subset_1(E_759,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_756),u1_struct_0(B_758))))
      | ~ v1_funct_2(E_759,u1_struct_0(D_756),u1_struct_0(B_758))
      | ~ v1_funct_1(E_759)
      | ~ m1_pre_topc(D_756,A_757)
      | v2_struct_0(D_756)
      | ~ m1_pre_topc(C_761,A_757)
      | v2_struct_0(C_761)
      | ~ l1_pre_topc(B_758)
      | ~ v2_pre_topc(B_758)
      | v2_struct_0(B_758)
      | ~ l1_pre_topc(A_757)
      | ~ v2_pre_topc(A_757)
      | v2_struct_0(A_757) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_770,plain,(
    ! [F_762] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ r1_tarski(F_762,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_762)
      | ~ v3_pre_topc(F_762,'#skF_5')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_762,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_178,c_766])).

tff(c_777,plain,(
    ! [F_762] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ r1_tarski(F_762,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_762)
      | ~ v3_pre_topc(F_762,'#skF_5')
      | ~ m1_subset_1(F_762,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_64,c_62,c_52,c_48,c_46,c_44,c_42,c_40,c_36,c_77,c_770])).

tff(c_779,plain,(
    ! [F_763] :
      ( ~ r1_tarski(F_763,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_763)
      | ~ v3_pre_topc(F_763,'#skF_5')
      | ~ m1_subset_1(F_763,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_66,c_54,c_50,c_203,c_777])).

tff(c_785,plain,(
    ! [A_764] :
      ( ~ r1_tarski(A_764,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',A_764)
      | ~ v3_pre_topc(A_764,'#skF_5')
      | ~ r1_tarski(A_764,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_10,c_779])).

tff(c_803,plain,(
    ! [A_765] :
      ( ~ r1_tarski(A_765,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',A_765)
      | ~ v3_pre_topc(A_765,'#skF_5')
      | ~ r1_tarski(A_765,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_559,c_785])).

tff(c_816,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | ~ v3_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_803])).

tff(c_824,plain,(
    ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_30,c_816])).

tff(c_32,plain,(
    v3_pre_topc('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_482,plain,(
    ! [D_717,C_718,A_719] :
      ( v3_pre_topc(D_717,C_718)
      | ~ m1_subset_1(D_717,k1_zfmisc_1(u1_struct_0(C_718)))
      | ~ v3_pre_topc(D_717,A_719)
      | ~ m1_pre_topc(C_718,A_719)
      | ~ m1_subset_1(D_717,k1_zfmisc_1(u1_struct_0(A_719)))
      | ~ l1_pre_topc(A_719) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_826,plain,(
    ! [A_767,C_768,A_769] :
      ( v3_pre_topc(A_767,C_768)
      | ~ v3_pre_topc(A_767,A_769)
      | ~ m1_pre_topc(C_768,A_769)
      | ~ m1_subset_1(A_767,k1_zfmisc_1(u1_struct_0(A_769)))
      | ~ l1_pre_topc(A_769)
      | ~ r1_tarski(A_767,u1_struct_0(C_768)) ) ),
    inference(resolution,[status(thm)],[c_10,c_482])).

tff(c_836,plain,(
    ! [A_767] :
      ( v3_pre_topc(A_767,'#skF_5')
      | ~ v3_pre_topc(A_767,'#skF_3')
      | ~ m1_subset_1(A_767,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_767,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_48,c_826])).

tff(c_932,plain,(
    ! [A_780] :
      ( v3_pre_topc(A_780,'#skF_5')
      | ~ v3_pre_topc(A_780,'#skF_3')
      | ~ m1_subset_1(A_780,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_780,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_836])).

tff(c_939,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ v3_pre_topc('#skF_7','#skF_3')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_932])).

tff(c_943,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_939])).

tff(c_944,plain,(
    ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_824,c_943])).

tff(c_953,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_559,c_944])).

tff(c_957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_953])).

tff(c_958,plain,(
    r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_1420,plain,(
    ! [D_835,E_834,C_831,B_832,A_830,G_833] :
      ( r1_tmap_1(D_835,B_832,k3_tmap_1(A_830,B_832,C_831,D_835,E_834),G_833)
      | ~ r1_tmap_1(C_831,B_832,E_834,G_833)
      | ~ m1_pre_topc(D_835,C_831)
      | ~ m1_subset_1(G_833,u1_struct_0(D_835))
      | ~ m1_subset_1(G_833,u1_struct_0(C_831))
      | ~ m1_subset_1(E_834,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_831),u1_struct_0(B_832))))
      | ~ v1_funct_2(E_834,u1_struct_0(C_831),u1_struct_0(B_832))
      | ~ v1_funct_1(E_834)
      | ~ m1_pre_topc(D_835,A_830)
      | v2_struct_0(D_835)
      | ~ m1_pre_topc(C_831,A_830)
      | v2_struct_0(C_831)
      | ~ l1_pre_topc(B_832)
      | ~ v2_pre_topc(B_832)
      | v2_struct_0(B_832)
      | ~ l1_pre_topc(A_830)
      | ~ v2_pre_topc(A_830)
      | v2_struct_0(A_830) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1422,plain,(
    ! [D_835,A_830,G_833] :
      ( r1_tmap_1(D_835,'#skF_2',k3_tmap_1(A_830,'#skF_2','#skF_5',D_835,'#skF_6'),G_833)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_833)
      | ~ m1_pre_topc(D_835,'#skF_5')
      | ~ m1_subset_1(G_833,u1_struct_0(D_835))
      | ~ m1_subset_1(G_833,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_835,A_830)
      | v2_struct_0(D_835)
      | ~ m1_pre_topc('#skF_5',A_830)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_830)
      | ~ v2_pre_topc(A_830)
      | v2_struct_0(A_830) ) ),
    inference(resolution,[status(thm)],[c_42,c_1420])).

tff(c_1428,plain,(
    ! [D_835,A_830,G_833] :
      ( r1_tmap_1(D_835,'#skF_2',k3_tmap_1(A_830,'#skF_2','#skF_5',D_835,'#skF_6'),G_833)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_833)
      | ~ m1_pre_topc(D_835,'#skF_5')
      | ~ m1_subset_1(G_833,u1_struct_0(D_835))
      | ~ m1_subset_1(G_833,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_835,A_830)
      | v2_struct_0(D_835)
      | ~ m1_pre_topc('#skF_5',A_830)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_830)
      | ~ v2_pre_topc(A_830)
      | v2_struct_0(A_830) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_46,c_44,c_1422])).

tff(c_1433,plain,(
    ! [D_836,A_837,G_838] :
      ( r1_tmap_1(D_836,'#skF_2',k3_tmap_1(A_837,'#skF_2','#skF_5',D_836,'#skF_6'),G_838)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_838)
      | ~ m1_pre_topc(D_836,'#skF_5')
      | ~ m1_subset_1(G_838,u1_struct_0(D_836))
      | ~ m1_subset_1(G_838,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_836,A_837)
      | v2_struct_0(D_836)
      | ~ m1_pre_topc('#skF_5',A_837)
      | ~ l1_pre_topc(A_837)
      | ~ v2_pre_topc(A_837)
      | v2_struct_0(A_837) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_50,c_1428])).

tff(c_959,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_1436,plain,
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
    inference(resolution,[status(thm)],[c_1433,c_959])).

tff(c_1439,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_48,c_52,c_36,c_77,c_40,c_958,c_1436])).

tff(c_1441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_1439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:34:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.72  
% 4.20/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.72  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 4.20/1.72  
% 4.20/1.72  %Foreground sorts:
% 4.20/1.72  
% 4.20/1.72  
% 4.20/1.72  %Background operators:
% 4.20/1.72  
% 4.20/1.72  
% 4.20/1.72  %Foreground operators:
% 4.20/1.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.20/1.72  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.20/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.20/1.72  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.20/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.20/1.72  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.20/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.20/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.20/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.20/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.20/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.20/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.20/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.20/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.20/1.72  tff('#skF_9', type, '#skF_9': $i).
% 4.20/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.20/1.72  tff('#skF_8', type, '#skF_8': $i).
% 4.20/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.20/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.20/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.72  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.20/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.20/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.20/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.20/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/1.72  
% 4.20/1.74  tff(f_242, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 4.20/1.74  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.20/1.74  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.20/1.74  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.20/1.74  tff(f_184, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.20/1.74  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 4.20/1.74  tff(f_127, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.20/1.74  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_48, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_52, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_36, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_26, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_34, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_77, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_34])).
% 4.20/1.74  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.20/1.74  tff(c_93, plain, (![A_672, B_673]: (~r2_hidden('#skF_1'(A_672, B_673), B_673) | r1_tarski(A_672, B_673))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.20/1.74  tff(c_98, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_93])).
% 4.20/1.74  tff(c_290, plain, (![B_705, C_706, A_707]: (r1_tarski(u1_struct_0(B_705), u1_struct_0(C_706)) | ~m1_pre_topc(B_705, C_706) | ~m1_pre_topc(C_706, A_707) | ~m1_pre_topc(B_705, A_707) | ~l1_pre_topc(A_707) | ~v2_pre_topc(A_707))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.20/1.74  tff(c_296, plain, (![B_705]: (r1_tarski(u1_struct_0(B_705), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_705, '#skF_5') | ~m1_pre_topc(B_705, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_290])).
% 4.20/1.74  tff(c_305, plain, (![B_705]: (r1_tarski(u1_struct_0(B_705), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_705, '#skF_5') | ~m1_pre_topc(B_705, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_296])).
% 4.20/1.74  tff(c_28, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_104, plain, (![C_675, B_676, A_677]: (r2_hidden(C_675, B_676) | ~r2_hidden(C_675, A_677) | ~r1_tarski(A_677, B_676))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.20/1.74  tff(c_180, plain, (![A_689, B_690, B_691]: (r2_hidden('#skF_1'(A_689, B_690), B_691) | ~r1_tarski(A_689, B_691) | r1_tarski(A_689, B_690))), inference(resolution, [status(thm)], [c_6, c_104])).
% 4.20/1.74  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.20/1.74  tff(c_189, plain, (![A_692, B_693, B_694, B_695]: (r2_hidden('#skF_1'(A_692, B_693), B_694) | ~r1_tarski(B_695, B_694) | ~r1_tarski(A_692, B_695) | r1_tarski(A_692, B_693))), inference(resolution, [status(thm)], [c_180, c_2])).
% 4.20/1.74  tff(c_233, plain, (![A_699, B_700]: (r2_hidden('#skF_1'(A_699, B_700), u1_struct_0('#skF_4')) | ~r1_tarski(A_699, '#skF_7') | r1_tarski(A_699, B_700))), inference(resolution, [status(thm)], [c_28, c_189])).
% 4.20/1.74  tff(c_526, plain, (![A_725, B_726, B_727]: (r2_hidden('#skF_1'(A_725, B_726), B_727) | ~r1_tarski(u1_struct_0('#skF_4'), B_727) | ~r1_tarski(A_725, '#skF_7') | r1_tarski(A_725, B_726))), inference(resolution, [status(thm)], [c_233, c_2])).
% 4.20/1.74  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.20/1.74  tff(c_535, plain, (![B_728, A_729]: (~r1_tarski(u1_struct_0('#skF_4'), B_728) | ~r1_tarski(A_729, '#skF_7') | r1_tarski(A_729, B_728))), inference(resolution, [status(thm)], [c_526, c_4])).
% 4.20/1.74  tff(c_541, plain, (![A_729]: (~r1_tarski(A_729, '#skF_7') | r1_tarski(A_729, u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_305, c_535])).
% 4.20/1.74  tff(c_559, plain, (![A_729]: (~r1_tarski(A_729, '#skF_7') | r1_tarski(A_729, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_40, c_541])).
% 4.20/1.74  tff(c_30, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.20/1.74  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_50, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_74, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_75, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_74])).
% 4.20/1.74  tff(c_178, plain, (r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_75])).
% 4.20/1.74  tff(c_68, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_76, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_68])).
% 4.20/1.74  tff(c_203, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_76])).
% 4.20/1.74  tff(c_64, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_44, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_766, plain, (![A_757, D_756, B_758, E_759, C_761, F_762, H_760]: (r1_tmap_1(D_756, B_758, E_759, H_760) | ~r1_tmap_1(C_761, B_758, k3_tmap_1(A_757, B_758, D_756, C_761, E_759), H_760) | ~r1_tarski(F_762, u1_struct_0(C_761)) | ~r2_hidden(H_760, F_762) | ~v3_pre_topc(F_762, D_756) | ~m1_subset_1(H_760, u1_struct_0(C_761)) | ~m1_subset_1(H_760, u1_struct_0(D_756)) | ~m1_subset_1(F_762, k1_zfmisc_1(u1_struct_0(D_756))) | ~m1_pre_topc(C_761, D_756) | ~m1_subset_1(E_759, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_756), u1_struct_0(B_758)))) | ~v1_funct_2(E_759, u1_struct_0(D_756), u1_struct_0(B_758)) | ~v1_funct_1(E_759) | ~m1_pre_topc(D_756, A_757) | v2_struct_0(D_756) | ~m1_pre_topc(C_761, A_757) | v2_struct_0(C_761) | ~l1_pre_topc(B_758) | ~v2_pre_topc(B_758) | v2_struct_0(B_758) | ~l1_pre_topc(A_757) | ~v2_pre_topc(A_757) | v2_struct_0(A_757))), inference(cnfTransformation, [status(thm)], [f_184])).
% 4.20/1.74  tff(c_770, plain, (![F_762]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~r1_tarski(F_762, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_762) | ~v3_pre_topc(F_762, '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_762, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_178, c_766])).
% 4.20/1.74  tff(c_777, plain, (![F_762]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~r1_tarski(F_762, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_762) | ~v3_pre_topc(F_762, '#skF_5') | ~m1_subset_1(F_762, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_64, c_62, c_52, c_48, c_46, c_44, c_42, c_40, c_36, c_77, c_770])).
% 4.20/1.74  tff(c_779, plain, (![F_763]: (~r1_tarski(F_763, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_763) | ~v3_pre_topc(F_763, '#skF_5') | ~m1_subset_1(F_763, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_66, c_54, c_50, c_203, c_777])).
% 4.20/1.74  tff(c_785, plain, (![A_764]: (~r1_tarski(A_764, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', A_764) | ~v3_pre_topc(A_764, '#skF_5') | ~r1_tarski(A_764, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_10, c_779])).
% 4.20/1.74  tff(c_803, plain, (![A_765]: (~r1_tarski(A_765, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', A_765) | ~v3_pre_topc(A_765, '#skF_5') | ~r1_tarski(A_765, '#skF_7'))), inference(resolution, [status(thm)], [c_559, c_785])).
% 4.20/1.74  tff(c_816, plain, (~r2_hidden('#skF_8', '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_28, c_803])).
% 4.20/1.74  tff(c_824, plain, (~v3_pre_topc('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_30, c_816])).
% 4.20/1.74  tff(c_32, plain, (v3_pre_topc('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_38, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.20/1.74  tff(c_482, plain, (![D_717, C_718, A_719]: (v3_pre_topc(D_717, C_718) | ~m1_subset_1(D_717, k1_zfmisc_1(u1_struct_0(C_718))) | ~v3_pre_topc(D_717, A_719) | ~m1_pre_topc(C_718, A_719) | ~m1_subset_1(D_717, k1_zfmisc_1(u1_struct_0(A_719))) | ~l1_pre_topc(A_719))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.20/1.74  tff(c_826, plain, (![A_767, C_768, A_769]: (v3_pre_topc(A_767, C_768) | ~v3_pre_topc(A_767, A_769) | ~m1_pre_topc(C_768, A_769) | ~m1_subset_1(A_767, k1_zfmisc_1(u1_struct_0(A_769))) | ~l1_pre_topc(A_769) | ~r1_tarski(A_767, u1_struct_0(C_768)))), inference(resolution, [status(thm)], [c_10, c_482])).
% 4.20/1.74  tff(c_836, plain, (![A_767]: (v3_pre_topc(A_767, '#skF_5') | ~v3_pre_topc(A_767, '#skF_3') | ~m1_subset_1(A_767, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_767, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_48, c_826])).
% 4.20/1.74  tff(c_932, plain, (![A_780]: (v3_pre_topc(A_780, '#skF_5') | ~v3_pre_topc(A_780, '#skF_3') | ~m1_subset_1(A_780, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_780, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_836])).
% 4.20/1.74  tff(c_939, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_3') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_932])).
% 4.20/1.74  tff(c_943, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_939])).
% 4.20/1.74  tff(c_944, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_824, c_943])).
% 4.20/1.74  tff(c_953, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_559, c_944])).
% 4.20/1.74  tff(c_957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_953])).
% 4.20/1.74  tff(c_958, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_75])).
% 4.20/1.74  tff(c_1420, plain, (![D_835, E_834, C_831, B_832, A_830, G_833]: (r1_tmap_1(D_835, B_832, k3_tmap_1(A_830, B_832, C_831, D_835, E_834), G_833) | ~r1_tmap_1(C_831, B_832, E_834, G_833) | ~m1_pre_topc(D_835, C_831) | ~m1_subset_1(G_833, u1_struct_0(D_835)) | ~m1_subset_1(G_833, u1_struct_0(C_831)) | ~m1_subset_1(E_834, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_831), u1_struct_0(B_832)))) | ~v1_funct_2(E_834, u1_struct_0(C_831), u1_struct_0(B_832)) | ~v1_funct_1(E_834) | ~m1_pre_topc(D_835, A_830) | v2_struct_0(D_835) | ~m1_pre_topc(C_831, A_830) | v2_struct_0(C_831) | ~l1_pre_topc(B_832) | ~v2_pre_topc(B_832) | v2_struct_0(B_832) | ~l1_pre_topc(A_830) | ~v2_pre_topc(A_830) | v2_struct_0(A_830))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.20/1.74  tff(c_1422, plain, (![D_835, A_830, G_833]: (r1_tmap_1(D_835, '#skF_2', k3_tmap_1(A_830, '#skF_2', '#skF_5', D_835, '#skF_6'), G_833) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_833) | ~m1_pre_topc(D_835, '#skF_5') | ~m1_subset_1(G_833, u1_struct_0(D_835)) | ~m1_subset_1(G_833, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_835, A_830) | v2_struct_0(D_835) | ~m1_pre_topc('#skF_5', A_830) | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_830) | ~v2_pre_topc(A_830) | v2_struct_0(A_830))), inference(resolution, [status(thm)], [c_42, c_1420])).
% 4.20/1.74  tff(c_1428, plain, (![D_835, A_830, G_833]: (r1_tmap_1(D_835, '#skF_2', k3_tmap_1(A_830, '#skF_2', '#skF_5', D_835, '#skF_6'), G_833) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_833) | ~m1_pre_topc(D_835, '#skF_5') | ~m1_subset_1(G_833, u1_struct_0(D_835)) | ~m1_subset_1(G_833, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_835, A_830) | v2_struct_0(D_835) | ~m1_pre_topc('#skF_5', A_830) | v2_struct_0('#skF_5') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_830) | ~v2_pre_topc(A_830) | v2_struct_0(A_830))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_46, c_44, c_1422])).
% 4.20/1.74  tff(c_1433, plain, (![D_836, A_837, G_838]: (r1_tmap_1(D_836, '#skF_2', k3_tmap_1(A_837, '#skF_2', '#skF_5', D_836, '#skF_6'), G_838) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_838) | ~m1_pre_topc(D_836, '#skF_5') | ~m1_subset_1(G_838, u1_struct_0(D_836)) | ~m1_subset_1(G_838, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_836, A_837) | v2_struct_0(D_836) | ~m1_pre_topc('#skF_5', A_837) | ~l1_pre_topc(A_837) | ~v2_pre_topc(A_837) | v2_struct_0(A_837))), inference(negUnitSimplification, [status(thm)], [c_66, c_50, c_1428])).
% 4.20/1.74  tff(c_959, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_75])).
% 4.20/1.74  tff(c_1436, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1433, c_959])).
% 4.20/1.74  tff(c_1439, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_48, c_52, c_36, c_77, c_40, c_958, c_1436])).
% 4.20/1.74  tff(c_1441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_1439])).
% 4.20/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.74  
% 4.20/1.74  Inference rules
% 4.20/1.74  ----------------------
% 4.20/1.74  #Ref     : 0
% 4.20/1.74  #Sup     : 298
% 4.20/1.74  #Fact    : 0
% 4.20/1.74  #Define  : 0
% 4.20/1.74  #Split   : 24
% 4.20/1.74  #Chain   : 0
% 4.20/1.74  #Close   : 0
% 4.20/1.74  
% 4.20/1.74  Ordering : KBO
% 4.20/1.74  
% 4.20/1.74  Simplification rules
% 4.20/1.74  ----------------------
% 4.20/1.74  #Subsume      : 89
% 4.20/1.74  #Demod        : 164
% 4.20/1.74  #Tautology    : 70
% 4.20/1.74  #SimpNegUnit  : 8
% 4.20/1.74  #BackRed      : 0
% 4.20/1.74  
% 4.20/1.74  #Partial instantiations: 0
% 4.20/1.74  #Strategies tried      : 1
% 4.20/1.74  
% 4.20/1.75  Timing (in seconds)
% 4.20/1.75  ----------------------
% 4.20/1.75  Preprocessing        : 0.39
% 4.20/1.75  Parsing              : 0.19
% 4.20/1.75  CNF conversion       : 0.07
% 4.20/1.75  Main loop            : 0.54
% 4.20/1.75  Inferencing          : 0.18
% 4.20/1.75  Reduction            : 0.17
% 4.20/1.75  Demodulation         : 0.12
% 4.20/1.75  BG Simplification    : 0.02
% 4.20/1.75  Subsumption          : 0.12
% 4.20/1.75  Abstraction          : 0.02
% 4.20/1.75  MUC search           : 0.00
% 4.20/1.75  Cooper               : 0.00
% 4.20/1.75  Total                : 0.97
% 4.20/1.75  Index Insertion      : 0.00
% 4.20/1.75  Index Deletion       : 0.00
% 4.20/1.75  Index Matching       : 0.00
% 4.20/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
