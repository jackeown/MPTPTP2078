%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:23 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 247 expanded)
%              Number of leaves         :   36 ( 114 expanded)
%              Depth                    :   15
%              Number of atoms          :  350 (2129 expanded)
%              Number of equality atoms :    4 (  82 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_246,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( m1_connsp_2(D,A,C)
                            & r1_tarski(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_188,axiom,(
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

tff(f_133,axiom,(
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

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_50,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_38,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_28,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_36,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_79,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36])).

tff(c_42,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_32,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_111,plain,(
    ! [B_677,A_678] :
      ( v2_pre_topc(B_677)
      | ~ m1_pre_topc(B_677,A_678)
      | ~ l1_pre_topc(A_678)
      | ~ v2_pre_topc(A_678) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_120,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_111])).

tff(c_129,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_120])).

tff(c_84,plain,(
    ! [B_671,A_672] :
      ( l1_pre_topc(B_671)
      | ~ m1_pre_topc(B_671,A_672)
      | ~ l1_pre_topc(A_672) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_84])).

tff(c_100,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_93])).

tff(c_34,plain,(
    v3_pre_topc('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_296,plain,(
    ! [A_697,B_698,C_699] :
      ( r1_tarski('#skF_1'(A_697,B_698,C_699),B_698)
      | ~ r2_hidden(C_699,B_698)
      | ~ m1_subset_1(C_699,u1_struct_0(A_697))
      | ~ v3_pre_topc(B_698,A_697)
      | ~ m1_subset_1(B_698,k1_zfmisc_1(u1_struct_0(A_697)))
      | ~ l1_pre_topc(A_697)
      | ~ v2_pre_topc(A_697)
      | v2_struct_0(A_697) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_298,plain,(
    ! [C_699] :
      ( r1_tarski('#skF_1'('#skF_6','#skF_8',C_699),'#skF_8')
      | ~ r2_hidden(C_699,'#skF_8')
      | ~ m1_subset_1(C_699,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc('#skF_8','#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_296])).

tff(c_301,plain,(
    ! [C_699] :
      ( r1_tarski('#skF_1'('#skF_6','#skF_8',C_699),'#skF_8')
      | ~ r2_hidden(C_699,'#skF_8')
      | ~ m1_subset_1(C_699,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_100,c_34,c_298])).

tff(c_302,plain,(
    ! [C_699] :
      ( r1_tarski('#skF_1'('#skF_6','#skF_8',C_699),'#skF_8')
      | ~ r2_hidden(C_699,'#skF_8')
      | ~ m1_subset_1(C_699,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_301])).

tff(c_313,plain,(
    ! [A_706,B_707,C_708] :
      ( m1_connsp_2('#skF_1'(A_706,B_707,C_708),A_706,C_708)
      | ~ r2_hidden(C_708,B_707)
      | ~ m1_subset_1(C_708,u1_struct_0(A_706))
      | ~ v3_pre_topc(B_707,A_706)
      | ~ m1_subset_1(B_707,k1_zfmisc_1(u1_struct_0(A_706)))
      | ~ l1_pre_topc(A_706)
      | ~ v2_pre_topc(A_706)
      | v2_struct_0(A_706) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_315,plain,(
    ! [C_708] :
      ( m1_connsp_2('#skF_1'('#skF_6','#skF_8',C_708),'#skF_6',C_708)
      | ~ r2_hidden(C_708,'#skF_8')
      | ~ m1_subset_1(C_708,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc('#skF_8','#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_313])).

tff(c_318,plain,(
    ! [C_708] :
      ( m1_connsp_2('#skF_1'('#skF_6','#skF_8',C_708),'#skF_6',C_708)
      | ~ r2_hidden(C_708,'#skF_8')
      | ~ m1_subset_1(C_708,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_100,c_34,c_315])).

tff(c_319,plain,(
    ! [C_708] :
      ( m1_connsp_2('#skF_1'('#skF_6','#skF_8',C_708),'#skF_6',C_708)
      | ~ r2_hidden(C_708,'#skF_8')
      | ~ m1_subset_1(C_708,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_318])).

tff(c_30,plain,(
    r1_tarski('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_103,plain,(
    ! [A_673,C_674,B_675] :
      ( r1_tarski(A_673,C_674)
      | ~ r1_tarski(B_675,C_674)
      | ~ r1_tarski(A_673,B_675) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_673] :
      ( r1_tarski(A_673,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_673,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_30,c_103])).

tff(c_18,plain,(
    ! [A_10,B_24,C_31] :
      ( m1_subset_1('#skF_1'(A_10,B_24,C_31),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ r2_hidden(C_31,B_24)
      | ~ m1_subset_1(C_31,u1_struct_0(A_10))
      | ~ v3_pre_topc(B_24,A_10)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_10')
    | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_78,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_9')
    | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_70])).

tff(c_130,plain,(
    ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_60,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_48,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_46,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_9')
    | r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_77,plain,
    ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_9')
    | r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_76])).

tff(c_151,plain,(
    r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_77])).

tff(c_372,plain,(
    ! [A_726,C_731,F_728,B_727,D_729,H_730,E_732] :
      ( r1_tmap_1(D_729,B_727,E_732,H_730)
      | ~ r1_tmap_1(C_731,B_727,k3_tmap_1(A_726,B_727,D_729,C_731,E_732),H_730)
      | ~ m1_connsp_2(F_728,D_729,H_730)
      | ~ r1_tarski(F_728,u1_struct_0(C_731))
      | ~ m1_subset_1(H_730,u1_struct_0(C_731))
      | ~ m1_subset_1(H_730,u1_struct_0(D_729))
      | ~ m1_subset_1(F_728,k1_zfmisc_1(u1_struct_0(D_729)))
      | ~ m1_pre_topc(C_731,D_729)
      | ~ m1_subset_1(E_732,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_729),u1_struct_0(B_727))))
      | ~ v1_funct_2(E_732,u1_struct_0(D_729),u1_struct_0(B_727))
      | ~ v1_funct_1(E_732)
      | ~ m1_pre_topc(D_729,A_726)
      | v2_struct_0(D_729)
      | ~ m1_pre_topc(C_731,A_726)
      | v2_struct_0(C_731)
      | ~ l1_pre_topc(B_727)
      | ~ v2_pre_topc(B_727)
      | v2_struct_0(B_727)
      | ~ l1_pre_topc(A_726)
      | ~ v2_pre_topc(A_726)
      | v2_struct_0(A_726) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_376,plain,(
    ! [F_728] :
      ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_9')
      | ~ m1_connsp_2(F_728,'#skF_6','#skF_9')
      | ~ r1_tarski(F_728,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(F_728,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_5','#skF_6')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc('#skF_6','#skF_3')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_151,c_372])).

tff(c_383,plain,(
    ! [F_728] :
      ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_9')
      | ~ m1_connsp_2(F_728,'#skF_6','#skF_9')
      | ~ r1_tarski(F_728,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_728,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_54,c_50,c_48,c_46,c_44,c_42,c_38,c_79,c_376])).

tff(c_385,plain,(
    ! [F_733] :
      ( ~ m1_connsp_2(F_733,'#skF_6','#skF_9')
      | ~ r1_tarski(F_733,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_733,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_56,c_52,c_130,c_383])).

tff(c_389,plain,(
    ! [B_24,C_31] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',B_24,C_31),'#skF_6','#skF_9')
      | ~ r1_tarski('#skF_1'('#skF_6',B_24,C_31),u1_struct_0('#skF_5'))
      | ~ r2_hidden(C_31,B_24)
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(B_24,'#skF_6')
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18,c_385])).

tff(c_395,plain,(
    ! [B_24,C_31] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',B_24,C_31),'#skF_6','#skF_9')
      | ~ r1_tarski('#skF_1'('#skF_6',B_24,C_31),u1_struct_0('#skF_5'))
      | ~ r2_hidden(C_31,B_24)
      | ~ m1_subset_1(C_31,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(B_24,'#skF_6')
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_100,c_389])).

tff(c_400,plain,(
    ! [B_734,C_735] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',B_734,C_735),'#skF_6','#skF_9')
      | ~ r1_tarski('#skF_1'('#skF_6',B_734,C_735),u1_struct_0('#skF_5'))
      | ~ r2_hidden(C_735,B_734)
      | ~ m1_subset_1(C_735,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(B_734,'#skF_6')
      | ~ m1_subset_1(B_734,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_395])).

tff(c_405,plain,(
    ! [B_736,C_737] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',B_736,C_737),'#skF_6','#skF_9')
      | ~ r2_hidden(C_737,B_736)
      | ~ m1_subset_1(C_737,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(B_736,'#skF_6')
      | ~ m1_subset_1(B_736,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r1_tarski('#skF_1'('#skF_6',B_736,C_737),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_106,c_400])).

tff(c_408,plain,
    ( ~ v3_pre_topc('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ r1_tarski('#skF_1'('#skF_6','#skF_8','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_319,c_405])).

tff(c_411,plain,(
    ~ r1_tarski('#skF_1'('#skF_6','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_40,c_34,c_408])).

tff(c_414,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_302,c_411])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_414])).

tff(c_420,plain,(
    r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_655,plain,(
    ! [E_778,B_779,G_781,A_777,D_780,C_776] :
      ( r1_tmap_1(D_780,B_779,k3_tmap_1(A_777,B_779,C_776,D_780,E_778),G_781)
      | ~ r1_tmap_1(C_776,B_779,E_778,G_781)
      | ~ m1_pre_topc(D_780,C_776)
      | ~ m1_subset_1(G_781,u1_struct_0(D_780))
      | ~ m1_subset_1(G_781,u1_struct_0(C_776))
      | ~ m1_subset_1(E_778,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_776),u1_struct_0(B_779))))
      | ~ v1_funct_2(E_778,u1_struct_0(C_776),u1_struct_0(B_779))
      | ~ v1_funct_1(E_778)
      | ~ m1_pre_topc(D_780,A_777)
      | v2_struct_0(D_780)
      | ~ m1_pre_topc(C_776,A_777)
      | v2_struct_0(C_776)
      | ~ l1_pre_topc(B_779)
      | ~ v2_pre_topc(B_779)
      | v2_struct_0(B_779)
      | ~ l1_pre_topc(A_777)
      | ~ v2_pre_topc(A_777)
      | v2_struct_0(A_777) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_657,plain,(
    ! [D_780,A_777,G_781] :
      ( r1_tmap_1(D_780,'#skF_4',k3_tmap_1(A_777,'#skF_4','#skF_6',D_780,'#skF_7'),G_781)
      | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7',G_781)
      | ~ m1_pre_topc(D_780,'#skF_6')
      | ~ m1_subset_1(G_781,u1_struct_0(D_780))
      | ~ m1_subset_1(G_781,u1_struct_0('#skF_6'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_780,A_777)
      | v2_struct_0(D_780)
      | ~ m1_pre_topc('#skF_6',A_777)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_777)
      | ~ v2_pre_topc(A_777)
      | v2_struct_0(A_777) ) ),
    inference(resolution,[status(thm)],[c_44,c_655])).

tff(c_660,plain,(
    ! [D_780,A_777,G_781] :
      ( r1_tmap_1(D_780,'#skF_4',k3_tmap_1(A_777,'#skF_4','#skF_6',D_780,'#skF_7'),G_781)
      | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7',G_781)
      | ~ m1_pre_topc(D_780,'#skF_6')
      | ~ m1_subset_1(G_781,u1_struct_0(D_780))
      | ~ m1_subset_1(G_781,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_780,A_777)
      | v2_struct_0(D_780)
      | ~ m1_pre_topc('#skF_6',A_777)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_777)
      | ~ v2_pre_topc(A_777)
      | v2_struct_0(A_777) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_46,c_657])).

tff(c_662,plain,(
    ! [D_782,A_783,G_784] :
      ( r1_tmap_1(D_782,'#skF_4',k3_tmap_1(A_783,'#skF_4','#skF_6',D_782,'#skF_7'),G_784)
      | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7',G_784)
      | ~ m1_pre_topc(D_782,'#skF_6')
      | ~ m1_subset_1(G_784,u1_struct_0(D_782))
      | ~ m1_subset_1(G_784,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_782,A_783)
      | v2_struct_0(D_782)
      | ~ m1_pre_topc('#skF_6',A_783)
      | ~ l1_pre_topc(A_783)
      | ~ v2_pre_topc(A_783)
      | v2_struct_0(A_783) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_52,c_660])).

tff(c_419,plain,(
    ~ r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_665,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_9')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_662,c_419])).

tff(c_668,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_50,c_54,c_38,c_79,c_42,c_420,c_665])).

tff(c_670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_56,c_668])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.50  
% 3.20/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.50  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 3.20/1.50  
% 3.20/1.50  %Foreground sorts:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Background operators:
% 3.20/1.50  
% 3.20/1.50  
% 3.20/1.50  %Foreground operators:
% 3.20/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.20/1.50  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.20/1.50  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.20/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.20/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.50  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.50  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.20/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.20/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.20/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.50  tff('#skF_10', type, '#skF_10': $i).
% 3.20/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.20/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.50  tff('#skF_9', type, '#skF_9': $i).
% 3.20/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.20/1.50  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.20/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.20/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.20/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.50  
% 3.55/1.52  tff(f_246, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.55/1.52  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.55/1.52  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.55/1.52  tff(f_73, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 3.55/1.52  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.55/1.52  tff(f_188, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 3.55/1.52  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.55/1.52  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_50, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_38, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_28, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_36, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_79, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_36])).
% 3.55/1.52  tff(c_42, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_32, plain, (r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_52, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_111, plain, (![B_677, A_678]: (v2_pre_topc(B_677) | ~m1_pre_topc(B_677, A_678) | ~l1_pre_topc(A_678) | ~v2_pre_topc(A_678))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.55/1.52  tff(c_120, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_111])).
% 3.55/1.52  tff(c_129, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_120])).
% 3.55/1.52  tff(c_84, plain, (![B_671, A_672]: (l1_pre_topc(B_671) | ~m1_pre_topc(B_671, A_672) | ~l1_pre_topc(A_672))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.55/1.52  tff(c_93, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_84])).
% 3.55/1.52  tff(c_100, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_93])).
% 3.55/1.52  tff(c_34, plain, (v3_pre_topc('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_40, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_296, plain, (![A_697, B_698, C_699]: (r1_tarski('#skF_1'(A_697, B_698, C_699), B_698) | ~r2_hidden(C_699, B_698) | ~m1_subset_1(C_699, u1_struct_0(A_697)) | ~v3_pre_topc(B_698, A_697) | ~m1_subset_1(B_698, k1_zfmisc_1(u1_struct_0(A_697))) | ~l1_pre_topc(A_697) | ~v2_pre_topc(A_697) | v2_struct_0(A_697))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.55/1.52  tff(c_298, plain, (![C_699]: (r1_tarski('#skF_1'('#skF_6', '#skF_8', C_699), '#skF_8') | ~r2_hidden(C_699, '#skF_8') | ~m1_subset_1(C_699, u1_struct_0('#skF_6')) | ~v3_pre_topc('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_296])).
% 3.55/1.52  tff(c_301, plain, (![C_699]: (r1_tarski('#skF_1'('#skF_6', '#skF_8', C_699), '#skF_8') | ~r2_hidden(C_699, '#skF_8') | ~m1_subset_1(C_699, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_100, c_34, c_298])).
% 3.55/1.52  tff(c_302, plain, (![C_699]: (r1_tarski('#skF_1'('#skF_6', '#skF_8', C_699), '#skF_8') | ~r2_hidden(C_699, '#skF_8') | ~m1_subset_1(C_699, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_52, c_301])).
% 3.55/1.52  tff(c_313, plain, (![A_706, B_707, C_708]: (m1_connsp_2('#skF_1'(A_706, B_707, C_708), A_706, C_708) | ~r2_hidden(C_708, B_707) | ~m1_subset_1(C_708, u1_struct_0(A_706)) | ~v3_pre_topc(B_707, A_706) | ~m1_subset_1(B_707, k1_zfmisc_1(u1_struct_0(A_706))) | ~l1_pre_topc(A_706) | ~v2_pre_topc(A_706) | v2_struct_0(A_706))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.55/1.52  tff(c_315, plain, (![C_708]: (m1_connsp_2('#skF_1'('#skF_6', '#skF_8', C_708), '#skF_6', C_708) | ~r2_hidden(C_708, '#skF_8') | ~m1_subset_1(C_708, u1_struct_0('#skF_6')) | ~v3_pre_topc('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_313])).
% 3.55/1.52  tff(c_318, plain, (![C_708]: (m1_connsp_2('#skF_1'('#skF_6', '#skF_8', C_708), '#skF_6', C_708) | ~r2_hidden(C_708, '#skF_8') | ~m1_subset_1(C_708, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_100, c_34, c_315])).
% 3.55/1.52  tff(c_319, plain, (![C_708]: (m1_connsp_2('#skF_1'('#skF_6', '#skF_8', C_708), '#skF_6', C_708) | ~r2_hidden(C_708, '#skF_8') | ~m1_subset_1(C_708, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_52, c_318])).
% 3.55/1.52  tff(c_30, plain, (r1_tarski('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_103, plain, (![A_673, C_674, B_675]: (r1_tarski(A_673, C_674) | ~r1_tarski(B_675, C_674) | ~r1_tarski(A_673, B_675))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.52  tff(c_106, plain, (![A_673]: (r1_tarski(A_673, u1_struct_0('#skF_5')) | ~r1_tarski(A_673, '#skF_8'))), inference(resolution, [status(thm)], [c_30, c_103])).
% 3.55/1.52  tff(c_18, plain, (![A_10, B_24, C_31]: (m1_subset_1('#skF_1'(A_10, B_24, C_31), k1_zfmisc_1(u1_struct_0(A_10))) | ~r2_hidden(C_31, B_24) | ~m1_subset_1(C_31, u1_struct_0(A_10)) | ~v3_pre_topc(B_24, A_10) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.55/1.52  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_70, plain, (~r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_10') | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_78, plain, (~r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_9') | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_70])).
% 3.55/1.52  tff(c_130, plain, (~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_78])).
% 3.55/1.52  tff(c_60, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_48, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_46, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_76, plain, (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_9') | r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_246])).
% 3.55/1.52  tff(c_77, plain, (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_9') | r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_76])).
% 3.55/1.52  tff(c_151, plain, (r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_130, c_77])).
% 3.55/1.52  tff(c_372, plain, (![A_726, C_731, F_728, B_727, D_729, H_730, E_732]: (r1_tmap_1(D_729, B_727, E_732, H_730) | ~r1_tmap_1(C_731, B_727, k3_tmap_1(A_726, B_727, D_729, C_731, E_732), H_730) | ~m1_connsp_2(F_728, D_729, H_730) | ~r1_tarski(F_728, u1_struct_0(C_731)) | ~m1_subset_1(H_730, u1_struct_0(C_731)) | ~m1_subset_1(H_730, u1_struct_0(D_729)) | ~m1_subset_1(F_728, k1_zfmisc_1(u1_struct_0(D_729))) | ~m1_pre_topc(C_731, D_729) | ~m1_subset_1(E_732, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_729), u1_struct_0(B_727)))) | ~v1_funct_2(E_732, u1_struct_0(D_729), u1_struct_0(B_727)) | ~v1_funct_1(E_732) | ~m1_pre_topc(D_729, A_726) | v2_struct_0(D_729) | ~m1_pre_topc(C_731, A_726) | v2_struct_0(C_731) | ~l1_pre_topc(B_727) | ~v2_pre_topc(B_727) | v2_struct_0(B_727) | ~l1_pre_topc(A_726) | ~v2_pre_topc(A_726) | v2_struct_0(A_726))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.55/1.52  tff(c_376, plain, (![F_728]: (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_9') | ~m1_connsp_2(F_728, '#skF_6', '#skF_9') | ~r1_tarski(F_728, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1(F_728, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_3') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_151, c_372])).
% 3.55/1.52  tff(c_383, plain, (![F_728]: (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_9') | ~m1_connsp_2(F_728, '#skF_6', '#skF_9') | ~r1_tarski(F_728, u1_struct_0('#skF_5')) | ~m1_subset_1(F_728, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_54, c_50, c_48, c_46, c_44, c_42, c_38, c_79, c_376])).
% 3.55/1.52  tff(c_385, plain, (![F_733]: (~m1_connsp_2(F_733, '#skF_6', '#skF_9') | ~r1_tarski(F_733, u1_struct_0('#skF_5')) | ~m1_subset_1(F_733, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_56, c_52, c_130, c_383])).
% 3.55/1.52  tff(c_389, plain, (![B_24, C_31]: (~m1_connsp_2('#skF_1'('#skF_6', B_24, C_31), '#skF_6', '#skF_9') | ~r1_tarski('#skF_1'('#skF_6', B_24, C_31), u1_struct_0('#skF_5')) | ~r2_hidden(C_31, B_24) | ~m1_subset_1(C_31, u1_struct_0('#skF_6')) | ~v3_pre_topc(B_24, '#skF_6') | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_18, c_385])).
% 3.55/1.52  tff(c_395, plain, (![B_24, C_31]: (~m1_connsp_2('#skF_1'('#skF_6', B_24, C_31), '#skF_6', '#skF_9') | ~r1_tarski('#skF_1'('#skF_6', B_24, C_31), u1_struct_0('#skF_5')) | ~r2_hidden(C_31, B_24) | ~m1_subset_1(C_31, u1_struct_0('#skF_6')) | ~v3_pre_topc(B_24, '#skF_6') | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_100, c_389])).
% 3.55/1.52  tff(c_400, plain, (![B_734, C_735]: (~m1_connsp_2('#skF_1'('#skF_6', B_734, C_735), '#skF_6', '#skF_9') | ~r1_tarski('#skF_1'('#skF_6', B_734, C_735), u1_struct_0('#skF_5')) | ~r2_hidden(C_735, B_734) | ~m1_subset_1(C_735, u1_struct_0('#skF_6')) | ~v3_pre_topc(B_734, '#skF_6') | ~m1_subset_1(B_734, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_395])).
% 3.55/1.52  tff(c_405, plain, (![B_736, C_737]: (~m1_connsp_2('#skF_1'('#skF_6', B_736, C_737), '#skF_6', '#skF_9') | ~r2_hidden(C_737, B_736) | ~m1_subset_1(C_737, u1_struct_0('#skF_6')) | ~v3_pre_topc(B_736, '#skF_6') | ~m1_subset_1(B_736, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r1_tarski('#skF_1'('#skF_6', B_736, C_737), '#skF_8'))), inference(resolution, [status(thm)], [c_106, c_400])).
% 3.55/1.52  tff(c_408, plain, (~v3_pre_topc('#skF_8', '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r1_tarski('#skF_1'('#skF_6', '#skF_8', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_9', '#skF_8') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_319, c_405])).
% 3.55/1.52  tff(c_411, plain, (~r1_tarski('#skF_1'('#skF_6', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_40, c_34, c_408])).
% 3.55/1.52  tff(c_414, plain, (~r2_hidden('#skF_9', '#skF_8') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_302, c_411])).
% 3.55/1.52  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_414])).
% 3.55/1.52  tff(c_420, plain, (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_78])).
% 3.55/1.52  tff(c_655, plain, (![E_778, B_779, G_781, A_777, D_780, C_776]: (r1_tmap_1(D_780, B_779, k3_tmap_1(A_777, B_779, C_776, D_780, E_778), G_781) | ~r1_tmap_1(C_776, B_779, E_778, G_781) | ~m1_pre_topc(D_780, C_776) | ~m1_subset_1(G_781, u1_struct_0(D_780)) | ~m1_subset_1(G_781, u1_struct_0(C_776)) | ~m1_subset_1(E_778, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_776), u1_struct_0(B_779)))) | ~v1_funct_2(E_778, u1_struct_0(C_776), u1_struct_0(B_779)) | ~v1_funct_1(E_778) | ~m1_pre_topc(D_780, A_777) | v2_struct_0(D_780) | ~m1_pre_topc(C_776, A_777) | v2_struct_0(C_776) | ~l1_pre_topc(B_779) | ~v2_pre_topc(B_779) | v2_struct_0(B_779) | ~l1_pre_topc(A_777) | ~v2_pre_topc(A_777) | v2_struct_0(A_777))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.55/1.52  tff(c_657, plain, (![D_780, A_777, G_781]: (r1_tmap_1(D_780, '#skF_4', k3_tmap_1(A_777, '#skF_4', '#skF_6', D_780, '#skF_7'), G_781) | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', G_781) | ~m1_pre_topc(D_780, '#skF_6') | ~m1_subset_1(G_781, u1_struct_0(D_780)) | ~m1_subset_1(G_781, u1_struct_0('#skF_6')) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc(D_780, A_777) | v2_struct_0(D_780) | ~m1_pre_topc('#skF_6', A_777) | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_777) | ~v2_pre_topc(A_777) | v2_struct_0(A_777))), inference(resolution, [status(thm)], [c_44, c_655])).
% 3.55/1.52  tff(c_660, plain, (![D_780, A_777, G_781]: (r1_tmap_1(D_780, '#skF_4', k3_tmap_1(A_777, '#skF_4', '#skF_6', D_780, '#skF_7'), G_781) | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', G_781) | ~m1_pre_topc(D_780, '#skF_6') | ~m1_subset_1(G_781, u1_struct_0(D_780)) | ~m1_subset_1(G_781, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_780, A_777) | v2_struct_0(D_780) | ~m1_pre_topc('#skF_6', A_777) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_777) | ~v2_pre_topc(A_777) | v2_struct_0(A_777))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_46, c_657])).
% 3.55/1.52  tff(c_662, plain, (![D_782, A_783, G_784]: (r1_tmap_1(D_782, '#skF_4', k3_tmap_1(A_783, '#skF_4', '#skF_6', D_782, '#skF_7'), G_784) | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', G_784) | ~m1_pre_topc(D_782, '#skF_6') | ~m1_subset_1(G_784, u1_struct_0(D_782)) | ~m1_subset_1(G_784, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_782, A_783) | v2_struct_0(D_782) | ~m1_pre_topc('#skF_6', A_783) | ~l1_pre_topc(A_783) | ~v2_pre_topc(A_783) | v2_struct_0(A_783))), inference(negUnitSimplification, [status(thm)], [c_62, c_52, c_660])).
% 3.55/1.52  tff(c_419, plain, (~r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_9')), inference(splitRight, [status(thm)], [c_78])).
% 3.55/1.52  tff(c_665, plain, (~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_9') | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_662, c_419])).
% 3.55/1.52  tff(c_668, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_50, c_54, c_38, c_79, c_42, c_420, c_665])).
% 3.55/1.52  tff(c_670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_56, c_668])).
% 3.55/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.52  
% 3.55/1.52  Inference rules
% 3.55/1.52  ----------------------
% 3.55/1.52  #Ref     : 0
% 3.55/1.52  #Sup     : 110
% 3.55/1.52  #Fact    : 0
% 3.55/1.52  #Define  : 0
% 3.55/1.52  #Split   : 11
% 3.55/1.52  #Chain   : 0
% 3.55/1.52  #Close   : 0
% 3.55/1.52  
% 3.55/1.52  Ordering : KBO
% 3.55/1.52  
% 3.55/1.52  Simplification rules
% 3.55/1.52  ----------------------
% 3.55/1.52  #Subsume      : 19
% 3.55/1.52  #Demod        : 227
% 3.55/1.52  #Tautology    : 45
% 3.55/1.52  #SimpNegUnit  : 18
% 3.55/1.52  #BackRed      : 0
% 3.55/1.52  
% 3.55/1.52  #Partial instantiations: 0
% 3.55/1.52  #Strategies tried      : 1
% 3.55/1.52  
% 3.55/1.52  Timing (in seconds)
% 3.55/1.52  ----------------------
% 3.55/1.53  Preprocessing        : 0.39
% 3.55/1.53  Parsing              : 0.18
% 3.55/1.53  CNF conversion       : 0.07
% 3.55/1.53  Main loop            : 0.35
% 3.55/1.53  Inferencing          : 0.13
% 3.55/1.53  Reduction            : 0.11
% 3.55/1.53  Demodulation         : 0.08
% 3.55/1.53  BG Simplification    : 0.02
% 3.55/1.53  Subsumption          : 0.07
% 3.55/1.53  Abstraction          : 0.01
% 3.55/1.53  MUC search           : 0.00
% 3.55/1.53  Cooper               : 0.00
% 3.55/1.53  Total                : 0.78
% 3.55/1.53  Index Insertion      : 0.00
% 3.55/1.53  Index Deletion       : 0.00
% 3.55/1.53  Index Matching       : 0.00
% 3.55/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
