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
% DateTime   : Thu Dec  3 10:27:24 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 187 expanded)
%              Number of leaves         :   33 (  90 expanded)
%              Depth                    :    9
%              Number of atoms          :  283 (1641 expanded)
%              Number of equality atoms :    4 (  69 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_221,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_60,axiom,(
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

tff(f_163,axiom,(
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

tff(f_108,axiom,(
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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_14,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_24,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_65,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_24])).

tff(c_22,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_16,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_20,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_18,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_66,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_90,plain,(
    ! [B_645,A_646] :
      ( v2_pre_topc(B_645)
      | ~ m1_pre_topc(B_645,A_646)
      | ~ l1_pre_topc(A_646)
      | ~ v2_pre_topc(A_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_93,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_90])).

tff(c_102,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_93])).

tff(c_71,plain,(
    ! [B_643,A_644] :
      ( l1_pre_topc(B_643)
      | ~ m1_pre_topc(B_643,A_644)
      | ~ l1_pre_topc(A_644) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_83,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_74])).

tff(c_113,plain,(
    ! [B_647,A_648,C_649] :
      ( m1_connsp_2(B_647,A_648,C_649)
      | ~ r2_hidden(C_649,B_647)
      | ~ v3_pre_topc(B_647,A_648)
      | ~ m1_subset_1(C_649,u1_struct_0(A_648))
      | ~ m1_subset_1(B_647,k1_zfmisc_1(u1_struct_0(A_648)))
      | ~ l1_pre_topc(A_648)
      | ~ v2_pre_topc(A_648)
      | v2_struct_0(A_648) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,(
    ! [B_647] :
      ( m1_connsp_2(B_647,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_647)
      | ~ v3_pre_topc(B_647,'#skF_4')
      | ~ m1_subset_1(B_647,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65,c_113])).

tff(c_120,plain,(
    ! [B_647] :
      ( m1_connsp_2(B_647,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_647)
      | ~ v3_pre_topc(B_647,'#skF_4')
      | ~ m1_subset_1(B_647,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_83,c_115])).

tff(c_126,plain,(
    ! [B_650] :
      ( m1_connsp_2(B_650,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_650)
      | ~ v3_pre_topc(B_650,'#skF_4')
      | ~ m1_subset_1(B_650,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_120])).

tff(c_129,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_126])).

tff(c_132,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_66,c_129])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_56,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_64,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_56])).

tff(c_111,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_32,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_62,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_63,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_62])).

tff(c_112,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_63])).

tff(c_142,plain,(
    ! [C_666,E_663,B_662,D_665,F_661,A_664,H_667] :
      ( r1_tmap_1(D_665,B_662,E_663,H_667)
      | ~ r1_tmap_1(C_666,B_662,k3_tmap_1(A_664,B_662,D_665,C_666,E_663),H_667)
      | ~ m1_connsp_2(F_661,D_665,H_667)
      | ~ r1_tarski(F_661,u1_struct_0(C_666))
      | ~ m1_subset_1(H_667,u1_struct_0(C_666))
      | ~ m1_subset_1(H_667,u1_struct_0(D_665))
      | ~ m1_subset_1(F_661,k1_zfmisc_1(u1_struct_0(D_665)))
      | ~ m1_pre_topc(C_666,D_665)
      | ~ m1_subset_1(E_663,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_665),u1_struct_0(B_662))))
      | ~ v1_funct_2(E_663,u1_struct_0(D_665),u1_struct_0(B_662))
      | ~ v1_funct_1(E_663)
      | ~ m1_pre_topc(D_665,A_664)
      | v2_struct_0(D_665)
      | ~ m1_pre_topc(C_666,A_664)
      | v2_struct_0(C_666)
      | ~ l1_pre_topc(B_662)
      | ~ v2_pre_topc(B_662)
      | v2_struct_0(B_662)
      | ~ l1_pre_topc(A_664)
      | ~ v2_pre_topc(A_664)
      | v2_struct_0(A_664) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_146,plain,(
    ! [F_661] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(F_661,'#skF_4','#skF_8')
      | ~ r1_tarski(F_661,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_661,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_112,c_142])).

tff(c_153,plain,(
    ! [F_661] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(F_661,'#skF_4','#skF_8')
      | ~ r1_tarski(F_661,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_661,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_44,c_40,c_36,c_34,c_32,c_30,c_28,c_65,c_22,c_146])).

tff(c_155,plain,(
    ! [F_668] :
      ( ~ m1_connsp_2(F_668,'#skF_4','#skF_8')
      | ~ r1_tarski(F_668,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_668,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_42,c_38,c_111,c_153])).

tff(c_158,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_155])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_132,c_158])).

tff(c_164,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_187,plain,(
    ! [G_676,C_677,D_675,A_678,B_673,E_674] :
      ( r1_tmap_1(D_675,B_673,k3_tmap_1(A_678,B_673,C_677,D_675,E_674),G_676)
      | ~ r1_tmap_1(C_677,B_673,E_674,G_676)
      | ~ m1_pre_topc(D_675,C_677)
      | ~ m1_subset_1(G_676,u1_struct_0(D_675))
      | ~ m1_subset_1(G_676,u1_struct_0(C_677))
      | ~ m1_subset_1(E_674,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_677),u1_struct_0(B_673))))
      | ~ v1_funct_2(E_674,u1_struct_0(C_677),u1_struct_0(B_673))
      | ~ v1_funct_1(E_674)
      | ~ m1_pre_topc(D_675,A_678)
      | v2_struct_0(D_675)
      | ~ m1_pre_topc(C_677,A_678)
      | v2_struct_0(C_677)
      | ~ l1_pre_topc(B_673)
      | ~ v2_pre_topc(B_673)
      | v2_struct_0(B_673)
      | ~ l1_pre_topc(A_678)
      | ~ v2_pre_topc(A_678)
      | v2_struct_0(A_678) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_189,plain,(
    ! [D_675,A_678,G_676] :
      ( r1_tmap_1(D_675,'#skF_2',k3_tmap_1(A_678,'#skF_2','#skF_4',D_675,'#skF_5'),G_676)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_676)
      | ~ m1_pre_topc(D_675,'#skF_4')
      | ~ m1_subset_1(G_676,u1_struct_0(D_675))
      | ~ m1_subset_1(G_676,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_675,A_678)
      | v2_struct_0(D_675)
      | ~ m1_pre_topc('#skF_4',A_678)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_678)
      | ~ v2_pre_topc(A_678)
      | v2_struct_0(A_678) ) ),
    inference(resolution,[status(thm)],[c_30,c_187])).

tff(c_192,plain,(
    ! [D_675,A_678,G_676] :
      ( r1_tmap_1(D_675,'#skF_2',k3_tmap_1(A_678,'#skF_2','#skF_4',D_675,'#skF_5'),G_676)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_676)
      | ~ m1_pre_topc(D_675,'#skF_4')
      | ~ m1_subset_1(G_676,u1_struct_0(D_675))
      | ~ m1_subset_1(G_676,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_675,A_678)
      | v2_struct_0(D_675)
      | ~ m1_pre_topc('#skF_4',A_678)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_678)
      | ~ v2_pre_topc(A_678)
      | v2_struct_0(A_678) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_32,c_189])).

tff(c_195,plain,(
    ! [D_680,A_681,G_682] :
      ( r1_tmap_1(D_680,'#skF_2',k3_tmap_1(A_681,'#skF_2','#skF_4',D_680,'#skF_5'),G_682)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_682)
      | ~ m1_pre_topc(D_680,'#skF_4')
      | ~ m1_subset_1(G_682,u1_struct_0(D_680))
      | ~ m1_subset_1(G_682,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_680,A_681)
      | v2_struct_0(D_680)
      | ~ m1_pre_topc('#skF_4',A_681)
      | ~ l1_pre_topc(A_681)
      | ~ v2_pre_topc(A_681)
      | v2_struct_0(A_681) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38,c_192])).

tff(c_163,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_198,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_195,c_163])).

tff(c_201,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_36,c_40,c_65,c_22,c_28,c_164,c_198])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_42,c_201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:48:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.36  
% 2.89/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.37  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.89/1.37  
% 2.89/1.37  %Foreground sorts:
% 2.89/1.37  
% 2.89/1.37  
% 2.89/1.37  %Background operators:
% 2.89/1.37  
% 2.89/1.37  
% 2.89/1.37  %Foreground operators:
% 2.89/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.37  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.89/1.37  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.89/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.89/1.37  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.89/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.37  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.89/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.89/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.89/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.89/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.89/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.89/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.89/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.37  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.89/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.89/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.37  
% 2.89/1.39  tff(f_221, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 2.89/1.39  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.89/1.39  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.89/1.39  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.89/1.39  tff(f_163, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 2.89/1.39  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 2.89/1.39  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_14, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_24, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_65, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_24])).
% 2.89/1.39  tff(c_22, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_16, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_20, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_18, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_66, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 2.89/1.39  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_90, plain, (![B_645, A_646]: (v2_pre_topc(B_645) | ~m1_pre_topc(B_645, A_646) | ~l1_pre_topc(A_646) | ~v2_pre_topc(A_646))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.89/1.39  tff(c_93, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_90])).
% 2.89/1.39  tff(c_102, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_93])).
% 2.89/1.39  tff(c_71, plain, (![B_643, A_644]: (l1_pre_topc(B_643) | ~m1_pre_topc(B_643, A_644) | ~l1_pre_topc(A_644))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.39  tff(c_74, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_71])).
% 2.89/1.39  tff(c_83, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_74])).
% 2.89/1.39  tff(c_113, plain, (![B_647, A_648, C_649]: (m1_connsp_2(B_647, A_648, C_649) | ~r2_hidden(C_649, B_647) | ~v3_pre_topc(B_647, A_648) | ~m1_subset_1(C_649, u1_struct_0(A_648)) | ~m1_subset_1(B_647, k1_zfmisc_1(u1_struct_0(A_648))) | ~l1_pre_topc(A_648) | ~v2_pre_topc(A_648) | v2_struct_0(A_648))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.89/1.39  tff(c_115, plain, (![B_647]: (m1_connsp_2(B_647, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_647) | ~v3_pre_topc(B_647, '#skF_4') | ~m1_subset_1(B_647, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_65, c_113])).
% 2.89/1.39  tff(c_120, plain, (![B_647]: (m1_connsp_2(B_647, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_647) | ~v3_pre_topc(B_647, '#skF_4') | ~m1_subset_1(B_647, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_83, c_115])).
% 2.89/1.39  tff(c_126, plain, (![B_650]: (m1_connsp_2(B_650, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_650) | ~v3_pre_topc(B_650, '#skF_4') | ~m1_subset_1(B_650, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_120])).
% 2.89/1.39  tff(c_129, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_126])).
% 2.89/1.39  tff(c_132, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_66, c_129])).
% 2.89/1.39  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_56, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_64, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_56])).
% 2.89/1.39  tff(c_111, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_64])).
% 2.89/1.39  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_32, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_62, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_221])).
% 2.89/1.39  tff(c_63, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_62])).
% 2.89/1.39  tff(c_112, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_111, c_63])).
% 2.89/1.39  tff(c_142, plain, (![C_666, E_663, B_662, D_665, F_661, A_664, H_667]: (r1_tmap_1(D_665, B_662, E_663, H_667) | ~r1_tmap_1(C_666, B_662, k3_tmap_1(A_664, B_662, D_665, C_666, E_663), H_667) | ~m1_connsp_2(F_661, D_665, H_667) | ~r1_tarski(F_661, u1_struct_0(C_666)) | ~m1_subset_1(H_667, u1_struct_0(C_666)) | ~m1_subset_1(H_667, u1_struct_0(D_665)) | ~m1_subset_1(F_661, k1_zfmisc_1(u1_struct_0(D_665))) | ~m1_pre_topc(C_666, D_665) | ~m1_subset_1(E_663, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_665), u1_struct_0(B_662)))) | ~v1_funct_2(E_663, u1_struct_0(D_665), u1_struct_0(B_662)) | ~v1_funct_1(E_663) | ~m1_pre_topc(D_665, A_664) | v2_struct_0(D_665) | ~m1_pre_topc(C_666, A_664) | v2_struct_0(C_666) | ~l1_pre_topc(B_662) | ~v2_pre_topc(B_662) | v2_struct_0(B_662) | ~l1_pre_topc(A_664) | ~v2_pre_topc(A_664) | v2_struct_0(A_664))), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.89/1.39  tff(c_146, plain, (![F_661]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(F_661, '#skF_4', '#skF_8') | ~r1_tarski(F_661, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(F_661, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_112, c_142])).
% 2.89/1.39  tff(c_153, plain, (![F_661]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(F_661, '#skF_4', '#skF_8') | ~r1_tarski(F_661, u1_struct_0('#skF_3')) | ~m1_subset_1(F_661, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_44, c_40, c_36, c_34, c_32, c_30, c_28, c_65, c_22, c_146])).
% 2.89/1.39  tff(c_155, plain, (![F_668]: (~m1_connsp_2(F_668, '#skF_4', '#skF_8') | ~r1_tarski(F_668, u1_struct_0('#skF_3')) | ~m1_subset_1(F_668, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_42, c_38, c_111, c_153])).
% 2.89/1.39  tff(c_158, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_155])).
% 2.89/1.39  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_132, c_158])).
% 2.89/1.39  tff(c_164, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_64])).
% 2.89/1.39  tff(c_187, plain, (![G_676, C_677, D_675, A_678, B_673, E_674]: (r1_tmap_1(D_675, B_673, k3_tmap_1(A_678, B_673, C_677, D_675, E_674), G_676) | ~r1_tmap_1(C_677, B_673, E_674, G_676) | ~m1_pre_topc(D_675, C_677) | ~m1_subset_1(G_676, u1_struct_0(D_675)) | ~m1_subset_1(G_676, u1_struct_0(C_677)) | ~m1_subset_1(E_674, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_677), u1_struct_0(B_673)))) | ~v1_funct_2(E_674, u1_struct_0(C_677), u1_struct_0(B_673)) | ~v1_funct_1(E_674) | ~m1_pre_topc(D_675, A_678) | v2_struct_0(D_675) | ~m1_pre_topc(C_677, A_678) | v2_struct_0(C_677) | ~l1_pre_topc(B_673) | ~v2_pre_topc(B_673) | v2_struct_0(B_673) | ~l1_pre_topc(A_678) | ~v2_pre_topc(A_678) | v2_struct_0(A_678))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.39  tff(c_189, plain, (![D_675, A_678, G_676]: (r1_tmap_1(D_675, '#skF_2', k3_tmap_1(A_678, '#skF_2', '#skF_4', D_675, '#skF_5'), G_676) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_676) | ~m1_pre_topc(D_675, '#skF_4') | ~m1_subset_1(G_676, u1_struct_0(D_675)) | ~m1_subset_1(G_676, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_675, A_678) | v2_struct_0(D_675) | ~m1_pre_topc('#skF_4', A_678) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_678) | ~v2_pre_topc(A_678) | v2_struct_0(A_678))), inference(resolution, [status(thm)], [c_30, c_187])).
% 2.89/1.39  tff(c_192, plain, (![D_675, A_678, G_676]: (r1_tmap_1(D_675, '#skF_2', k3_tmap_1(A_678, '#skF_2', '#skF_4', D_675, '#skF_5'), G_676) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_676) | ~m1_pre_topc(D_675, '#skF_4') | ~m1_subset_1(G_676, u1_struct_0(D_675)) | ~m1_subset_1(G_676, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_675, A_678) | v2_struct_0(D_675) | ~m1_pre_topc('#skF_4', A_678) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_678) | ~v2_pre_topc(A_678) | v2_struct_0(A_678))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_32, c_189])).
% 2.89/1.39  tff(c_195, plain, (![D_680, A_681, G_682]: (r1_tmap_1(D_680, '#skF_2', k3_tmap_1(A_681, '#skF_2', '#skF_4', D_680, '#skF_5'), G_682) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_682) | ~m1_pre_topc(D_680, '#skF_4') | ~m1_subset_1(G_682, u1_struct_0(D_680)) | ~m1_subset_1(G_682, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_680, A_681) | v2_struct_0(D_680) | ~m1_pre_topc('#skF_4', A_681) | ~l1_pre_topc(A_681) | ~v2_pre_topc(A_681) | v2_struct_0(A_681))), inference(negUnitSimplification, [status(thm)], [c_48, c_38, c_192])).
% 2.89/1.39  tff(c_163, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_64])).
% 2.89/1.39  tff(c_198, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_195, c_163])).
% 2.89/1.39  tff(c_201, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_36, c_40, c_65, c_22, c_28, c_164, c_198])).
% 2.89/1.39  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_42, c_201])).
% 2.89/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  
% 2.89/1.39  Inference rules
% 2.89/1.39  ----------------------
% 2.89/1.39  #Ref     : 0
% 2.89/1.39  #Sup     : 20
% 2.89/1.39  #Fact    : 0
% 2.89/1.39  #Define  : 0
% 2.89/1.39  #Split   : 1
% 2.89/1.39  #Chain   : 0
% 2.89/1.39  #Close   : 0
% 2.89/1.39  
% 2.89/1.39  Ordering : KBO
% 2.89/1.39  
% 2.89/1.39  Simplification rules
% 2.89/1.39  ----------------------
% 2.89/1.39  #Subsume      : 1
% 2.89/1.39  #Demod        : 63
% 2.89/1.39  #Tautology    : 8
% 2.89/1.39  #SimpNegUnit  : 11
% 2.89/1.39  #BackRed      : 0
% 2.89/1.39  
% 2.89/1.39  #Partial instantiations: 0
% 2.89/1.39  #Strategies tried      : 1
% 2.89/1.39  
% 2.89/1.39  Timing (in seconds)
% 2.89/1.39  ----------------------
% 2.89/1.39  Preprocessing        : 0.39
% 2.89/1.39  Parsing              : 0.19
% 2.89/1.39  CNF conversion       : 0.07
% 2.89/1.39  Main loop            : 0.21
% 2.89/1.39  Inferencing          : 0.07
% 2.89/1.39  Reduction            : 0.07
% 2.89/1.39  Demodulation         : 0.05
% 2.89/1.39  BG Simplification    : 0.02
% 2.89/1.39  Subsumption          : 0.03
% 2.89/1.39  Abstraction          : 0.01
% 2.89/1.39  MUC search           : 0.00
% 2.89/1.39  Cooper               : 0.00
% 2.89/1.39  Total                : 0.64
% 2.89/1.39  Index Insertion      : 0.00
% 2.89/1.39  Index Deletion       : 0.00
% 2.89/1.39  Index Matching       : 0.00
% 2.89/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
