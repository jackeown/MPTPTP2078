%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:02 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 232 expanded)
%              Number of leaves         :   33 ( 103 expanded)
%              Depth                    :   19
%              Number of atoms          :  307 (1686 expanded)
%              Number of equality atoms :    7 (  85 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_180,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ( ( v3_pre_topc(E,B)
                                    & r2_hidden(F,E)
                                    & r1_tarski(E,u1_struct_0(D))
                                    & F = G )
                                 => ( r1_tmap_1(B,A,C,F)
                                  <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( r1_tarski(E,u1_struct_0(D))
                                  & m1_connsp_2(E,B,F)
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_22,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_67,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_30])).

tff(c_24,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_42,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_26,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_85,plain,(
    ! [A_274,B_275] :
      ( r1_tarski(k1_tops_1(A_274,B_275),B_275)
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ l1_pre_topc(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_87,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_85])).

tff(c_90,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_87])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,
    ( k1_tops_1('#skF_2','#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_5')) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_94,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_28,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [B_279,A_280,C_281] :
      ( r1_tarski(B_279,k1_tops_1(A_280,C_281))
      | ~ r1_tarski(B_279,C_281)
      | ~ v3_pre_topc(B_279,A_280)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_100,plain,(
    ! [B_279] :
      ( r1_tarski(B_279,k1_tops_1('#skF_2','#skF_5'))
      | ~ r1_tarski(B_279,'#skF_5')
      | ~ v3_pre_topc(B_279,'#skF_2')
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_98])).

tff(c_104,plain,(
    ! [B_282] :
      ( r1_tarski(B_282,k1_tops_1('#skF_2','#skF_5'))
      | ~ r1_tarski(B_282,'#skF_5')
      | ~ v3_pre_topc(B_282,'#skF_2')
      | ~ m1_subset_1(B_282,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_100])).

tff(c_107,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_104])).

tff(c_110,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6,c_107])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_110])).

tff(c_113,plain,(
    k1_tops_1('#skF_2','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_145,plain,(
    ! [C_293,A_294,B_295] :
      ( m1_connsp_2(C_293,A_294,B_295)
      | ~ r2_hidden(B_295,k1_tops_1(A_294,C_293))
      | ~ m1_subset_1(C_293,k1_zfmisc_1(u1_struct_0(A_294)))
      | ~ m1_subset_1(B_295,u1_struct_0(A_294))
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | v2_struct_0(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_147,plain,(
    ! [B_295] :
      ( m1_connsp_2('#skF_5','#skF_2',B_295)
      | ~ r2_hidden(B_295,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_295,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_145])).

tff(c_149,plain,(
    ! [B_295] :
      ( m1_connsp_2('#skF_5','#skF_2',B_295)
      | ~ r2_hidden(B_295,'#skF_5')
      | ~ m1_subset_1(B_295,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_34,c_147])).

tff(c_151,plain,(
    ! [B_296] :
      ( m1_connsp_2('#skF_5','#skF_2',B_296)
      | ~ r2_hidden(B_296,'#skF_5')
      | ~ m1_subset_1(B_296,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_149])).

tff(c_154,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_151])).

tff(c_157,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_154])).

tff(c_64,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_65,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_64])).

tff(c_122,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_58,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_7')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_66,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_58])).

tff(c_124,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_66])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_171,plain,(
    ! [A_304,G_305,D_308,B_306,E_307,C_303] :
      ( r1_tmap_1(B_306,A_304,C_303,G_305)
      | ~ r1_tmap_1(D_308,A_304,k2_tmap_1(B_306,A_304,C_303,D_308),G_305)
      | ~ m1_connsp_2(E_307,B_306,G_305)
      | ~ r1_tarski(E_307,u1_struct_0(D_308))
      | ~ m1_subset_1(G_305,u1_struct_0(D_308))
      | ~ m1_subset_1(G_305,u1_struct_0(B_306))
      | ~ m1_subset_1(E_307,k1_zfmisc_1(u1_struct_0(B_306)))
      | ~ m1_pre_topc(D_308,B_306)
      | v2_struct_0(D_308)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_306),u1_struct_0(A_304))))
      | ~ v1_funct_2(C_303,u1_struct_0(B_306),u1_struct_0(A_304))
      | ~ v1_funct_1(C_303)
      | ~ l1_pre_topc(B_306)
      | ~ v2_pre_topc(B_306)
      | v2_struct_0(B_306)
      | ~ l1_pre_topc(A_304)
      | ~ v2_pre_topc(A_304)
      | v2_struct_0(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_173,plain,(
    ! [E_307] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_307,'#skF_2','#skF_6')
      | ~ r1_tarski(E_307,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_307,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_122,c_171])).

tff(c_176,plain,(
    ! [E_307] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_307,'#skF_2','#skF_6')
      | ~ r1_tarski(E_307,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_307,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_44,c_42,c_40,c_36,c_32,c_67,c_173])).

tff(c_178,plain,(
    ! [E_309] :
      ( ~ m1_connsp_2(E_309,'#skF_2','#skF_6')
      | ~ r1_tarski(E_309,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_309,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_38,c_124,c_176])).

tff(c_181,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_178])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_157,c_181])).

tff(c_186,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_210,plain,(
    ! [C_320,A_321,B_322] :
      ( m1_connsp_2(C_320,A_321,B_322)
      | ~ r2_hidden(B_322,k1_tops_1(A_321,C_320))
      | ~ m1_subset_1(C_320,k1_zfmisc_1(u1_struct_0(A_321)))
      | ~ m1_subset_1(B_322,u1_struct_0(A_321))
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_212,plain,(
    ! [B_322] :
      ( m1_connsp_2('#skF_5','#skF_2',B_322)
      | ~ r2_hidden(B_322,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_322,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_210])).

tff(c_214,plain,(
    ! [B_322] :
      ( m1_connsp_2('#skF_5','#skF_2',B_322)
      | ~ r2_hidden(B_322,'#skF_5')
      | ~ m1_subset_1(B_322,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_34,c_212])).

tff(c_217,plain,(
    ! [B_329] :
      ( m1_connsp_2('#skF_5','#skF_2',B_329)
      | ~ r2_hidden(B_329,'#skF_5')
      | ~ m1_subset_1(B_329,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_214])).

tff(c_220,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_217])).

tff(c_223,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_220])).

tff(c_230,plain,(
    ! [D_335,E_334,A_331,B_333,C_330,G_332] :
      ( r1_tmap_1(D_335,A_331,k2_tmap_1(B_333,A_331,C_330,D_335),G_332)
      | ~ r1_tmap_1(B_333,A_331,C_330,G_332)
      | ~ m1_connsp_2(E_334,B_333,G_332)
      | ~ r1_tarski(E_334,u1_struct_0(D_335))
      | ~ m1_subset_1(G_332,u1_struct_0(D_335))
      | ~ m1_subset_1(G_332,u1_struct_0(B_333))
      | ~ m1_subset_1(E_334,k1_zfmisc_1(u1_struct_0(B_333)))
      | ~ m1_pre_topc(D_335,B_333)
      | v2_struct_0(D_335)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_333),u1_struct_0(A_331))))
      | ~ v1_funct_2(C_330,u1_struct_0(B_333),u1_struct_0(A_331))
      | ~ v1_funct_1(C_330)
      | ~ l1_pre_topc(B_333)
      | ~ v2_pre_topc(B_333)
      | v2_struct_0(B_333)
      | ~ l1_pre_topc(A_331)
      | ~ v2_pre_topc(A_331)
      | v2_struct_0(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_232,plain,(
    ! [D_335,A_331,C_330] :
      ( r1_tmap_1(D_335,A_331,k2_tmap_1('#skF_2',A_331,C_330,D_335),'#skF_6')
      | ~ r1_tmap_1('#skF_2',A_331,C_330,'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_335))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_335))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(D_335,'#skF_2')
      | v2_struct_0(D_335)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_331))))
      | ~ v1_funct_2(C_330,u1_struct_0('#skF_2'),u1_struct_0(A_331))
      | ~ v1_funct_1(C_330)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_331)
      | ~ v2_pre_topc(A_331)
      | v2_struct_0(A_331) ) ),
    inference(resolution,[status(thm)],[c_223,c_230])).

tff(c_235,plain,(
    ! [D_335,A_331,C_330] :
      ( r1_tmap_1(D_335,A_331,k2_tmap_1('#skF_2',A_331,C_330,D_335),'#skF_6')
      | ~ r1_tmap_1('#skF_2',A_331,C_330,'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_335))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_335))
      | ~ m1_pre_topc(D_335,'#skF_2')
      | v2_struct_0(D_335)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_331))))
      | ~ v1_funct_2(C_330,u1_struct_0('#skF_2'),u1_struct_0(A_331))
      | ~ v1_funct_1(C_330)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_331)
      | ~ v2_pre_topc(A_331)
      | v2_struct_0(A_331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_34,c_32,c_232])).

tff(c_237,plain,(
    ! [D_336,A_337,C_338] :
      ( r1_tmap_1(D_336,A_337,k2_tmap_1('#skF_2',A_337,C_338,D_336),'#skF_6')
      | ~ r1_tmap_1('#skF_2',A_337,C_338,'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_336))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_336))
      | ~ m1_pre_topc(D_336,'#skF_2')
      | v2_struct_0(D_336)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_337))))
      | ~ v1_funct_2(C_338,u1_struct_0('#skF_2'),u1_struct_0(A_337))
      | ~ v1_funct_1(C_338)
      | ~ l1_pre_topc(A_337)
      | ~ v2_pre_topc(A_337)
      | v2_struct_0(A_337) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_235])).

tff(c_239,plain,(
    ! [D_336] :
      ( r1_tmap_1(D_336,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_336),'#skF_6')
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_336))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_336))
      | ~ m1_pre_topc(D_336,'#skF_2')
      | v2_struct_0(D_336)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_237])).

tff(c_242,plain,(
    ! [D_336] :
      ( r1_tmap_1(D_336,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_336),'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_336))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_336))
      | ~ m1_pre_topc(D_336,'#skF_2')
      | v2_struct_0(D_336)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_44,c_42,c_186,c_239])).

tff(c_244,plain,(
    ! [D_339] :
      ( r1_tmap_1(D_339,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_339),'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_339))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_339))
      | ~ m1_pre_topc(D_339,'#skF_2')
      | v2_struct_0(D_339) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_242])).

tff(c_187,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_249,plain,
    ( ~ r1_tarski('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_244,c_187])).

tff(c_256,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_67,c_24,c_249])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.34  
% 2.57/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.35  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.57/1.35  
% 2.57/1.35  %Foreground sorts:
% 2.57/1.35  
% 2.57/1.35  
% 2.57/1.35  %Background operators:
% 2.57/1.35  
% 2.57/1.35  
% 2.57/1.35  %Foreground operators:
% 2.57/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.57/1.35  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.57/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.57/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.35  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.57/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.57/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.57/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.57/1.35  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.57/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.57/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.57/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.35  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.57/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.57/1.35  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.57/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.57/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.35  
% 2.83/1.37  tff(f_180, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 2.83/1.37  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.83/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.83/1.37  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 2.83/1.37  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.83/1.37  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 2.83/1.37  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_22, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_30, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_67, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_30])).
% 2.83/1.37  tff(c_24, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_42, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_26, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_32, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_85, plain, (![A_274, B_275]: (r1_tarski(k1_tops_1(A_274, B_275), B_275) | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0(A_274))) | ~l1_pre_topc(A_274))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.83/1.37  tff(c_87, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_85])).
% 2.83/1.37  tff(c_90, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_87])).
% 2.83/1.37  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.37  tff(c_93, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_5'))), inference(resolution, [status(thm)], [c_90, c_2])).
% 2.83/1.37  tff(c_94, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_5'))), inference(splitLeft, [status(thm)], [c_93])).
% 2.83/1.37  tff(c_28, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.37  tff(c_98, plain, (![B_279, A_280, C_281]: (r1_tarski(B_279, k1_tops_1(A_280, C_281)) | ~r1_tarski(B_279, C_281) | ~v3_pre_topc(B_279, A_280) | ~m1_subset_1(C_281, k1_zfmisc_1(u1_struct_0(A_280))) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.83/1.37  tff(c_100, plain, (![B_279]: (r1_tarski(B_279, k1_tops_1('#skF_2', '#skF_5')) | ~r1_tarski(B_279, '#skF_5') | ~v3_pre_topc(B_279, '#skF_2') | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_98])).
% 2.83/1.37  tff(c_104, plain, (![B_282]: (r1_tarski(B_282, k1_tops_1('#skF_2', '#skF_5')) | ~r1_tarski(B_282, '#skF_5') | ~v3_pre_topc(B_282, '#skF_2') | ~m1_subset_1(B_282, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_100])).
% 2.83/1.37  tff(c_107, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_104])).
% 2.83/1.37  tff(c_110, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6, c_107])).
% 2.83/1.37  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_110])).
% 2.83/1.37  tff(c_113, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_93])).
% 2.83/1.37  tff(c_145, plain, (![C_293, A_294, B_295]: (m1_connsp_2(C_293, A_294, B_295) | ~r2_hidden(B_295, k1_tops_1(A_294, C_293)) | ~m1_subset_1(C_293, k1_zfmisc_1(u1_struct_0(A_294))) | ~m1_subset_1(B_295, u1_struct_0(A_294)) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | v2_struct_0(A_294))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.83/1.37  tff(c_147, plain, (![B_295]: (m1_connsp_2('#skF_5', '#skF_2', B_295) | ~r2_hidden(B_295, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_295, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_145])).
% 2.83/1.37  tff(c_149, plain, (![B_295]: (m1_connsp_2('#skF_5', '#skF_2', B_295) | ~r2_hidden(B_295, '#skF_5') | ~m1_subset_1(B_295, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_34, c_147])).
% 2.83/1.37  tff(c_151, plain, (![B_296]: (m1_connsp_2('#skF_5', '#skF_2', B_296) | ~r2_hidden(B_296, '#skF_5') | ~m1_subset_1(B_296, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_149])).
% 2.83/1.37  tff(c_154, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_151])).
% 2.83/1.37  tff(c_157, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_154])).
% 2.83/1.37  tff(c_64, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_65, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_64])).
% 2.83/1.37  tff(c_122, plain, (r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_65])).
% 2.83/1.37  tff(c_58, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_7') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_66, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_58])).
% 2.83/1.37  tff(c_124, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_66])).
% 2.83/1.37  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.83/1.37  tff(c_171, plain, (![A_304, G_305, D_308, B_306, E_307, C_303]: (r1_tmap_1(B_306, A_304, C_303, G_305) | ~r1_tmap_1(D_308, A_304, k2_tmap_1(B_306, A_304, C_303, D_308), G_305) | ~m1_connsp_2(E_307, B_306, G_305) | ~r1_tarski(E_307, u1_struct_0(D_308)) | ~m1_subset_1(G_305, u1_struct_0(D_308)) | ~m1_subset_1(G_305, u1_struct_0(B_306)) | ~m1_subset_1(E_307, k1_zfmisc_1(u1_struct_0(B_306))) | ~m1_pre_topc(D_308, B_306) | v2_struct_0(D_308) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_306), u1_struct_0(A_304)))) | ~v1_funct_2(C_303, u1_struct_0(B_306), u1_struct_0(A_304)) | ~v1_funct_1(C_303) | ~l1_pre_topc(B_306) | ~v2_pre_topc(B_306) | v2_struct_0(B_306) | ~l1_pre_topc(A_304) | ~v2_pre_topc(A_304) | v2_struct_0(A_304))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.83/1.37  tff(c_173, plain, (![E_307]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_307, '#skF_2', '#skF_6') | ~r1_tarski(E_307, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1(E_307, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_122, c_171])).
% 2.83/1.37  tff(c_176, plain, (![E_307]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_307, '#skF_2', '#skF_6') | ~r1_tarski(E_307, u1_struct_0('#skF_4')) | ~m1_subset_1(E_307, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_46, c_44, c_42, c_40, c_36, c_32, c_67, c_173])).
% 2.83/1.37  tff(c_178, plain, (![E_309]: (~m1_connsp_2(E_309, '#skF_2', '#skF_6') | ~r1_tarski(E_309, u1_struct_0('#skF_4')) | ~m1_subset_1(E_309, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_50, c_38, c_124, c_176])).
% 2.83/1.37  tff(c_181, plain, (~m1_connsp_2('#skF_5', '#skF_2', '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_178])).
% 2.83/1.37  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_157, c_181])).
% 2.83/1.37  tff(c_186, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_65])).
% 2.83/1.37  tff(c_210, plain, (![C_320, A_321, B_322]: (m1_connsp_2(C_320, A_321, B_322) | ~r2_hidden(B_322, k1_tops_1(A_321, C_320)) | ~m1_subset_1(C_320, k1_zfmisc_1(u1_struct_0(A_321))) | ~m1_subset_1(B_322, u1_struct_0(A_321)) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.83/1.37  tff(c_212, plain, (![B_322]: (m1_connsp_2('#skF_5', '#skF_2', B_322) | ~r2_hidden(B_322, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_322, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_210])).
% 2.83/1.37  tff(c_214, plain, (![B_322]: (m1_connsp_2('#skF_5', '#skF_2', B_322) | ~r2_hidden(B_322, '#skF_5') | ~m1_subset_1(B_322, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_34, c_212])).
% 2.83/1.37  tff(c_217, plain, (![B_329]: (m1_connsp_2('#skF_5', '#skF_2', B_329) | ~r2_hidden(B_329, '#skF_5') | ~m1_subset_1(B_329, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_214])).
% 2.83/1.37  tff(c_220, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_217])).
% 2.83/1.37  tff(c_223, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_220])).
% 2.83/1.37  tff(c_230, plain, (![D_335, E_334, A_331, B_333, C_330, G_332]: (r1_tmap_1(D_335, A_331, k2_tmap_1(B_333, A_331, C_330, D_335), G_332) | ~r1_tmap_1(B_333, A_331, C_330, G_332) | ~m1_connsp_2(E_334, B_333, G_332) | ~r1_tarski(E_334, u1_struct_0(D_335)) | ~m1_subset_1(G_332, u1_struct_0(D_335)) | ~m1_subset_1(G_332, u1_struct_0(B_333)) | ~m1_subset_1(E_334, k1_zfmisc_1(u1_struct_0(B_333))) | ~m1_pre_topc(D_335, B_333) | v2_struct_0(D_335) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_333), u1_struct_0(A_331)))) | ~v1_funct_2(C_330, u1_struct_0(B_333), u1_struct_0(A_331)) | ~v1_funct_1(C_330) | ~l1_pre_topc(B_333) | ~v2_pre_topc(B_333) | v2_struct_0(B_333) | ~l1_pre_topc(A_331) | ~v2_pre_topc(A_331) | v2_struct_0(A_331))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.83/1.37  tff(c_232, plain, (![D_335, A_331, C_330]: (r1_tmap_1(D_335, A_331, k2_tmap_1('#skF_2', A_331, C_330, D_335), '#skF_6') | ~r1_tmap_1('#skF_2', A_331, C_330, '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_335)) | ~m1_subset_1('#skF_6', u1_struct_0(D_335)) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(D_335, '#skF_2') | v2_struct_0(D_335) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_331)))) | ~v1_funct_2(C_330, u1_struct_0('#skF_2'), u1_struct_0(A_331)) | ~v1_funct_1(C_330) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_331) | ~v2_pre_topc(A_331) | v2_struct_0(A_331))), inference(resolution, [status(thm)], [c_223, c_230])).
% 2.83/1.37  tff(c_235, plain, (![D_335, A_331, C_330]: (r1_tmap_1(D_335, A_331, k2_tmap_1('#skF_2', A_331, C_330, D_335), '#skF_6') | ~r1_tmap_1('#skF_2', A_331, C_330, '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_335)) | ~m1_subset_1('#skF_6', u1_struct_0(D_335)) | ~m1_pre_topc(D_335, '#skF_2') | v2_struct_0(D_335) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_331)))) | ~v1_funct_2(C_330, u1_struct_0('#skF_2'), u1_struct_0(A_331)) | ~v1_funct_1(C_330) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_331) | ~v2_pre_topc(A_331) | v2_struct_0(A_331))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_34, c_32, c_232])).
% 2.83/1.37  tff(c_237, plain, (![D_336, A_337, C_338]: (r1_tmap_1(D_336, A_337, k2_tmap_1('#skF_2', A_337, C_338, D_336), '#skF_6') | ~r1_tmap_1('#skF_2', A_337, C_338, '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_336)) | ~m1_subset_1('#skF_6', u1_struct_0(D_336)) | ~m1_pre_topc(D_336, '#skF_2') | v2_struct_0(D_336) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_337)))) | ~v1_funct_2(C_338, u1_struct_0('#skF_2'), u1_struct_0(A_337)) | ~v1_funct_1(C_338) | ~l1_pre_topc(A_337) | ~v2_pre_topc(A_337) | v2_struct_0(A_337))), inference(negUnitSimplification, [status(thm)], [c_50, c_235])).
% 2.83/1.37  tff(c_239, plain, (![D_336]: (r1_tmap_1(D_336, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_336), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_336)) | ~m1_subset_1('#skF_6', u1_struct_0(D_336)) | ~m1_pre_topc(D_336, '#skF_2') | v2_struct_0(D_336) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_237])).
% 2.83/1.37  tff(c_242, plain, (![D_336]: (r1_tmap_1(D_336, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_336), '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_336)) | ~m1_subset_1('#skF_6', u1_struct_0(D_336)) | ~m1_pre_topc(D_336, '#skF_2') | v2_struct_0(D_336) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_44, c_42, c_186, c_239])).
% 2.83/1.37  tff(c_244, plain, (![D_339]: (r1_tmap_1(D_339, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_339), '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_339)) | ~m1_subset_1('#skF_6', u1_struct_0(D_339)) | ~m1_pre_topc(D_339, '#skF_2') | v2_struct_0(D_339))), inference(negUnitSimplification, [status(thm)], [c_56, c_242])).
% 2.83/1.37  tff(c_187, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_65])).
% 2.83/1.37  tff(c_249, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_244, c_187])).
% 2.83/1.37  tff(c_256, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_67, c_24, c_249])).
% 2.83/1.37  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_256])).
% 2.83/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.37  
% 2.83/1.37  Inference rules
% 2.83/1.37  ----------------------
% 2.83/1.37  #Ref     : 0
% 2.83/1.37  #Sup     : 29
% 2.83/1.37  #Fact    : 0
% 2.83/1.37  #Define  : 0
% 2.83/1.37  #Split   : 4
% 2.83/1.37  #Chain   : 0
% 2.83/1.37  #Close   : 0
% 2.83/1.37  
% 2.83/1.37  Ordering : KBO
% 2.83/1.37  
% 2.83/1.37  Simplification rules
% 2.83/1.37  ----------------------
% 2.83/1.37  #Subsume      : 1
% 2.83/1.37  #Demod        : 80
% 2.83/1.37  #Tautology    : 17
% 2.83/1.37  #SimpNegUnit  : 14
% 2.83/1.37  #BackRed      : 1
% 2.83/1.37  
% 2.83/1.37  #Partial instantiations: 0
% 2.83/1.37  #Strategies tried      : 1
% 2.83/1.37  
% 2.83/1.37  Timing (in seconds)
% 2.83/1.37  ----------------------
% 2.83/1.37  Preprocessing        : 0.35
% 2.83/1.37  Parsing              : 0.17
% 2.83/1.37  CNF conversion       : 0.05
% 2.83/1.37  Main loop            : 0.24
% 2.83/1.37  Inferencing          : 0.09
% 2.83/1.37  Reduction            : 0.08
% 2.83/1.37  Demodulation         : 0.06
% 2.83/1.37  BG Simplification    : 0.02
% 2.83/1.37  Subsumption          : 0.05
% 2.83/1.37  Abstraction          : 0.01
% 2.83/1.37  MUC search           : 0.00
% 2.83/1.37  Cooper               : 0.00
% 2.83/1.37  Total                : 0.63
% 2.83/1.37  Index Insertion      : 0.00
% 2.83/1.37  Index Deletion       : 0.00
% 2.83/1.37  Index Matching       : 0.00
% 2.83/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
