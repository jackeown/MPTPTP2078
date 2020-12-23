%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:25 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 8.05s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 487 expanded)
%              Number of leaves         :   39 ( 193 expanded)
%              Depth                    :   12
%              Number of atoms          :  445 (3489 expanded)
%              Number of equality atoms :    6 ( 125 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_281,negated_conjecture,(
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

tff(f_57,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_223,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & r1_tarski(D,C)
                    & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_168,axiom,(
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

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_72,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_62,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_66,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_40,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_48,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_91,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_48])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_42,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_98,plain,(
    ! [B_695,A_696] :
      ( l1_pre_topc(B_695)
      | ~ m1_pre_topc(B_695,A_696)
      | ~ l1_pre_topc(A_696) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_104,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_98])).

tff(c_111,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_104])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_240,plain,(
    ! [C_720,A_721,B_722] :
      ( m1_subset_1(C_720,k1_zfmisc_1(u1_struct_0(A_721)))
      | ~ m1_subset_1(C_720,k1_zfmisc_1(u1_struct_0(B_722)))
      | ~ m1_pre_topc(B_722,A_721)
      | ~ l1_pre_topc(A_721) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_270,plain,(
    ! [A_729,A_730,B_731] :
      ( m1_subset_1(A_729,k1_zfmisc_1(u1_struct_0(A_730)))
      | ~ m1_pre_topc(B_731,A_730)
      | ~ l1_pre_topc(A_730)
      | ~ r1_tarski(A_729,u1_struct_0(B_731)) ) ),
    inference(resolution,[status(thm)],[c_10,c_240])).

tff(c_274,plain,(
    ! [A_729] :
      ( m1_subset_1(A_729,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_729,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_54,c_270])).

tff(c_282,plain,(
    ! [A_729] :
      ( m1_subset_1(A_729,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_729,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_274])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_82,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_90,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_82])).

tff(c_170,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_78,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_58,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_88,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_89,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_88])).

tff(c_239,plain,(
    r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_89])).

tff(c_1941,plain,(
    ! [B_884,C_885,E_881,D_883,H_879,F_880,A_882] :
      ( r1_tmap_1(D_883,B_884,E_881,H_879)
      | ~ r1_tmap_1(C_885,B_884,k3_tmap_1(A_882,B_884,D_883,C_885,E_881),H_879)
      | ~ m1_connsp_2(F_880,D_883,H_879)
      | ~ r1_tarski(F_880,u1_struct_0(C_885))
      | ~ m1_subset_1(H_879,u1_struct_0(C_885))
      | ~ m1_subset_1(H_879,u1_struct_0(D_883))
      | ~ m1_subset_1(F_880,k1_zfmisc_1(u1_struct_0(D_883)))
      | ~ m1_pre_topc(C_885,D_883)
      | ~ m1_subset_1(E_881,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_883),u1_struct_0(B_884))))
      | ~ v1_funct_2(E_881,u1_struct_0(D_883),u1_struct_0(B_884))
      | ~ v1_funct_1(E_881)
      | ~ m1_pre_topc(D_883,A_882)
      | v2_struct_0(D_883)
      | ~ m1_pre_topc(C_885,A_882)
      | v2_struct_0(C_885)
      | ~ l1_pre_topc(B_884)
      | ~ v2_pre_topc(B_884)
      | v2_struct_0(B_884)
      | ~ l1_pre_topc(A_882)
      | ~ v2_pre_topc(A_882)
      | v2_struct_0(A_882) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_1943,plain,(
    ! [F_880] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_880,'#skF_5','#skF_8')
      | ~ r1_tarski(F_880,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_880,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_239,c_1941])).

tff(c_1946,plain,(
    ! [F_880] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_880,'#skF_5','#skF_8')
      | ~ r1_tarski(F_880,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_880,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_78,c_76,c_66,c_62,c_60,c_58,c_56,c_54,c_50,c_91,c_1943])).

tff(c_1948,plain,(
    ! [F_886] :
      ( ~ m1_connsp_2(F_886,'#skF_5','#skF_8')
      | ~ r1_tarski(F_886,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_886,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_80,c_68,c_64,c_170,c_1946])).

tff(c_1994,plain,(
    ! [A_887] :
      ( ~ m1_connsp_2(A_887,'#skF_5','#skF_8')
      | ~ r1_tarski(A_887,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_282,c_1948])).

tff(c_2056,plain,(
    ~ m1_connsp_2('#skF_7','#skF_5','#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_1994])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_322,plain,(
    ! [D_735,C_736,A_737] :
      ( v3_pre_topc(D_735,C_736)
      | ~ m1_subset_1(D_735,k1_zfmisc_1(u1_struct_0(C_736)))
      | ~ v3_pre_topc(D_735,A_737)
      | ~ m1_pre_topc(C_736,A_737)
      | ~ m1_subset_1(D_735,k1_zfmisc_1(u1_struct_0(A_737)))
      | ~ l1_pre_topc(A_737) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2059,plain,(
    ! [A_889,C_890,A_891] :
      ( v3_pre_topc(A_889,C_890)
      | ~ v3_pre_topc(A_889,A_891)
      | ~ m1_pre_topc(C_890,A_891)
      | ~ m1_subset_1(A_889,k1_zfmisc_1(u1_struct_0(A_891)))
      | ~ l1_pre_topc(A_891)
      | ~ r1_tarski(A_889,u1_struct_0(C_890)) ) ),
    inference(resolution,[status(thm)],[c_10,c_322])).

tff(c_2063,plain,(
    ! [A_889] :
      ( v3_pre_topc(A_889,'#skF_4')
      | ~ v3_pre_topc(A_889,'#skF_5')
      | ~ m1_subset_1(A_889,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_889,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_54,c_2059])).

tff(c_2078,plain,(
    ! [A_892] :
      ( v3_pre_topc(A_892,'#skF_4')
      | ~ v3_pre_topc(A_892,'#skF_5')
      | ~ m1_subset_1(A_892,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_892,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2063])).

tff(c_2124,plain,(
    ! [A_893] :
      ( v3_pre_topc(A_893,'#skF_4')
      | ~ v3_pre_topc(A_893,'#skF_5')
      | ~ r1_tarski(A_893,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_282,c_2078])).

tff(c_2186,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_2124])).

tff(c_2188,plain,(
    ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2186])).

tff(c_289,plain,(
    ! [A_732] :
      ( m1_subset_1(A_732,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_732,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_274])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_299,plain,(
    ! [A_732] :
      ( r1_tarski(A_732,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_732,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_289,c_8])).

tff(c_276,plain,(
    ! [A_729] :
      ( m1_subset_1(A_729,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_729,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_62,c_270])).

tff(c_311,plain,(
    ! [A_734] :
      ( m1_subset_1(A_734,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_734,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_276])).

tff(c_340,plain,(
    ! [A_738] :
      ( r1_tarski(A_738,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_738,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_311,c_8])).

tff(c_356,plain,(
    r1_tarski(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_340])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_117,plain,(
    ! [A_697,B_698] :
      ( r1_tarski(A_697,B_698)
      | ~ m1_subset_1(A_697,k1_zfmisc_1(B_698)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_121,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_117])).

tff(c_44,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_171,plain,(
    ! [A_705,C_706,B_707] :
      ( m1_subset_1(A_705,C_706)
      | ~ m1_subset_1(B_707,k1_zfmisc_1(C_706))
      | ~ r2_hidden(A_705,B_707) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,(
    ! [A_709,B_710,A_711] :
      ( m1_subset_1(A_709,B_710)
      | ~ r2_hidden(A_709,A_711)
      | ~ r1_tarski(A_711,B_710) ) ),
    inference(resolution,[status(thm)],[c_10,c_171])).

tff(c_186,plain,(
    ! [B_712] :
      ( m1_subset_1('#skF_8',B_712)
      | ~ r1_tarski('#skF_7',B_712) ) ),
    inference(resolution,[status(thm)],[c_44,c_182])).

tff(c_197,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_121,c_186])).

tff(c_46,plain,(
    v3_pre_topc('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_278,plain,(
    ! [A_729] :
      ( m1_subset_1(A_729,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_729,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_66,c_270])).

tff(c_288,plain,(
    ! [A_729] :
      ( m1_subset_1(A_729,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_729,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_278])).

tff(c_1000,plain,(
    ! [C_798,A_799,B_800,D_801] :
      ( m1_connsp_2(C_798,A_799,B_800)
      | ~ r2_hidden(B_800,D_801)
      | ~ r1_tarski(D_801,C_798)
      | ~ v3_pre_topc(D_801,A_799)
      | ~ m1_subset_1(D_801,k1_zfmisc_1(u1_struct_0(A_799)))
      | ~ m1_subset_1(C_798,k1_zfmisc_1(u1_struct_0(A_799)))
      | ~ m1_subset_1(B_800,u1_struct_0(A_799))
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2189,plain,(
    ! [C_894,A_895] :
      ( m1_connsp_2(C_894,A_895,'#skF_8')
      | ~ r1_tarski('#skF_7',C_894)
      | ~ v3_pre_topc('#skF_7',A_895)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_895)))
      | ~ m1_subset_1(C_894,k1_zfmisc_1(u1_struct_0(A_895)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_895))
      | ~ l1_pre_topc(A_895)
      | ~ v2_pre_topc(A_895)
      | v2_struct_0(A_895) ) ),
    inference(resolution,[status(thm)],[c_44,c_1000])).

tff(c_2201,plain,(
    ! [C_894] :
      ( m1_connsp_2(C_894,'#skF_3','#skF_8')
      | ~ r1_tarski('#skF_7',C_894)
      | ~ v3_pre_topc('#skF_7','#skF_3')
      | ~ m1_subset_1(C_894,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_7',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_288,c_2189])).

tff(c_2224,plain,(
    ! [C_894] :
      ( m1_connsp_2(C_894,'#skF_3','#skF_8')
      | ~ r1_tarski('#skF_7',C_894)
      | ~ m1_subset_1(C_894,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72,c_70,c_197,c_46,c_2201])).

tff(c_2280,plain,(
    ! [C_899] :
      ( m1_connsp_2(C_899,'#skF_3','#skF_8')
      | ~ r1_tarski('#skF_7',C_899)
      | ~ m1_subset_1(C_899,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2224])).

tff(c_2410,plain,(
    ! [A_901] :
      ( m1_connsp_2(A_901,'#skF_3','#skF_8')
      | ~ r1_tarski('#skF_7',A_901)
      | ~ r1_tarski(A_901,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_2280])).

tff(c_2481,plain,
    ( m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_8')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_356,c_2410])).

tff(c_2491,plain,(
    ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2481])).

tff(c_2498,plain,(
    ~ r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_299,c_2491])).

tff(c_2508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2498])).

tff(c_2510,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2481])).

tff(c_2065,plain,(
    ! [A_889] :
      ( v3_pre_topc(A_889,'#skF_5')
      | ~ v3_pre_topc(A_889,'#skF_3')
      | ~ m1_subset_1(A_889,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_889,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_62,c_2059])).

tff(c_2606,plain,(
    ! [A_909] :
      ( v3_pre_topc(A_909,'#skF_5')
      | ~ v3_pre_topc(A_909,'#skF_3')
      | ~ m1_subset_1(A_909,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_909,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2065])).

tff(c_2639,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ v3_pre_topc('#skF_7','#skF_3')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_2606])).

tff(c_2662,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2510,c_46,c_2639])).

tff(c_2664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2188,c_2662])).

tff(c_2666,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2186])).

tff(c_149,plain,(
    ! [B_703,A_704] :
      ( v2_pre_topc(B_703)
      | ~ m1_pre_topc(B_703,A_704)
      | ~ l1_pre_topc(A_704)
      | ~ v2_pre_topc(A_704) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_155,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_149])).

tff(c_164,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_155])).

tff(c_2667,plain,(
    ! [C_910,A_911] :
      ( m1_connsp_2(C_910,A_911,'#skF_8')
      | ~ r1_tarski('#skF_7',C_910)
      | ~ v3_pre_topc('#skF_7',A_911)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_911)))
      | ~ m1_subset_1(C_910,k1_zfmisc_1(u1_struct_0(A_911)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_911))
      | ~ l1_pre_topc(A_911)
      | ~ v2_pre_topc(A_911)
      | v2_struct_0(A_911) ) ),
    inference(resolution,[status(thm)],[c_44,c_1000])).

tff(c_2685,plain,(
    ! [C_910] :
      ( m1_connsp_2(C_910,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_910)
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(C_910,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski('#skF_7',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_282,c_2667])).

tff(c_2710,plain,(
    ! [C_910] :
      ( m1_connsp_2(C_910,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_910)
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(C_910,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_164,c_111,c_50,c_2685])).

tff(c_2711,plain,(
    ! [C_910] :
      ( m1_connsp_2(C_910,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_910)
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(C_910,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2710])).

tff(c_3009,plain,(
    ! [C_921] :
      ( m1_connsp_2(C_921,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_921)
      | ~ m1_subset_1(C_921,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2666,c_2711])).

tff(c_3132,plain,(
    ! [A_923] :
      ( m1_connsp_2(A_923,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',A_923)
      | ~ r1_tarski(A_923,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_282,c_3009])).

tff(c_3171,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_8')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_3132])).

tff(c_3205,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3171])).

tff(c_3207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2056,c_3205])).

tff(c_3209,plain,(
    r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_4482,plain,(
    ! [D_1075,A_1076,G_1072,C_1073,E_1077,B_1074] :
      ( r1_tmap_1(D_1075,B_1074,k3_tmap_1(A_1076,B_1074,C_1073,D_1075,E_1077),G_1072)
      | ~ r1_tmap_1(C_1073,B_1074,E_1077,G_1072)
      | ~ m1_pre_topc(D_1075,C_1073)
      | ~ m1_subset_1(G_1072,u1_struct_0(D_1075))
      | ~ m1_subset_1(G_1072,u1_struct_0(C_1073))
      | ~ m1_subset_1(E_1077,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1073),u1_struct_0(B_1074))))
      | ~ v1_funct_2(E_1077,u1_struct_0(C_1073),u1_struct_0(B_1074))
      | ~ v1_funct_1(E_1077)
      | ~ m1_pre_topc(D_1075,A_1076)
      | v2_struct_0(D_1075)
      | ~ m1_pre_topc(C_1073,A_1076)
      | v2_struct_0(C_1073)
      | ~ l1_pre_topc(B_1074)
      | ~ v2_pre_topc(B_1074)
      | v2_struct_0(B_1074)
      | ~ l1_pre_topc(A_1076)
      | ~ v2_pre_topc(A_1076)
      | v2_struct_0(A_1076) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_4484,plain,(
    ! [D_1075,A_1076,G_1072] :
      ( r1_tmap_1(D_1075,'#skF_2',k3_tmap_1(A_1076,'#skF_2','#skF_5',D_1075,'#skF_6'),G_1072)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_1072)
      | ~ m1_pre_topc(D_1075,'#skF_5')
      | ~ m1_subset_1(G_1072,u1_struct_0(D_1075))
      | ~ m1_subset_1(G_1072,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_1075,A_1076)
      | v2_struct_0(D_1075)
      | ~ m1_pre_topc('#skF_5',A_1076)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1076)
      | ~ v2_pre_topc(A_1076)
      | v2_struct_0(A_1076) ) ),
    inference(resolution,[status(thm)],[c_56,c_4482])).

tff(c_4490,plain,(
    ! [D_1075,A_1076,G_1072] :
      ( r1_tmap_1(D_1075,'#skF_2',k3_tmap_1(A_1076,'#skF_2','#skF_5',D_1075,'#skF_6'),G_1072)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_1072)
      | ~ m1_pre_topc(D_1075,'#skF_5')
      | ~ m1_subset_1(G_1072,u1_struct_0(D_1075))
      | ~ m1_subset_1(G_1072,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_1075,A_1076)
      | v2_struct_0(D_1075)
      | ~ m1_pre_topc('#skF_5',A_1076)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1076)
      | ~ v2_pre_topc(A_1076)
      | v2_struct_0(A_1076) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_60,c_58,c_4484])).

tff(c_7051,plain,(
    ! [D_1204,A_1205,G_1206] :
      ( r1_tmap_1(D_1204,'#skF_2',k3_tmap_1(A_1205,'#skF_2','#skF_5',D_1204,'#skF_6'),G_1206)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_1206)
      | ~ m1_pre_topc(D_1204,'#skF_5')
      | ~ m1_subset_1(G_1206,u1_struct_0(D_1204))
      | ~ m1_subset_1(G_1206,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_1204,A_1205)
      | v2_struct_0(D_1204)
      | ~ m1_pre_topc('#skF_5',A_1205)
      | ~ l1_pre_topc(A_1205)
      | ~ v2_pre_topc(A_1205)
      | v2_struct_0(A_1205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_64,c_4490])).

tff(c_3208,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_7056,plain,
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
    inference(resolution,[status(thm)],[c_7051,c_3208])).

tff(c_7063,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_62,c_66,c_50,c_91,c_54,c_3209,c_7056])).

tff(c_7065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_7063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.78/2.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/2.65  
% 7.78/2.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/2.66  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4
% 7.78/2.66  
% 7.78/2.66  %Foreground sorts:
% 7.78/2.66  
% 7.78/2.66  
% 7.78/2.66  %Background operators:
% 7.78/2.66  
% 7.78/2.66  
% 7.78/2.66  %Foreground operators:
% 7.78/2.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.78/2.66  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 7.78/2.66  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.78/2.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.78/2.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.78/2.66  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.78/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.78/2.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.78/2.66  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 7.78/2.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.78/2.66  tff('#skF_7', type, '#skF_7': $i).
% 7.78/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.78/2.66  tff('#skF_5', type, '#skF_5': $i).
% 7.78/2.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.78/2.66  tff('#skF_6', type, '#skF_6': $i).
% 7.78/2.66  tff('#skF_2', type, '#skF_2': $i).
% 7.78/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.78/2.66  tff('#skF_9', type, '#skF_9': $i).
% 7.78/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.78/2.66  tff('#skF_8', type, '#skF_8': $i).
% 7.78/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.78/2.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.78/2.66  tff('#skF_4', type, '#skF_4': $i).
% 7.78/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.78/2.66  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.78/2.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.78/2.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.78/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.78/2.66  
% 8.05/2.68  tff(f_281, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tmap_1)).
% 8.05/2.68  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.05/2.68  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.05/2.68  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 8.05/2.68  tff(f_223, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 8.05/2.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.05/2.68  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 8.05/2.68  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 8.05/2.68  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 8.05/2.68  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 8.05/2.68  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 8.05/2.68  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_72, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_62, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_66, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_50, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_40, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_48, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_91, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_48])).
% 8.05/2.68  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_42, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_98, plain, (![B_695, A_696]: (l1_pre_topc(B_695) | ~m1_pre_topc(B_695, A_696) | ~l1_pre_topc(A_696))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.05/2.68  tff(c_104, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_98])).
% 8.05/2.68  tff(c_111, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_104])).
% 8.05/2.68  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.05/2.68  tff(c_240, plain, (![C_720, A_721, B_722]: (m1_subset_1(C_720, k1_zfmisc_1(u1_struct_0(A_721))) | ~m1_subset_1(C_720, k1_zfmisc_1(u1_struct_0(B_722))) | ~m1_pre_topc(B_722, A_721) | ~l1_pre_topc(A_721))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.05/2.68  tff(c_270, plain, (![A_729, A_730, B_731]: (m1_subset_1(A_729, k1_zfmisc_1(u1_struct_0(A_730))) | ~m1_pre_topc(B_731, A_730) | ~l1_pre_topc(A_730) | ~r1_tarski(A_729, u1_struct_0(B_731)))), inference(resolution, [status(thm)], [c_10, c_240])).
% 8.05/2.68  tff(c_274, plain, (![A_729]: (m1_subset_1(A_729, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_729, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_54, c_270])).
% 8.05/2.68  tff(c_282, plain, (![A_729]: (m1_subset_1(A_729, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(A_729, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_274])).
% 8.05/2.68  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_82, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_90, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_82])).
% 8.05/2.68  tff(c_170, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_90])).
% 8.05/2.68  tff(c_78, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_58, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_88, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_89, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_88])).
% 8.05/2.68  tff(c_239, plain, (r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_170, c_89])).
% 8.05/2.68  tff(c_1941, plain, (![B_884, C_885, E_881, D_883, H_879, F_880, A_882]: (r1_tmap_1(D_883, B_884, E_881, H_879) | ~r1_tmap_1(C_885, B_884, k3_tmap_1(A_882, B_884, D_883, C_885, E_881), H_879) | ~m1_connsp_2(F_880, D_883, H_879) | ~r1_tarski(F_880, u1_struct_0(C_885)) | ~m1_subset_1(H_879, u1_struct_0(C_885)) | ~m1_subset_1(H_879, u1_struct_0(D_883)) | ~m1_subset_1(F_880, k1_zfmisc_1(u1_struct_0(D_883))) | ~m1_pre_topc(C_885, D_883) | ~m1_subset_1(E_881, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_883), u1_struct_0(B_884)))) | ~v1_funct_2(E_881, u1_struct_0(D_883), u1_struct_0(B_884)) | ~v1_funct_1(E_881) | ~m1_pre_topc(D_883, A_882) | v2_struct_0(D_883) | ~m1_pre_topc(C_885, A_882) | v2_struct_0(C_885) | ~l1_pre_topc(B_884) | ~v2_pre_topc(B_884) | v2_struct_0(B_884) | ~l1_pre_topc(A_882) | ~v2_pre_topc(A_882) | v2_struct_0(A_882))), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.05/2.68  tff(c_1943, plain, (![F_880]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_connsp_2(F_880, '#skF_5', '#skF_8') | ~r1_tarski(F_880, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_880, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_239, c_1941])).
% 8.05/2.68  tff(c_1946, plain, (![F_880]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_connsp_2(F_880, '#skF_5', '#skF_8') | ~r1_tarski(F_880, u1_struct_0('#skF_4')) | ~m1_subset_1(F_880, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_78, c_76, c_66, c_62, c_60, c_58, c_56, c_54, c_50, c_91, c_1943])).
% 8.05/2.68  tff(c_1948, plain, (![F_886]: (~m1_connsp_2(F_886, '#skF_5', '#skF_8') | ~r1_tarski(F_886, u1_struct_0('#skF_4')) | ~m1_subset_1(F_886, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_80, c_68, c_64, c_170, c_1946])).
% 8.05/2.68  tff(c_1994, plain, (![A_887]: (~m1_connsp_2(A_887, '#skF_5', '#skF_8') | ~r1_tarski(A_887, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_282, c_1948])).
% 8.05/2.68  tff(c_2056, plain, (~m1_connsp_2('#skF_7', '#skF_5', '#skF_8')), inference(resolution, [status(thm)], [c_42, c_1994])).
% 8.05/2.68  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.05/2.68  tff(c_322, plain, (![D_735, C_736, A_737]: (v3_pre_topc(D_735, C_736) | ~m1_subset_1(D_735, k1_zfmisc_1(u1_struct_0(C_736))) | ~v3_pre_topc(D_735, A_737) | ~m1_pre_topc(C_736, A_737) | ~m1_subset_1(D_735, k1_zfmisc_1(u1_struct_0(A_737))) | ~l1_pre_topc(A_737))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.05/2.68  tff(c_2059, plain, (![A_889, C_890, A_891]: (v3_pre_topc(A_889, C_890) | ~v3_pre_topc(A_889, A_891) | ~m1_pre_topc(C_890, A_891) | ~m1_subset_1(A_889, k1_zfmisc_1(u1_struct_0(A_891))) | ~l1_pre_topc(A_891) | ~r1_tarski(A_889, u1_struct_0(C_890)))), inference(resolution, [status(thm)], [c_10, c_322])).
% 8.05/2.68  tff(c_2063, plain, (![A_889]: (v3_pre_topc(A_889, '#skF_4') | ~v3_pre_topc(A_889, '#skF_5') | ~m1_subset_1(A_889, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_889, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_54, c_2059])).
% 8.05/2.68  tff(c_2078, plain, (![A_892]: (v3_pre_topc(A_892, '#skF_4') | ~v3_pre_topc(A_892, '#skF_5') | ~m1_subset_1(A_892, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(A_892, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2063])).
% 8.05/2.68  tff(c_2124, plain, (![A_893]: (v3_pre_topc(A_893, '#skF_4') | ~v3_pre_topc(A_893, '#skF_5') | ~r1_tarski(A_893, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_282, c_2078])).
% 8.05/2.68  tff(c_2186, plain, (v3_pre_topc('#skF_7', '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_2124])).
% 8.05/2.68  tff(c_2188, plain, (~v3_pre_topc('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_2186])).
% 8.05/2.68  tff(c_289, plain, (![A_732]: (m1_subset_1(A_732, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(A_732, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_274])).
% 8.05/2.68  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.05/2.68  tff(c_299, plain, (![A_732]: (r1_tarski(A_732, u1_struct_0('#skF_5')) | ~r1_tarski(A_732, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_289, c_8])).
% 8.05/2.68  tff(c_276, plain, (![A_729]: (m1_subset_1(A_729, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_729, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_62, c_270])).
% 8.05/2.68  tff(c_311, plain, (![A_734]: (m1_subset_1(A_734, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_734, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_276])).
% 8.05/2.68  tff(c_340, plain, (![A_738]: (r1_tarski(A_738, u1_struct_0('#skF_3')) | ~r1_tarski(A_738, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_311, c_8])).
% 8.05/2.68  tff(c_356, plain, (r1_tarski(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_340])).
% 8.05/2.68  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_117, plain, (![A_697, B_698]: (r1_tarski(A_697, B_698) | ~m1_subset_1(A_697, k1_zfmisc_1(B_698)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.05/2.68  tff(c_121, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_117])).
% 8.05/2.68  tff(c_44, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_171, plain, (![A_705, C_706, B_707]: (m1_subset_1(A_705, C_706) | ~m1_subset_1(B_707, k1_zfmisc_1(C_706)) | ~r2_hidden(A_705, B_707))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.05/2.68  tff(c_182, plain, (![A_709, B_710, A_711]: (m1_subset_1(A_709, B_710) | ~r2_hidden(A_709, A_711) | ~r1_tarski(A_711, B_710))), inference(resolution, [status(thm)], [c_10, c_171])).
% 8.05/2.68  tff(c_186, plain, (![B_712]: (m1_subset_1('#skF_8', B_712) | ~r1_tarski('#skF_7', B_712))), inference(resolution, [status(thm)], [c_44, c_182])).
% 8.05/2.68  tff(c_197, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_121, c_186])).
% 8.05/2.68  tff(c_46, plain, (v3_pre_topc('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_281])).
% 8.05/2.68  tff(c_278, plain, (![A_729]: (m1_subset_1(A_729, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_729, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_66, c_270])).
% 8.05/2.68  tff(c_288, plain, (![A_729]: (m1_subset_1(A_729, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_729, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_278])).
% 8.05/2.68  tff(c_1000, plain, (![C_798, A_799, B_800, D_801]: (m1_connsp_2(C_798, A_799, B_800) | ~r2_hidden(B_800, D_801) | ~r1_tarski(D_801, C_798) | ~v3_pre_topc(D_801, A_799) | ~m1_subset_1(D_801, k1_zfmisc_1(u1_struct_0(A_799))) | ~m1_subset_1(C_798, k1_zfmisc_1(u1_struct_0(A_799))) | ~m1_subset_1(B_800, u1_struct_0(A_799)) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799) | v2_struct_0(A_799))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.05/2.68  tff(c_2189, plain, (![C_894, A_895]: (m1_connsp_2(C_894, A_895, '#skF_8') | ~r1_tarski('#skF_7', C_894) | ~v3_pre_topc('#skF_7', A_895) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_895))) | ~m1_subset_1(C_894, k1_zfmisc_1(u1_struct_0(A_895))) | ~m1_subset_1('#skF_8', u1_struct_0(A_895)) | ~l1_pre_topc(A_895) | ~v2_pre_topc(A_895) | v2_struct_0(A_895))), inference(resolution, [status(thm)], [c_44, c_1000])).
% 8.05/2.68  tff(c_2201, plain, (![C_894]: (m1_connsp_2(C_894, '#skF_3', '#skF_8') | ~r1_tarski('#skF_7', C_894) | ~v3_pre_topc('#skF_7', '#skF_3') | ~m1_subset_1(C_894, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_7', u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_288, c_2189])).
% 8.05/2.68  tff(c_2224, plain, (![C_894]: (m1_connsp_2(C_894, '#skF_3', '#skF_8') | ~r1_tarski('#skF_7', C_894) | ~m1_subset_1(C_894, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_72, c_70, c_197, c_46, c_2201])).
% 8.05/2.68  tff(c_2280, plain, (![C_899]: (m1_connsp_2(C_899, '#skF_3', '#skF_8') | ~r1_tarski('#skF_7', C_899) | ~m1_subset_1(C_899, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_2224])).
% 8.05/2.68  tff(c_2410, plain, (![A_901]: (m1_connsp_2(A_901, '#skF_3', '#skF_8') | ~r1_tarski('#skF_7', A_901) | ~r1_tarski(A_901, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_2280])).
% 8.05/2.68  tff(c_2481, plain, (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_356, c_2410])).
% 8.05/2.68  tff(c_2491, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_2481])).
% 8.05/2.68  tff(c_2498, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_299, c_2491])).
% 8.05/2.68  tff(c_2508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_2498])).
% 8.05/2.68  tff(c_2510, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_2481])).
% 8.05/2.68  tff(c_2065, plain, (![A_889]: (v3_pre_topc(A_889, '#skF_5') | ~v3_pre_topc(A_889, '#skF_3') | ~m1_subset_1(A_889, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_889, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_62, c_2059])).
% 8.05/2.68  tff(c_2606, plain, (![A_909]: (v3_pre_topc(A_909, '#skF_5') | ~v3_pre_topc(A_909, '#skF_3') | ~m1_subset_1(A_909, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_909, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2065])).
% 8.05/2.68  tff(c_2639, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_3') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_2606])).
% 8.05/2.68  tff(c_2662, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2510, c_46, c_2639])).
% 8.05/2.68  tff(c_2664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2188, c_2662])).
% 8.05/2.68  tff(c_2666, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_2186])).
% 8.05/2.68  tff(c_149, plain, (![B_703, A_704]: (v2_pre_topc(B_703) | ~m1_pre_topc(B_703, A_704) | ~l1_pre_topc(A_704) | ~v2_pre_topc(A_704))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.05/2.68  tff(c_155, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_149])).
% 8.05/2.68  tff(c_164, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_155])).
% 8.05/2.68  tff(c_2667, plain, (![C_910, A_911]: (m1_connsp_2(C_910, A_911, '#skF_8') | ~r1_tarski('#skF_7', C_910) | ~v3_pre_topc('#skF_7', A_911) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_911))) | ~m1_subset_1(C_910, k1_zfmisc_1(u1_struct_0(A_911))) | ~m1_subset_1('#skF_8', u1_struct_0(A_911)) | ~l1_pre_topc(A_911) | ~v2_pre_topc(A_911) | v2_struct_0(A_911))), inference(resolution, [status(thm)], [c_44, c_1000])).
% 8.05/2.68  tff(c_2685, plain, (![C_910]: (m1_connsp_2(C_910, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_910) | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(C_910, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski('#skF_7', u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_282, c_2667])).
% 8.05/2.68  tff(c_2710, plain, (![C_910]: (m1_connsp_2(C_910, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_910) | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(C_910, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_164, c_111, c_50, c_2685])).
% 8.05/2.68  tff(c_2711, plain, (![C_910]: (m1_connsp_2(C_910, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_910) | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(C_910, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_2710])).
% 8.05/2.68  tff(c_3009, plain, (![C_921]: (m1_connsp_2(C_921, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_921) | ~m1_subset_1(C_921, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_2666, c_2711])).
% 8.05/2.68  tff(c_3132, plain, (![A_923]: (m1_connsp_2(A_923, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', A_923) | ~r1_tarski(A_923, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_282, c_3009])).
% 8.05/2.68  tff(c_3171, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_42, c_3132])).
% 8.05/2.68  tff(c_3205, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3171])).
% 8.05/2.68  tff(c_3207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2056, c_3205])).
% 8.05/2.68  tff(c_3209, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 8.05/2.68  tff(c_4482, plain, (![D_1075, A_1076, G_1072, C_1073, E_1077, B_1074]: (r1_tmap_1(D_1075, B_1074, k3_tmap_1(A_1076, B_1074, C_1073, D_1075, E_1077), G_1072) | ~r1_tmap_1(C_1073, B_1074, E_1077, G_1072) | ~m1_pre_topc(D_1075, C_1073) | ~m1_subset_1(G_1072, u1_struct_0(D_1075)) | ~m1_subset_1(G_1072, u1_struct_0(C_1073)) | ~m1_subset_1(E_1077, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1073), u1_struct_0(B_1074)))) | ~v1_funct_2(E_1077, u1_struct_0(C_1073), u1_struct_0(B_1074)) | ~v1_funct_1(E_1077) | ~m1_pre_topc(D_1075, A_1076) | v2_struct_0(D_1075) | ~m1_pre_topc(C_1073, A_1076) | v2_struct_0(C_1073) | ~l1_pre_topc(B_1074) | ~v2_pre_topc(B_1074) | v2_struct_0(B_1074) | ~l1_pre_topc(A_1076) | ~v2_pre_topc(A_1076) | v2_struct_0(A_1076))), inference(cnfTransformation, [status(thm)], [f_168])).
% 8.05/2.68  tff(c_4484, plain, (![D_1075, A_1076, G_1072]: (r1_tmap_1(D_1075, '#skF_2', k3_tmap_1(A_1076, '#skF_2', '#skF_5', D_1075, '#skF_6'), G_1072) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_1072) | ~m1_pre_topc(D_1075, '#skF_5') | ~m1_subset_1(G_1072, u1_struct_0(D_1075)) | ~m1_subset_1(G_1072, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_1075, A_1076) | v2_struct_0(D_1075) | ~m1_pre_topc('#skF_5', A_1076) | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1076) | ~v2_pre_topc(A_1076) | v2_struct_0(A_1076))), inference(resolution, [status(thm)], [c_56, c_4482])).
% 8.05/2.68  tff(c_4490, plain, (![D_1075, A_1076, G_1072]: (r1_tmap_1(D_1075, '#skF_2', k3_tmap_1(A_1076, '#skF_2', '#skF_5', D_1075, '#skF_6'), G_1072) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_1072) | ~m1_pre_topc(D_1075, '#skF_5') | ~m1_subset_1(G_1072, u1_struct_0(D_1075)) | ~m1_subset_1(G_1072, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_1075, A_1076) | v2_struct_0(D_1075) | ~m1_pre_topc('#skF_5', A_1076) | v2_struct_0('#skF_5') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1076) | ~v2_pre_topc(A_1076) | v2_struct_0(A_1076))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_60, c_58, c_4484])).
% 8.05/2.68  tff(c_7051, plain, (![D_1204, A_1205, G_1206]: (r1_tmap_1(D_1204, '#skF_2', k3_tmap_1(A_1205, '#skF_2', '#skF_5', D_1204, '#skF_6'), G_1206) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_1206) | ~m1_pre_topc(D_1204, '#skF_5') | ~m1_subset_1(G_1206, u1_struct_0(D_1204)) | ~m1_subset_1(G_1206, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_1204, A_1205) | v2_struct_0(D_1204) | ~m1_pre_topc('#skF_5', A_1205) | ~l1_pre_topc(A_1205) | ~v2_pre_topc(A_1205) | v2_struct_0(A_1205))), inference(negUnitSimplification, [status(thm)], [c_80, c_64, c_4490])).
% 8.05/2.68  tff(c_3208, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 8.05/2.68  tff(c_7056, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_7051, c_3208])).
% 8.05/2.68  tff(c_7063, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_62, c_66, c_50, c_91, c_54, c_3209, c_7056])).
% 8.05/2.68  tff(c_7065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_7063])).
% 8.05/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.05/2.68  
% 8.05/2.68  Inference rules
% 8.05/2.68  ----------------------
% 8.05/2.68  #Ref     : 0
% 8.05/2.68  #Sup     : 1285
% 8.05/2.68  #Fact    : 0
% 8.05/2.68  #Define  : 0
% 8.05/2.68  #Split   : 32
% 8.05/2.68  #Chain   : 0
% 8.05/2.68  #Close   : 0
% 8.05/2.68  
% 8.05/2.68  Ordering : KBO
% 8.05/2.68  
% 8.05/2.68  Simplification rules
% 8.05/2.68  ----------------------
% 8.05/2.68  #Subsume      : 398
% 8.05/2.68  #Demod        : 1239
% 8.05/2.68  #Tautology    : 173
% 8.05/2.68  #SimpNegUnit  : 122
% 8.05/2.68  #BackRed      : 0
% 8.05/2.68  
% 8.05/2.68  #Partial instantiations: 0
% 8.05/2.68  #Strategies tried      : 1
% 8.05/2.68  
% 8.05/2.68  Timing (in seconds)
% 8.05/2.68  ----------------------
% 8.05/2.69  Preprocessing        : 0.45
% 8.05/2.69  Parsing              : 0.22
% 8.08/2.69  CNF conversion       : 0.08
% 8.08/2.69  Main loop            : 1.38
% 8.08/2.69  Inferencing          : 0.46
% 8.08/2.69  Reduction            : 0.45
% 8.08/2.69  Demodulation         : 0.32
% 8.08/2.69  BG Simplification    : 0.05
% 8.08/2.69  Subsumption          : 0.33
% 8.08/2.69  Abstraction          : 0.05
% 8.08/2.69  MUC search           : 0.00
% 8.08/2.69  Cooper               : 0.00
% 8.08/2.69  Total                : 1.88
% 8.08/2.69  Index Insertion      : 0.00
% 8.08/2.69  Index Deletion       : 0.00
% 8.08/2.69  Index Matching       : 0.00
% 8.08/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
