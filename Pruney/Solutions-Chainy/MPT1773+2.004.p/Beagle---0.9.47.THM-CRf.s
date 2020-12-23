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
% DateTime   : Thu Dec  3 10:27:22 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 353 expanded)
%              Number of leaves         :   39 ( 155 expanded)
%              Depth                    :   15
%              Number of atoms          :  454 (3087 expanded)
%              Number of equality atoms :   33 ( 147 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_323,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_107,axiom,(
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

tff(f_166,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_134,axiom,(
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
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_253,axiom,(
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

tff(f_206,axiom,(
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
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_40,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_48,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_91,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_48])).

tff(c_42,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_78,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_62,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_129,plain,(
    ! [B_540,A_541] :
      ( v2_pre_topc(B_540)
      | ~ m1_pre_topc(B_540,A_541)
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_135,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_129])).

tff(c_144,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_135])).

tff(c_98,plain,(
    ! [B_536,A_537] :
      ( l1_pre_topc(B_536)
      | ~ m1_pre_topc(B_536,A_537)
      | ~ l1_pre_topc(A_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_104,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_98])).

tff(c_111,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_104])).

tff(c_46,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_44,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_419,plain,(
    ! [C_595,A_596,B_597,D_598] :
      ( m1_connsp_2(C_595,A_596,B_597)
      | ~ r2_hidden(B_597,D_598)
      | ~ r1_tarski(D_598,C_595)
      | ~ v3_pre_topc(D_598,A_596)
      | ~ m1_subset_1(D_598,k1_zfmisc_1(u1_struct_0(A_596)))
      | ~ m1_subset_1(C_595,k1_zfmisc_1(u1_struct_0(A_596)))
      | ~ m1_subset_1(B_597,u1_struct_0(A_596))
      | ~ l1_pre_topc(A_596)
      | ~ v2_pre_topc(A_596)
      | v2_struct_0(A_596) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_442,plain,(
    ! [C_604,A_605] :
      ( m1_connsp_2(C_604,A_605,'#skF_8')
      | ~ r1_tarski('#skF_7',C_604)
      | ~ v3_pre_topc('#skF_7',A_605)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_605)))
      | ~ m1_subset_1(C_604,k1_zfmisc_1(u1_struct_0(A_605)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_605))
      | ~ l1_pre_topc(A_605)
      | ~ v2_pre_topc(A_605)
      | v2_struct_0(A_605) ) ),
    inference(resolution,[status(thm)],[c_44,c_419])).

tff(c_444,plain,(
    ! [C_604] :
      ( m1_connsp_2(C_604,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_604)
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(C_604,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_442])).

tff(c_447,plain,(
    ! [C_604] :
      ( m1_connsp_2(C_604,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_604)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_111,c_50,c_46,c_444])).

tff(c_449,plain,(
    ! [C_606] :
      ( m1_connsp_2(C_606,'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',C_606)
      | ~ m1_subset_1(C_606,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_447])).

tff(c_456,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_8')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_449])).

tff(c_463,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_456])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_82,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_90,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_82])).

tff(c_128,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_72,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_58,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_66,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_532,plain,(
    ! [D_617,E_619,B_615,A_618,C_616] :
      ( k3_tmap_1(A_618,B_615,C_616,D_617,E_619) = k2_partfun1(u1_struct_0(C_616),u1_struct_0(B_615),E_619,u1_struct_0(D_617))
      | ~ m1_pre_topc(D_617,C_616)
      | ~ m1_subset_1(E_619,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_616),u1_struct_0(B_615))))
      | ~ v1_funct_2(E_619,u1_struct_0(C_616),u1_struct_0(B_615))
      | ~ v1_funct_1(E_619)
      | ~ m1_pre_topc(D_617,A_618)
      | ~ m1_pre_topc(C_616,A_618)
      | ~ l1_pre_topc(B_615)
      | ~ v2_pre_topc(B_615)
      | v2_struct_0(B_615)
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_534,plain,(
    ! [A_618,D_617] :
      ( k3_tmap_1(A_618,'#skF_3','#skF_5',D_617,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_617))
      | ~ m1_pre_topc(D_617,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_617,A_618)
      | ~ m1_pre_topc('#skF_5',A_618)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(resolution,[status(thm)],[c_56,c_532])).

tff(c_537,plain,(
    ! [A_618,D_617] :
      ( k3_tmap_1(A_618,'#skF_3','#skF_5',D_617,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_617))
      | ~ m1_pre_topc(D_617,'#skF_5')
      | ~ m1_pre_topc(D_617,A_618)
      | ~ m1_pre_topc('#skF_5',A_618)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_618)
      | ~ v2_pre_topc(A_618)
      | v2_struct_0(A_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_58,c_534])).

tff(c_539,plain,(
    ! [A_620,D_621] :
      ( k3_tmap_1(A_620,'#skF_3','#skF_5',D_621,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_621))
      | ~ m1_pre_topc(D_621,'#skF_5')
      | ~ m1_pre_topc(D_621,A_620)
      | ~ m1_pre_topc('#skF_5',A_620)
      | ~ l1_pre_topc(A_620)
      | ~ v2_pre_topc(A_620)
      | v2_struct_0(A_620) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_537])).

tff(c_547,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_539])).

tff(c_559,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_54,c_547])).

tff(c_560,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_559])).

tff(c_426,plain,(
    ! [A_599,B_600,C_601,D_602] :
      ( k2_partfun1(u1_struct_0(A_599),u1_struct_0(B_600),C_601,u1_struct_0(D_602)) = k2_tmap_1(A_599,B_600,C_601,D_602)
      | ~ m1_pre_topc(D_602,A_599)
      | ~ m1_subset_1(C_601,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_599),u1_struct_0(B_600))))
      | ~ v1_funct_2(C_601,u1_struct_0(A_599),u1_struct_0(B_600))
      | ~ v1_funct_1(C_601)
      | ~ l1_pre_topc(B_600)
      | ~ v2_pre_topc(B_600)
      | v2_struct_0(B_600)
      | ~ l1_pre_topc(A_599)
      | ~ v2_pre_topc(A_599)
      | v2_struct_0(A_599) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_428,plain,(
    ! [D_602] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_602)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_602)
      | ~ m1_pre_topc(D_602,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_426])).

tff(c_431,plain,(
    ! [D_602] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_602)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_602)
      | ~ m1_pre_topc(D_602,'#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_111,c_72,c_70,c_60,c_58,c_428])).

tff(c_432,plain,(
    ! [D_602] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_602)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_602)
      | ~ m1_pre_topc(D_602,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_74,c_431])).

tff(c_564,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_432])).

tff(c_571,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_564])).

tff(c_88,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_323])).

tff(c_89,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_88])).

tff(c_195,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_89])).

tff(c_576,plain,(
    r1_tmap_1('#skF_4','#skF_3',k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_195])).

tff(c_718,plain,(
    ! [A_667,G_666,C_662,D_663,B_665,E_664] :
      ( r1_tmap_1(B_665,A_667,C_662,G_666)
      | ~ r1_tmap_1(D_663,A_667,k2_tmap_1(B_665,A_667,C_662,D_663),G_666)
      | ~ m1_connsp_2(E_664,B_665,G_666)
      | ~ r1_tarski(E_664,u1_struct_0(D_663))
      | ~ m1_subset_1(G_666,u1_struct_0(D_663))
      | ~ m1_subset_1(G_666,u1_struct_0(B_665))
      | ~ m1_subset_1(E_664,k1_zfmisc_1(u1_struct_0(B_665)))
      | ~ m1_pre_topc(D_663,B_665)
      | v2_struct_0(D_663)
      | ~ m1_subset_1(C_662,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_665),u1_struct_0(A_667))))
      | ~ v1_funct_2(C_662,u1_struct_0(B_665),u1_struct_0(A_667))
      | ~ v1_funct_1(C_662)
      | ~ l1_pre_topc(B_665)
      | ~ v2_pre_topc(B_665)
      | v2_struct_0(B_665)
      | ~ l1_pre_topc(A_667)
      | ~ v2_pre_topc(A_667)
      | v2_struct_0(A_667) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_722,plain,(
    ! [E_664] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(E_664,'#skF_5','#skF_8')
      | ~ r1_tarski(E_664,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_664,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_576,c_718])).

tff(c_729,plain,(
    ! [E_664] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(E_664,'#skF_5','#skF_8')
      | ~ r1_tarski(E_664,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_664,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_144,c_111,c_60,c_58,c_56,c_54,c_50,c_91,c_722])).

tff(c_731,plain,(
    ! [E_668] :
      ( ~ m1_connsp_2(E_668,'#skF_5','#skF_8')
      | ~ r1_tarski(E_668,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_668,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_64,c_68,c_128,c_729])).

tff(c_747,plain,
    ( ~ m1_connsp_2('#skF_7','#skF_5','#skF_8')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_731])).

tff(c_758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_463,c_747])).

tff(c_760,plain,(
    r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_761,plain,(
    ! [B_669,A_670] :
      ( v2_pre_topc(B_669)
      | ~ m1_pre_topc(B_669,A_670)
      | ~ l1_pre_topc(A_670)
      | ~ v2_pre_topc(A_670) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_767,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_761])).

tff(c_776,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_767])).

tff(c_1243,plain,(
    ! [D_764,F_763,B_767,A_766,C_765] :
      ( r1_tmap_1(D_764,A_766,k2_tmap_1(B_767,A_766,C_765,D_764),F_763)
      | ~ r1_tmap_1(B_767,A_766,C_765,F_763)
      | ~ m1_subset_1(F_763,u1_struct_0(D_764))
      | ~ m1_subset_1(F_763,u1_struct_0(B_767))
      | ~ m1_pre_topc(D_764,B_767)
      | v2_struct_0(D_764)
      | ~ m1_subset_1(C_765,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_767),u1_struct_0(A_766))))
      | ~ v1_funct_2(C_765,u1_struct_0(B_767),u1_struct_0(A_766))
      | ~ v1_funct_1(C_765)
      | ~ l1_pre_topc(B_767)
      | ~ v2_pre_topc(B_767)
      | v2_struct_0(B_767)
      | ~ l1_pre_topc(A_766)
      | ~ v2_pre_topc(A_766)
      | v2_struct_0(A_766) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_1245,plain,(
    ! [D_764,F_763] :
      ( r1_tmap_1(D_764,'#skF_3',k2_tmap_1('#skF_5','#skF_3','#skF_6',D_764),F_763)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',F_763)
      | ~ m1_subset_1(F_763,u1_struct_0(D_764))
      | ~ m1_subset_1(F_763,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_764,'#skF_5')
      | v2_struct_0(D_764)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_1243])).

tff(c_1248,plain,(
    ! [D_764,F_763] :
      ( r1_tmap_1(D_764,'#skF_3',k2_tmap_1('#skF_5','#skF_3','#skF_6',D_764),F_763)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',F_763)
      | ~ m1_subset_1(F_763,u1_struct_0(D_764))
      | ~ m1_subset_1(F_763,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_764,'#skF_5')
      | v2_struct_0(D_764)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_776,c_111,c_60,c_58,c_1245])).

tff(c_1250,plain,(
    ! [D_768,F_769] :
      ( r1_tmap_1(D_768,'#skF_3',k2_tmap_1('#skF_5','#skF_3','#skF_6',D_768),F_769)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',F_769)
      | ~ m1_subset_1(F_769,u1_struct_0(D_768))
      | ~ m1_subset_1(F_769,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_768,'#skF_5')
      | v2_struct_0(D_768) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_64,c_1248])).

tff(c_1165,plain,(
    ! [E_750,B_746,D_748,C_747,A_749] :
      ( k3_tmap_1(A_749,B_746,C_747,D_748,E_750) = k2_partfun1(u1_struct_0(C_747),u1_struct_0(B_746),E_750,u1_struct_0(D_748))
      | ~ m1_pre_topc(D_748,C_747)
      | ~ m1_subset_1(E_750,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_747),u1_struct_0(B_746))))
      | ~ v1_funct_2(E_750,u1_struct_0(C_747),u1_struct_0(B_746))
      | ~ v1_funct_1(E_750)
      | ~ m1_pre_topc(D_748,A_749)
      | ~ m1_pre_topc(C_747,A_749)
      | ~ l1_pre_topc(B_746)
      | ~ v2_pre_topc(B_746)
      | v2_struct_0(B_746)
      | ~ l1_pre_topc(A_749)
      | ~ v2_pre_topc(A_749)
      | v2_struct_0(A_749) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1167,plain,(
    ! [A_749,D_748] :
      ( k3_tmap_1(A_749,'#skF_3','#skF_5',D_748,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_748))
      | ~ m1_pre_topc(D_748,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_748,A_749)
      | ~ m1_pre_topc('#skF_5',A_749)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_749)
      | ~ v2_pre_topc(A_749)
      | v2_struct_0(A_749) ) ),
    inference(resolution,[status(thm)],[c_56,c_1165])).

tff(c_1170,plain,(
    ! [A_749,D_748] :
      ( k3_tmap_1(A_749,'#skF_3','#skF_5',D_748,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_748))
      | ~ m1_pre_topc(D_748,'#skF_5')
      | ~ m1_pre_topc(D_748,A_749)
      | ~ m1_pre_topc('#skF_5',A_749)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_749)
      | ~ v2_pre_topc(A_749)
      | v2_struct_0(A_749) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_58,c_1167])).

tff(c_1172,plain,(
    ! [A_751,D_752] :
      ( k3_tmap_1(A_751,'#skF_3','#skF_5',D_752,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_752))
      | ~ m1_pre_topc(D_752,'#skF_5')
      | ~ m1_pre_topc(D_752,A_751)
      | ~ m1_pre_topc('#skF_5',A_751)
      | ~ l1_pre_topc(A_751)
      | ~ v2_pre_topc(A_751)
      | v2_struct_0(A_751) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1170])).

tff(c_1180,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1172])).

tff(c_1192,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_54,c_1180])).

tff(c_1193,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1192])).

tff(c_1065,plain,(
    ! [A_730,B_731,C_732,D_733] :
      ( k2_partfun1(u1_struct_0(A_730),u1_struct_0(B_731),C_732,u1_struct_0(D_733)) = k2_tmap_1(A_730,B_731,C_732,D_733)
      | ~ m1_pre_topc(D_733,A_730)
      | ~ m1_subset_1(C_732,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_730),u1_struct_0(B_731))))
      | ~ v1_funct_2(C_732,u1_struct_0(A_730),u1_struct_0(B_731))
      | ~ v1_funct_1(C_732)
      | ~ l1_pre_topc(B_731)
      | ~ v2_pre_topc(B_731)
      | v2_struct_0(B_731)
      | ~ l1_pre_topc(A_730)
      | ~ v2_pre_topc(A_730)
      | v2_struct_0(A_730) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1067,plain,(
    ! [D_733] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_733)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_733)
      | ~ m1_pre_topc(D_733,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1065])).

tff(c_1070,plain,(
    ! [D_733] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_733)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_733)
      | ~ m1_pre_topc(D_733,'#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_111,c_72,c_70,c_60,c_58,c_1067])).

tff(c_1071,plain,(
    ! [D_733] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_733)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_733)
      | ~ m1_pre_topc(D_733,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_74,c_1070])).

tff(c_1197,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_1071])).

tff(c_1204,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1197])).

tff(c_759,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_1209,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3',k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1204,c_759])).

tff(c_1253,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1250,c_1209])).

tff(c_1256,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_91,c_760,c_1253])).

tff(c_1258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.79  
% 4.69/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.80  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4
% 4.69/1.80  
% 4.69/1.80  %Foreground sorts:
% 4.69/1.80  
% 4.69/1.80  
% 4.69/1.80  %Background operators:
% 4.69/1.80  
% 4.69/1.80  
% 4.69/1.80  %Foreground operators:
% 4.69/1.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.69/1.80  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.69/1.80  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.69/1.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.69/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.69/1.80  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.69/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.69/1.80  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.69/1.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.69/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.69/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.69/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.69/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.69/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.69/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.69/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.69/1.80  tff('#skF_9', type, '#skF_9': $i).
% 4.69/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.69/1.80  tff('#skF_8', type, '#skF_8': $i).
% 4.69/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.69/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.69/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.80  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.69/1.80  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.69/1.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.69/1.80  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.69/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.69/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.69/1.80  
% 4.81/1.82  tff(f_323, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.81/1.82  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.81/1.82  tff(f_46, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.81/1.82  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.81/1.82  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 4.81/1.82  tff(f_166, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 4.81/1.82  tff(f_134, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.81/1.82  tff(f_253, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 4.81/1.82  tff(f_206, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 4.81/1.82  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_50, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_40, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_48, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_91, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_48])).
% 4.81/1.82  tff(c_42, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.81/1.82  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_78, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_62, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_129, plain, (![B_540, A_541]: (v2_pre_topc(B_540) | ~m1_pre_topc(B_540, A_541) | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.81/1.82  tff(c_135, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_129])).
% 4.81/1.82  tff(c_144, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_135])).
% 4.81/1.82  tff(c_98, plain, (![B_536, A_537]: (l1_pre_topc(B_536) | ~m1_pre_topc(B_536, A_537) | ~l1_pre_topc(A_537))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.81/1.82  tff(c_104, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_98])).
% 4.81/1.82  tff(c_111, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_104])).
% 4.81/1.82  tff(c_46, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_44, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_419, plain, (![C_595, A_596, B_597, D_598]: (m1_connsp_2(C_595, A_596, B_597) | ~r2_hidden(B_597, D_598) | ~r1_tarski(D_598, C_595) | ~v3_pre_topc(D_598, A_596) | ~m1_subset_1(D_598, k1_zfmisc_1(u1_struct_0(A_596))) | ~m1_subset_1(C_595, k1_zfmisc_1(u1_struct_0(A_596))) | ~m1_subset_1(B_597, u1_struct_0(A_596)) | ~l1_pre_topc(A_596) | ~v2_pre_topc(A_596) | v2_struct_0(A_596))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.81/1.82  tff(c_442, plain, (![C_604, A_605]: (m1_connsp_2(C_604, A_605, '#skF_8') | ~r1_tarski('#skF_7', C_604) | ~v3_pre_topc('#skF_7', A_605) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_605))) | ~m1_subset_1(C_604, k1_zfmisc_1(u1_struct_0(A_605))) | ~m1_subset_1('#skF_8', u1_struct_0(A_605)) | ~l1_pre_topc(A_605) | ~v2_pre_topc(A_605) | v2_struct_0(A_605))), inference(resolution, [status(thm)], [c_44, c_419])).
% 4.81/1.82  tff(c_444, plain, (![C_604]: (m1_connsp_2(C_604, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_604) | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(C_604, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_442])).
% 4.81/1.82  tff(c_447, plain, (![C_604]: (m1_connsp_2(C_604, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_604) | ~m1_subset_1(C_604, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_111, c_50, c_46, c_444])).
% 4.81/1.82  tff(c_449, plain, (![C_606]: (m1_connsp_2(C_606, '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', C_606) | ~m1_subset_1(C_606, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_447])).
% 4.81/1.82  tff(c_456, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_449])).
% 4.81/1.82  tff(c_463, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_456])).
% 4.81/1.82  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_82, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_90, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_82])).
% 4.81/1.82  tff(c_128, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_90])).
% 4.81/1.82  tff(c_72, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_58, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_66, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_532, plain, (![D_617, E_619, B_615, A_618, C_616]: (k3_tmap_1(A_618, B_615, C_616, D_617, E_619)=k2_partfun1(u1_struct_0(C_616), u1_struct_0(B_615), E_619, u1_struct_0(D_617)) | ~m1_pre_topc(D_617, C_616) | ~m1_subset_1(E_619, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_616), u1_struct_0(B_615)))) | ~v1_funct_2(E_619, u1_struct_0(C_616), u1_struct_0(B_615)) | ~v1_funct_1(E_619) | ~m1_pre_topc(D_617, A_618) | ~m1_pre_topc(C_616, A_618) | ~l1_pre_topc(B_615) | ~v2_pre_topc(B_615) | v2_struct_0(B_615) | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.81/1.82  tff(c_534, plain, (![A_618, D_617]: (k3_tmap_1(A_618, '#skF_3', '#skF_5', D_617, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_617)) | ~m1_pre_topc(D_617, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_617, A_618) | ~m1_pre_topc('#skF_5', A_618) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618))), inference(resolution, [status(thm)], [c_56, c_532])).
% 4.81/1.82  tff(c_537, plain, (![A_618, D_617]: (k3_tmap_1(A_618, '#skF_3', '#skF_5', D_617, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_617)) | ~m1_pre_topc(D_617, '#skF_5') | ~m1_pre_topc(D_617, A_618) | ~m1_pre_topc('#skF_5', A_618) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_618) | ~v2_pre_topc(A_618) | v2_struct_0(A_618))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_58, c_534])).
% 4.81/1.82  tff(c_539, plain, (![A_620, D_621]: (k3_tmap_1(A_620, '#skF_3', '#skF_5', D_621, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_621)) | ~m1_pre_topc(D_621, '#skF_5') | ~m1_pre_topc(D_621, A_620) | ~m1_pre_topc('#skF_5', A_620) | ~l1_pre_topc(A_620) | ~v2_pre_topc(A_620) | v2_struct_0(A_620))), inference(negUnitSimplification, [status(thm)], [c_74, c_537])).
% 4.81/1.82  tff(c_547, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_539])).
% 4.81/1.82  tff(c_559, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_62, c_54, c_547])).
% 4.81/1.82  tff(c_560, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_80, c_559])).
% 4.81/1.82  tff(c_426, plain, (![A_599, B_600, C_601, D_602]: (k2_partfun1(u1_struct_0(A_599), u1_struct_0(B_600), C_601, u1_struct_0(D_602))=k2_tmap_1(A_599, B_600, C_601, D_602) | ~m1_pre_topc(D_602, A_599) | ~m1_subset_1(C_601, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_599), u1_struct_0(B_600)))) | ~v1_funct_2(C_601, u1_struct_0(A_599), u1_struct_0(B_600)) | ~v1_funct_1(C_601) | ~l1_pre_topc(B_600) | ~v2_pre_topc(B_600) | v2_struct_0(B_600) | ~l1_pre_topc(A_599) | ~v2_pre_topc(A_599) | v2_struct_0(A_599))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.81/1.82  tff(c_428, plain, (![D_602]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_602))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_602) | ~m1_pre_topc(D_602, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_426])).
% 4.81/1.82  tff(c_431, plain, (![D_602]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_602))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_602) | ~m1_pre_topc(D_602, '#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_111, c_72, c_70, c_60, c_58, c_428])).
% 4.81/1.82  tff(c_432, plain, (![D_602]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_602))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_602) | ~m1_pre_topc(D_602, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_74, c_431])).
% 4.81/1.82  tff(c_564, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_560, c_432])).
% 4.81/1.82  tff(c_571, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_564])).
% 4.81/1.82  tff(c_88, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_323])).
% 4.81/1.82  tff(c_89, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_88])).
% 4.81/1.82  tff(c_195, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_128, c_89])).
% 4.81/1.82  tff(c_576, plain, (r1_tmap_1('#skF_4', '#skF_3', k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_571, c_195])).
% 4.81/1.82  tff(c_718, plain, (![A_667, G_666, C_662, D_663, B_665, E_664]: (r1_tmap_1(B_665, A_667, C_662, G_666) | ~r1_tmap_1(D_663, A_667, k2_tmap_1(B_665, A_667, C_662, D_663), G_666) | ~m1_connsp_2(E_664, B_665, G_666) | ~r1_tarski(E_664, u1_struct_0(D_663)) | ~m1_subset_1(G_666, u1_struct_0(D_663)) | ~m1_subset_1(G_666, u1_struct_0(B_665)) | ~m1_subset_1(E_664, k1_zfmisc_1(u1_struct_0(B_665))) | ~m1_pre_topc(D_663, B_665) | v2_struct_0(D_663) | ~m1_subset_1(C_662, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_665), u1_struct_0(A_667)))) | ~v1_funct_2(C_662, u1_struct_0(B_665), u1_struct_0(A_667)) | ~v1_funct_1(C_662) | ~l1_pre_topc(B_665) | ~v2_pre_topc(B_665) | v2_struct_0(B_665) | ~l1_pre_topc(A_667) | ~v2_pre_topc(A_667) | v2_struct_0(A_667))), inference(cnfTransformation, [status(thm)], [f_253])).
% 4.81/1.82  tff(c_722, plain, (![E_664]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(E_664, '#skF_5', '#skF_8') | ~r1_tarski(E_664, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(E_664, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_576, c_718])).
% 4.81/1.82  tff(c_729, plain, (![E_664]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(E_664, '#skF_5', '#skF_8') | ~r1_tarski(E_664, u1_struct_0('#skF_4')) | ~m1_subset_1(E_664, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_144, c_111, c_60, c_58, c_56, c_54, c_50, c_91, c_722])).
% 4.81/1.82  tff(c_731, plain, (![E_668]: (~m1_connsp_2(E_668, '#skF_5', '#skF_8') | ~r1_tarski(E_668, u1_struct_0('#skF_4')) | ~m1_subset_1(E_668, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_64, c_68, c_128, c_729])).
% 4.81/1.82  tff(c_747, plain, (~m1_connsp_2('#skF_7', '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_731])).
% 4.81/1.82  tff(c_758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_463, c_747])).
% 4.81/1.82  tff(c_760, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 4.81/1.82  tff(c_761, plain, (![B_669, A_670]: (v2_pre_topc(B_669) | ~m1_pre_topc(B_669, A_670) | ~l1_pre_topc(A_670) | ~v2_pre_topc(A_670))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.81/1.82  tff(c_767, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_761])).
% 4.81/1.82  tff(c_776, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_767])).
% 4.81/1.82  tff(c_1243, plain, (![D_764, F_763, B_767, A_766, C_765]: (r1_tmap_1(D_764, A_766, k2_tmap_1(B_767, A_766, C_765, D_764), F_763) | ~r1_tmap_1(B_767, A_766, C_765, F_763) | ~m1_subset_1(F_763, u1_struct_0(D_764)) | ~m1_subset_1(F_763, u1_struct_0(B_767)) | ~m1_pre_topc(D_764, B_767) | v2_struct_0(D_764) | ~m1_subset_1(C_765, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_767), u1_struct_0(A_766)))) | ~v1_funct_2(C_765, u1_struct_0(B_767), u1_struct_0(A_766)) | ~v1_funct_1(C_765) | ~l1_pre_topc(B_767) | ~v2_pre_topc(B_767) | v2_struct_0(B_767) | ~l1_pre_topc(A_766) | ~v2_pre_topc(A_766) | v2_struct_0(A_766))), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.81/1.82  tff(c_1245, plain, (![D_764, F_763]: (r1_tmap_1(D_764, '#skF_3', k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_764), F_763) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', F_763) | ~m1_subset_1(F_763, u1_struct_0(D_764)) | ~m1_subset_1(F_763, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_764, '#skF_5') | v2_struct_0(D_764) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_1243])).
% 4.81/1.82  tff(c_1248, plain, (![D_764, F_763]: (r1_tmap_1(D_764, '#skF_3', k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_764), F_763) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', F_763) | ~m1_subset_1(F_763, u1_struct_0(D_764)) | ~m1_subset_1(F_763, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_764, '#skF_5') | v2_struct_0(D_764) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_776, c_111, c_60, c_58, c_1245])).
% 4.81/1.82  tff(c_1250, plain, (![D_768, F_769]: (r1_tmap_1(D_768, '#skF_3', k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_768), F_769) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', F_769) | ~m1_subset_1(F_769, u1_struct_0(D_768)) | ~m1_subset_1(F_769, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_768, '#skF_5') | v2_struct_0(D_768))), inference(negUnitSimplification, [status(thm)], [c_74, c_64, c_1248])).
% 4.81/1.82  tff(c_1165, plain, (![E_750, B_746, D_748, C_747, A_749]: (k3_tmap_1(A_749, B_746, C_747, D_748, E_750)=k2_partfun1(u1_struct_0(C_747), u1_struct_0(B_746), E_750, u1_struct_0(D_748)) | ~m1_pre_topc(D_748, C_747) | ~m1_subset_1(E_750, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_747), u1_struct_0(B_746)))) | ~v1_funct_2(E_750, u1_struct_0(C_747), u1_struct_0(B_746)) | ~v1_funct_1(E_750) | ~m1_pre_topc(D_748, A_749) | ~m1_pre_topc(C_747, A_749) | ~l1_pre_topc(B_746) | ~v2_pre_topc(B_746) | v2_struct_0(B_746) | ~l1_pre_topc(A_749) | ~v2_pre_topc(A_749) | v2_struct_0(A_749))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.81/1.82  tff(c_1167, plain, (![A_749, D_748]: (k3_tmap_1(A_749, '#skF_3', '#skF_5', D_748, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_748)) | ~m1_pre_topc(D_748, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_748, A_749) | ~m1_pre_topc('#skF_5', A_749) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_749) | ~v2_pre_topc(A_749) | v2_struct_0(A_749))), inference(resolution, [status(thm)], [c_56, c_1165])).
% 4.81/1.82  tff(c_1170, plain, (![A_749, D_748]: (k3_tmap_1(A_749, '#skF_3', '#skF_5', D_748, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_748)) | ~m1_pre_topc(D_748, '#skF_5') | ~m1_pre_topc(D_748, A_749) | ~m1_pre_topc('#skF_5', A_749) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_749) | ~v2_pre_topc(A_749) | v2_struct_0(A_749))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_58, c_1167])).
% 4.81/1.82  tff(c_1172, plain, (![A_751, D_752]: (k3_tmap_1(A_751, '#skF_3', '#skF_5', D_752, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_752)) | ~m1_pre_topc(D_752, '#skF_5') | ~m1_pre_topc(D_752, A_751) | ~m1_pre_topc('#skF_5', A_751) | ~l1_pre_topc(A_751) | ~v2_pre_topc(A_751) | v2_struct_0(A_751))), inference(negUnitSimplification, [status(thm)], [c_74, c_1170])).
% 4.81/1.82  tff(c_1180, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1172])).
% 4.81/1.82  tff(c_1192, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_62, c_54, c_1180])).
% 4.81/1.82  tff(c_1193, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_80, c_1192])).
% 4.81/1.82  tff(c_1065, plain, (![A_730, B_731, C_732, D_733]: (k2_partfun1(u1_struct_0(A_730), u1_struct_0(B_731), C_732, u1_struct_0(D_733))=k2_tmap_1(A_730, B_731, C_732, D_733) | ~m1_pre_topc(D_733, A_730) | ~m1_subset_1(C_732, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_730), u1_struct_0(B_731)))) | ~v1_funct_2(C_732, u1_struct_0(A_730), u1_struct_0(B_731)) | ~v1_funct_1(C_732) | ~l1_pre_topc(B_731) | ~v2_pre_topc(B_731) | v2_struct_0(B_731) | ~l1_pre_topc(A_730) | ~v2_pre_topc(A_730) | v2_struct_0(A_730))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.81/1.82  tff(c_1067, plain, (![D_733]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_733))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_733) | ~m1_pre_topc(D_733, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1065])).
% 4.81/1.82  tff(c_1070, plain, (![D_733]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_733))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_733) | ~m1_pre_topc(D_733, '#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_776, c_111, c_72, c_70, c_60, c_58, c_1067])).
% 4.81/1.82  tff(c_1071, plain, (![D_733]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_733))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_733) | ~m1_pre_topc(D_733, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_74, c_1070])).
% 4.81/1.82  tff(c_1197, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1193, c_1071])).
% 4.81/1.82  tff(c_1204, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1197])).
% 4.81/1.82  tff(c_759, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 4.81/1.82  tff(c_1209, plain, (~r1_tmap_1('#skF_4', '#skF_3', k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1204, c_759])).
% 4.81/1.82  tff(c_1253, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1250, c_1209])).
% 4.81/1.82  tff(c_1256, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_91, c_760, c_1253])).
% 4.81/1.82  tff(c_1258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1256])).
% 4.81/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.82  
% 4.81/1.82  Inference rules
% 4.81/1.82  ----------------------
% 4.81/1.82  #Ref     : 0
% 4.81/1.82  #Sup     : 218
% 4.81/1.82  #Fact    : 0
% 4.81/1.82  #Define  : 0
% 4.81/1.82  #Split   : 8
% 4.81/1.82  #Chain   : 0
% 4.81/1.82  #Close   : 0
% 4.81/1.82  
% 4.81/1.82  Ordering : KBO
% 4.81/1.82  
% 4.81/1.82  Simplification rules
% 4.81/1.82  ----------------------
% 4.81/1.82  #Subsume      : 34
% 4.81/1.82  #Demod        : 326
% 4.81/1.82  #Tautology    : 64
% 4.81/1.82  #SimpNegUnit  : 92
% 4.81/1.82  #BackRed      : 4
% 4.81/1.82  
% 4.81/1.82  #Partial instantiations: 0
% 4.81/1.82  #Strategies tried      : 1
% 4.81/1.82  
% 4.81/1.82  Timing (in seconds)
% 4.81/1.82  ----------------------
% 4.81/1.82  Preprocessing        : 0.45
% 4.81/1.82  Parsing              : 0.22
% 4.81/1.82  CNF conversion       : 0.07
% 4.81/1.82  Main loop            : 0.57
% 4.81/1.82  Inferencing          : 0.21
% 4.81/1.82  Reduction            : 0.19
% 4.81/1.82  Demodulation         : 0.13
% 4.81/1.82  BG Simplification    : 0.04
% 4.81/1.82  Subsumption          : 0.11
% 4.81/1.82  Abstraction          : 0.02
% 4.81/1.82  MUC search           : 0.00
% 4.81/1.82  Cooper               : 0.00
% 4.81/1.82  Total                : 1.07
% 4.81/1.82  Index Insertion      : 0.00
% 4.81/1.82  Index Deletion       : 0.00
% 4.81/1.82  Index Matching       : 0.00
% 4.81/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
