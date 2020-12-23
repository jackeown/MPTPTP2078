%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:25 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 676 expanded)
%              Number of leaves         :   39 ( 275 expanded)
%              Depth                    :   21
%              Number of atoms          :  540 (6158 expanded)
%              Number of equality atoms :   41 ( 314 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_302,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_72,axiom,(
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

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_131,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_99,axiom,(
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

tff(f_244,axiom,(
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

tff(f_175,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_28,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_79,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_30,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_96,plain,(
    ! [B_655,A_656] :
      ( l1_pre_topc(B_655)
      | ~ m1_pre_topc(B_655,A_656)
      | ~ l1_pre_topc(A_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_108,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_96])).

tff(c_116,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_108])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_192,plain,(
    ! [C_665,A_666,B_667] :
      ( m1_subset_1(C_665,k1_zfmisc_1(u1_struct_0(A_666)))
      | ~ m1_subset_1(C_665,k1_zfmisc_1(u1_struct_0(B_667)))
      | ~ m1_pre_topc(B_667,A_666)
      | ~ l1_pre_topc(A_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_209,plain,(
    ! [A_670,A_671,B_672] :
      ( m1_subset_1(A_670,k1_zfmisc_1(u1_struct_0(A_671)))
      | ~ m1_pre_topc(B_672,A_671)
      | ~ l1_pre_topc(A_671)
      | ~ r1_tarski(A_670,u1_struct_0(B_672)) ) ),
    inference(resolution,[status(thm)],[c_4,c_192])).

tff(c_217,plain,(
    ! [A_670] :
      ( m1_subset_1(A_670,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_670,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_42,c_209])).

tff(c_241,plain,(
    ! [A_675] :
      ( m1_subset_1(A_675,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_675,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_217])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_249,plain,(
    ! [A_676] :
      ( r1_tarski(A_676,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_676,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_241,c_2])).

tff(c_260,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_249])).

tff(c_34,plain,(
    v3_pre_topc('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_289,plain,(
    ! [D_683,C_684,A_685] :
      ( v3_pre_topc(D_683,C_684)
      | ~ m1_subset_1(D_683,k1_zfmisc_1(u1_struct_0(C_684)))
      | ~ v3_pre_topc(D_683,A_685)
      | ~ m1_pre_topc(C_684,A_685)
      | ~ m1_subset_1(D_683,k1_zfmisc_1(u1_struct_0(A_685)))
      | ~ l1_pre_topc(A_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_558,plain,(
    ! [A_720,C_721,A_722] :
      ( v3_pre_topc(A_720,C_721)
      | ~ v3_pre_topc(A_720,A_722)
      | ~ m1_pre_topc(C_721,A_722)
      | ~ m1_subset_1(A_720,k1_zfmisc_1(u1_struct_0(A_722)))
      | ~ l1_pre_topc(A_722)
      | ~ r1_tarski(A_720,u1_struct_0(C_721)) ) ),
    inference(resolution,[status(thm)],[c_4,c_289])).

tff(c_568,plain,(
    ! [A_720] :
      ( v3_pre_topc(A_720,'#skF_4')
      | ~ v3_pre_topc(A_720,'#skF_2')
      | ~ m1_subset_1(A_720,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_720,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_50,c_558])).

tff(c_954,plain,(
    ! [A_748] :
      ( v3_pre_topc(A_748,'#skF_4')
      | ~ v3_pre_topc(A_748,'#skF_2')
      | ~ m1_subset_1(A_748,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_748,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_568])).

tff(c_983,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_954])).

tff(c_1001,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_34,c_983])).

tff(c_32,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_80,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_18,plain,(
    ! [A_77] :
      ( m1_pre_topc(A_77,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_46,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_547,plain,(
    ! [A_719,D_717,E_718,C_715,B_716] :
      ( k3_tmap_1(A_719,B_716,C_715,D_717,E_718) = k2_partfun1(u1_struct_0(C_715),u1_struct_0(B_716),E_718,u1_struct_0(D_717))
      | ~ m1_pre_topc(D_717,C_715)
      | ~ m1_subset_1(E_718,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_715),u1_struct_0(B_716))))
      | ~ v1_funct_2(E_718,u1_struct_0(C_715),u1_struct_0(B_716))
      | ~ v1_funct_1(E_718)
      | ~ m1_pre_topc(D_717,A_719)
      | ~ m1_pre_topc(C_715,A_719)
      | ~ l1_pre_topc(B_716)
      | ~ v2_pre_topc(B_716)
      | v2_struct_0(B_716)
      | ~ l1_pre_topc(A_719)
      | ~ v2_pre_topc(A_719)
      | v2_struct_0(A_719) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_549,plain,(
    ! [A_719,D_717] :
      ( k3_tmap_1(A_719,'#skF_1','#skF_4',D_717,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_717))
      | ~ m1_pre_topc(D_717,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_717,A_719)
      | ~ m1_pre_topc('#skF_4',A_719)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_719)
      | ~ v2_pre_topc(A_719)
      | v2_struct_0(A_719) ) ),
    inference(resolution,[status(thm)],[c_44,c_547])).

tff(c_555,plain,(
    ! [A_719,D_717] :
      ( k3_tmap_1(A_719,'#skF_1','#skF_4',D_717,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_717))
      | ~ m1_pre_topc(D_717,'#skF_4')
      | ~ m1_pre_topc(D_717,A_719)
      | ~ m1_pre_topc('#skF_4',A_719)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_719)
      | ~ v2_pre_topc(A_719)
      | v2_struct_0(A_719) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_46,c_549])).

tff(c_628,plain,(
    ! [A_724,D_725] :
      ( k3_tmap_1(A_724,'#skF_1','#skF_4',D_725,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_725))
      | ~ m1_pre_topc(D_725,'#skF_4')
      | ~ m1_pre_topc(D_725,A_724)
      | ~ m1_pre_topc('#skF_4',A_724)
      | ~ l1_pre_topc(A_724)
      | ~ v2_pre_topc(A_724)
      | v2_struct_0(A_724) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_555])).

tff(c_638,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_628])).

tff(c_653,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_638])).

tff(c_654,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_653])).

tff(c_709,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_654])).

tff(c_712,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_709])).

tff(c_716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_712])).

tff(c_718,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_10,plain,(
    ! [C_15,A_9,B_13] :
      ( m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(B_13)))
      | ~ m1_pre_topc(B_13,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_247,plain,(
    ! [A_675,A_9] :
      ( m1_subset_1(A_675,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_pre_topc('#skF_4',A_9)
      | ~ l1_pre_topc(A_9)
      | ~ r1_tarski(A_675,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_241,c_10])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_78,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_70])).

tff(c_161,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_634,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_628])).

tff(c_645,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_42,c_634])).

tff(c_646,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_645])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_123,plain,(
    ! [B_657,A_658] :
      ( v2_pre_topc(B_657)
      | ~ m1_pre_topc(B_657,A_658)
      | ~ l1_pre_topc(A_658)
      | ~ v2_pre_topc(A_658) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_135,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_123])).

tff(c_145,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_135])).

tff(c_406,plain,(
    ! [A_697,B_698,C_699,D_700] :
      ( k2_partfun1(u1_struct_0(A_697),u1_struct_0(B_698),C_699,u1_struct_0(D_700)) = k2_tmap_1(A_697,B_698,C_699,D_700)
      | ~ m1_pre_topc(D_700,A_697)
      | ~ m1_subset_1(C_699,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_697),u1_struct_0(B_698))))
      | ~ v1_funct_2(C_699,u1_struct_0(A_697),u1_struct_0(B_698))
      | ~ v1_funct_1(C_699)
      | ~ l1_pre_topc(B_698)
      | ~ v2_pre_topc(B_698)
      | v2_struct_0(B_698)
      | ~ l1_pre_topc(A_697)
      | ~ v2_pre_topc(A_697)
      | v2_struct_0(A_697) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_408,plain,(
    ! [D_700] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_700)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_700)
      | ~ m1_pre_topc(D_700,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_406])).

tff(c_414,plain,(
    ! [D_700] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_700)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_700)
      | ~ m1_pre_topc(D_700,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_116,c_66,c_64,c_48,c_46,c_408])).

tff(c_415,plain,(
    ! [D_700] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_700)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_700)
      | ~ m1_pre_topc(D_700,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_68,c_414])).

tff(c_680,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_415])).

tff(c_687,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_680])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_77,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_76])).

tff(c_239,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_77])).

tff(c_703,plain,(
    r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_239])).

tff(c_702,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_646])).

tff(c_636,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_628])).

tff(c_649,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_116,c_42,c_636])).

tff(c_650,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_649])).

tff(c_854,plain,(
    k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_702,c_650])).

tff(c_24,plain,(
    ! [D_372,H_402,F_396,E_388,A_148,C_340,B_276] :
      ( r1_tmap_1(D_372,B_276,E_388,H_402)
      | ~ r1_tmap_1(C_340,B_276,k3_tmap_1(A_148,B_276,D_372,C_340,E_388),H_402)
      | ~ r1_tarski(F_396,u1_struct_0(C_340))
      | ~ r2_hidden(H_402,F_396)
      | ~ v3_pre_topc(F_396,D_372)
      | ~ m1_subset_1(H_402,u1_struct_0(C_340))
      | ~ m1_subset_1(H_402,u1_struct_0(D_372))
      | ~ m1_subset_1(F_396,k1_zfmisc_1(u1_struct_0(D_372)))
      | ~ m1_pre_topc(C_340,D_372)
      | ~ m1_subset_1(E_388,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_372),u1_struct_0(B_276))))
      | ~ v1_funct_2(E_388,u1_struct_0(D_372),u1_struct_0(B_276))
      | ~ v1_funct_1(E_388)
      | ~ m1_pre_topc(D_372,A_148)
      | v2_struct_0(D_372)
      | ~ m1_pre_topc(C_340,A_148)
      | v2_struct_0(C_340)
      | ~ l1_pre_topc(B_276)
      | ~ v2_pre_topc(B_276)
      | v2_struct_0(B_276)
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_857,plain,(
    ! [H_402,F_396] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5',H_402)
      | ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),H_402)
      | ~ r1_tarski(F_396,u1_struct_0('#skF_3'))
      | ~ r2_hidden(H_402,F_396)
      | ~ v3_pre_topc(F_396,'#skF_4')
      | ~ m1_subset_1(H_402,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_402,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_396,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_24])).

tff(c_861,plain,(
    ! [H_402,F_396] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5',H_402)
      | ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),H_402)
      | ~ r1_tarski(F_396,u1_struct_0('#skF_3'))
      | ~ r2_hidden(H_402,F_396)
      | ~ v3_pre_topc(F_396,'#skF_4')
      | ~ m1_subset_1(H_402,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_402,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_396,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_116,c_66,c_64,c_42,c_718,c_48,c_46,c_44,c_42,c_857])).

tff(c_1355,plain,(
    ! [H_785,F_786] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5',H_785)
      | ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),H_785)
      | ~ r1_tarski(F_786,u1_struct_0('#skF_3'))
      | ~ r2_hidden(H_785,F_786)
      | ~ v3_pre_topc(F_786,'#skF_4')
      | ~ m1_subset_1(H_785,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_785,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_786,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_68,c_56,c_861])).

tff(c_1360,plain,(
    ! [F_786] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_786,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_786)
      | ~ v3_pre_topc(F_786,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_786,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_703,c_1355])).

tff(c_1367,plain,(
    ! [F_786] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_786,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_786)
      | ~ v3_pre_topc(F_786,'#skF_4')
      | ~ m1_subset_1(F_786,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_36,c_1360])).

tff(c_1369,plain,(
    ! [F_787] :
      ( ~ r1_tarski(F_787,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_787)
      | ~ v3_pre_topc(F_787,'#skF_4')
      | ~ m1_subset_1(F_787,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_1367])).

tff(c_1373,plain,(
    ! [A_675] :
      ( ~ r2_hidden('#skF_8',A_675)
      | ~ v3_pre_topc(A_675,'#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_675,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_247,c_1369])).

tff(c_1407,plain,(
    ! [A_788] :
      ( ~ r2_hidden('#skF_8',A_788)
      | ~ v3_pre_topc(A_788,'#skF_4')
      | ~ r1_tarski(A_788,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_718,c_1373])).

tff(c_1418,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1407])).

tff(c_1428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1001,c_80,c_1418])).

tff(c_1430,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1819,plain,(
    ! [A_842,C_845,B_843,D_841,F_844] :
      ( r1_tmap_1(D_841,A_842,k2_tmap_1(B_843,A_842,C_845,D_841),F_844)
      | ~ r1_tmap_1(B_843,A_842,C_845,F_844)
      | ~ m1_subset_1(F_844,u1_struct_0(D_841))
      | ~ m1_subset_1(F_844,u1_struct_0(B_843))
      | ~ m1_pre_topc(D_841,B_843)
      | v2_struct_0(D_841)
      | ~ m1_subset_1(C_845,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_843),u1_struct_0(A_842))))
      | ~ v1_funct_2(C_845,u1_struct_0(B_843),u1_struct_0(A_842))
      | ~ v1_funct_1(C_845)
      | ~ l1_pre_topc(B_843)
      | ~ v2_pre_topc(B_843)
      | v2_struct_0(B_843)
      | ~ l1_pre_topc(A_842)
      | ~ v2_pre_topc(A_842)
      | v2_struct_0(A_842) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1821,plain,(
    ! [D_841,F_844] :
      ( r1_tmap_1(D_841,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_841),F_844)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_844)
      | ~ m1_subset_1(F_844,u1_struct_0(D_841))
      | ~ m1_subset_1(F_844,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_841,'#skF_4')
      | v2_struct_0(D_841)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_1819])).

tff(c_1827,plain,(
    ! [D_841,F_844] :
      ( r1_tmap_1(D_841,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_841),F_844)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_844)
      | ~ m1_subset_1(F_844,u1_struct_0(D_841))
      | ~ m1_subset_1(F_844,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_841,'#skF_4')
      | v2_struct_0(D_841)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_145,c_116,c_48,c_46,c_1821])).

tff(c_1979,plain,(
    ! [D_856,F_857] :
      ( r1_tmap_1(D_856,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_856),F_857)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_857)
      | ~ m1_subset_1(F_857,u1_struct_0(D_856))
      | ~ m1_subset_1(F_857,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_856,'#skF_4')
      | v2_struct_0(D_856) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_52,c_1827])).

tff(c_1696,plain,(
    ! [D_831,C_829,B_830,E_832,A_833] :
      ( k3_tmap_1(A_833,B_830,C_829,D_831,E_832) = k2_partfun1(u1_struct_0(C_829),u1_struct_0(B_830),E_832,u1_struct_0(D_831))
      | ~ m1_pre_topc(D_831,C_829)
      | ~ m1_subset_1(E_832,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_829),u1_struct_0(B_830))))
      | ~ v1_funct_2(E_832,u1_struct_0(C_829),u1_struct_0(B_830))
      | ~ v1_funct_1(E_832)
      | ~ m1_pre_topc(D_831,A_833)
      | ~ m1_pre_topc(C_829,A_833)
      | ~ l1_pre_topc(B_830)
      | ~ v2_pre_topc(B_830)
      | v2_struct_0(B_830)
      | ~ l1_pre_topc(A_833)
      | ~ v2_pre_topc(A_833)
      | v2_struct_0(A_833) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1698,plain,(
    ! [A_833,D_831] :
      ( k3_tmap_1(A_833,'#skF_1','#skF_4',D_831,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_831))
      | ~ m1_pre_topc(D_831,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_831,A_833)
      | ~ m1_pre_topc('#skF_4',A_833)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_833)
      | ~ v2_pre_topc(A_833)
      | v2_struct_0(A_833) ) ),
    inference(resolution,[status(thm)],[c_44,c_1696])).

tff(c_1704,plain,(
    ! [A_833,D_831] :
      ( k3_tmap_1(A_833,'#skF_1','#skF_4',D_831,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_831))
      | ~ m1_pre_topc(D_831,'#skF_4')
      | ~ m1_pre_topc(D_831,A_833)
      | ~ m1_pre_topc('#skF_4',A_833)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_833)
      | ~ v2_pre_topc(A_833)
      | v2_struct_0(A_833) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_46,c_1698])).

tff(c_1755,plain,(
    ! [A_839,D_840] :
      ( k3_tmap_1(A_839,'#skF_1','#skF_4',D_840,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_840))
      | ~ m1_pre_topc(D_840,'#skF_4')
      | ~ m1_pre_topc(D_840,A_839)
      | ~ m1_pre_topc('#skF_4',A_839)
      | ~ l1_pre_topc(A_839)
      | ~ v2_pre_topc(A_839)
      | v2_struct_0(A_839) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1704])).

tff(c_1761,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1755])).

tff(c_1772,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_42,c_1761])).

tff(c_1773,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1772])).

tff(c_1597,plain,(
    ! [A_814,B_815,C_816,D_817] :
      ( k2_partfun1(u1_struct_0(A_814),u1_struct_0(B_815),C_816,u1_struct_0(D_817)) = k2_tmap_1(A_814,B_815,C_816,D_817)
      | ~ m1_pre_topc(D_817,A_814)
      | ~ m1_subset_1(C_816,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_814),u1_struct_0(B_815))))
      | ~ v1_funct_2(C_816,u1_struct_0(A_814),u1_struct_0(B_815))
      | ~ v1_funct_1(C_816)
      | ~ l1_pre_topc(B_815)
      | ~ v2_pre_topc(B_815)
      | v2_struct_0(B_815)
      | ~ l1_pre_topc(A_814)
      | ~ v2_pre_topc(A_814)
      | v2_struct_0(A_814) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1599,plain,(
    ! [D_817] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_817)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_817)
      | ~ m1_pre_topc(D_817,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_1597])).

tff(c_1605,plain,(
    ! [D_817] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_817)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_817)
      | ~ m1_pre_topc(D_817,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_116,c_66,c_64,c_48,c_46,c_1599])).

tff(c_1606,plain,(
    ! [D_817] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_817)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_817)
      | ~ m1_pre_topc(D_817,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_68,c_1605])).

tff(c_1785,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1773,c_1606])).

tff(c_1792,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1785])).

tff(c_1429,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1797,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1792,c_1429])).

tff(c_1982,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1979,c_1797])).

tff(c_1985,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_79,c_36,c_1430,c_1982])).

tff(c_1987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1985])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.83/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.91  
% 5.19/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/1.91  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 5.19/1.91  
% 5.19/1.91  %Foreground sorts:
% 5.19/1.91  
% 5.19/1.91  
% 5.19/1.91  %Background operators:
% 5.19/1.91  
% 5.19/1.91  
% 5.19/1.91  %Foreground operators:
% 5.19/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.19/1.91  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.19/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.19/1.91  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.19/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.19/1.91  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.19/1.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.19/1.91  tff('#skF_7', type, '#skF_7': $i).
% 5.19/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.19/1.91  tff('#skF_5', type, '#skF_5': $i).
% 5.19/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.19/1.91  tff('#skF_6', type, '#skF_6': $i).
% 5.19/1.91  tff('#skF_2', type, '#skF_2': $i).
% 5.19/1.91  tff('#skF_3', type, '#skF_3': $i).
% 5.19/1.91  tff('#skF_1', type, '#skF_1': $i).
% 5.19/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.19/1.91  tff('#skF_8', type, '#skF_8': $i).
% 5.19/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.19/1.91  tff('#skF_4', type, '#skF_4': $i).
% 5.19/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/1.91  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.19/1.91  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.19/1.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.19/1.91  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.19/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.19/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.19/1.91  
% 5.19/1.94  tff(f_302, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tmap_1)).
% 5.19/1.94  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.19/1.94  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.19/1.94  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 5.19/1.94  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 5.19/1.94  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.19/1.94  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 5.19/1.94  tff(f_38, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.19/1.94  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.19/1.94  tff(f_244, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 5.19/1.94  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 5.19/1.94  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_28, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_38, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_79, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 5.19/1.94  tff(c_36, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_30, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_96, plain, (![B_655, A_656]: (l1_pre_topc(B_655) | ~m1_pre_topc(B_655, A_656) | ~l1_pre_topc(A_656))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.19/1.94  tff(c_108, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_96])).
% 5.19/1.94  tff(c_116, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_108])).
% 5.19/1.94  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.19/1.94  tff(c_192, plain, (![C_665, A_666, B_667]: (m1_subset_1(C_665, k1_zfmisc_1(u1_struct_0(A_666))) | ~m1_subset_1(C_665, k1_zfmisc_1(u1_struct_0(B_667))) | ~m1_pre_topc(B_667, A_666) | ~l1_pre_topc(A_666))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.19/1.94  tff(c_209, plain, (![A_670, A_671, B_672]: (m1_subset_1(A_670, k1_zfmisc_1(u1_struct_0(A_671))) | ~m1_pre_topc(B_672, A_671) | ~l1_pre_topc(A_671) | ~r1_tarski(A_670, u1_struct_0(B_672)))), inference(resolution, [status(thm)], [c_4, c_192])).
% 5.19/1.94  tff(c_217, plain, (![A_670]: (m1_subset_1(A_670, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_670, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_42, c_209])).
% 5.19/1.94  tff(c_241, plain, (![A_675]: (m1_subset_1(A_675, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_675, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_217])).
% 5.19/1.94  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.19/1.94  tff(c_249, plain, (![A_676]: (r1_tarski(A_676, u1_struct_0('#skF_4')) | ~r1_tarski(A_676, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_241, c_2])).
% 5.19/1.94  tff(c_260, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_249])).
% 5.19/1.94  tff(c_34, plain, (v3_pre_topc('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_289, plain, (![D_683, C_684, A_685]: (v3_pre_topc(D_683, C_684) | ~m1_subset_1(D_683, k1_zfmisc_1(u1_struct_0(C_684))) | ~v3_pre_topc(D_683, A_685) | ~m1_pre_topc(C_684, A_685) | ~m1_subset_1(D_683, k1_zfmisc_1(u1_struct_0(A_685))) | ~l1_pre_topc(A_685))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.19/1.94  tff(c_558, plain, (![A_720, C_721, A_722]: (v3_pre_topc(A_720, C_721) | ~v3_pre_topc(A_720, A_722) | ~m1_pre_topc(C_721, A_722) | ~m1_subset_1(A_720, k1_zfmisc_1(u1_struct_0(A_722))) | ~l1_pre_topc(A_722) | ~r1_tarski(A_720, u1_struct_0(C_721)))), inference(resolution, [status(thm)], [c_4, c_289])).
% 5.19/1.94  tff(c_568, plain, (![A_720]: (v3_pre_topc(A_720, '#skF_4') | ~v3_pre_topc(A_720, '#skF_2') | ~m1_subset_1(A_720, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_720, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_50, c_558])).
% 5.19/1.94  tff(c_954, plain, (![A_748]: (v3_pre_topc(A_748, '#skF_4') | ~v3_pre_topc(A_748, '#skF_2') | ~m1_subset_1(A_748, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_748, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_568])).
% 5.19/1.94  tff(c_983, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_954])).
% 5.19/1.94  tff(c_1001, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_34, c_983])).
% 5.19/1.94  tff(c_32, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_80, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 5.19/1.94  tff(c_18, plain, (![A_77]: (m1_pre_topc(A_77, A_77) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.19/1.94  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_46, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_547, plain, (![A_719, D_717, E_718, C_715, B_716]: (k3_tmap_1(A_719, B_716, C_715, D_717, E_718)=k2_partfun1(u1_struct_0(C_715), u1_struct_0(B_716), E_718, u1_struct_0(D_717)) | ~m1_pre_topc(D_717, C_715) | ~m1_subset_1(E_718, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_715), u1_struct_0(B_716)))) | ~v1_funct_2(E_718, u1_struct_0(C_715), u1_struct_0(B_716)) | ~v1_funct_1(E_718) | ~m1_pre_topc(D_717, A_719) | ~m1_pre_topc(C_715, A_719) | ~l1_pre_topc(B_716) | ~v2_pre_topc(B_716) | v2_struct_0(B_716) | ~l1_pre_topc(A_719) | ~v2_pre_topc(A_719) | v2_struct_0(A_719))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.19/1.94  tff(c_549, plain, (![A_719, D_717]: (k3_tmap_1(A_719, '#skF_1', '#skF_4', D_717, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_717)) | ~m1_pre_topc(D_717, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_717, A_719) | ~m1_pre_topc('#skF_4', A_719) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_719) | ~v2_pre_topc(A_719) | v2_struct_0(A_719))), inference(resolution, [status(thm)], [c_44, c_547])).
% 5.19/1.94  tff(c_555, plain, (![A_719, D_717]: (k3_tmap_1(A_719, '#skF_1', '#skF_4', D_717, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_717)) | ~m1_pre_topc(D_717, '#skF_4') | ~m1_pre_topc(D_717, A_719) | ~m1_pre_topc('#skF_4', A_719) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_719) | ~v2_pre_topc(A_719) | v2_struct_0(A_719))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_46, c_549])).
% 5.19/1.94  tff(c_628, plain, (![A_724, D_725]: (k3_tmap_1(A_724, '#skF_1', '#skF_4', D_725, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_725)) | ~m1_pre_topc(D_725, '#skF_4') | ~m1_pre_topc(D_725, A_724) | ~m1_pre_topc('#skF_4', A_724) | ~l1_pre_topc(A_724) | ~v2_pre_topc(A_724) | v2_struct_0(A_724))), inference(negUnitSimplification, [status(thm)], [c_68, c_555])).
% 5.19/1.94  tff(c_638, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_628])).
% 5.19/1.94  tff(c_653, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_638])).
% 5.19/1.94  tff(c_654, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_653])).
% 5.19/1.94  tff(c_709, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_654])).
% 5.19/1.94  tff(c_712, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_709])).
% 5.19/1.94  tff(c_716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_712])).
% 5.19/1.94  tff(c_718, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_654])).
% 5.19/1.94  tff(c_10, plain, (![C_15, A_9, B_13]: (m1_subset_1(C_15, k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(C_15, k1_zfmisc_1(u1_struct_0(B_13))) | ~m1_pre_topc(B_13, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.19/1.94  tff(c_247, plain, (![A_675, A_9]: (m1_subset_1(A_675, k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_pre_topc('#skF_4', A_9) | ~l1_pre_topc(A_9) | ~r1_tarski(A_675, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_241, c_10])).
% 5.19/1.94  tff(c_70, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_78, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_70])).
% 5.19/1.94  tff(c_161, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_78])).
% 5.19/1.94  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_634, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_628])).
% 5.19/1.94  tff(c_645, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_42, c_634])).
% 5.19/1.94  tff(c_646, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_645])).
% 5.19/1.94  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_123, plain, (![B_657, A_658]: (v2_pre_topc(B_657) | ~m1_pre_topc(B_657, A_658) | ~l1_pre_topc(A_658) | ~v2_pre_topc(A_658))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.19/1.94  tff(c_135, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_123])).
% 5.19/1.94  tff(c_145, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_135])).
% 5.19/1.94  tff(c_406, plain, (![A_697, B_698, C_699, D_700]: (k2_partfun1(u1_struct_0(A_697), u1_struct_0(B_698), C_699, u1_struct_0(D_700))=k2_tmap_1(A_697, B_698, C_699, D_700) | ~m1_pre_topc(D_700, A_697) | ~m1_subset_1(C_699, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_697), u1_struct_0(B_698)))) | ~v1_funct_2(C_699, u1_struct_0(A_697), u1_struct_0(B_698)) | ~v1_funct_1(C_699) | ~l1_pre_topc(B_698) | ~v2_pre_topc(B_698) | v2_struct_0(B_698) | ~l1_pre_topc(A_697) | ~v2_pre_topc(A_697) | v2_struct_0(A_697))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.19/1.94  tff(c_408, plain, (![D_700]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_700))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_700) | ~m1_pre_topc(D_700, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_406])).
% 5.19/1.94  tff(c_414, plain, (![D_700]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_700))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_700) | ~m1_pre_topc(D_700, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_116, c_66, c_64, c_48, c_46, c_408])).
% 5.19/1.94  tff(c_415, plain, (![D_700]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_700))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_700) | ~m1_pre_topc(D_700, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_68, c_414])).
% 5.19/1.94  tff(c_680, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_646, c_415])).
% 5.19/1.94  tff(c_687, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_680])).
% 5.19/1.94  tff(c_76, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_302])).
% 5.19/1.94  tff(c_77, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_76])).
% 5.19/1.94  tff(c_239, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_161, c_77])).
% 5.19/1.94  tff(c_703, plain, (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_687, c_239])).
% 5.19/1.94  tff(c_702, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_687, c_646])).
% 5.19/1.94  tff(c_636, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_628])).
% 5.19/1.94  tff(c_649, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_116, c_42, c_636])).
% 5.19/1.94  tff(c_650, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_649])).
% 5.19/1.94  tff(c_854, plain, (k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_718, c_702, c_650])).
% 5.19/1.94  tff(c_24, plain, (![D_372, H_402, F_396, E_388, A_148, C_340, B_276]: (r1_tmap_1(D_372, B_276, E_388, H_402) | ~r1_tmap_1(C_340, B_276, k3_tmap_1(A_148, B_276, D_372, C_340, E_388), H_402) | ~r1_tarski(F_396, u1_struct_0(C_340)) | ~r2_hidden(H_402, F_396) | ~v3_pre_topc(F_396, D_372) | ~m1_subset_1(H_402, u1_struct_0(C_340)) | ~m1_subset_1(H_402, u1_struct_0(D_372)) | ~m1_subset_1(F_396, k1_zfmisc_1(u1_struct_0(D_372))) | ~m1_pre_topc(C_340, D_372) | ~m1_subset_1(E_388, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_372), u1_struct_0(B_276)))) | ~v1_funct_2(E_388, u1_struct_0(D_372), u1_struct_0(B_276)) | ~v1_funct_1(E_388) | ~m1_pre_topc(D_372, A_148) | v2_struct_0(D_372) | ~m1_pre_topc(C_340, A_148) | v2_struct_0(C_340) | ~l1_pre_topc(B_276) | ~v2_pre_topc(B_276) | v2_struct_0(B_276) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.19/1.94  tff(c_857, plain, (![H_402, F_396]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', H_402) | ~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), H_402) | ~r1_tarski(F_396, u1_struct_0('#skF_3')) | ~r2_hidden(H_402, F_396) | ~v3_pre_topc(F_396, '#skF_4') | ~m1_subset_1(H_402, u1_struct_0('#skF_3')) | ~m1_subset_1(H_402, u1_struct_0('#skF_4')) | ~m1_subset_1(F_396, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_854, c_24])).
% 5.19/1.94  tff(c_861, plain, (![H_402, F_396]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', H_402) | ~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), H_402) | ~r1_tarski(F_396, u1_struct_0('#skF_3')) | ~r2_hidden(H_402, F_396) | ~v3_pre_topc(F_396, '#skF_4') | ~m1_subset_1(H_402, u1_struct_0('#skF_3')) | ~m1_subset_1(H_402, u1_struct_0('#skF_4')) | ~m1_subset_1(F_396, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_116, c_66, c_64, c_42, c_718, c_48, c_46, c_44, c_42, c_857])).
% 5.19/1.94  tff(c_1355, plain, (![H_785, F_786]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', H_785) | ~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), H_785) | ~r1_tarski(F_786, u1_struct_0('#skF_3')) | ~r2_hidden(H_785, F_786) | ~v3_pre_topc(F_786, '#skF_4') | ~m1_subset_1(H_785, u1_struct_0('#skF_3')) | ~m1_subset_1(H_785, u1_struct_0('#skF_4')) | ~m1_subset_1(F_786, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_68, c_56, c_861])).
% 5.19/1.94  tff(c_1360, plain, (![F_786]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(F_786, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_786) | ~v3_pre_topc(F_786, '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(F_786, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_703, c_1355])).
% 5.19/1.94  tff(c_1367, plain, (![F_786]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(F_786, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_786) | ~v3_pre_topc(F_786, '#skF_4') | ~m1_subset_1(F_786, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_36, c_1360])).
% 5.19/1.94  tff(c_1369, plain, (![F_787]: (~r1_tarski(F_787, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_787) | ~v3_pre_topc(F_787, '#skF_4') | ~m1_subset_1(F_787, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_161, c_1367])).
% 5.19/1.94  tff(c_1373, plain, (![A_675]: (~r2_hidden('#skF_8', A_675) | ~v3_pre_topc(A_675, '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_675, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_247, c_1369])).
% 5.19/1.94  tff(c_1407, plain, (![A_788]: (~r2_hidden('#skF_8', A_788) | ~v3_pre_topc(A_788, '#skF_4') | ~r1_tarski(A_788, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_718, c_1373])).
% 5.19/1.94  tff(c_1418, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_1407])).
% 5.19/1.94  tff(c_1428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1001, c_80, c_1418])).
% 5.19/1.94  tff(c_1430, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 5.19/1.94  tff(c_1819, plain, (![A_842, C_845, B_843, D_841, F_844]: (r1_tmap_1(D_841, A_842, k2_tmap_1(B_843, A_842, C_845, D_841), F_844) | ~r1_tmap_1(B_843, A_842, C_845, F_844) | ~m1_subset_1(F_844, u1_struct_0(D_841)) | ~m1_subset_1(F_844, u1_struct_0(B_843)) | ~m1_pre_topc(D_841, B_843) | v2_struct_0(D_841) | ~m1_subset_1(C_845, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_843), u1_struct_0(A_842)))) | ~v1_funct_2(C_845, u1_struct_0(B_843), u1_struct_0(A_842)) | ~v1_funct_1(C_845) | ~l1_pre_topc(B_843) | ~v2_pre_topc(B_843) | v2_struct_0(B_843) | ~l1_pre_topc(A_842) | ~v2_pre_topc(A_842) | v2_struct_0(A_842))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.19/1.94  tff(c_1821, plain, (![D_841, F_844]: (r1_tmap_1(D_841, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_841), F_844) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_844) | ~m1_subset_1(F_844, u1_struct_0(D_841)) | ~m1_subset_1(F_844, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_841, '#skF_4') | v2_struct_0(D_841) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_1819])).
% 5.19/1.94  tff(c_1827, plain, (![D_841, F_844]: (r1_tmap_1(D_841, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_841), F_844) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_844) | ~m1_subset_1(F_844, u1_struct_0(D_841)) | ~m1_subset_1(F_844, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_841, '#skF_4') | v2_struct_0(D_841) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_145, c_116, c_48, c_46, c_1821])).
% 5.19/1.94  tff(c_1979, plain, (![D_856, F_857]: (r1_tmap_1(D_856, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_856), F_857) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_857) | ~m1_subset_1(F_857, u1_struct_0(D_856)) | ~m1_subset_1(F_857, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_856, '#skF_4') | v2_struct_0(D_856))), inference(negUnitSimplification, [status(thm)], [c_68, c_52, c_1827])).
% 5.19/1.94  tff(c_1696, plain, (![D_831, C_829, B_830, E_832, A_833]: (k3_tmap_1(A_833, B_830, C_829, D_831, E_832)=k2_partfun1(u1_struct_0(C_829), u1_struct_0(B_830), E_832, u1_struct_0(D_831)) | ~m1_pre_topc(D_831, C_829) | ~m1_subset_1(E_832, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_829), u1_struct_0(B_830)))) | ~v1_funct_2(E_832, u1_struct_0(C_829), u1_struct_0(B_830)) | ~v1_funct_1(E_832) | ~m1_pre_topc(D_831, A_833) | ~m1_pre_topc(C_829, A_833) | ~l1_pre_topc(B_830) | ~v2_pre_topc(B_830) | v2_struct_0(B_830) | ~l1_pre_topc(A_833) | ~v2_pre_topc(A_833) | v2_struct_0(A_833))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.19/1.94  tff(c_1698, plain, (![A_833, D_831]: (k3_tmap_1(A_833, '#skF_1', '#skF_4', D_831, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_831)) | ~m1_pre_topc(D_831, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_831, A_833) | ~m1_pre_topc('#skF_4', A_833) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_833) | ~v2_pre_topc(A_833) | v2_struct_0(A_833))), inference(resolution, [status(thm)], [c_44, c_1696])).
% 5.19/1.94  tff(c_1704, plain, (![A_833, D_831]: (k3_tmap_1(A_833, '#skF_1', '#skF_4', D_831, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_831)) | ~m1_pre_topc(D_831, '#skF_4') | ~m1_pre_topc(D_831, A_833) | ~m1_pre_topc('#skF_4', A_833) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_833) | ~v2_pre_topc(A_833) | v2_struct_0(A_833))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_46, c_1698])).
% 5.19/1.94  tff(c_1755, plain, (![A_839, D_840]: (k3_tmap_1(A_839, '#skF_1', '#skF_4', D_840, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_840)) | ~m1_pre_topc(D_840, '#skF_4') | ~m1_pre_topc(D_840, A_839) | ~m1_pre_topc('#skF_4', A_839) | ~l1_pre_topc(A_839) | ~v2_pre_topc(A_839) | v2_struct_0(A_839))), inference(negUnitSimplification, [status(thm)], [c_68, c_1704])).
% 5.19/1.94  tff(c_1761, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1755])).
% 5.19/1.94  tff(c_1772, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_42, c_1761])).
% 5.19/1.94  tff(c_1773, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_1772])).
% 5.19/1.94  tff(c_1597, plain, (![A_814, B_815, C_816, D_817]: (k2_partfun1(u1_struct_0(A_814), u1_struct_0(B_815), C_816, u1_struct_0(D_817))=k2_tmap_1(A_814, B_815, C_816, D_817) | ~m1_pre_topc(D_817, A_814) | ~m1_subset_1(C_816, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_814), u1_struct_0(B_815)))) | ~v1_funct_2(C_816, u1_struct_0(A_814), u1_struct_0(B_815)) | ~v1_funct_1(C_816) | ~l1_pre_topc(B_815) | ~v2_pre_topc(B_815) | v2_struct_0(B_815) | ~l1_pre_topc(A_814) | ~v2_pre_topc(A_814) | v2_struct_0(A_814))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.19/1.94  tff(c_1599, plain, (![D_817]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_817))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_817) | ~m1_pre_topc(D_817, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_1597])).
% 5.19/1.94  tff(c_1605, plain, (![D_817]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_817))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_817) | ~m1_pre_topc(D_817, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_116, c_66, c_64, c_48, c_46, c_1599])).
% 5.19/1.94  tff(c_1606, plain, (![D_817]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_817))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_817) | ~m1_pre_topc(D_817, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_68, c_1605])).
% 5.19/1.94  tff(c_1785, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1773, c_1606])).
% 5.19/1.94  tff(c_1792, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1785])).
% 5.19/1.94  tff(c_1429, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 5.19/1.94  tff(c_1797, plain, (~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1792, c_1429])).
% 5.19/1.94  tff(c_1982, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1979, c_1797])).
% 5.19/1.94  tff(c_1985, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_79, c_36, c_1430, c_1982])).
% 5.19/1.94  tff(c_1987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1985])).
% 5.19/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/1.94  
% 5.19/1.94  Inference rules
% 5.19/1.94  ----------------------
% 5.19/1.94  #Ref     : 0
% 5.19/1.94  #Sup     : 381
% 5.19/1.94  #Fact    : 0
% 5.19/1.94  #Define  : 0
% 5.19/1.94  #Split   : 7
% 5.19/1.94  #Chain   : 0
% 5.19/1.94  #Close   : 0
% 5.19/1.94  
% 5.19/1.94  Ordering : KBO
% 5.19/1.94  
% 5.19/1.94  Simplification rules
% 5.19/1.94  ----------------------
% 5.19/1.94  #Subsume      : 117
% 5.19/1.94  #Demod        : 558
% 5.19/1.94  #Tautology    : 127
% 5.19/1.94  #SimpNegUnit  : 39
% 5.19/1.94  #BackRed      : 6
% 5.19/1.94  
% 5.19/1.94  #Partial instantiations: 0
% 5.19/1.94  #Strategies tried      : 1
% 5.19/1.94  
% 5.19/1.94  Timing (in seconds)
% 5.19/1.94  ----------------------
% 5.19/1.94  Preprocessing        : 0.45
% 5.19/1.95  Parsing              : 0.23
% 5.19/1.95  CNF conversion       : 0.07
% 5.19/1.95  Main loop            : 0.71
% 5.19/1.95  Inferencing          : 0.23
% 5.19/1.95  Reduction            : 0.25
% 5.19/1.95  Demodulation         : 0.18
% 5.19/1.95  BG Simplification    : 0.03
% 5.19/1.95  Subsumption          : 0.14
% 5.19/1.95  Abstraction          : 0.03
% 5.19/1.95  MUC search           : 0.00
% 5.19/1.95  Cooper               : 0.00
% 5.19/1.95  Total                : 1.21
% 5.19/1.95  Index Insertion      : 0.00
% 5.19/1.95  Index Deletion       : 0.00
% 5.19/1.95  Index Matching       : 0.00
% 5.19/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
