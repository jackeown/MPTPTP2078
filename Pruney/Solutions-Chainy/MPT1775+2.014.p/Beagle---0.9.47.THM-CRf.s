%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:29 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :  141 (1225 expanded)
%              Number of leaves         :   43 ( 479 expanded)
%              Depth                    :   22
%              Number of atoms          :  489 (9682 expanded)
%              Number of equality atoms :    5 ( 405 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_312,negated_conjecture,(
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
                       => ( ( v1_tsep_1(C,D)
                            & m1_pre_topc(C,D) )
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( F = G
                                   => ( r1_tmap_1(D,B,E,F)
                                    <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_146,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_139,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( m1_connsp_2(C,A,B)
                  & ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                     => ~ ( m1_connsp_2(D,A,B)
                          & v3_pre_topc(D,A)
                          & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_261,axiom,(
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

tff(f_92,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

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

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_58,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_42,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_87,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_93,plain,(
    ! [B_556,A_557] :
      ( l1_pre_topc(B_556)
      | ~ m1_pre_topc(B_556,A_557)
      | ~ l1_pre_topc(A_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_99,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_93])).

tff(c_108,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_99])).

tff(c_114,plain,(
    ! [B_561,A_562] :
      ( v2_pre_topc(B_561)
      | ~ m1_pre_topc(B_561,A_562)
      | ~ l1_pre_topc(A_562)
      | ~ v2_pre_topc(A_562) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_120,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_114])).

tff(c_129,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_120])).

tff(c_50,plain,(
    v1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_32,plain,(
    ! [B_45,A_43] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_204,plain,(
    ! [B_580,A_581] :
      ( v3_pre_topc(u1_struct_0(B_580),A_581)
      | ~ v1_tsep_1(B_580,A_581)
      | ~ m1_subset_1(u1_struct_0(B_580),k1_zfmisc_1(u1_struct_0(A_581)))
      | ~ m1_pre_topc(B_580,A_581)
      | ~ l1_pre_topc(A_581)
      | ~ v2_pre_topc(A_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_208,plain,(
    ! [B_45,A_43] :
      ( v3_pre_topc(u1_struct_0(B_45),A_43)
      | ~ v1_tsep_1(B_45,A_43)
      | ~ v2_pre_topc(A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_32,c_204])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_219,plain,(
    ! [A_590,B_591,C_592] :
      ( r1_tarski('#skF_1'(A_590,B_591,C_592),C_592)
      | ~ m1_connsp_2(C_592,A_590,B_591)
      | ~ m1_subset_1(C_592,k1_zfmisc_1(u1_struct_0(A_590)))
      | ~ m1_subset_1(B_591,u1_struct_0(A_590))
      | ~ l1_pre_topc(A_590)
      | ~ v2_pre_topc(A_590)
      | v2_struct_0(A_590) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_222,plain,(
    ! [A_43,B_591,B_45] :
      ( r1_tarski('#skF_1'(A_43,B_591,u1_struct_0(B_45)),u1_struct_0(B_45))
      | ~ m1_connsp_2(u1_struct_0(B_45),A_43,B_591)
      | ~ m1_subset_1(B_591,u1_struct_0(A_43))
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_32,c_219])).

tff(c_22,plain,(
    ! [A_22,B_30,C_34] :
      ( m1_subset_1('#skF_1'(A_22,B_30,C_34),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_connsp_2(C_34,A_22,B_30)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_30,u1_struct_0(A_22))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_84,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_85,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_84])).

tff(c_135,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_78,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_86,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_78])).

tff(c_163,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_86])).

tff(c_68,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_54,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_513,plain,(
    ! [E_651,A_656,D_652,H_655,F_650,B_654,C_653] :
      ( r1_tmap_1(D_652,B_654,E_651,H_655)
      | ~ r1_tmap_1(C_653,B_654,k3_tmap_1(A_656,B_654,D_652,C_653,E_651),H_655)
      | ~ m1_connsp_2(F_650,D_652,H_655)
      | ~ r1_tarski(F_650,u1_struct_0(C_653))
      | ~ m1_subset_1(H_655,u1_struct_0(C_653))
      | ~ m1_subset_1(H_655,u1_struct_0(D_652))
      | ~ m1_subset_1(F_650,k1_zfmisc_1(u1_struct_0(D_652)))
      | ~ m1_pre_topc(C_653,D_652)
      | ~ m1_subset_1(E_651,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_652),u1_struct_0(B_654))))
      | ~ v1_funct_2(E_651,u1_struct_0(D_652),u1_struct_0(B_654))
      | ~ v1_funct_1(E_651)
      | ~ m1_pre_topc(D_652,A_656)
      | v2_struct_0(D_652)
      | ~ m1_pre_topc(C_653,A_656)
      | v2_struct_0(C_653)
      | ~ l1_pre_topc(B_654)
      | ~ v2_pre_topc(B_654)
      | v2_struct_0(B_654)
      | ~ l1_pre_topc(A_656)
      | ~ v2_pre_topc(A_656)
      | v2_struct_0(A_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_515,plain,(
    ! [F_650] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_650,'#skF_5','#skF_8')
      | ~ r1_tarski(F_650,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_650,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_2')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_135,c_513])).

tff(c_518,plain,(
    ! [F_650] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_650,'#skF_5','#skF_8')
      | ~ r1_tarski(F_650,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_650,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_62,c_58,c_56,c_54,c_52,c_48,c_87,c_44,c_515])).

tff(c_520,plain,(
    ! [F_657] :
      ( ~ m1_connsp_2(F_657,'#skF_5','#skF_8')
      | ~ r1_tarski(F_657,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_657,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_64,c_60,c_163,c_518])).

tff(c_531,plain,(
    ! [B_30,C_34] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_30,C_34),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_5',B_30,C_34),u1_struct_0('#skF_4'))
      | ~ m1_connsp_2(C_34,'#skF_5',B_30)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_30,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_520])).

tff(c_546,plain,(
    ! [B_30,C_34] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_30,C_34),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_5',B_30,C_34),u1_struct_0('#skF_4'))
      | ~ m1_connsp_2(C_34,'#skF_5',B_30)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_30,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_108,c_531])).

tff(c_553,plain,(
    ! [B_659,C_660] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_659,C_660),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_5',B_659,C_660),u1_struct_0('#skF_4'))
      | ~ m1_connsp_2(C_660,'#skF_5',B_659)
      | ~ m1_subset_1(C_660,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_659,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_546])).

tff(c_561,plain,(
    ! [B_591] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_591,u1_struct_0('#skF_4')),'#skF_5','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_5',B_591)
      | ~ m1_subset_1(B_591,u1_struct_0('#skF_5'))
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_222,c_553])).

tff(c_567,plain,(
    ! [B_591] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_591,u1_struct_0('#skF_4')),'#skF_5','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_5',B_591)
      | ~ m1_subset_1(B_591,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_48,c_129,c_561])).

tff(c_568,plain,(
    ! [B_591] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_591,u1_struct_0('#skF_4')),'#skF_5','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_5',B_591)
      | ~ m1_subset_1(B_591,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_567])).

tff(c_569,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_568])).

tff(c_575,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_569])).

tff(c_582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_48,c_575])).

tff(c_584,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_568])).

tff(c_223,plain,(
    ! [B_593,A_594,C_595] :
      ( m1_connsp_2(B_593,A_594,C_595)
      | ~ r2_hidden(C_595,B_593)
      | ~ v3_pre_topc(B_593,A_594)
      | ~ m1_subset_1(C_595,u1_struct_0(A_594))
      | ~ m1_subset_1(B_593,k1_zfmisc_1(u1_struct_0(A_594)))
      | ~ l1_pre_topc(A_594)
      | ~ v2_pre_topc(A_594)
      | v2_struct_0(A_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_227,plain,(
    ! [B_593] :
      ( m1_connsp_2(B_593,'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',B_593)
      | ~ v3_pre_topc(B_593,'#skF_5')
      | ~ m1_subset_1(B_593,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_87,c_223])).

tff(c_234,plain,(
    ! [B_593] :
      ( m1_connsp_2(B_593,'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',B_593)
      | ~ v3_pre_topc(B_593,'#skF_5')
      | ~ m1_subset_1(B_593,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_108,c_227])).

tff(c_235,plain,(
    ! [B_593] :
      ( m1_connsp_2(B_593,'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',B_593)
      | ~ v3_pre_topc(B_593,'#skF_5')
      | ~ m1_subset_1(B_593,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_234])).

tff(c_605,plain,
    ( m1_connsp_2(u1_struct_0('#skF_4'),'#skF_5','#skF_8')
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_584,c_235])).

tff(c_616,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_605])).

tff(c_619,plain,
    ( ~ v1_tsep_1('#skF_4','#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_208,c_616])).

tff(c_623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_48,c_129,c_50,c_619])).

tff(c_625,plain,(
    v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_605])).

tff(c_96,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_93])).

tff(c_105,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_96])).

tff(c_6,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_624,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_4'))
    | m1_connsp_2(u1_struct_0('#skF_4'),'#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_605])).

tff(c_633,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_624])).

tff(c_636,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_633])).

tff(c_639,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_636])).

tff(c_10,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_642,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_639,c_10])).

tff(c_645,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_642])).

tff(c_648,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_645])).

tff(c_652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_648])).

tff(c_654,plain,(
    r2_hidden('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_653,plain,(
    m1_connsp_2(u1_struct_0('#skF_4'),'#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_244,plain,(
    ! [B_597] :
      ( m1_connsp_2(B_597,'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',B_597)
      | ~ v3_pre_topc(B_597,'#skF_5')
      | ~ m1_subset_1(B_597,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_234])).

tff(c_248,plain,(
    ! [B_45] :
      ( m1_connsp_2(u1_struct_0(B_45),'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',u1_struct_0(B_45))
      | ~ v3_pre_topc(u1_struct_0(B_45),'#skF_5')
      | ~ m1_pre_topc(B_45,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_244])).

tff(c_259,plain,(
    ! [B_599] :
      ( m1_connsp_2(u1_struct_0(B_599),'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',u1_struct_0(B_599))
      | ~ v3_pre_topc(u1_struct_0(B_599),'#skF_5')
      | ~ m1_pre_topc(B_599,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_248])).

tff(c_12,plain,(
    ! [C_14,A_11,B_12] :
      ( m1_subset_1(C_14,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_connsp_2(C_14,A_11,B_12)
      | ~ m1_subset_1(B_12,u1_struct_0(A_11))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_261,plain,(
    ! [B_599] :
      ( m1_subset_1(u1_struct_0(B_599),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_8',u1_struct_0(B_599))
      | ~ v3_pre_topc(u1_struct_0(B_599),'#skF_5')
      | ~ m1_pre_topc(B_599,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_259,c_12])).

tff(c_264,plain,(
    ! [B_599] :
      ( m1_subset_1(u1_struct_0(B_599),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_8',u1_struct_0(B_599))
      | ~ v3_pre_topc(u1_struct_0(B_599),'#skF_5')
      | ~ m1_pre_topc(B_599,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_108,c_87,c_261])).

tff(c_265,plain,(
    ! [B_599] :
      ( m1_subset_1(u1_struct_0(B_599),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_599))
      | ~ v3_pre_topc(u1_struct_0(B_599),'#skF_5')
      | ~ m1_pre_topc(B_599,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_264])).

tff(c_300,plain,(
    ! [A_602,B_603,C_604] :
      ( m1_connsp_2('#skF_1'(A_602,B_603,C_604),A_602,B_603)
      | ~ m1_connsp_2(C_604,A_602,B_603)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(u1_struct_0(A_602)))
      | ~ m1_subset_1(B_603,u1_struct_0(A_602))
      | ~ l1_pre_topc(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_302,plain,(
    ! [B_603,B_599] :
      ( m1_connsp_2('#skF_1'('#skF_5',B_603,u1_struct_0(B_599)),'#skF_5',B_603)
      | ~ m1_connsp_2(u1_struct_0(B_599),'#skF_5',B_603)
      | ~ m1_subset_1(B_603,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_8',u1_struct_0(B_599))
      | ~ v3_pre_topc(u1_struct_0(B_599),'#skF_5')
      | ~ m1_pre_topc(B_599,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_265,c_300])).

tff(c_309,plain,(
    ! [B_603,B_599] :
      ( m1_connsp_2('#skF_1'('#skF_5',B_603,u1_struct_0(B_599)),'#skF_5',B_603)
      | ~ m1_connsp_2(u1_struct_0(B_599),'#skF_5',B_603)
      | ~ m1_subset_1(B_603,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_8',u1_struct_0(B_599))
      | ~ v3_pre_topc(u1_struct_0(B_599),'#skF_5')
      | ~ m1_pre_topc(B_599,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_108,c_302])).

tff(c_310,plain,(
    ! [B_603,B_599] :
      ( m1_connsp_2('#skF_1'('#skF_5',B_603,u1_struct_0(B_599)),'#skF_5',B_603)
      | ~ m1_connsp_2(u1_struct_0(B_599),'#skF_5',B_603)
      | ~ m1_subset_1(B_603,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_599))
      | ~ v3_pre_topc(u1_struct_0(B_599),'#skF_5')
      | ~ m1_pre_topc(B_599,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_309])).

tff(c_665,plain,(
    ! [B_670] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_670,u1_struct_0('#skF_4')),'#skF_5','#skF_8')
      | ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_5',B_670)
      | ~ m1_subset_1(B_670,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_568])).

tff(c_673,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_310,c_665])).

tff(c_684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_625,c_654,c_87,c_653,c_673])).

tff(c_685,plain,(
    r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_936,plain,(
    ! [D_742,B_739,G_741,E_743,A_738,C_740] :
      ( r1_tmap_1(D_742,B_739,k3_tmap_1(A_738,B_739,C_740,D_742,E_743),G_741)
      | ~ r1_tmap_1(C_740,B_739,E_743,G_741)
      | ~ m1_pre_topc(D_742,C_740)
      | ~ m1_subset_1(G_741,u1_struct_0(D_742))
      | ~ m1_subset_1(G_741,u1_struct_0(C_740))
      | ~ m1_subset_1(E_743,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_740),u1_struct_0(B_739))))
      | ~ v1_funct_2(E_743,u1_struct_0(C_740),u1_struct_0(B_739))
      | ~ v1_funct_1(E_743)
      | ~ m1_pre_topc(D_742,A_738)
      | v2_struct_0(D_742)
      | ~ m1_pre_topc(C_740,A_738)
      | v2_struct_0(C_740)
      | ~ l1_pre_topc(B_739)
      | ~ v2_pre_topc(B_739)
      | v2_struct_0(B_739)
      | ~ l1_pre_topc(A_738)
      | ~ v2_pre_topc(A_738)
      | v2_struct_0(A_738) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_938,plain,(
    ! [D_742,A_738,G_741] :
      ( r1_tmap_1(D_742,'#skF_3',k3_tmap_1(A_738,'#skF_3','#skF_5',D_742,'#skF_6'),G_741)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_741)
      | ~ m1_pre_topc(D_742,'#skF_5')
      | ~ m1_subset_1(G_741,u1_struct_0(D_742))
      | ~ m1_subset_1(G_741,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_742,A_738)
      | v2_struct_0(D_742)
      | ~ m1_pre_topc('#skF_5',A_738)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_738)
      | ~ v2_pre_topc(A_738)
      | v2_struct_0(A_738) ) ),
    inference(resolution,[status(thm)],[c_52,c_936])).

tff(c_941,plain,(
    ! [D_742,A_738,G_741] :
      ( r1_tmap_1(D_742,'#skF_3',k3_tmap_1(A_738,'#skF_3','#skF_5',D_742,'#skF_6'),G_741)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_741)
      | ~ m1_pre_topc(D_742,'#skF_5')
      | ~ m1_subset_1(G_741,u1_struct_0(D_742))
      | ~ m1_subset_1(G_741,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_742,A_738)
      | v2_struct_0(D_742)
      | ~ m1_pre_topc('#skF_5',A_738)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_738)
      | ~ v2_pre_topc(A_738)
      | v2_struct_0(A_738) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_56,c_54,c_938])).

tff(c_1118,plain,(
    ! [D_773,A_774,G_775] :
      ( r1_tmap_1(D_773,'#skF_3',k3_tmap_1(A_774,'#skF_3','#skF_5',D_773,'#skF_6'),G_775)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_775)
      | ~ m1_pre_topc(D_773,'#skF_5')
      | ~ m1_subset_1(G_775,u1_struct_0(D_773))
      | ~ m1_subset_1(G_775,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_773,A_774)
      | v2_struct_0(D_773)
      | ~ m1_pre_topc('#skF_5',A_774)
      | ~ l1_pre_topc(A_774)
      | ~ v2_pre_topc(A_774)
      | v2_struct_0(A_774) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_60,c_941])).

tff(c_688,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_86])).

tff(c_1123,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1118,c_688])).

tff(c_1130,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_58,c_62,c_87,c_44,c_48,c_685,c_1123])).

tff(c_1132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_64,c_1130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:00:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.18/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.75  
% 4.18/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.76  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 4.18/1.76  
% 4.18/1.76  %Foreground sorts:
% 4.18/1.76  
% 4.18/1.76  
% 4.18/1.76  %Background operators:
% 4.18/1.76  
% 4.18/1.76  
% 4.18/1.76  %Foreground operators:
% 4.18/1.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.18/1.76  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.18/1.76  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.18/1.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.18/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.18/1.76  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.18/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.18/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.18/1.76  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.18/1.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.18/1.76  tff('#skF_7', type, '#skF_7': $i).
% 4.18/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.18/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.18/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.18/1.76  tff('#skF_6', type, '#skF_6': $i).
% 4.18/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.18/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.18/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.18/1.76  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.18/1.76  tff('#skF_8', type, '#skF_8': $i).
% 4.18/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.18/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.18/1.76  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.18/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.18/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.18/1.76  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.18/1.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.18/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.18/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.18/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.18/1.76  
% 4.18/1.78  tff(f_312, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.18/1.78  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.18/1.78  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.18/1.78  tff(f_146, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.18/1.78  tff(f_139, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.18/1.78  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 4.18/1.78  tff(f_261, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.18/1.78  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 4.18/1.78  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.18/1.78  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.18/1.78  tff(f_59, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.18/1.78  tff(f_73, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 4.18/1.78  tff(f_206, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.18/1.78  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_58, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_42, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_87, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 4.18/1.78  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_93, plain, (![B_556, A_557]: (l1_pre_topc(B_556) | ~m1_pre_topc(B_556, A_557) | ~l1_pre_topc(A_557))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.18/1.78  tff(c_99, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_93])).
% 4.18/1.78  tff(c_108, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_99])).
% 4.18/1.78  tff(c_114, plain, (![B_561, A_562]: (v2_pre_topc(B_561) | ~m1_pre_topc(B_561, A_562) | ~l1_pre_topc(A_562) | ~v2_pre_topc(A_562))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.18/1.78  tff(c_120, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_114])).
% 4.18/1.78  tff(c_129, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_120])).
% 4.18/1.78  tff(c_50, plain, (v1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_32, plain, (![B_45, A_43]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.18/1.78  tff(c_204, plain, (![B_580, A_581]: (v3_pre_topc(u1_struct_0(B_580), A_581) | ~v1_tsep_1(B_580, A_581) | ~m1_subset_1(u1_struct_0(B_580), k1_zfmisc_1(u1_struct_0(A_581))) | ~m1_pre_topc(B_580, A_581) | ~l1_pre_topc(A_581) | ~v2_pre_topc(A_581))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.18/1.78  tff(c_208, plain, (![B_45, A_43]: (v3_pre_topc(u1_struct_0(B_45), A_43) | ~v1_tsep_1(B_45, A_43) | ~v2_pre_topc(A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_32, c_204])).
% 4.18/1.78  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_219, plain, (![A_590, B_591, C_592]: (r1_tarski('#skF_1'(A_590, B_591, C_592), C_592) | ~m1_connsp_2(C_592, A_590, B_591) | ~m1_subset_1(C_592, k1_zfmisc_1(u1_struct_0(A_590))) | ~m1_subset_1(B_591, u1_struct_0(A_590)) | ~l1_pre_topc(A_590) | ~v2_pre_topc(A_590) | v2_struct_0(A_590))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.18/1.78  tff(c_222, plain, (![A_43, B_591, B_45]: (r1_tarski('#skF_1'(A_43, B_591, u1_struct_0(B_45)), u1_struct_0(B_45)) | ~m1_connsp_2(u1_struct_0(B_45), A_43, B_591) | ~m1_subset_1(B_591, u1_struct_0(A_43)) | ~v2_pre_topc(A_43) | v2_struct_0(A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_32, c_219])).
% 4.18/1.78  tff(c_22, plain, (![A_22, B_30, C_34]: (m1_subset_1('#skF_1'(A_22, B_30, C_34), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_connsp_2(C_34, A_22, B_30) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_30, u1_struct_0(A_22)) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.18/1.78  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_84, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_85, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_84])).
% 4.18/1.78  tff(c_135, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_85])).
% 4.18/1.78  tff(c_78, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_86, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_78])).
% 4.18/1.78  tff(c_163, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_86])).
% 4.18/1.78  tff(c_68, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_54, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_312])).
% 4.18/1.78  tff(c_513, plain, (![E_651, A_656, D_652, H_655, F_650, B_654, C_653]: (r1_tmap_1(D_652, B_654, E_651, H_655) | ~r1_tmap_1(C_653, B_654, k3_tmap_1(A_656, B_654, D_652, C_653, E_651), H_655) | ~m1_connsp_2(F_650, D_652, H_655) | ~r1_tarski(F_650, u1_struct_0(C_653)) | ~m1_subset_1(H_655, u1_struct_0(C_653)) | ~m1_subset_1(H_655, u1_struct_0(D_652)) | ~m1_subset_1(F_650, k1_zfmisc_1(u1_struct_0(D_652))) | ~m1_pre_topc(C_653, D_652) | ~m1_subset_1(E_651, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_652), u1_struct_0(B_654)))) | ~v1_funct_2(E_651, u1_struct_0(D_652), u1_struct_0(B_654)) | ~v1_funct_1(E_651) | ~m1_pre_topc(D_652, A_656) | v2_struct_0(D_652) | ~m1_pre_topc(C_653, A_656) | v2_struct_0(C_653) | ~l1_pre_topc(B_654) | ~v2_pre_topc(B_654) | v2_struct_0(B_654) | ~l1_pre_topc(A_656) | ~v2_pre_topc(A_656) | v2_struct_0(A_656))), inference(cnfTransformation, [status(thm)], [f_261])).
% 4.18/1.78  tff(c_515, plain, (![F_650]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_650, '#skF_5', '#skF_8') | ~r1_tarski(F_650, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_650, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_135, c_513])).
% 4.18/1.78  tff(c_518, plain, (![F_650]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_650, '#skF_5', '#skF_8') | ~r1_tarski(F_650, u1_struct_0('#skF_4')) | ~m1_subset_1(F_650, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_62, c_58, c_56, c_54, c_52, c_48, c_87, c_44, c_515])).
% 4.18/1.78  tff(c_520, plain, (![F_657]: (~m1_connsp_2(F_657, '#skF_5', '#skF_8') | ~r1_tarski(F_657, u1_struct_0('#skF_4')) | ~m1_subset_1(F_657, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_64, c_60, c_163, c_518])).
% 4.18/1.78  tff(c_531, plain, (![B_30, C_34]: (~m1_connsp_2('#skF_1'('#skF_5', B_30, C_34), '#skF_5', '#skF_8') | ~r1_tarski('#skF_1'('#skF_5', B_30, C_34), u1_struct_0('#skF_4')) | ~m1_connsp_2(C_34, '#skF_5', B_30) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_30, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_22, c_520])).
% 4.18/1.78  tff(c_546, plain, (![B_30, C_34]: (~m1_connsp_2('#skF_1'('#skF_5', B_30, C_34), '#skF_5', '#skF_8') | ~r1_tarski('#skF_1'('#skF_5', B_30, C_34), u1_struct_0('#skF_4')) | ~m1_connsp_2(C_34, '#skF_5', B_30) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_30, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_108, c_531])).
% 4.18/1.78  tff(c_553, plain, (![B_659, C_660]: (~m1_connsp_2('#skF_1'('#skF_5', B_659, C_660), '#skF_5', '#skF_8') | ~r1_tarski('#skF_1'('#skF_5', B_659, C_660), u1_struct_0('#skF_4')) | ~m1_connsp_2(C_660, '#skF_5', B_659) | ~m1_subset_1(C_660, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_659, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_546])).
% 4.18/1.78  tff(c_561, plain, (![B_591]: (~m1_connsp_2('#skF_1'('#skF_5', B_591, u1_struct_0('#skF_4')), '#skF_5', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_5', B_591) | ~m1_subset_1(B_591, u1_struct_0('#skF_5')) | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_222, c_553])).
% 4.18/1.78  tff(c_567, plain, (![B_591]: (~m1_connsp_2('#skF_1'('#skF_5', B_591, u1_struct_0('#skF_4')), '#skF_5', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_5', B_591) | ~m1_subset_1(B_591, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_48, c_129, c_561])).
% 4.18/1.78  tff(c_568, plain, (![B_591]: (~m1_connsp_2('#skF_1'('#skF_5', B_591, u1_struct_0('#skF_4')), '#skF_5', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_5', B_591) | ~m1_subset_1(B_591, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_567])).
% 4.18/1.78  tff(c_569, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_568])).
% 4.18/1.78  tff(c_575, plain, (~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_32, c_569])).
% 4.18/1.78  tff(c_582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_48, c_575])).
% 4.18/1.78  tff(c_584, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_568])).
% 4.18/1.78  tff(c_223, plain, (![B_593, A_594, C_595]: (m1_connsp_2(B_593, A_594, C_595) | ~r2_hidden(C_595, B_593) | ~v3_pre_topc(B_593, A_594) | ~m1_subset_1(C_595, u1_struct_0(A_594)) | ~m1_subset_1(B_593, k1_zfmisc_1(u1_struct_0(A_594))) | ~l1_pre_topc(A_594) | ~v2_pre_topc(A_594) | v2_struct_0(A_594))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.18/1.78  tff(c_227, plain, (![B_593]: (m1_connsp_2(B_593, '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', B_593) | ~v3_pre_topc(B_593, '#skF_5') | ~m1_subset_1(B_593, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_87, c_223])).
% 4.18/1.78  tff(c_234, plain, (![B_593]: (m1_connsp_2(B_593, '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', B_593) | ~v3_pre_topc(B_593, '#skF_5') | ~m1_subset_1(B_593, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_108, c_227])).
% 4.18/1.78  tff(c_235, plain, (![B_593]: (m1_connsp_2(B_593, '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', B_593) | ~v3_pre_topc(B_593, '#skF_5') | ~m1_subset_1(B_593, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_234])).
% 4.18/1.78  tff(c_605, plain, (m1_connsp_2(u1_struct_0('#skF_4'), '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_584, c_235])).
% 4.18/1.78  tff(c_616, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_605])).
% 4.18/1.78  tff(c_619, plain, (~v1_tsep_1('#skF_4', '#skF_5') | ~v2_pre_topc('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_208, c_616])).
% 4.18/1.78  tff(c_623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_48, c_129, c_50, c_619])).
% 4.18/1.78  tff(c_625, plain, (v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_605])).
% 4.18/1.78  tff(c_96, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_93])).
% 4.18/1.78  tff(c_105, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_96])).
% 4.18/1.78  tff(c_6, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.18/1.78  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.18/1.78  tff(c_624, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_4')) | m1_connsp_2(u1_struct_0('#skF_4'), '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_605])).
% 4.18/1.78  tff(c_633, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_624])).
% 4.18/1.78  tff(c_636, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2, c_633])).
% 4.18/1.78  tff(c_639, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_636])).
% 4.18/1.78  tff(c_10, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.18/1.78  tff(c_642, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_639, c_10])).
% 4.18/1.78  tff(c_645, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_642])).
% 4.18/1.78  tff(c_648, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_645])).
% 4.18/1.78  tff(c_652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_648])).
% 4.18/1.78  tff(c_654, plain, (r2_hidden('#skF_8', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_624])).
% 4.18/1.78  tff(c_653, plain, (m1_connsp_2(u1_struct_0('#skF_4'), '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_624])).
% 4.18/1.78  tff(c_244, plain, (![B_597]: (m1_connsp_2(B_597, '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', B_597) | ~v3_pre_topc(B_597, '#skF_5') | ~m1_subset_1(B_597, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_234])).
% 4.18/1.78  tff(c_248, plain, (![B_45]: (m1_connsp_2(u1_struct_0(B_45), '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0(B_45)) | ~v3_pre_topc(u1_struct_0(B_45), '#skF_5') | ~m1_pre_topc(B_45, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_244])).
% 4.18/1.78  tff(c_259, plain, (![B_599]: (m1_connsp_2(u1_struct_0(B_599), '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0(B_599)) | ~v3_pre_topc(u1_struct_0(B_599), '#skF_5') | ~m1_pre_topc(B_599, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_248])).
% 4.18/1.78  tff(c_12, plain, (![C_14, A_11, B_12]: (m1_subset_1(C_14, k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_connsp_2(C_14, A_11, B_12) | ~m1_subset_1(B_12, u1_struct_0(A_11)) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.18/1.78  tff(c_261, plain, (![B_599]: (m1_subset_1(u1_struct_0(B_599), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_8', u1_struct_0(B_599)) | ~v3_pre_topc(u1_struct_0(B_599), '#skF_5') | ~m1_pre_topc(B_599, '#skF_5'))), inference(resolution, [status(thm)], [c_259, c_12])).
% 4.18/1.78  tff(c_264, plain, (![B_599]: (m1_subset_1(u1_struct_0(B_599), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | ~r2_hidden('#skF_8', u1_struct_0(B_599)) | ~v3_pre_topc(u1_struct_0(B_599), '#skF_5') | ~m1_pre_topc(B_599, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_108, c_87, c_261])).
% 4.18/1.78  tff(c_265, plain, (![B_599]: (m1_subset_1(u1_struct_0(B_599), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden('#skF_8', u1_struct_0(B_599)) | ~v3_pre_topc(u1_struct_0(B_599), '#skF_5') | ~m1_pre_topc(B_599, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_264])).
% 4.18/1.78  tff(c_300, plain, (![A_602, B_603, C_604]: (m1_connsp_2('#skF_1'(A_602, B_603, C_604), A_602, B_603) | ~m1_connsp_2(C_604, A_602, B_603) | ~m1_subset_1(C_604, k1_zfmisc_1(u1_struct_0(A_602))) | ~m1_subset_1(B_603, u1_struct_0(A_602)) | ~l1_pre_topc(A_602) | ~v2_pre_topc(A_602) | v2_struct_0(A_602))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.18/1.78  tff(c_302, plain, (![B_603, B_599]: (m1_connsp_2('#skF_1'('#skF_5', B_603, u1_struct_0(B_599)), '#skF_5', B_603) | ~m1_connsp_2(u1_struct_0(B_599), '#skF_5', B_603) | ~m1_subset_1(B_603, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_8', u1_struct_0(B_599)) | ~v3_pre_topc(u1_struct_0(B_599), '#skF_5') | ~m1_pre_topc(B_599, '#skF_5'))), inference(resolution, [status(thm)], [c_265, c_300])).
% 4.18/1.78  tff(c_309, plain, (![B_603, B_599]: (m1_connsp_2('#skF_1'('#skF_5', B_603, u1_struct_0(B_599)), '#skF_5', B_603) | ~m1_connsp_2(u1_struct_0(B_599), '#skF_5', B_603) | ~m1_subset_1(B_603, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~r2_hidden('#skF_8', u1_struct_0(B_599)) | ~v3_pre_topc(u1_struct_0(B_599), '#skF_5') | ~m1_pre_topc(B_599, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_108, c_302])).
% 4.18/1.78  tff(c_310, plain, (![B_603, B_599]: (m1_connsp_2('#skF_1'('#skF_5', B_603, u1_struct_0(B_599)), '#skF_5', B_603) | ~m1_connsp_2(u1_struct_0(B_599), '#skF_5', B_603) | ~m1_subset_1(B_603, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_8', u1_struct_0(B_599)) | ~v3_pre_topc(u1_struct_0(B_599), '#skF_5') | ~m1_pre_topc(B_599, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_309])).
% 4.18/1.78  tff(c_665, plain, (![B_670]: (~m1_connsp_2('#skF_1'('#skF_5', B_670, u1_struct_0('#skF_4')), '#skF_5', '#skF_8') | ~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_5', B_670) | ~m1_subset_1(B_670, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_568])).
% 4.18/1.78  tff(c_673, plain, (~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~r2_hidden('#skF_8', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_310, c_665])).
% 4.18/1.78  tff(c_684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_625, c_654, c_87, c_653, c_673])).
% 4.18/1.78  tff(c_685, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_85])).
% 4.18/1.78  tff(c_936, plain, (![D_742, B_739, G_741, E_743, A_738, C_740]: (r1_tmap_1(D_742, B_739, k3_tmap_1(A_738, B_739, C_740, D_742, E_743), G_741) | ~r1_tmap_1(C_740, B_739, E_743, G_741) | ~m1_pre_topc(D_742, C_740) | ~m1_subset_1(G_741, u1_struct_0(D_742)) | ~m1_subset_1(G_741, u1_struct_0(C_740)) | ~m1_subset_1(E_743, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_740), u1_struct_0(B_739)))) | ~v1_funct_2(E_743, u1_struct_0(C_740), u1_struct_0(B_739)) | ~v1_funct_1(E_743) | ~m1_pre_topc(D_742, A_738) | v2_struct_0(D_742) | ~m1_pre_topc(C_740, A_738) | v2_struct_0(C_740) | ~l1_pre_topc(B_739) | ~v2_pre_topc(B_739) | v2_struct_0(B_739) | ~l1_pre_topc(A_738) | ~v2_pre_topc(A_738) | v2_struct_0(A_738))), inference(cnfTransformation, [status(thm)], [f_206])).
% 4.18/1.78  tff(c_938, plain, (![D_742, A_738, G_741]: (r1_tmap_1(D_742, '#skF_3', k3_tmap_1(A_738, '#skF_3', '#skF_5', D_742, '#skF_6'), G_741) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_741) | ~m1_pre_topc(D_742, '#skF_5') | ~m1_subset_1(G_741, u1_struct_0(D_742)) | ~m1_subset_1(G_741, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_742, A_738) | v2_struct_0(D_742) | ~m1_pre_topc('#skF_5', A_738) | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_738) | ~v2_pre_topc(A_738) | v2_struct_0(A_738))), inference(resolution, [status(thm)], [c_52, c_936])).
% 4.18/1.78  tff(c_941, plain, (![D_742, A_738, G_741]: (r1_tmap_1(D_742, '#skF_3', k3_tmap_1(A_738, '#skF_3', '#skF_5', D_742, '#skF_6'), G_741) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_741) | ~m1_pre_topc(D_742, '#skF_5') | ~m1_subset_1(G_741, u1_struct_0(D_742)) | ~m1_subset_1(G_741, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_742, A_738) | v2_struct_0(D_742) | ~m1_pre_topc('#skF_5', A_738) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_738) | ~v2_pre_topc(A_738) | v2_struct_0(A_738))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_56, c_54, c_938])).
% 4.18/1.78  tff(c_1118, plain, (![D_773, A_774, G_775]: (r1_tmap_1(D_773, '#skF_3', k3_tmap_1(A_774, '#skF_3', '#skF_5', D_773, '#skF_6'), G_775) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_775) | ~m1_pre_topc(D_773, '#skF_5') | ~m1_subset_1(G_775, u1_struct_0(D_773)) | ~m1_subset_1(G_775, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_773, A_774) | v2_struct_0(D_773) | ~m1_pre_topc('#skF_5', A_774) | ~l1_pre_topc(A_774) | ~v2_pre_topc(A_774) | v2_struct_0(A_774))), inference(negUnitSimplification, [status(thm)], [c_70, c_60, c_941])).
% 4.18/1.78  tff(c_688, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_685, c_86])).
% 4.18/1.78  tff(c_1123, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1118, c_688])).
% 4.18/1.78  tff(c_1130, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_58, c_62, c_87, c_44, c_48, c_685, c_1123])).
% 4.18/1.78  tff(c_1132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_64, c_1130])).
% 4.18/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.78  
% 4.18/1.78  Inference rules
% 4.18/1.78  ----------------------
% 4.18/1.78  #Ref     : 0
% 4.18/1.78  #Sup     : 178
% 4.18/1.78  #Fact    : 0
% 4.18/1.78  #Define  : 0
% 4.18/1.78  #Split   : 7
% 4.18/1.78  #Chain   : 0
% 4.18/1.78  #Close   : 0
% 4.18/1.78  
% 4.18/1.78  Ordering : KBO
% 4.18/1.78  
% 4.18/1.78  Simplification rules
% 4.18/1.78  ----------------------
% 4.18/1.78  #Subsume      : 20
% 4.18/1.78  #Demod        : 269
% 4.18/1.78  #Tautology    : 22
% 4.18/1.78  #SimpNegUnit  : 75
% 4.18/1.78  #BackRed      : 0
% 4.18/1.78  
% 4.18/1.78  #Partial instantiations: 0
% 4.18/1.78  #Strategies tried      : 1
% 4.18/1.78  
% 4.18/1.78  Timing (in seconds)
% 4.18/1.78  ----------------------
% 4.59/1.79  Preprocessing        : 0.44
% 4.59/1.79  Parsing              : 0.23
% 4.59/1.79  CNF conversion       : 0.06
% 4.59/1.79  Main loop            : 0.53
% 4.59/1.79  Inferencing          : 0.19
% 4.59/1.79  Reduction            : 0.18
% 4.59/1.79  Demodulation         : 0.14
% 4.59/1.79  BG Simplification    : 0.03
% 4.59/1.79  Subsumption          : 0.09
% 4.59/1.79  Abstraction          : 0.02
% 4.59/1.79  MUC search           : 0.00
% 4.59/1.79  Cooper               : 0.00
% 4.59/1.79  Total                : 1.01
% 4.59/1.79  Index Insertion      : 0.00
% 4.59/1.79  Index Deletion       : 0.00
% 4.59/1.79  Index Matching       : 0.00
% 4.59/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
