%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:05 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 453 expanded)
%              Number of leaves         :   35 ( 188 expanded)
%              Depth                    :   20
%              Number of atoms          :  425 (4082 expanded)
%              Number of equality atoms :   11 ( 515 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_271,negated_conjecture,(
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
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( A = k1_tsep_1(A,D,E)
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(A))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(E))
                                     => ( ( F = G
                                          & F = H )
                                       => ( r1_tmap_1(A,B,C,F)
                                        <=> ( r1_tmap_1(D,B,k2_tmap_1(A,B,C,D),G)
                                            & r1_tmap_1(E,B,k2_tmap_1(A,B,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_tmap_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_128,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_124,axiom,(
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
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(k1_tsep_1(A,D,E)))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ! [H] :
                                  ( m1_subset_1(H,u1_struct_0(E))
                                 => ( ( F = G
                                      & F = H )
                                   => ( r1_tmap_1(k1_tsep_1(A,D,E),B,k2_tmap_1(A,B,C,k1_tsep_1(A,D,E)),F)
                                    <=> ( r1_tmap_1(D,B,k2_tmap_1(A,B,C,D),G)
                                        & r1_tmap_1(E,B,k2_tmap_1(A,B,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_tmap_1)).

tff(f_215,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_42,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_28,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_77,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_38,plain,(
    m1_pre_topc('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_26,plain,(
    '#skF_7' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_79,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_30,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_80,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_30])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_10,plain,(
    ! [A_14,B_15] :
      ( m1_connsp_2('#skF_1'(A_14,B_15),A_14,B_15)
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_185,plain,(
    ! [C_729,A_730,B_731] :
      ( m1_subset_1(C_729,k1_zfmisc_1(u1_struct_0(A_730)))
      | ~ m1_connsp_2(C_729,A_730,B_731)
      | ~ m1_subset_1(B_731,u1_struct_0(A_730))
      | ~ l1_pre_topc(A_730)
      | ~ v2_pre_topc(A_730)
      | v2_struct_0(A_730) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_189,plain,(
    ! [A_732,B_733] :
      ( m1_subset_1('#skF_1'(A_732,B_733),k1_zfmisc_1(u1_struct_0(A_732)))
      | ~ m1_subset_1(B_733,u1_struct_0(A_732))
      | ~ l1_pre_topc(A_732)
      | ~ v2_pre_topc(A_732)
      | v2_struct_0(A_732) ) ),
    inference(resolution,[status(thm)],[c_10,c_185])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_193,plain,(
    ! [A_732,B_733] :
      ( r1_tarski('#skF_1'(A_732,B_733),u1_struct_0(A_732))
      | ~ m1_subset_1(B_733,u1_struct_0(A_732))
      | ~ l1_pre_topc(A_732)
      | ~ v2_pre_topc(A_732)
      | v2_struct_0(A_732) ) ),
    inference(resolution,[status(thm)],[c_189,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_272] :
      ( m1_pre_topc(A_272,A_272)
      | ~ l1_pre_topc(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_74,plain,
    ( r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_7')
    | r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_78,plain,
    ( r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_74])).

tff(c_106,plain,(
    r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_70,plain,
    ( r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_7')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_70])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_76])).

tff(c_107,plain,(
    r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_64,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_75,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_64])).

tff(c_81,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_75])).

tff(c_196,plain,(
    ~ r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_107,c_81])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_48,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_36,plain,(
    k1_tsep_1('#skF_2','#skF_5','#skF_6') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_392,plain,(
    ! [B_793,C_789,E_794,A_790,H_791,D_792] :
      ( r1_tmap_1(k1_tsep_1(A_790,D_792,E_794),B_793,k2_tmap_1(A_790,B_793,C_789,k1_tsep_1(A_790,D_792,E_794)),H_791)
      | ~ r1_tmap_1(E_794,B_793,k2_tmap_1(A_790,B_793,C_789,E_794),H_791)
      | ~ r1_tmap_1(D_792,B_793,k2_tmap_1(A_790,B_793,C_789,D_792),H_791)
      | ~ m1_subset_1(H_791,u1_struct_0(E_794))
      | ~ m1_subset_1(H_791,u1_struct_0(D_792))
      | ~ m1_subset_1(H_791,u1_struct_0(k1_tsep_1(A_790,D_792,E_794)))
      | ~ m1_pre_topc(E_794,A_790)
      | v2_struct_0(E_794)
      | ~ m1_pre_topc(D_792,A_790)
      | v2_struct_0(D_792)
      | ~ m1_subset_1(C_789,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790),u1_struct_0(B_793))))
      | ~ v1_funct_2(C_789,u1_struct_0(A_790),u1_struct_0(B_793))
      | ~ v1_funct_1(C_789)
      | ~ l1_pre_topc(B_793)
      | ~ v2_pre_topc(B_793)
      | v2_struct_0(B_793)
      | ~ l1_pre_topc(A_790)
      | ~ v2_pre_topc(A_790)
      | v2_struct_0(A_790) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_397,plain,(
    ! [D_792,E_794,H_791] :
      ( r1_tmap_1(k1_tsep_1('#skF_2',D_792,E_794),'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',k1_tsep_1('#skF_2',D_792,E_794)),H_791)
      | ~ r1_tmap_1(E_794,'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',E_794),H_791)
      | ~ r1_tmap_1(D_792,'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',D_792),H_791)
      | ~ m1_subset_1(H_791,u1_struct_0(E_794))
      | ~ m1_subset_1(H_791,u1_struct_0(D_792))
      | ~ m1_subset_1(H_791,u1_struct_0(k1_tsep_1('#skF_2',D_792,E_794)))
      | ~ m1_pre_topc(E_794,'#skF_2')
      | v2_struct_0(E_794)
      | ~ m1_pre_topc(D_792,'#skF_2')
      | v2_struct_0(D_792)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_392])).

tff(c_401,plain,(
    ! [D_792,E_794,H_791] :
      ( r1_tmap_1(k1_tsep_1('#skF_2',D_792,E_794),'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',k1_tsep_1('#skF_2',D_792,E_794)),H_791)
      | ~ r1_tmap_1(E_794,'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',E_794),H_791)
      | ~ r1_tmap_1(D_792,'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',D_792),H_791)
      | ~ m1_subset_1(H_791,u1_struct_0(E_794))
      | ~ m1_subset_1(H_791,u1_struct_0(D_792))
      | ~ m1_subset_1(H_791,u1_struct_0(k1_tsep_1('#skF_2',D_792,E_794)))
      | ~ m1_pre_topc(E_794,'#skF_2')
      | v2_struct_0(E_794)
      | ~ m1_pre_topc(D_792,'#skF_2')
      | v2_struct_0(D_792)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_50,c_48,c_397])).

tff(c_424,plain,(
    ! [D_800,E_801,H_802] :
      ( r1_tmap_1(k1_tsep_1('#skF_2',D_800,E_801),'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',k1_tsep_1('#skF_2',D_800,E_801)),H_802)
      | ~ r1_tmap_1(E_801,'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',E_801),H_802)
      | ~ r1_tmap_1(D_800,'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',D_800),H_802)
      | ~ m1_subset_1(H_802,u1_struct_0(E_801))
      | ~ m1_subset_1(H_802,u1_struct_0(D_800))
      | ~ m1_subset_1(H_802,u1_struct_0(k1_tsep_1('#skF_2',D_800,E_801)))
      | ~ m1_pre_topc(E_801,'#skF_2')
      | v2_struct_0(E_801)
      | ~ m1_pre_topc(D_800,'#skF_2')
      | v2_struct_0(D_800) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_401])).

tff(c_433,plain,(
    ! [H_802] :
      ( r1_tmap_1('#skF_2','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',k1_tsep_1('#skF_2','#skF_5','#skF_6')),H_802)
      | ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_6'),H_802)
      | ~ r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5'),H_802)
      | ~ m1_subset_1(H_802,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(H_802,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_802,u1_struct_0(k1_tsep_1('#skF_2','#skF_5','#skF_6')))
      | ~ m1_pre_topc('#skF_6','#skF_2')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_2')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_424])).

tff(c_450,plain,(
    ! [H_802] :
      ( r1_tmap_1('#skF_2','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_2'),H_802)
      | ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_6'),H_802)
      | ~ r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5'),H_802)
      | ~ m1_subset_1(H_802,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(H_802,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_802,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_36,c_433])).

tff(c_455,plain,(
    ! [H_803] :
      ( r1_tmap_1('#skF_2','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_2'),H_803)
      | ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_6'),H_803)
      | ~ r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5'),H_803)
      | ~ m1_subset_1(H_803,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(H_803,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_803,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_450])).

tff(c_465,plain,
    ( r1_tmap_1('#skF_2','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_2'),'#skF_8')
    | ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_106,c_455])).

tff(c_473,plain,(
    r1_tmap_1('#skF_2','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_2'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_32,c_80,c_107,c_465])).

tff(c_22,plain,(
    ! [C_432,A_336,D_448,B_400,G_462,E_456] :
      ( r1_tmap_1(B_400,A_336,C_432,G_462)
      | ~ r1_tmap_1(D_448,A_336,k2_tmap_1(B_400,A_336,C_432,D_448),G_462)
      | ~ m1_connsp_2(E_456,B_400,G_462)
      | ~ r1_tarski(E_456,u1_struct_0(D_448))
      | ~ m1_subset_1(G_462,u1_struct_0(D_448))
      | ~ m1_subset_1(G_462,u1_struct_0(B_400))
      | ~ m1_subset_1(E_456,k1_zfmisc_1(u1_struct_0(B_400)))
      | ~ m1_pre_topc(D_448,B_400)
      | v2_struct_0(D_448)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_400),u1_struct_0(A_336))))
      | ~ v1_funct_2(C_432,u1_struct_0(B_400),u1_struct_0(A_336))
      | ~ v1_funct_1(C_432)
      | ~ l1_pre_topc(B_400)
      | ~ v2_pre_topc(B_400)
      | v2_struct_0(B_400)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_475,plain,(
    ! [E_456] :
      ( r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_connsp_2(E_456,'#skF_2','#skF_8')
      | ~ r1_tarski(E_456,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_456,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_473,c_22])).

tff(c_478,plain,(
    ! [E_456] :
      ( r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_connsp_2(E_456,'#skF_2','#skF_8')
      | ~ r1_tarski(E_456,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_456,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_2','#skF_2')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_60,c_58,c_50,c_48,c_46,c_77,c_475])).

tff(c_479,plain,(
    ! [E_456] :
      ( ~ m1_connsp_2(E_456,'#skF_2','#skF_8')
      | ~ r1_tarski(E_456,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_456,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_2','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_196,c_478])).

tff(c_502,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_479])).

tff(c_505,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_502])).

tff(c_509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_505])).

tff(c_549,plain,(
    ! [E_811] :
      ( ~ m1_connsp_2(E_811,'#skF_2','#skF_8')
      | ~ r1_tarski(E_811,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_811,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_479])).

tff(c_563,plain,(
    ! [A_812] :
      ( ~ m1_connsp_2(A_812,'#skF_2','#skF_8')
      | ~ r1_tarski(A_812,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_4,c_549])).

tff(c_567,plain,(
    ! [B_733] :
      ( ~ m1_connsp_2('#skF_1'('#skF_2',B_733),'#skF_2','#skF_8')
      | ~ m1_subset_1(B_733,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_193,c_563])).

tff(c_570,plain,(
    ! [B_733] :
      ( ~ m1_connsp_2('#skF_1'('#skF_2',B_733),'#skF_2','#skF_8')
      | ~ m1_subset_1(B_733,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_567])).

tff(c_572,plain,(
    ! [B_813] :
      ( ~ m1_connsp_2('#skF_1'('#skF_2',B_813),'#skF_2','#skF_8')
      | ~ m1_subset_1(B_813,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_570])).

tff(c_576,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_572])).

tff(c_579,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_77,c_576])).

tff(c_581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_579])).

tff(c_582,plain,(
    r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_673,plain,(
    ! [F_835,B_838,C_836,A_837,D_839] :
      ( r1_tmap_1(D_839,A_837,k2_tmap_1(B_838,A_837,C_836,D_839),F_835)
      | ~ r1_tmap_1(B_838,A_837,C_836,F_835)
      | ~ m1_subset_1(F_835,u1_struct_0(D_839))
      | ~ m1_subset_1(F_835,u1_struct_0(B_838))
      | ~ m1_pre_topc(D_839,B_838)
      | v2_struct_0(D_839)
      | ~ m1_subset_1(C_836,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_838),u1_struct_0(A_837))))
      | ~ v1_funct_2(C_836,u1_struct_0(B_838),u1_struct_0(A_837))
      | ~ v1_funct_1(C_836)
      | ~ l1_pre_topc(B_838)
      | ~ v2_pre_topc(B_838)
      | v2_struct_0(B_838)
      | ~ l1_pre_topc(A_837)
      | ~ v2_pre_topc(A_837)
      | v2_struct_0(A_837) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_678,plain,(
    ! [D_839,F_835] :
      ( r1_tmap_1(D_839,'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',D_839),F_835)
      | ~ r1_tmap_1('#skF_2','#skF_3','#skF_4',F_835)
      | ~ m1_subset_1(F_835,u1_struct_0(D_839))
      | ~ m1_subset_1(F_835,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_839,'#skF_2')
      | v2_struct_0(D_839)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_673])).

tff(c_682,plain,(
    ! [D_839,F_835] :
      ( r1_tmap_1(D_839,'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',D_839),F_835)
      | ~ r1_tmap_1('#skF_2','#skF_3','#skF_4',F_835)
      | ~ m1_subset_1(F_835,u1_struct_0(D_839))
      | ~ m1_subset_1(F_835,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_839,'#skF_2')
      | v2_struct_0(D_839)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_60,c_58,c_50,c_48,c_678])).

tff(c_684,plain,(
    ! [D_840,F_841] :
      ( r1_tmap_1(D_840,'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',D_840),F_841)
      | ~ r1_tmap_1('#skF_2','#skF_3','#skF_4',F_841)
      | ~ m1_subset_1(F_841,u1_struct_0(D_840))
      | ~ m1_subset_1(F_841,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_840,'#skF_2')
      | v2_struct_0(D_840) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_682])).

tff(c_583,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_687,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_6','#skF_2')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_684,c_583])).

tff(c_690,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_77,c_80,c_582,c_687])).

tff(c_692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_690])).

tff(c_693,plain,(
    r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_785,plain,(
    ! [B_866,C_864,D_867,A_865,F_863] :
      ( r1_tmap_1(D_867,A_865,k2_tmap_1(B_866,A_865,C_864,D_867),F_863)
      | ~ r1_tmap_1(B_866,A_865,C_864,F_863)
      | ~ m1_subset_1(F_863,u1_struct_0(D_867))
      | ~ m1_subset_1(F_863,u1_struct_0(B_866))
      | ~ m1_pre_topc(D_867,B_866)
      | v2_struct_0(D_867)
      | ~ m1_subset_1(C_864,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_866),u1_struct_0(A_865))))
      | ~ v1_funct_2(C_864,u1_struct_0(B_866),u1_struct_0(A_865))
      | ~ v1_funct_1(C_864)
      | ~ l1_pre_topc(B_866)
      | ~ v2_pre_topc(B_866)
      | v2_struct_0(B_866)
      | ~ l1_pre_topc(A_865)
      | ~ v2_pre_topc(A_865)
      | v2_struct_0(A_865) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_790,plain,(
    ! [D_867,F_863] :
      ( r1_tmap_1(D_867,'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',D_867),F_863)
      | ~ r1_tmap_1('#skF_2','#skF_3','#skF_4',F_863)
      | ~ m1_subset_1(F_863,u1_struct_0(D_867))
      | ~ m1_subset_1(F_863,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_867,'#skF_2')
      | v2_struct_0(D_867)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_785])).

tff(c_794,plain,(
    ! [D_867,F_863] :
      ( r1_tmap_1(D_867,'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',D_867),F_863)
      | ~ r1_tmap_1('#skF_2','#skF_3','#skF_4',F_863)
      | ~ m1_subset_1(F_863,u1_struct_0(D_867))
      | ~ m1_subset_1(F_863,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_867,'#skF_2')
      | v2_struct_0(D_867)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_60,c_58,c_50,c_48,c_790])).

tff(c_797,plain,(
    ! [D_874,F_875] :
      ( r1_tmap_1(D_874,'#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4',D_874),F_875)
      | ~ r1_tmap_1('#skF_2','#skF_3','#skF_4',F_875)
      | ~ m1_subset_1(F_875,u1_struct_0(D_874))
      | ~ m1_subset_1(F_875,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_874,'#skF_2')
      | v2_struct_0(D_874) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_794])).

tff(c_694,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_802,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_797,c_694])).

tff(c_809,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_77,c_32,c_693,c_802])).

tff(c_811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:55:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.83/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.67  
% 3.83/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.68  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 3.83/1.68  
% 3.83/1.68  %Foreground sorts:
% 3.83/1.68  
% 3.83/1.68  
% 3.83/1.68  %Background operators:
% 3.83/1.68  
% 3.83/1.68  
% 3.83/1.68  %Foreground operators:
% 3.83/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.83/1.68  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.83/1.68  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.83/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.83/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.68  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.83/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.83/1.68  tff('#skF_7', type, '#skF_7': $i).
% 3.83/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.83/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.83/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.83/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.83/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.83/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.83/1.68  tff('#skF_9', type, '#skF_9': $i).
% 3.83/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.83/1.68  tff('#skF_8', type, '#skF_8': $i).
% 3.83/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.83/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.83/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.68  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.83/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.83/1.68  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.83/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.83/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.83/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.83/1.68  
% 3.83/1.70  tff(f_271, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((A = k1_tsep_1(A, D, E)) => (![F]: (m1_subset_1(F, u1_struct_0(A)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(E)) => (((F = G) & (F = H)) => (r1_tmap_1(A, B, C, F) <=> (r1_tmap_1(D, B, k2_tmap_1(A, B, C, D), G) & r1_tmap_1(E, B, k2_tmap_1(A, B, C, E), H))))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_tmap_1)).
% 3.83/1.70  tff(f_71, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.83/1.70  tff(f_59, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.83/1.70  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.83/1.70  tff(f_128, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.83/1.70  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (![F]: (m1_subset_1(F, u1_struct_0(k1_tsep_1(A, D, E))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(E)) => (((F = G) & (F = H)) => (r1_tmap_1(k1_tsep_1(A, D, E), B, k2_tmap_1(A, B, C, k1_tsep_1(A, D, E)), F) <=> (r1_tmap_1(D, B, k2_tmap_1(A, B, C, D), G) & r1_tmap_1(E, B, k2_tmap_1(A, B, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_tmap_1)).
% 3.83/1.70  tff(f_215, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.83/1.70  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.83/1.70  tff(c_44, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_42, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_28, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_34, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_77, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_34])).
% 3.83/1.70  tff(c_32, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_40, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_38, plain, (m1_pre_topc('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_26, plain, ('#skF_7'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_79, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 3.83/1.70  tff(c_30, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_80, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_30])).
% 3.83/1.70  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_10, plain, (![A_14, B_15]: (m1_connsp_2('#skF_1'(A_14, B_15), A_14, B_15) | ~m1_subset_1(B_15, u1_struct_0(A_14)) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.83/1.70  tff(c_185, plain, (![C_729, A_730, B_731]: (m1_subset_1(C_729, k1_zfmisc_1(u1_struct_0(A_730))) | ~m1_connsp_2(C_729, A_730, B_731) | ~m1_subset_1(B_731, u1_struct_0(A_730)) | ~l1_pre_topc(A_730) | ~v2_pre_topc(A_730) | v2_struct_0(A_730))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.83/1.70  tff(c_189, plain, (![A_732, B_733]: (m1_subset_1('#skF_1'(A_732, B_733), k1_zfmisc_1(u1_struct_0(A_732))) | ~m1_subset_1(B_733, u1_struct_0(A_732)) | ~l1_pre_topc(A_732) | ~v2_pre_topc(A_732) | v2_struct_0(A_732))), inference(resolution, [status(thm)], [c_10, c_185])).
% 3.83/1.70  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.83/1.70  tff(c_193, plain, (![A_732, B_733]: (r1_tarski('#skF_1'(A_732, B_733), u1_struct_0(A_732)) | ~m1_subset_1(B_733, u1_struct_0(A_732)) | ~l1_pre_topc(A_732) | ~v2_pre_topc(A_732) | v2_struct_0(A_732))), inference(resolution, [status(thm)], [c_189, c_2])).
% 3.83/1.70  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.83/1.70  tff(c_18, plain, (![A_272]: (m1_pre_topc(A_272, A_272) | ~l1_pre_topc(A_272))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.83/1.70  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_74, plain, (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_7') | r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_78, plain, (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_74])).
% 3.83/1.70  tff(c_106, plain, (r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_78])).
% 3.83/1.70  tff(c_70, plain, (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_7') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_76, plain, (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_70])).
% 3.83/1.70  tff(c_82, plain, (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_76])).
% 3.83/1.70  tff(c_107, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_82])).
% 3.83/1.70  tff(c_64, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_75, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_64])).
% 3.83/1.70  tff(c_81, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_75])).
% 3.83/1.70  tff(c_196, plain, (~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_107, c_81])).
% 3.83/1.70  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_48, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_36, plain, (k1_tsep_1('#skF_2', '#skF_5', '#skF_6')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.83/1.70  tff(c_392, plain, (![B_793, C_789, E_794, A_790, H_791, D_792]: (r1_tmap_1(k1_tsep_1(A_790, D_792, E_794), B_793, k2_tmap_1(A_790, B_793, C_789, k1_tsep_1(A_790, D_792, E_794)), H_791) | ~r1_tmap_1(E_794, B_793, k2_tmap_1(A_790, B_793, C_789, E_794), H_791) | ~r1_tmap_1(D_792, B_793, k2_tmap_1(A_790, B_793, C_789, D_792), H_791) | ~m1_subset_1(H_791, u1_struct_0(E_794)) | ~m1_subset_1(H_791, u1_struct_0(D_792)) | ~m1_subset_1(H_791, u1_struct_0(k1_tsep_1(A_790, D_792, E_794))) | ~m1_pre_topc(E_794, A_790) | v2_struct_0(E_794) | ~m1_pre_topc(D_792, A_790) | v2_struct_0(D_792) | ~m1_subset_1(C_789, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790), u1_struct_0(B_793)))) | ~v1_funct_2(C_789, u1_struct_0(A_790), u1_struct_0(B_793)) | ~v1_funct_1(C_789) | ~l1_pre_topc(B_793) | ~v2_pre_topc(B_793) | v2_struct_0(B_793) | ~l1_pre_topc(A_790) | ~v2_pre_topc(A_790) | v2_struct_0(A_790))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.83/1.70  tff(c_397, plain, (![D_792, E_794, H_791]: (r1_tmap_1(k1_tsep_1('#skF_2', D_792, E_794), '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', k1_tsep_1('#skF_2', D_792, E_794)), H_791) | ~r1_tmap_1(E_794, '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', E_794), H_791) | ~r1_tmap_1(D_792, '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', D_792), H_791) | ~m1_subset_1(H_791, u1_struct_0(E_794)) | ~m1_subset_1(H_791, u1_struct_0(D_792)) | ~m1_subset_1(H_791, u1_struct_0(k1_tsep_1('#skF_2', D_792, E_794))) | ~m1_pre_topc(E_794, '#skF_2') | v2_struct_0(E_794) | ~m1_pre_topc(D_792, '#skF_2') | v2_struct_0(D_792) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_392])).
% 3.83/1.70  tff(c_401, plain, (![D_792, E_794, H_791]: (r1_tmap_1(k1_tsep_1('#skF_2', D_792, E_794), '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', k1_tsep_1('#skF_2', D_792, E_794)), H_791) | ~r1_tmap_1(E_794, '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', E_794), H_791) | ~r1_tmap_1(D_792, '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', D_792), H_791) | ~m1_subset_1(H_791, u1_struct_0(E_794)) | ~m1_subset_1(H_791, u1_struct_0(D_792)) | ~m1_subset_1(H_791, u1_struct_0(k1_tsep_1('#skF_2', D_792, E_794))) | ~m1_pre_topc(E_794, '#skF_2') | v2_struct_0(E_794) | ~m1_pre_topc(D_792, '#skF_2') | v2_struct_0(D_792) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_50, c_48, c_397])).
% 3.83/1.70  tff(c_424, plain, (![D_800, E_801, H_802]: (r1_tmap_1(k1_tsep_1('#skF_2', D_800, E_801), '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', k1_tsep_1('#skF_2', D_800, E_801)), H_802) | ~r1_tmap_1(E_801, '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', E_801), H_802) | ~r1_tmap_1(D_800, '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', D_800), H_802) | ~m1_subset_1(H_802, u1_struct_0(E_801)) | ~m1_subset_1(H_802, u1_struct_0(D_800)) | ~m1_subset_1(H_802, u1_struct_0(k1_tsep_1('#skF_2', D_800, E_801))) | ~m1_pre_topc(E_801, '#skF_2') | v2_struct_0(E_801) | ~m1_pre_topc(D_800, '#skF_2') | v2_struct_0(D_800))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_401])).
% 3.83/1.70  tff(c_433, plain, (![H_802]: (r1_tmap_1('#skF_2', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', k1_tsep_1('#skF_2', '#skF_5', '#skF_6')), H_802) | ~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), H_802) | ~r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), H_802) | ~m1_subset_1(H_802, u1_struct_0('#skF_6')) | ~m1_subset_1(H_802, u1_struct_0('#skF_5')) | ~m1_subset_1(H_802, u1_struct_0(k1_tsep_1('#skF_2', '#skF_5', '#skF_6'))) | ~m1_pre_topc('#skF_6', '#skF_2') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_424])).
% 3.83/1.70  tff(c_450, plain, (![H_802]: (r1_tmap_1('#skF_2', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_2'), H_802) | ~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), H_802) | ~r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), H_802) | ~m1_subset_1(H_802, u1_struct_0('#skF_6')) | ~m1_subset_1(H_802, u1_struct_0('#skF_5')) | ~m1_subset_1(H_802, u1_struct_0('#skF_2')) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_36, c_433])).
% 3.83/1.70  tff(c_455, plain, (![H_803]: (r1_tmap_1('#skF_2', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_2'), H_803) | ~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), H_803) | ~r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), H_803) | ~m1_subset_1(H_803, u1_struct_0('#skF_6')) | ~m1_subset_1(H_803, u1_struct_0('#skF_5')) | ~m1_subset_1(H_803, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_450])).
% 3.83/1.70  tff(c_465, plain, (r1_tmap_1('#skF_2', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_2'), '#skF_8') | ~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_106, c_455])).
% 3.83/1.70  tff(c_473, plain, (r1_tmap_1('#skF_2', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_2'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_32, c_80, c_107, c_465])).
% 3.83/1.70  tff(c_22, plain, (![C_432, A_336, D_448, B_400, G_462, E_456]: (r1_tmap_1(B_400, A_336, C_432, G_462) | ~r1_tmap_1(D_448, A_336, k2_tmap_1(B_400, A_336, C_432, D_448), G_462) | ~m1_connsp_2(E_456, B_400, G_462) | ~r1_tarski(E_456, u1_struct_0(D_448)) | ~m1_subset_1(G_462, u1_struct_0(D_448)) | ~m1_subset_1(G_462, u1_struct_0(B_400)) | ~m1_subset_1(E_456, k1_zfmisc_1(u1_struct_0(B_400))) | ~m1_pre_topc(D_448, B_400) | v2_struct_0(D_448) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_400), u1_struct_0(A_336)))) | ~v1_funct_2(C_432, u1_struct_0(B_400), u1_struct_0(A_336)) | ~v1_funct_1(C_432) | ~l1_pre_topc(B_400) | ~v2_pre_topc(B_400) | v2_struct_0(B_400) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.83/1.70  tff(c_475, plain, (![E_456]: (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | ~m1_connsp_2(E_456, '#skF_2', '#skF_8') | ~r1_tarski(E_456, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_2')) | ~m1_subset_1(E_456, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_473, c_22])).
% 3.83/1.70  tff(c_478, plain, (![E_456]: (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | ~m1_connsp_2(E_456, '#skF_2', '#skF_8') | ~r1_tarski(E_456, u1_struct_0('#skF_2')) | ~m1_subset_1(E_456, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_60, c_58, c_50, c_48, c_46, c_77, c_475])).
% 3.83/1.70  tff(c_479, plain, (![E_456]: (~m1_connsp_2(E_456, '#skF_2', '#skF_8') | ~r1_tarski(E_456, u1_struct_0('#skF_2')) | ~m1_subset_1(E_456, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_2', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_196, c_478])).
% 3.83/1.70  tff(c_502, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_479])).
% 3.83/1.70  tff(c_505, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_502])).
% 3.83/1.70  tff(c_509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_505])).
% 3.83/1.70  tff(c_549, plain, (![E_811]: (~m1_connsp_2(E_811, '#skF_2', '#skF_8') | ~r1_tarski(E_811, u1_struct_0('#skF_2')) | ~m1_subset_1(E_811, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_479])).
% 3.83/1.70  tff(c_563, plain, (![A_812]: (~m1_connsp_2(A_812, '#skF_2', '#skF_8') | ~r1_tarski(A_812, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_4, c_549])).
% 3.83/1.70  tff(c_567, plain, (![B_733]: (~m1_connsp_2('#skF_1'('#skF_2', B_733), '#skF_2', '#skF_8') | ~m1_subset_1(B_733, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_193, c_563])).
% 3.83/1.70  tff(c_570, plain, (![B_733]: (~m1_connsp_2('#skF_1'('#skF_2', B_733), '#skF_2', '#skF_8') | ~m1_subset_1(B_733, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_567])).
% 3.83/1.70  tff(c_572, plain, (![B_813]: (~m1_connsp_2('#skF_1'('#skF_2', B_813), '#skF_2', '#skF_8') | ~m1_subset_1(B_813, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_570])).
% 3.83/1.70  tff(c_576, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_10, c_572])).
% 3.83/1.70  tff(c_579, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_77, c_576])).
% 3.83/1.70  tff(c_581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_579])).
% 3.83/1.70  tff(c_582, plain, (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_82])).
% 3.83/1.70  tff(c_673, plain, (![F_835, B_838, C_836, A_837, D_839]: (r1_tmap_1(D_839, A_837, k2_tmap_1(B_838, A_837, C_836, D_839), F_835) | ~r1_tmap_1(B_838, A_837, C_836, F_835) | ~m1_subset_1(F_835, u1_struct_0(D_839)) | ~m1_subset_1(F_835, u1_struct_0(B_838)) | ~m1_pre_topc(D_839, B_838) | v2_struct_0(D_839) | ~m1_subset_1(C_836, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_838), u1_struct_0(A_837)))) | ~v1_funct_2(C_836, u1_struct_0(B_838), u1_struct_0(A_837)) | ~v1_funct_1(C_836) | ~l1_pre_topc(B_838) | ~v2_pre_topc(B_838) | v2_struct_0(B_838) | ~l1_pre_topc(A_837) | ~v2_pre_topc(A_837) | v2_struct_0(A_837))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.83/1.70  tff(c_678, plain, (![D_839, F_835]: (r1_tmap_1(D_839, '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', D_839), F_835) | ~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', F_835) | ~m1_subset_1(F_835, u1_struct_0(D_839)) | ~m1_subset_1(F_835, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_839, '#skF_2') | v2_struct_0(D_839) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_673])).
% 3.83/1.70  tff(c_682, plain, (![D_839, F_835]: (r1_tmap_1(D_839, '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', D_839), F_835) | ~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', F_835) | ~m1_subset_1(F_835, u1_struct_0(D_839)) | ~m1_subset_1(F_835, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_839, '#skF_2') | v2_struct_0(D_839) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_60, c_58, c_50, c_48, c_678])).
% 3.83/1.70  tff(c_684, plain, (![D_840, F_841]: (r1_tmap_1(D_840, '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', D_840), F_841) | ~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', F_841) | ~m1_subset_1(F_841, u1_struct_0(D_840)) | ~m1_subset_1(F_841, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_840, '#skF_2') | v2_struct_0(D_840))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_682])).
% 3.83/1.70  tff(c_583, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_82])).
% 3.83/1.70  tff(c_687, plain, (~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_6', '#skF_2') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_684, c_583])).
% 3.83/1.70  tff(c_690, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_77, c_80, c_582, c_687])).
% 3.83/1.70  tff(c_692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_690])).
% 3.83/1.70  tff(c_693, plain, (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 3.83/1.70  tff(c_785, plain, (![B_866, C_864, D_867, A_865, F_863]: (r1_tmap_1(D_867, A_865, k2_tmap_1(B_866, A_865, C_864, D_867), F_863) | ~r1_tmap_1(B_866, A_865, C_864, F_863) | ~m1_subset_1(F_863, u1_struct_0(D_867)) | ~m1_subset_1(F_863, u1_struct_0(B_866)) | ~m1_pre_topc(D_867, B_866) | v2_struct_0(D_867) | ~m1_subset_1(C_864, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_866), u1_struct_0(A_865)))) | ~v1_funct_2(C_864, u1_struct_0(B_866), u1_struct_0(A_865)) | ~v1_funct_1(C_864) | ~l1_pre_topc(B_866) | ~v2_pre_topc(B_866) | v2_struct_0(B_866) | ~l1_pre_topc(A_865) | ~v2_pre_topc(A_865) | v2_struct_0(A_865))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.83/1.70  tff(c_790, plain, (![D_867, F_863]: (r1_tmap_1(D_867, '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', D_867), F_863) | ~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', F_863) | ~m1_subset_1(F_863, u1_struct_0(D_867)) | ~m1_subset_1(F_863, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_867, '#skF_2') | v2_struct_0(D_867) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_785])).
% 3.83/1.70  tff(c_794, plain, (![D_867, F_863]: (r1_tmap_1(D_867, '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', D_867), F_863) | ~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', F_863) | ~m1_subset_1(F_863, u1_struct_0(D_867)) | ~m1_subset_1(F_863, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_867, '#skF_2') | v2_struct_0(D_867) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_60, c_58, c_50, c_48, c_790])).
% 3.83/1.70  tff(c_797, plain, (![D_874, F_875]: (r1_tmap_1(D_874, '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', D_874), F_875) | ~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', F_875) | ~m1_subset_1(F_875, u1_struct_0(D_874)) | ~m1_subset_1(F_875, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_874, '#skF_2') | v2_struct_0(D_874))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_794])).
% 3.83/1.70  tff(c_694, plain, (~r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 3.83/1.70  tff(c_802, plain, (~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_797, c_694])).
% 3.83/1.70  tff(c_809, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_77, c_32, c_693, c_802])).
% 3.83/1.70  tff(c_811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_809])).
% 3.83/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.70  
% 3.83/1.70  Inference rules
% 3.83/1.70  ----------------------
% 3.83/1.70  #Ref     : 0
% 3.83/1.70  #Sup     : 125
% 3.83/1.70  #Fact    : 0
% 3.83/1.70  #Define  : 0
% 3.83/1.70  #Split   : 5
% 3.83/1.70  #Chain   : 0
% 3.83/1.70  #Close   : 0
% 3.83/1.70  
% 3.83/1.70  Ordering : KBO
% 3.83/1.70  
% 3.83/1.70  Simplification rules
% 3.83/1.70  ----------------------
% 3.83/1.70  #Subsume      : 29
% 3.83/1.70  #Demod        : 280
% 3.83/1.70  #Tautology    : 40
% 3.83/1.70  #SimpNegUnit  : 74
% 3.83/1.70  #BackRed      : 0
% 3.83/1.70  
% 3.83/1.70  #Partial instantiations: 0
% 3.83/1.70  #Strategies tried      : 1
% 3.83/1.70  
% 3.83/1.70  Timing (in seconds)
% 3.83/1.70  ----------------------
% 3.83/1.71  Preprocessing        : 0.43
% 3.83/1.71  Parsing              : 0.22
% 3.83/1.71  CNF conversion       : 0.07
% 3.83/1.71  Main loop            : 0.43
% 3.83/1.71  Inferencing          : 0.15
% 3.83/1.71  Reduction            : 0.14
% 3.83/1.71  Demodulation         : 0.10
% 3.83/1.71  BG Simplification    : 0.02
% 3.83/1.71  Subsumption          : 0.09
% 3.83/1.71  Abstraction          : 0.02
% 3.83/1.71  MUC search           : 0.00
% 3.83/1.71  Cooper               : 0.00
% 3.83/1.71  Total                : 0.91
% 3.83/1.71  Index Insertion      : 0.00
% 3.83/1.71  Index Deletion       : 0.00
% 3.83/1.71  Index Matching       : 0.00
% 3.83/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
