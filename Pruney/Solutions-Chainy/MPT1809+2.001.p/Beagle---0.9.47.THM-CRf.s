%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:04 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 490 expanded)
%              Number of leaves         :   41 ( 210 expanded)
%              Depth                    :   12
%              Number of atoms          :  597 (4249 expanded)
%              Number of equality atoms :   50 ( 556 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_227,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_tmap_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_96,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_171,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_tmap_1)).

tff(c_32,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_85,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40])).

tff(c_34,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_88,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_82])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_83,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_80])).

tff(c_89,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_83])).

tff(c_124,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_84,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_76])).

tff(c_102,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_81,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_70])).

tff(c_87,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_81])).

tff(c_272,plain,(
    ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_102,c_87])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_44,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_42,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_237,plain,(
    ! [A_582,B_583,C_584] :
      ( m1_pre_topc(k1_tsep_1(A_582,B_583,C_584),A_582)
      | ~ m1_pre_topc(C_584,A_582)
      | v2_struct_0(C_584)
      | ~ m1_pre_topc(B_583,A_582)
      | v2_struct_0(B_583)
      | ~ l1_pre_topc(A_582)
      | v2_struct_0(A_582) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_246,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_237])).

tff(c_251,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_48,c_44,c_246])).

tff(c_252,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_50,c_46,c_251])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_54,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_141,plain,(
    ! [A_559,B_560,C_561,D_562] :
      ( k2_partfun1(A_559,B_560,C_561,D_562) = k7_relat_1(C_561,D_562)
      | ~ m1_subset_1(C_561,k1_zfmisc_1(k2_zfmisc_1(A_559,B_560)))
      | ~ v1_funct_1(C_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_143,plain,(
    ! [D_562] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_562) = k7_relat_1('#skF_3',D_562)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_141])).

tff(c_146,plain,(
    ! [D_562] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_562) = k7_relat_1('#skF_3',D_562) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_143])).

tff(c_291,plain,(
    ! [A_594,B_595,C_596,D_597] :
      ( k2_partfun1(u1_struct_0(A_594),u1_struct_0(B_595),C_596,u1_struct_0(D_597)) = k2_tmap_1(A_594,B_595,C_596,D_597)
      | ~ m1_pre_topc(D_597,A_594)
      | ~ m1_subset_1(C_596,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_594),u1_struct_0(B_595))))
      | ~ v1_funct_2(C_596,u1_struct_0(A_594),u1_struct_0(B_595))
      | ~ v1_funct_1(C_596)
      | ~ l1_pre_topc(B_595)
      | ~ v2_pre_topc(B_595)
      | v2_struct_0(B_595)
      | ~ l1_pre_topc(A_594)
      | ~ v2_pre_topc(A_594)
      | v2_struct_0(A_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_293,plain,(
    ! [D_597] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_597)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_597)
      | ~ m1_pre_topc(D_597,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_291])).

tff(c_296,plain,(
    ! [D_597] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_597)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_597)
      | ~ m1_pre_topc(D_597,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_56,c_54,c_146,c_293])).

tff(c_298,plain,(
    ! [D_598] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_598)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_598)
      | ~ m1_pre_topc(D_598,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_296])).

tff(c_103,plain,(
    ! [C_542,A_543,B_544] :
      ( v1_relat_1(C_542)
      | ~ m1_subset_1(C_542,k1_zfmisc_1(k2_zfmisc_1(A_543,B_544))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_103])).

tff(c_108,plain,(
    ! [C_545,A_546,B_547] :
      ( v4_relat_1(C_545,A_546)
      | ~ m1_subset_1(C_545,k1_zfmisc_1(k2_zfmisc_1(A_546,B_547))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_112,plain,(
    v4_relat_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_108])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [B_555,A_556] :
      ( k7_relat_1(B_555,A_556) = B_555
      | ~ r1_tarski(k1_relat_1(B_555),A_556)
      | ~ v1_relat_1(B_555) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_130,plain,(
    ! [B_557,A_558] :
      ( k7_relat_1(B_557,A_558) = B_557
      | ~ v4_relat_1(B_557,A_558)
      | ~ v1_relat_1(B_557) ) ),
    inference(resolution,[status(thm)],[c_4,c_125])).

tff(c_133,plain,
    ( k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_130])).

tff(c_136,plain,(
    k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_133])).

tff(c_304,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_136])).

tff(c_313,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_304])).

tff(c_359,plain,(
    ! [D_622,H_623,A_620,E_624,B_621,C_619] :
      ( r1_tmap_1(k1_tsep_1(A_620,D_622,E_624),B_621,k2_tmap_1(A_620,B_621,C_619,k1_tsep_1(A_620,D_622,E_624)),H_623)
      | ~ r1_tmap_1(E_624,B_621,k2_tmap_1(A_620,B_621,C_619,E_624),H_623)
      | ~ r1_tmap_1(D_622,B_621,k2_tmap_1(A_620,B_621,C_619,D_622),H_623)
      | ~ m1_subset_1(H_623,u1_struct_0(E_624))
      | ~ m1_subset_1(H_623,u1_struct_0(D_622))
      | ~ m1_subset_1(H_623,u1_struct_0(k1_tsep_1(A_620,D_622,E_624)))
      | ~ m1_pre_topc(E_624,A_620)
      | v2_struct_0(E_624)
      | ~ m1_pre_topc(D_622,A_620)
      | v2_struct_0(D_622)
      | ~ m1_subset_1(C_619,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_620),u1_struct_0(B_621))))
      | ~ v1_funct_2(C_619,u1_struct_0(A_620),u1_struct_0(B_621))
      | ~ v1_funct_1(C_619)
      | ~ l1_pre_topc(B_621)
      | ~ v2_pre_topc(B_621)
      | v2_struct_0(B_621)
      | ~ l1_pre_topc(A_620)
      | ~ v2_pre_topc(A_620)
      | v2_struct_0(A_620) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_361,plain,(
    ! [D_622,E_624,H_623] :
      ( r1_tmap_1(k1_tsep_1('#skF_1',D_622,E_624),'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',D_622,E_624)),H_623)
      | ~ r1_tmap_1(E_624,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',E_624),H_623)
      | ~ r1_tmap_1(D_622,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_622),H_623)
      | ~ m1_subset_1(H_623,u1_struct_0(E_624))
      | ~ m1_subset_1(H_623,u1_struct_0(D_622))
      | ~ m1_subset_1(H_623,u1_struct_0(k1_tsep_1('#skF_1',D_622,E_624)))
      | ~ m1_pre_topc(E_624,'#skF_1')
      | v2_struct_0(E_624)
      | ~ m1_pre_topc(D_622,'#skF_1')
      | v2_struct_0(D_622)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_359])).

tff(c_364,plain,(
    ! [D_622,E_624,H_623] :
      ( r1_tmap_1(k1_tsep_1('#skF_1',D_622,E_624),'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',D_622,E_624)),H_623)
      | ~ r1_tmap_1(E_624,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',E_624),H_623)
      | ~ r1_tmap_1(D_622,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_622),H_623)
      | ~ m1_subset_1(H_623,u1_struct_0(E_624))
      | ~ m1_subset_1(H_623,u1_struct_0(D_622))
      | ~ m1_subset_1(H_623,u1_struct_0(k1_tsep_1('#skF_1',D_622,E_624)))
      | ~ m1_pre_topc(E_624,'#skF_1')
      | v2_struct_0(E_624)
      | ~ m1_pre_topc(D_622,'#skF_1')
      | v2_struct_0(D_622)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_56,c_54,c_361])).

tff(c_366,plain,(
    ! [D_625,E_626,H_627] :
      ( r1_tmap_1(k1_tsep_1('#skF_1',D_625,E_626),'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',D_625,E_626)),H_627)
      | ~ r1_tmap_1(E_626,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',E_626),H_627)
      | ~ r1_tmap_1(D_625,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_625),H_627)
      | ~ m1_subset_1(H_627,u1_struct_0(E_626))
      | ~ m1_subset_1(H_627,u1_struct_0(D_625))
      | ~ m1_subset_1(H_627,u1_struct_0(k1_tsep_1('#skF_1',D_625,E_626)))
      | ~ m1_pre_topc(E_626,'#skF_1')
      | v2_struct_0(E_626)
      | ~ m1_pre_topc(D_625,'#skF_1')
      | v2_struct_0(D_625) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_364])).

tff(c_373,plain,(
    ! [H_627] :
      ( r1_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),H_627)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_627)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_627)
      | ~ m1_subset_1(H_627,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_627,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_627,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_366])).

tff(c_386,plain,(
    ! [H_627] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_627)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_627)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_627)
      | ~ m1_subset_1(H_627,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_627,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_627,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_313,c_42,c_373])).

tff(c_391,plain,(
    ! [H_628] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_628)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_628)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_628)
      | ~ m1_subset_1(H_628,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_628,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_628,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_386])).

tff(c_397,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_102,c_391])).

tff(c_401,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_88,c_36,c_124,c_397])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_401])).

tff(c_404,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_520,plain,(
    ! [A_656,B_657,C_658] :
      ( m1_pre_topc(k1_tsep_1(A_656,B_657,C_658),A_656)
      | ~ m1_pre_topc(C_658,A_656)
      | v2_struct_0(C_658)
      | ~ m1_pre_topc(B_657,A_656)
      | v2_struct_0(B_657)
      | ~ l1_pre_topc(A_656)
      | v2_struct_0(A_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_529,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_520])).

tff(c_534,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_48,c_44,c_529])).

tff(c_535,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_50,c_46,c_534])).

tff(c_424,plain,(
    ! [A_633,B_634,C_635,D_636] :
      ( k2_partfun1(A_633,B_634,C_635,D_636) = k7_relat_1(C_635,D_636)
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(A_633,B_634)))
      | ~ v1_funct_1(C_635) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_426,plain,(
    ! [D_636] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_636) = k7_relat_1('#skF_3',D_636)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_424])).

tff(c_429,plain,(
    ! [D_636] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_636) = k7_relat_1('#skF_3',D_636) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_426])).

tff(c_572,plain,(
    ! [A_668,B_669,C_670,D_671] :
      ( k2_partfun1(u1_struct_0(A_668),u1_struct_0(B_669),C_670,u1_struct_0(D_671)) = k2_tmap_1(A_668,B_669,C_670,D_671)
      | ~ m1_pre_topc(D_671,A_668)
      | ~ m1_subset_1(C_670,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_668),u1_struct_0(B_669))))
      | ~ v1_funct_2(C_670,u1_struct_0(A_668),u1_struct_0(B_669))
      | ~ v1_funct_1(C_670)
      | ~ l1_pre_topc(B_669)
      | ~ v2_pre_topc(B_669)
      | v2_struct_0(B_669)
      | ~ l1_pre_topc(A_668)
      | ~ v2_pre_topc(A_668)
      | v2_struct_0(A_668) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_574,plain,(
    ! [D_671] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_671)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_671)
      | ~ m1_pre_topc(D_671,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_572])).

tff(c_577,plain,(
    ! [D_671] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_671)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_671)
      | ~ m1_pre_topc(D_671,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_56,c_54,c_429,c_574])).

tff(c_579,plain,(
    ! [D_672] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_672)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_672)
      | ~ m1_pre_topc(D_672,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_577])).

tff(c_408,plain,(
    ! [B_629,A_630] :
      ( k7_relat_1(B_629,A_630) = B_629
      | ~ r1_tarski(k1_relat_1(B_629),A_630)
      | ~ v1_relat_1(B_629) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_413,plain,(
    ! [B_631,A_632] :
      ( k7_relat_1(B_631,A_632) = B_631
      | ~ v4_relat_1(B_631,A_632)
      | ~ v1_relat_1(B_631) ) ),
    inference(resolution,[status(thm)],[c_4,c_408])).

tff(c_416,plain,
    ( k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_413])).

tff(c_419,plain,(
    k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_416])).

tff(c_585,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_419])).

tff(c_594,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_585])).

tff(c_614,plain,(
    ! [B_681,A_680,E_684,H_683,D_682,C_679] :
      ( r1_tmap_1(D_682,B_681,k2_tmap_1(A_680,B_681,C_679,D_682),H_683)
      | ~ r1_tmap_1(k1_tsep_1(A_680,D_682,E_684),B_681,k2_tmap_1(A_680,B_681,C_679,k1_tsep_1(A_680,D_682,E_684)),H_683)
      | ~ m1_subset_1(H_683,u1_struct_0(E_684))
      | ~ m1_subset_1(H_683,u1_struct_0(D_682))
      | ~ m1_subset_1(H_683,u1_struct_0(k1_tsep_1(A_680,D_682,E_684)))
      | ~ m1_pre_topc(E_684,A_680)
      | v2_struct_0(E_684)
      | ~ m1_pre_topc(D_682,A_680)
      | v2_struct_0(D_682)
      | ~ m1_subset_1(C_679,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_680),u1_struct_0(B_681))))
      | ~ v1_funct_2(C_679,u1_struct_0(A_680),u1_struct_0(B_681))
      | ~ v1_funct_1(C_679)
      | ~ l1_pre_topc(B_681)
      | ~ v2_pre_topc(B_681)
      | v2_struct_0(B_681)
      | ~ l1_pre_topc(A_680)
      | ~ v2_pre_topc(A_680)
      | v2_struct_0(A_680) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_616,plain,(
    ! [B_681,C_679,H_683] :
      ( r1_tmap_1('#skF_4',B_681,k2_tmap_1('#skF_1',B_681,C_679,'#skF_4'),H_683)
      | ~ r1_tmap_1('#skF_1',B_681,k2_tmap_1('#skF_1',B_681,C_679,k1_tsep_1('#skF_1','#skF_4','#skF_5')),H_683)
      | ~ m1_subset_1(H_683,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_683,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_683,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_679,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_681))))
      | ~ v1_funct_2(C_679,u1_struct_0('#skF_1'),u1_struct_0(B_681))
      | ~ v1_funct_1(C_679)
      | ~ l1_pre_topc(B_681)
      | ~ v2_pre_topc(B_681)
      | v2_struct_0(B_681)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_614])).

tff(c_620,plain,(
    ! [B_681,C_679,H_683] :
      ( r1_tmap_1('#skF_4',B_681,k2_tmap_1('#skF_1',B_681,C_679,'#skF_4'),H_683)
      | ~ r1_tmap_1('#skF_1',B_681,k2_tmap_1('#skF_1',B_681,C_679,'#skF_1'),H_683)
      | ~ m1_subset_1(H_683,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_683,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_683,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_679,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_681))))
      | ~ v1_funct_2(C_679,u1_struct_0('#skF_1'),u1_struct_0(B_681))
      | ~ v1_funct_1(C_679)
      | ~ l1_pre_topc(B_681)
      | ~ v2_pre_topc(B_681)
      | v2_struct_0(B_681)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_44,c_42,c_42,c_616])).

tff(c_633,plain,(
    ! [B_689,C_690,H_691] :
      ( r1_tmap_1('#skF_4',B_689,k2_tmap_1('#skF_1',B_689,C_690,'#skF_4'),H_691)
      | ~ r1_tmap_1('#skF_1',B_689,k2_tmap_1('#skF_1',B_689,C_690,'#skF_1'),H_691)
      | ~ m1_subset_1(H_691,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_691,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_691,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_690,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_689))))
      | ~ v1_funct_2(C_690,u1_struct_0('#skF_1'),u1_struct_0(B_689))
      | ~ v1_funct_1(C_690)
      | ~ l1_pre_topc(B_689)
      | ~ v2_pre_topc(B_689)
      | v2_struct_0(B_689) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_50,c_46,c_620])).

tff(c_635,plain,(
    ! [H_691] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_691)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_691)
      | ~ m1_subset_1(H_691,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_691,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_691,u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_633])).

tff(c_637,plain,(
    ! [H_691] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_691)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_691)
      | ~ m1_subset_1(H_691,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_691,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_691,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_635])).

tff(c_639,plain,(
    ! [H_692] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_692)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_692)
      | ~ m1_subset_1(H_692,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_692,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_692,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_637])).

tff(c_405,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_642,plain,
    ( ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_639,c_405])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_88,c_36,c_404,c_642])).

tff(c_647,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_783,plain,(
    ! [A_733,B_734,C_735] :
      ( m1_pre_topc(k1_tsep_1(A_733,B_734,C_735),A_733)
      | ~ m1_pre_topc(C_735,A_733)
      | v2_struct_0(C_735)
      | ~ m1_pre_topc(B_734,A_733)
      | v2_struct_0(B_734)
      | ~ l1_pre_topc(A_733)
      | v2_struct_0(A_733) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_792,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_783])).

tff(c_797,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_48,c_44,c_792])).

tff(c_798,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_50,c_46,c_797])).

tff(c_687,plain,(
    ! [A_710,B_711,C_712,D_713] :
      ( k2_partfun1(A_710,B_711,C_712,D_713) = k7_relat_1(C_712,D_713)
      | ~ m1_subset_1(C_712,k1_zfmisc_1(k2_zfmisc_1(A_710,B_711)))
      | ~ v1_funct_1(C_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_689,plain,(
    ! [D_713] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_713) = k7_relat_1('#skF_3',D_713)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_687])).

tff(c_692,plain,(
    ! [D_713] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_713) = k7_relat_1('#skF_3',D_713) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_689])).

tff(c_837,plain,(
    ! [A_745,B_746,C_747,D_748] :
      ( k2_partfun1(u1_struct_0(A_745),u1_struct_0(B_746),C_747,u1_struct_0(D_748)) = k2_tmap_1(A_745,B_746,C_747,D_748)
      | ~ m1_pre_topc(D_748,A_745)
      | ~ m1_subset_1(C_747,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_745),u1_struct_0(B_746))))
      | ~ v1_funct_2(C_747,u1_struct_0(A_745),u1_struct_0(B_746))
      | ~ v1_funct_1(C_747)
      | ~ l1_pre_topc(B_746)
      | ~ v2_pre_topc(B_746)
      | v2_struct_0(B_746)
      | ~ l1_pre_topc(A_745)
      | ~ v2_pre_topc(A_745)
      | v2_struct_0(A_745) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_839,plain,(
    ! [D_748] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_748)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_748)
      | ~ m1_pre_topc(D_748,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_837])).

tff(c_842,plain,(
    ! [D_748] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_748)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_748)
      | ~ m1_pre_topc(D_748,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_56,c_54,c_692,c_839])).

tff(c_844,plain,(
    ! [D_749] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_749)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_749)
      | ~ m1_pre_topc(D_749,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_842])).

tff(c_649,plain,(
    ! [C_693,A_694,B_695] :
      ( v1_relat_1(C_693)
      | ~ m1_subset_1(C_693,k1_zfmisc_1(k2_zfmisc_1(A_694,B_695))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_653,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_649])).

tff(c_654,plain,(
    ! [C_696,A_697,B_698] :
      ( v4_relat_1(C_696,A_697)
      | ~ m1_subset_1(C_696,k1_zfmisc_1(k2_zfmisc_1(A_697,B_698))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_658,plain,(
    v4_relat_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_654])).

tff(c_670,plain,(
    ! [B_706,A_707] :
      ( k7_relat_1(B_706,A_707) = B_706
      | ~ r1_tarski(k1_relat_1(B_706),A_707)
      | ~ v1_relat_1(B_706) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_675,plain,(
    ! [B_708,A_709] :
      ( k7_relat_1(B_708,A_709) = B_708
      | ~ v4_relat_1(B_708,A_709)
      | ~ v1_relat_1(B_708) ) ),
    inference(resolution,[status(thm)],[c_4,c_670])).

tff(c_678,plain,
    ( k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_658,c_675])).

tff(c_681,plain,(
    k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_678])).

tff(c_850,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_681])).

tff(c_859,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_798,c_850])).

tff(c_867,plain,(
    ! [H_754,E_755,D_753,A_751,B_752,C_750] :
      ( r1_tmap_1(E_755,B_752,k2_tmap_1(A_751,B_752,C_750,E_755),H_754)
      | ~ r1_tmap_1(k1_tsep_1(A_751,D_753,E_755),B_752,k2_tmap_1(A_751,B_752,C_750,k1_tsep_1(A_751,D_753,E_755)),H_754)
      | ~ m1_subset_1(H_754,u1_struct_0(E_755))
      | ~ m1_subset_1(H_754,u1_struct_0(D_753))
      | ~ m1_subset_1(H_754,u1_struct_0(k1_tsep_1(A_751,D_753,E_755)))
      | ~ m1_pre_topc(E_755,A_751)
      | v2_struct_0(E_755)
      | ~ m1_pre_topc(D_753,A_751)
      | v2_struct_0(D_753)
      | ~ m1_subset_1(C_750,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_751),u1_struct_0(B_752))))
      | ~ v1_funct_2(C_750,u1_struct_0(A_751),u1_struct_0(B_752))
      | ~ v1_funct_1(C_750)
      | ~ l1_pre_topc(B_752)
      | ~ v2_pre_topc(B_752)
      | v2_struct_0(B_752)
      | ~ l1_pre_topc(A_751)
      | ~ v2_pre_topc(A_751)
      | v2_struct_0(A_751) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_871,plain,(
    ! [B_752,C_750,H_754] :
      ( r1_tmap_1('#skF_5',B_752,k2_tmap_1('#skF_1',B_752,C_750,'#skF_5'),H_754)
      | ~ r1_tmap_1(k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_752,k2_tmap_1('#skF_1',B_752,C_750,'#skF_1'),H_754)
      | ~ m1_subset_1(H_754,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_754,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_754,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_750,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_752))))
      | ~ v1_funct_2(C_750,u1_struct_0('#skF_1'),u1_struct_0(B_752))
      | ~ v1_funct_1(C_750)
      | ~ l1_pre_topc(B_752)
      | ~ v2_pre_topc(B_752)
      | v2_struct_0(B_752)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_867])).

tff(c_876,plain,(
    ! [B_752,C_750,H_754] :
      ( r1_tmap_1('#skF_5',B_752,k2_tmap_1('#skF_1',B_752,C_750,'#skF_5'),H_754)
      | ~ r1_tmap_1('#skF_1',B_752,k2_tmap_1('#skF_1',B_752,C_750,'#skF_1'),H_754)
      | ~ m1_subset_1(H_754,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_754,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_754,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_750,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_752))))
      | ~ v1_funct_2(C_750,u1_struct_0('#skF_1'),u1_struct_0(B_752))
      | ~ v1_funct_1(C_750)
      | ~ l1_pre_topc(B_752)
      | ~ v2_pre_topc(B_752)
      | v2_struct_0(B_752)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_44,c_42,c_42,c_871])).

tff(c_879,plain,(
    ! [B_756,C_757,H_758] :
      ( r1_tmap_1('#skF_5',B_756,k2_tmap_1('#skF_1',B_756,C_757,'#skF_5'),H_758)
      | ~ r1_tmap_1('#skF_1',B_756,k2_tmap_1('#skF_1',B_756,C_757,'#skF_1'),H_758)
      | ~ m1_subset_1(H_758,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_758,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_758,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_757,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_756))))
      | ~ v1_funct_2(C_757,u1_struct_0('#skF_1'),u1_struct_0(B_756))
      | ~ v1_funct_1(C_757)
      | ~ l1_pre_topc(B_756)
      | ~ v2_pre_topc(B_756)
      | v2_struct_0(B_756) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_50,c_46,c_876])).

tff(c_881,plain,(
    ! [H_758] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_758)
      | ~ r1_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),H_758)
      | ~ m1_subset_1(H_758,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_758,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_758,u1_struct_0('#skF_1'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_879])).

tff(c_884,plain,(
    ! [H_758] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_758)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_758)
      | ~ m1_subset_1(H_758,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_758,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_758,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_859,c_881])).

tff(c_886,plain,(
    ! [H_759] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_759)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_759)
      | ~ m1_subset_1(H_759,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_759,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_759,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_884])).

tff(c_648,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_889,plain,
    ( ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_886,c_648])).

tff(c_893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_88,c_36,c_647,c_889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:29:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.65  
% 3.72/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.65  %$ r1_tmap_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.72/1.65  
% 3.72/1.65  %Foreground sorts:
% 3.72/1.65  
% 3.72/1.65  
% 3.72/1.65  %Background operators:
% 3.72/1.65  
% 3.72/1.65  
% 3.72/1.65  %Foreground operators:
% 3.72/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.72/1.65  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.72/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.72/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.65  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.72/1.65  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.72/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.72/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.72/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.72/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.72/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.72/1.65  tff('#skF_2', type, '#skF_2': $i).
% 4.08/1.65  tff('#skF_3', type, '#skF_3': $i).
% 4.08/1.65  tff('#skF_1', type, '#skF_1': $i).
% 4.08/1.65  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.08/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.08/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.08/1.65  tff('#skF_8', type, '#skF_8': $i).
% 4.08/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.08/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.08/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.08/1.65  tff('#skF_4', type, '#skF_4': $i).
% 4.08/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.08/1.65  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.08/1.65  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.08/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.08/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.08/1.65  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.08/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.08/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.08/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.08/1.65  
% 4.08/1.68  tff(f_227, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((A = k1_tsep_1(A, D, E)) => (![F]: (m1_subset_1(F, u1_struct_0(A)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(E)) => (((F = G) & (F = H)) => (r1_tmap_1(A, B, C, F) <=> (r1_tmap_1(D, B, k2_tmap_1(A, B, C, D), G) & r1_tmap_1(E, B, k2_tmap_1(A, B, C, E), H))))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_tmap_1)).
% 4.08/1.68  tff(f_118, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 4.08/1.68  tff(f_53, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.08/1.68  tff(f_96, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.08/1.68  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.08/1.68  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.08/1.68  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.08/1.68  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 4.08/1.68  tff(f_171, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (![F]: (m1_subset_1(F, u1_struct_0(k1_tsep_1(A, D, E))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(E)) => (((F = G) & (F = H)) => (r1_tmap_1(k1_tsep_1(A, D, E), B, k2_tmap_1(A, B, C, k1_tsep_1(A, D, E)), F) <=> (r1_tmap_1(D, B, k2_tmap_1(A, B, C, D), G) & r1_tmap_1(E, B, k2_tmap_1(A, B, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_tmap_1)).
% 4.08/1.68  tff(c_32, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_85, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_40])).
% 4.08/1.68  tff(c_34, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_38, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_82, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 4.08/1.68  tff(c_88, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_82])).
% 4.08/1.68  tff(c_36, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_80, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_83, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_80])).
% 4.08/1.68  tff(c_89, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_83])).
% 4.08/1.68  tff(c_124, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(splitLeft, [status(thm)], [c_89])).
% 4.08/1.68  tff(c_76, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_84, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_76])).
% 4.08/1.68  tff(c_102, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_84])).
% 4.08/1.68  tff(c_70, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_81, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_70])).
% 4.08/1.68  tff(c_87, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_81])).
% 4.08/1.68  tff(c_272, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_102, c_87])).
% 4.08/1.68  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_46, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_44, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_42, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_237, plain, (![A_582, B_583, C_584]: (m1_pre_topc(k1_tsep_1(A_582, B_583, C_584), A_582) | ~m1_pre_topc(C_584, A_582) | v2_struct_0(C_584) | ~m1_pre_topc(B_583, A_582) | v2_struct_0(B_583) | ~l1_pre_topc(A_582) | v2_struct_0(A_582))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.08/1.68  tff(c_246, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_42, c_237])).
% 4.08/1.68  tff(c_251, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_48, c_44, c_246])).
% 4.08/1.68  tff(c_252, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_50, c_46, c_251])).
% 4.08/1.68  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_54, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.08/1.68  tff(c_141, plain, (![A_559, B_560, C_561, D_562]: (k2_partfun1(A_559, B_560, C_561, D_562)=k7_relat_1(C_561, D_562) | ~m1_subset_1(C_561, k1_zfmisc_1(k2_zfmisc_1(A_559, B_560))) | ~v1_funct_1(C_561))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.08/1.68  tff(c_143, plain, (![D_562]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_562)=k7_relat_1('#skF_3', D_562) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_141])).
% 4.08/1.68  tff(c_146, plain, (![D_562]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_562)=k7_relat_1('#skF_3', D_562))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_143])).
% 4.08/1.68  tff(c_291, plain, (![A_594, B_595, C_596, D_597]: (k2_partfun1(u1_struct_0(A_594), u1_struct_0(B_595), C_596, u1_struct_0(D_597))=k2_tmap_1(A_594, B_595, C_596, D_597) | ~m1_pre_topc(D_597, A_594) | ~m1_subset_1(C_596, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_594), u1_struct_0(B_595)))) | ~v1_funct_2(C_596, u1_struct_0(A_594), u1_struct_0(B_595)) | ~v1_funct_1(C_596) | ~l1_pre_topc(B_595) | ~v2_pre_topc(B_595) | v2_struct_0(B_595) | ~l1_pre_topc(A_594) | ~v2_pre_topc(A_594) | v2_struct_0(A_594))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.08/1.68  tff(c_293, plain, (![D_597]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_597))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_597) | ~m1_pre_topc(D_597, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_291])).
% 4.08/1.68  tff(c_296, plain, (![D_597]: (k7_relat_1('#skF_3', u1_struct_0(D_597))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_597) | ~m1_pre_topc(D_597, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_56, c_54, c_146, c_293])).
% 4.08/1.68  tff(c_298, plain, (![D_598]: (k7_relat_1('#skF_3', u1_struct_0(D_598))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_598) | ~m1_pre_topc(D_598, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_296])).
% 4.08/1.68  tff(c_103, plain, (![C_542, A_543, B_544]: (v1_relat_1(C_542) | ~m1_subset_1(C_542, k1_zfmisc_1(k2_zfmisc_1(A_543, B_544))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.08/1.68  tff(c_107, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_103])).
% 4.08/1.68  tff(c_108, plain, (![C_545, A_546, B_547]: (v4_relat_1(C_545, A_546) | ~m1_subset_1(C_545, k1_zfmisc_1(k2_zfmisc_1(A_546, B_547))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.08/1.68  tff(c_112, plain, (v4_relat_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_108])).
% 4.08/1.68  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.08/1.68  tff(c_125, plain, (![B_555, A_556]: (k7_relat_1(B_555, A_556)=B_555 | ~r1_tarski(k1_relat_1(B_555), A_556) | ~v1_relat_1(B_555))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.08/1.68  tff(c_130, plain, (![B_557, A_558]: (k7_relat_1(B_557, A_558)=B_557 | ~v4_relat_1(B_557, A_558) | ~v1_relat_1(B_557))), inference(resolution, [status(thm)], [c_4, c_125])).
% 4.08/1.68  tff(c_133, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_130])).
% 4.08/1.68  tff(c_136, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_133])).
% 4.08/1.68  tff(c_304, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_298, c_136])).
% 4.08/1.68  tff(c_313, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_252, c_304])).
% 4.08/1.68  tff(c_359, plain, (![D_622, H_623, A_620, E_624, B_621, C_619]: (r1_tmap_1(k1_tsep_1(A_620, D_622, E_624), B_621, k2_tmap_1(A_620, B_621, C_619, k1_tsep_1(A_620, D_622, E_624)), H_623) | ~r1_tmap_1(E_624, B_621, k2_tmap_1(A_620, B_621, C_619, E_624), H_623) | ~r1_tmap_1(D_622, B_621, k2_tmap_1(A_620, B_621, C_619, D_622), H_623) | ~m1_subset_1(H_623, u1_struct_0(E_624)) | ~m1_subset_1(H_623, u1_struct_0(D_622)) | ~m1_subset_1(H_623, u1_struct_0(k1_tsep_1(A_620, D_622, E_624))) | ~m1_pre_topc(E_624, A_620) | v2_struct_0(E_624) | ~m1_pre_topc(D_622, A_620) | v2_struct_0(D_622) | ~m1_subset_1(C_619, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_620), u1_struct_0(B_621)))) | ~v1_funct_2(C_619, u1_struct_0(A_620), u1_struct_0(B_621)) | ~v1_funct_1(C_619) | ~l1_pre_topc(B_621) | ~v2_pre_topc(B_621) | v2_struct_0(B_621) | ~l1_pre_topc(A_620) | ~v2_pre_topc(A_620) | v2_struct_0(A_620))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.08/1.68  tff(c_361, plain, (![D_622, E_624, H_623]: (r1_tmap_1(k1_tsep_1('#skF_1', D_622, E_624), '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', D_622, E_624)), H_623) | ~r1_tmap_1(E_624, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', E_624), H_623) | ~r1_tmap_1(D_622, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_622), H_623) | ~m1_subset_1(H_623, u1_struct_0(E_624)) | ~m1_subset_1(H_623, u1_struct_0(D_622)) | ~m1_subset_1(H_623, u1_struct_0(k1_tsep_1('#skF_1', D_622, E_624))) | ~m1_pre_topc(E_624, '#skF_1') | v2_struct_0(E_624) | ~m1_pre_topc(D_622, '#skF_1') | v2_struct_0(D_622) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_359])).
% 4.08/1.68  tff(c_364, plain, (![D_622, E_624, H_623]: (r1_tmap_1(k1_tsep_1('#skF_1', D_622, E_624), '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', D_622, E_624)), H_623) | ~r1_tmap_1(E_624, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', E_624), H_623) | ~r1_tmap_1(D_622, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_622), H_623) | ~m1_subset_1(H_623, u1_struct_0(E_624)) | ~m1_subset_1(H_623, u1_struct_0(D_622)) | ~m1_subset_1(H_623, u1_struct_0(k1_tsep_1('#skF_1', D_622, E_624))) | ~m1_pre_topc(E_624, '#skF_1') | v2_struct_0(E_624) | ~m1_pre_topc(D_622, '#skF_1') | v2_struct_0(D_622) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_56, c_54, c_361])).
% 4.08/1.68  tff(c_366, plain, (![D_625, E_626, H_627]: (r1_tmap_1(k1_tsep_1('#skF_1', D_625, E_626), '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', D_625, E_626)), H_627) | ~r1_tmap_1(E_626, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', E_626), H_627) | ~r1_tmap_1(D_625, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_625), H_627) | ~m1_subset_1(H_627, u1_struct_0(E_626)) | ~m1_subset_1(H_627, u1_struct_0(D_625)) | ~m1_subset_1(H_627, u1_struct_0(k1_tsep_1('#skF_1', D_625, E_626))) | ~m1_pre_topc(E_626, '#skF_1') | v2_struct_0(E_626) | ~m1_pre_topc(D_625, '#skF_1') | v2_struct_0(D_625))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_364])).
% 4.08/1.68  tff(c_373, plain, (![H_627]: (r1_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), H_627) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_627) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_627) | ~m1_subset_1(H_627, u1_struct_0('#skF_5')) | ~m1_subset_1(H_627, u1_struct_0('#skF_4')) | ~m1_subset_1(H_627, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_366])).
% 4.08/1.68  tff(c_386, plain, (![H_627]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_627) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_627) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_627) | ~m1_subset_1(H_627, u1_struct_0('#skF_5')) | ~m1_subset_1(H_627, u1_struct_0('#skF_4')) | ~m1_subset_1(H_627, u1_struct_0('#skF_1')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_42, c_313, c_42, c_373])).
% 4.08/1.68  tff(c_391, plain, (![H_628]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_628) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_628) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_628) | ~m1_subset_1(H_628, u1_struct_0('#skF_5')) | ~m1_subset_1(H_628, u1_struct_0('#skF_4')) | ~m1_subset_1(H_628, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_386])).
% 4.08/1.68  tff(c_397, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_102, c_391])).
% 4.08/1.68  tff(c_401, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_88, c_36, c_124, c_397])).
% 4.08/1.68  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_401])).
% 4.08/1.68  tff(c_404, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_89])).
% 4.08/1.68  tff(c_520, plain, (![A_656, B_657, C_658]: (m1_pre_topc(k1_tsep_1(A_656, B_657, C_658), A_656) | ~m1_pre_topc(C_658, A_656) | v2_struct_0(C_658) | ~m1_pre_topc(B_657, A_656) | v2_struct_0(B_657) | ~l1_pre_topc(A_656) | v2_struct_0(A_656))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.08/1.68  tff(c_529, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_42, c_520])).
% 4.08/1.68  tff(c_534, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_48, c_44, c_529])).
% 4.08/1.68  tff(c_535, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_50, c_46, c_534])).
% 4.08/1.68  tff(c_424, plain, (![A_633, B_634, C_635, D_636]: (k2_partfun1(A_633, B_634, C_635, D_636)=k7_relat_1(C_635, D_636) | ~m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1(A_633, B_634))) | ~v1_funct_1(C_635))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.08/1.68  tff(c_426, plain, (![D_636]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_636)=k7_relat_1('#skF_3', D_636) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_424])).
% 4.08/1.68  tff(c_429, plain, (![D_636]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_636)=k7_relat_1('#skF_3', D_636))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_426])).
% 4.08/1.68  tff(c_572, plain, (![A_668, B_669, C_670, D_671]: (k2_partfun1(u1_struct_0(A_668), u1_struct_0(B_669), C_670, u1_struct_0(D_671))=k2_tmap_1(A_668, B_669, C_670, D_671) | ~m1_pre_topc(D_671, A_668) | ~m1_subset_1(C_670, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_668), u1_struct_0(B_669)))) | ~v1_funct_2(C_670, u1_struct_0(A_668), u1_struct_0(B_669)) | ~v1_funct_1(C_670) | ~l1_pre_topc(B_669) | ~v2_pre_topc(B_669) | v2_struct_0(B_669) | ~l1_pre_topc(A_668) | ~v2_pre_topc(A_668) | v2_struct_0(A_668))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.08/1.68  tff(c_574, plain, (![D_671]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_671))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_671) | ~m1_pre_topc(D_671, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_572])).
% 4.08/1.68  tff(c_577, plain, (![D_671]: (k7_relat_1('#skF_3', u1_struct_0(D_671))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_671) | ~m1_pre_topc(D_671, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_56, c_54, c_429, c_574])).
% 4.08/1.68  tff(c_579, plain, (![D_672]: (k7_relat_1('#skF_3', u1_struct_0(D_672))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_672) | ~m1_pre_topc(D_672, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_577])).
% 4.08/1.68  tff(c_408, plain, (![B_629, A_630]: (k7_relat_1(B_629, A_630)=B_629 | ~r1_tarski(k1_relat_1(B_629), A_630) | ~v1_relat_1(B_629))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.08/1.68  tff(c_413, plain, (![B_631, A_632]: (k7_relat_1(B_631, A_632)=B_631 | ~v4_relat_1(B_631, A_632) | ~v1_relat_1(B_631))), inference(resolution, [status(thm)], [c_4, c_408])).
% 4.08/1.68  tff(c_416, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_413])).
% 4.08/1.68  tff(c_419, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_416])).
% 4.08/1.68  tff(c_585, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_579, c_419])).
% 4.08/1.68  tff(c_594, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_535, c_585])).
% 4.08/1.68  tff(c_614, plain, (![B_681, A_680, E_684, H_683, D_682, C_679]: (r1_tmap_1(D_682, B_681, k2_tmap_1(A_680, B_681, C_679, D_682), H_683) | ~r1_tmap_1(k1_tsep_1(A_680, D_682, E_684), B_681, k2_tmap_1(A_680, B_681, C_679, k1_tsep_1(A_680, D_682, E_684)), H_683) | ~m1_subset_1(H_683, u1_struct_0(E_684)) | ~m1_subset_1(H_683, u1_struct_0(D_682)) | ~m1_subset_1(H_683, u1_struct_0(k1_tsep_1(A_680, D_682, E_684))) | ~m1_pre_topc(E_684, A_680) | v2_struct_0(E_684) | ~m1_pre_topc(D_682, A_680) | v2_struct_0(D_682) | ~m1_subset_1(C_679, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_680), u1_struct_0(B_681)))) | ~v1_funct_2(C_679, u1_struct_0(A_680), u1_struct_0(B_681)) | ~v1_funct_1(C_679) | ~l1_pre_topc(B_681) | ~v2_pre_topc(B_681) | v2_struct_0(B_681) | ~l1_pre_topc(A_680) | ~v2_pre_topc(A_680) | v2_struct_0(A_680))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.08/1.68  tff(c_616, plain, (![B_681, C_679, H_683]: (r1_tmap_1('#skF_4', B_681, k2_tmap_1('#skF_1', B_681, C_679, '#skF_4'), H_683) | ~r1_tmap_1('#skF_1', B_681, k2_tmap_1('#skF_1', B_681, C_679, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), H_683) | ~m1_subset_1(H_683, u1_struct_0('#skF_5')) | ~m1_subset_1(H_683, u1_struct_0('#skF_4')) | ~m1_subset_1(H_683, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_subset_1(C_679, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_681)))) | ~v1_funct_2(C_679, u1_struct_0('#skF_1'), u1_struct_0(B_681)) | ~v1_funct_1(C_679) | ~l1_pre_topc(B_681) | ~v2_pre_topc(B_681) | v2_struct_0(B_681) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_614])).
% 4.08/1.68  tff(c_620, plain, (![B_681, C_679, H_683]: (r1_tmap_1('#skF_4', B_681, k2_tmap_1('#skF_1', B_681, C_679, '#skF_4'), H_683) | ~r1_tmap_1('#skF_1', B_681, k2_tmap_1('#skF_1', B_681, C_679, '#skF_1'), H_683) | ~m1_subset_1(H_683, u1_struct_0('#skF_5')) | ~m1_subset_1(H_683, u1_struct_0('#skF_4')) | ~m1_subset_1(H_683, u1_struct_0('#skF_1')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~m1_subset_1(C_679, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_681)))) | ~v1_funct_2(C_679, u1_struct_0('#skF_1'), u1_struct_0(B_681)) | ~v1_funct_1(C_679) | ~l1_pre_topc(B_681) | ~v2_pre_topc(B_681) | v2_struct_0(B_681) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_44, c_42, c_42, c_616])).
% 4.08/1.68  tff(c_633, plain, (![B_689, C_690, H_691]: (r1_tmap_1('#skF_4', B_689, k2_tmap_1('#skF_1', B_689, C_690, '#skF_4'), H_691) | ~r1_tmap_1('#skF_1', B_689, k2_tmap_1('#skF_1', B_689, C_690, '#skF_1'), H_691) | ~m1_subset_1(H_691, u1_struct_0('#skF_5')) | ~m1_subset_1(H_691, u1_struct_0('#skF_4')) | ~m1_subset_1(H_691, u1_struct_0('#skF_1')) | ~m1_subset_1(C_690, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_689)))) | ~v1_funct_2(C_690, u1_struct_0('#skF_1'), u1_struct_0(B_689)) | ~v1_funct_1(C_690) | ~l1_pre_topc(B_689) | ~v2_pre_topc(B_689) | v2_struct_0(B_689))), inference(negUnitSimplification, [status(thm)], [c_68, c_50, c_46, c_620])).
% 4.08/1.68  tff(c_635, plain, (![H_691]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_691) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_691) | ~m1_subset_1(H_691, u1_struct_0('#skF_5')) | ~m1_subset_1(H_691, u1_struct_0('#skF_4')) | ~m1_subset_1(H_691, u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_594, c_633])).
% 4.08/1.68  tff(c_637, plain, (![H_691]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_691) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_691) | ~m1_subset_1(H_691, u1_struct_0('#skF_5')) | ~m1_subset_1(H_691, u1_struct_0('#skF_4')) | ~m1_subset_1(H_691, u1_struct_0('#skF_1')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_635])).
% 4.08/1.68  tff(c_639, plain, (![H_692]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_692) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_692) | ~m1_subset_1(H_692, u1_struct_0('#skF_5')) | ~m1_subset_1(H_692, u1_struct_0('#skF_4')) | ~m1_subset_1(H_692, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_62, c_637])).
% 4.08/1.68  tff(c_405, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(splitRight, [status(thm)], [c_89])).
% 4.08/1.68  tff(c_642, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_639, c_405])).
% 4.08/1.68  tff(c_646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_88, c_36, c_404, c_642])).
% 4.08/1.68  tff(c_647, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 4.08/1.68  tff(c_783, plain, (![A_733, B_734, C_735]: (m1_pre_topc(k1_tsep_1(A_733, B_734, C_735), A_733) | ~m1_pre_topc(C_735, A_733) | v2_struct_0(C_735) | ~m1_pre_topc(B_734, A_733) | v2_struct_0(B_734) | ~l1_pre_topc(A_733) | v2_struct_0(A_733))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.08/1.68  tff(c_792, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_42, c_783])).
% 4.08/1.68  tff(c_797, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_48, c_44, c_792])).
% 4.08/1.68  tff(c_798, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_50, c_46, c_797])).
% 4.08/1.68  tff(c_687, plain, (![A_710, B_711, C_712, D_713]: (k2_partfun1(A_710, B_711, C_712, D_713)=k7_relat_1(C_712, D_713) | ~m1_subset_1(C_712, k1_zfmisc_1(k2_zfmisc_1(A_710, B_711))) | ~v1_funct_1(C_712))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.08/1.68  tff(c_689, plain, (![D_713]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_713)=k7_relat_1('#skF_3', D_713) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_687])).
% 4.08/1.68  tff(c_692, plain, (![D_713]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_713)=k7_relat_1('#skF_3', D_713))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_689])).
% 4.08/1.68  tff(c_837, plain, (![A_745, B_746, C_747, D_748]: (k2_partfun1(u1_struct_0(A_745), u1_struct_0(B_746), C_747, u1_struct_0(D_748))=k2_tmap_1(A_745, B_746, C_747, D_748) | ~m1_pre_topc(D_748, A_745) | ~m1_subset_1(C_747, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_745), u1_struct_0(B_746)))) | ~v1_funct_2(C_747, u1_struct_0(A_745), u1_struct_0(B_746)) | ~v1_funct_1(C_747) | ~l1_pre_topc(B_746) | ~v2_pre_topc(B_746) | v2_struct_0(B_746) | ~l1_pre_topc(A_745) | ~v2_pre_topc(A_745) | v2_struct_0(A_745))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.08/1.68  tff(c_839, plain, (![D_748]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_748))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_748) | ~m1_pre_topc(D_748, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_837])).
% 4.08/1.68  tff(c_842, plain, (![D_748]: (k7_relat_1('#skF_3', u1_struct_0(D_748))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_748) | ~m1_pre_topc(D_748, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_56, c_54, c_692, c_839])).
% 4.08/1.68  tff(c_844, plain, (![D_749]: (k7_relat_1('#skF_3', u1_struct_0(D_749))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_749) | ~m1_pre_topc(D_749, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_842])).
% 4.08/1.68  tff(c_649, plain, (![C_693, A_694, B_695]: (v1_relat_1(C_693) | ~m1_subset_1(C_693, k1_zfmisc_1(k2_zfmisc_1(A_694, B_695))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.08/1.68  tff(c_653, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_649])).
% 4.08/1.68  tff(c_654, plain, (![C_696, A_697, B_698]: (v4_relat_1(C_696, A_697) | ~m1_subset_1(C_696, k1_zfmisc_1(k2_zfmisc_1(A_697, B_698))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.08/1.68  tff(c_658, plain, (v4_relat_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_654])).
% 4.08/1.68  tff(c_670, plain, (![B_706, A_707]: (k7_relat_1(B_706, A_707)=B_706 | ~r1_tarski(k1_relat_1(B_706), A_707) | ~v1_relat_1(B_706))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.08/1.68  tff(c_675, plain, (![B_708, A_709]: (k7_relat_1(B_708, A_709)=B_708 | ~v4_relat_1(B_708, A_709) | ~v1_relat_1(B_708))), inference(resolution, [status(thm)], [c_4, c_670])).
% 4.08/1.68  tff(c_678, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_658, c_675])).
% 4.08/1.68  tff(c_681, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_653, c_678])).
% 4.08/1.68  tff(c_850, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_844, c_681])).
% 4.08/1.68  tff(c_859, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_798, c_850])).
% 4.08/1.68  tff(c_867, plain, (![H_754, E_755, D_753, A_751, B_752, C_750]: (r1_tmap_1(E_755, B_752, k2_tmap_1(A_751, B_752, C_750, E_755), H_754) | ~r1_tmap_1(k1_tsep_1(A_751, D_753, E_755), B_752, k2_tmap_1(A_751, B_752, C_750, k1_tsep_1(A_751, D_753, E_755)), H_754) | ~m1_subset_1(H_754, u1_struct_0(E_755)) | ~m1_subset_1(H_754, u1_struct_0(D_753)) | ~m1_subset_1(H_754, u1_struct_0(k1_tsep_1(A_751, D_753, E_755))) | ~m1_pre_topc(E_755, A_751) | v2_struct_0(E_755) | ~m1_pre_topc(D_753, A_751) | v2_struct_0(D_753) | ~m1_subset_1(C_750, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_751), u1_struct_0(B_752)))) | ~v1_funct_2(C_750, u1_struct_0(A_751), u1_struct_0(B_752)) | ~v1_funct_1(C_750) | ~l1_pre_topc(B_752) | ~v2_pre_topc(B_752) | v2_struct_0(B_752) | ~l1_pre_topc(A_751) | ~v2_pre_topc(A_751) | v2_struct_0(A_751))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.08/1.68  tff(c_871, plain, (![B_752, C_750, H_754]: (r1_tmap_1('#skF_5', B_752, k2_tmap_1('#skF_1', B_752, C_750, '#skF_5'), H_754) | ~r1_tmap_1(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_752, k2_tmap_1('#skF_1', B_752, C_750, '#skF_1'), H_754) | ~m1_subset_1(H_754, u1_struct_0('#skF_5')) | ~m1_subset_1(H_754, u1_struct_0('#skF_4')) | ~m1_subset_1(H_754, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_subset_1(C_750, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_752)))) | ~v1_funct_2(C_750, u1_struct_0('#skF_1'), u1_struct_0(B_752)) | ~v1_funct_1(C_750) | ~l1_pre_topc(B_752) | ~v2_pre_topc(B_752) | v2_struct_0(B_752) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_867])).
% 4.08/1.68  tff(c_876, plain, (![B_752, C_750, H_754]: (r1_tmap_1('#skF_5', B_752, k2_tmap_1('#skF_1', B_752, C_750, '#skF_5'), H_754) | ~r1_tmap_1('#skF_1', B_752, k2_tmap_1('#skF_1', B_752, C_750, '#skF_1'), H_754) | ~m1_subset_1(H_754, u1_struct_0('#skF_5')) | ~m1_subset_1(H_754, u1_struct_0('#skF_4')) | ~m1_subset_1(H_754, u1_struct_0('#skF_1')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~m1_subset_1(C_750, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_752)))) | ~v1_funct_2(C_750, u1_struct_0('#skF_1'), u1_struct_0(B_752)) | ~v1_funct_1(C_750) | ~l1_pre_topc(B_752) | ~v2_pre_topc(B_752) | v2_struct_0(B_752) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_44, c_42, c_42, c_871])).
% 4.08/1.68  tff(c_879, plain, (![B_756, C_757, H_758]: (r1_tmap_1('#skF_5', B_756, k2_tmap_1('#skF_1', B_756, C_757, '#skF_5'), H_758) | ~r1_tmap_1('#skF_1', B_756, k2_tmap_1('#skF_1', B_756, C_757, '#skF_1'), H_758) | ~m1_subset_1(H_758, u1_struct_0('#skF_5')) | ~m1_subset_1(H_758, u1_struct_0('#skF_4')) | ~m1_subset_1(H_758, u1_struct_0('#skF_1')) | ~m1_subset_1(C_757, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_756)))) | ~v1_funct_2(C_757, u1_struct_0('#skF_1'), u1_struct_0(B_756)) | ~v1_funct_1(C_757) | ~l1_pre_topc(B_756) | ~v2_pre_topc(B_756) | v2_struct_0(B_756))), inference(negUnitSimplification, [status(thm)], [c_68, c_50, c_46, c_876])).
% 4.08/1.68  tff(c_881, plain, (![H_758]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_758) | ~r1_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), H_758) | ~m1_subset_1(H_758, u1_struct_0('#skF_5')) | ~m1_subset_1(H_758, u1_struct_0('#skF_4')) | ~m1_subset_1(H_758, u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_879])).
% 4.08/1.68  tff(c_884, plain, (![H_758]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_758) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_758) | ~m1_subset_1(H_758, u1_struct_0('#skF_5')) | ~m1_subset_1(H_758, u1_struct_0('#skF_4')) | ~m1_subset_1(H_758, u1_struct_0('#skF_1')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_859, c_881])).
% 4.08/1.68  tff(c_886, plain, (![H_759]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_759) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_759) | ~m1_subset_1(H_759, u1_struct_0('#skF_5')) | ~m1_subset_1(H_759, u1_struct_0('#skF_4')) | ~m1_subset_1(H_759, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_62, c_884])).
% 4.08/1.68  tff(c_648, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 4.08/1.68  tff(c_889, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_886, c_648])).
% 4.08/1.68  tff(c_893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_88, c_36, c_647, c_889])).
% 4.08/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.68  
% 4.08/1.68  Inference rules
% 4.08/1.68  ----------------------
% 4.08/1.68  #Ref     : 0
% 4.08/1.68  #Sup     : 152
% 4.08/1.68  #Fact    : 0
% 4.08/1.68  #Define  : 0
% 4.08/1.68  #Split   : 2
% 4.08/1.68  #Chain   : 0
% 4.08/1.68  #Close   : 0
% 4.08/1.68  
% 4.08/1.68  Ordering : KBO
% 4.08/1.68  
% 4.08/1.68  Simplification rules
% 4.08/1.68  ----------------------
% 4.08/1.68  #Subsume      : 7
% 4.08/1.68  #Demod        : 342
% 4.08/1.68  #Tautology    : 78
% 4.08/1.68  #SimpNegUnit  : 78
% 4.08/1.68  #BackRed      : 0
% 4.08/1.68  
% 4.08/1.68  #Partial instantiations: 0
% 4.08/1.68  #Strategies tried      : 1
% 4.08/1.68  
% 4.08/1.68  Timing (in seconds)
% 4.08/1.68  ----------------------
% 4.25/1.69  Preprocessing        : 0.41
% 4.25/1.69  Parsing              : 0.21
% 4.25/1.69  CNF conversion       : 0.06
% 4.25/1.69  Main loop            : 0.43
% 4.25/1.69  Inferencing          : 0.15
% 4.25/1.69  Reduction            : 0.14
% 4.25/1.69  Demodulation         : 0.10
% 4.25/1.69  BG Simplification    : 0.02
% 4.25/1.69  Subsumption          : 0.08
% 4.25/1.69  Abstraction          : 0.02
% 4.25/1.69  MUC search           : 0.00
% 4.25/1.69  Cooper               : 0.00
% 4.25/1.69  Total                : 0.91
% 4.25/1.69  Index Insertion      : 0.00
% 4.25/1.69  Index Deletion       : 0.00
% 4.25/1.69  Index Matching       : 0.00
% 4.25/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
