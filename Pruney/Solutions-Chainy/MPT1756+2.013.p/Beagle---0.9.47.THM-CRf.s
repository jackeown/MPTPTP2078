%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:03 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 368 expanded)
%              Number of leaves         :   35 ( 160 expanded)
%              Depth                    :   17
%              Number of atoms          :  332 (3055 expanded)
%              Number of equality atoms :    4 ( 133 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_228,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_60,axiom,(
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

tff(f_178,axiom,(
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

tff(f_84,axiom,(
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

tff(c_48,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_46,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_32,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_40,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_77,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_58,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_34,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_24,plain,(
    ! [B_42,A_40] :
      ( m1_subset_1(u1_struct_0(B_42),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_pre_topc(B_42,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_122,plain,(
    ! [A_374,B_375,C_376] :
      ( r1_tarski('#skF_1'(A_374,B_375,C_376),C_376)
      | ~ m1_connsp_2(C_376,A_374,B_375)
      | ~ m1_subset_1(C_376,k1_zfmisc_1(u1_struct_0(A_374)))
      | ~ m1_subset_1(B_375,u1_struct_0(A_374))
      | ~ l1_pre_topc(A_374)
      | ~ v2_pre_topc(A_374)
      | v2_struct_0(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_127,plain,(
    ! [A_40,B_375,B_42] :
      ( r1_tarski('#skF_1'(A_40,B_375,u1_struct_0(B_42)),u1_struct_0(B_42))
      | ~ m1_connsp_2(u1_struct_0(B_42),A_40,B_375)
      | ~ m1_subset_1(B_375,u1_struct_0(A_40))
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40)
      | ~ m1_pre_topc(B_42,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_24,c_122])).

tff(c_10,plain,(
    ! [A_4,B_12,C_16] :
      ( m1_subset_1('#skF_1'(A_4,B_12,C_16),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_connsp_2(C_16,A_4,B_12)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_12,u1_struct_0(A_4))
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_74,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_75,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_74])).

tff(c_96,plain,(
    r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_68,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_68])).

tff(c_98,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_76])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_52,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_342,plain,(
    ! [A_460,B_456,C_455,E_459,D_457,G_458] :
      ( r1_tmap_1(B_456,A_460,C_455,G_458)
      | ~ r1_tmap_1(D_457,A_460,k2_tmap_1(B_456,A_460,C_455,D_457),G_458)
      | ~ m1_connsp_2(E_459,B_456,G_458)
      | ~ r1_tarski(E_459,u1_struct_0(D_457))
      | ~ m1_subset_1(G_458,u1_struct_0(D_457))
      | ~ m1_subset_1(G_458,u1_struct_0(B_456))
      | ~ m1_subset_1(E_459,k1_zfmisc_1(u1_struct_0(B_456)))
      | ~ m1_pre_topc(D_457,B_456)
      | v2_struct_0(D_457)
      | ~ m1_subset_1(C_455,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_456),u1_struct_0(A_460))))
      | ~ v1_funct_2(C_455,u1_struct_0(B_456),u1_struct_0(A_460))
      | ~ v1_funct_1(C_455)
      | ~ l1_pre_topc(B_456)
      | ~ v2_pre_topc(B_456)
      | v2_struct_0(B_456)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_346,plain,(
    ! [E_459] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_459,'#skF_4','#skF_8')
      | ~ r1_tarski(E_459,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_459,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_96,c_342])).

tff(c_353,plain,(
    ! [E_459] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_459,'#skF_4','#skF_8')
      | ~ r1_tarski(E_459,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_459,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_54,c_52,c_50,c_46,c_42,c_77,c_346])).

tff(c_355,plain,(
    ! [E_461] :
      ( ~ m1_connsp_2(E_461,'#skF_4','#skF_8')
      | ~ r1_tarski(E_461,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_461,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_48,c_98,c_353])).

tff(c_359,plain,(
    ! [B_12,C_16] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_12,C_16),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4',B_12,C_16),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(C_16,'#skF_4',B_12)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_355])).

tff(c_373,plain,(
    ! [B_12,C_16] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_12,C_16),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4',B_12,C_16),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(C_16,'#skF_4',B_12)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_359])).

tff(c_386,plain,(
    ! [B_463,C_464] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_463,C_464),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4',B_463,C_464),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(C_464,'#skF_4',B_463)
      | ~ m1_subset_1(C_464,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_463,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_373])).

tff(c_390,plain,(
    ! [B_375] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_375,u1_struct_0('#skF_6')),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_375)
      | ~ m1_subset_1(B_375,u1_struct_0('#skF_4'))
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_127,c_386])).

tff(c_393,plain,(
    ! [B_375] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_375,u1_struct_0('#skF_6')),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_375)
      | ~ m1_subset_1(B_375,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_58,c_390])).

tff(c_394,plain,(
    ! [B_375] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_375,u1_struct_0('#skF_6')),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_375)
      | ~ m1_subset_1(B_375,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_393])).

tff(c_395,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_398,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_395])).

tff(c_402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_398])).

tff(c_404,plain,(
    m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_38,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_36,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_227,plain,(
    ! [C_422,A_423,B_424,D_425] :
      ( m1_connsp_2(C_422,A_423,B_424)
      | ~ r2_hidden(B_424,D_425)
      | ~ r1_tarski(D_425,C_422)
      | ~ v3_pre_topc(D_425,A_423)
      | ~ m1_subset_1(D_425,k1_zfmisc_1(u1_struct_0(A_423)))
      | ~ m1_subset_1(C_422,k1_zfmisc_1(u1_struct_0(A_423)))
      | ~ m1_subset_1(B_424,u1_struct_0(A_423))
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423)
      | v2_struct_0(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_237,plain,(
    ! [C_426,A_427] :
      ( m1_connsp_2(C_426,A_427,'#skF_8')
      | ~ r1_tarski('#skF_7',C_426)
      | ~ v3_pre_topc('#skF_7',A_427)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_427)))
      | ~ m1_subset_1(C_426,k1_zfmisc_1(u1_struct_0(A_427)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_427))
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(resolution,[status(thm)],[c_36,c_227])).

tff(c_239,plain,(
    ! [C_426] :
      ( m1_connsp_2(C_426,'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',C_426)
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(C_426,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_237])).

tff(c_242,plain,(
    ! [C_426] :
      ( m1_connsp_2(C_426,'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',C_426)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_38,c_239])).

tff(c_243,plain,(
    ! [C_426] :
      ( m1_connsp_2(C_426,'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',C_426)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_242])).

tff(c_414,plain,
    ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_404,c_243])).

tff(c_434,plain,(
    m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_414])).

tff(c_157,plain,(
    ! [A_392,B_393,C_394] :
      ( m1_connsp_2('#skF_1'(A_392,B_393,C_394),A_392,B_393)
      | ~ m1_connsp_2(C_394,A_392,B_393)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(u1_struct_0(A_392)))
      | ~ m1_subset_1(B_393,u1_struct_0(A_392))
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_162,plain,(
    ! [A_40,B_393,B_42] :
      ( m1_connsp_2('#skF_1'(A_40,B_393,u1_struct_0(B_42)),A_40,B_393)
      | ~ m1_connsp_2(u1_struct_0(B_42),A_40,B_393)
      | ~ m1_subset_1(B_393,u1_struct_0(A_40))
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40)
      | ~ m1_pre_topc(B_42,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_24,c_157])).

tff(c_482,plain,(
    ! [B_473] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_473,u1_struct_0('#skF_6')),'#skF_4','#skF_8')
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_473)
      | ~ m1_subset_1(B_473,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_490,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_162,c_482])).

tff(c_496,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_58,c_42,c_434,c_490])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_496])).

tff(c_499,plain,(
    r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_703,plain,(
    ! [C_544,B_547,D_548,A_546,F_545] :
      ( r1_tmap_1(D_548,A_546,k2_tmap_1(B_547,A_546,C_544,D_548),F_545)
      | ~ r1_tmap_1(B_547,A_546,C_544,F_545)
      | ~ m1_subset_1(F_545,u1_struct_0(D_548))
      | ~ m1_subset_1(F_545,u1_struct_0(B_547))
      | ~ m1_pre_topc(D_548,B_547)
      | v2_struct_0(D_548)
      | ~ m1_subset_1(C_544,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_547),u1_struct_0(A_546))))
      | ~ v1_funct_2(C_544,u1_struct_0(B_547),u1_struct_0(A_546))
      | ~ v1_funct_1(C_544)
      | ~ l1_pre_topc(B_547)
      | ~ v2_pre_topc(B_547)
      | v2_struct_0(B_547)
      | ~ l1_pre_topc(A_546)
      | ~ v2_pre_topc(A_546)
      | v2_struct_0(A_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_705,plain,(
    ! [D_548,F_545] :
      ( r1_tmap_1(D_548,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_548),F_545)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_545)
      | ~ m1_subset_1(F_545,u1_struct_0(D_548))
      | ~ m1_subset_1(F_545,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_548,'#skF_4')
      | v2_struct_0(D_548)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_703])).

tff(c_708,plain,(
    ! [D_548,F_545] :
      ( r1_tmap_1(D_548,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_548),F_545)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_545)
      | ~ m1_subset_1(F_545,u1_struct_0(D_548))
      | ~ m1_subset_1(F_545,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_548,'#skF_4')
      | v2_struct_0(D_548)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_54,c_52,c_705])).

tff(c_735,plain,(
    ! [D_552,F_553] :
      ( r1_tmap_1(D_552,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_552),F_553)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_553)
      | ~ m1_subset_1(F_553,u1_struct_0(D_552))
      | ~ m1_subset_1(F_553,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_552,'#skF_4')
      | v2_struct_0(D_552) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_708])).

tff(c_500,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_738,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_735,c_500])).

tff(c_741,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_77,c_499,c_738])).

tff(c_743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.65  
% 3.75/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.65  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 3.75/1.65  
% 3.75/1.65  %Foreground sorts:
% 3.75/1.65  
% 3.75/1.65  
% 3.75/1.65  %Background operators:
% 3.75/1.65  
% 3.75/1.65  
% 3.75/1.65  %Foreground operators:
% 3.75/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.75/1.65  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.75/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.75/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.75/1.65  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.75/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.75/1.65  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.75/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.75/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.75/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.75/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.75/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.75/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.75/1.65  tff('#skF_9', type, '#skF_9': $i).
% 3.75/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.75/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.75/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.75/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.65  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.75/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.75/1.65  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.75/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.75/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.75/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.65  
% 3.75/1.67  tff(f_228, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 3.75/1.67  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.75/1.67  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.75/1.67  tff(f_178, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.75/1.67  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 3.75/1.67  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.75/1.67  tff(c_48, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_46, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_42, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_32, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_40, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_77, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_40])).
% 3.75/1.67  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_58, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_34, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_24, plain, (![B_42, A_40]: (m1_subset_1(u1_struct_0(B_42), k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_pre_topc(B_42, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.75/1.67  tff(c_122, plain, (![A_374, B_375, C_376]: (r1_tarski('#skF_1'(A_374, B_375, C_376), C_376) | ~m1_connsp_2(C_376, A_374, B_375) | ~m1_subset_1(C_376, k1_zfmisc_1(u1_struct_0(A_374))) | ~m1_subset_1(B_375, u1_struct_0(A_374)) | ~l1_pre_topc(A_374) | ~v2_pre_topc(A_374) | v2_struct_0(A_374))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.75/1.67  tff(c_127, plain, (![A_40, B_375, B_42]: (r1_tarski('#skF_1'(A_40, B_375, u1_struct_0(B_42)), u1_struct_0(B_42)) | ~m1_connsp_2(u1_struct_0(B_42), A_40, B_375) | ~m1_subset_1(B_375, u1_struct_0(A_40)) | ~v2_pre_topc(A_40) | v2_struct_0(A_40) | ~m1_pre_topc(B_42, A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_24, c_122])).
% 3.75/1.67  tff(c_10, plain, (![A_4, B_12, C_16]: (m1_subset_1('#skF_1'(A_4, B_12, C_16), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_connsp_2(C_16, A_4, B_12) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(B_12, u1_struct_0(A_4)) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.75/1.67  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_74, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_75, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_74])).
% 3.75/1.67  tff(c_96, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_75])).
% 3.75/1.67  tff(c_68, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_76, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_68])).
% 3.75/1.67  tff(c_98, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_76])).
% 3.75/1.67  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_52, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_342, plain, (![A_460, B_456, C_455, E_459, D_457, G_458]: (r1_tmap_1(B_456, A_460, C_455, G_458) | ~r1_tmap_1(D_457, A_460, k2_tmap_1(B_456, A_460, C_455, D_457), G_458) | ~m1_connsp_2(E_459, B_456, G_458) | ~r1_tarski(E_459, u1_struct_0(D_457)) | ~m1_subset_1(G_458, u1_struct_0(D_457)) | ~m1_subset_1(G_458, u1_struct_0(B_456)) | ~m1_subset_1(E_459, k1_zfmisc_1(u1_struct_0(B_456))) | ~m1_pre_topc(D_457, B_456) | v2_struct_0(D_457) | ~m1_subset_1(C_455, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_456), u1_struct_0(A_460)))) | ~v1_funct_2(C_455, u1_struct_0(B_456), u1_struct_0(A_460)) | ~v1_funct_1(C_455) | ~l1_pre_topc(B_456) | ~v2_pre_topc(B_456) | v2_struct_0(B_456) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.75/1.67  tff(c_346, plain, (![E_459]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_459, '#skF_4', '#skF_8') | ~r1_tarski(E_459, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_459, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_96, c_342])).
% 3.75/1.67  tff(c_353, plain, (![E_459]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_459, '#skF_4', '#skF_8') | ~r1_tarski(E_459, u1_struct_0('#skF_6')) | ~m1_subset_1(E_459, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_54, c_52, c_50, c_46, c_42, c_77, c_346])).
% 3.75/1.67  tff(c_355, plain, (![E_461]: (~m1_connsp_2(E_461, '#skF_4', '#skF_8') | ~r1_tarski(E_461, u1_struct_0('#skF_6')) | ~m1_subset_1(E_461, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_48, c_98, c_353])).
% 3.75/1.67  tff(c_359, plain, (![B_12, C_16]: (~m1_connsp_2('#skF_1'('#skF_4', B_12, C_16), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', B_12, C_16), u1_struct_0('#skF_6')) | ~m1_connsp_2(C_16, '#skF_4', B_12) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_12, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_10, c_355])).
% 3.75/1.67  tff(c_373, plain, (![B_12, C_16]: (~m1_connsp_2('#skF_1'('#skF_4', B_12, C_16), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', B_12, C_16), u1_struct_0('#skF_6')) | ~m1_connsp_2(C_16, '#skF_4', B_12) | ~m1_subset_1(C_16, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_12, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_359])).
% 3.75/1.67  tff(c_386, plain, (![B_463, C_464]: (~m1_connsp_2('#skF_1'('#skF_4', B_463, C_464), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', B_463, C_464), u1_struct_0('#skF_6')) | ~m1_connsp_2(C_464, '#skF_4', B_463) | ~m1_subset_1(C_464, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_463, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_373])).
% 3.75/1.67  tff(c_390, plain, (![B_375]: (~m1_connsp_2('#skF_1'('#skF_4', B_375, u1_struct_0('#skF_6')), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_375) | ~m1_subset_1(B_375, u1_struct_0('#skF_4')) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_127, c_386])).
% 3.75/1.67  tff(c_393, plain, (![B_375]: (~m1_connsp_2('#skF_1'('#skF_4', B_375, u1_struct_0('#skF_6')), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_375) | ~m1_subset_1(B_375, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_58, c_390])).
% 3.75/1.67  tff(c_394, plain, (![B_375]: (~m1_connsp_2('#skF_1'('#skF_4', B_375, u1_struct_0('#skF_6')), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_375) | ~m1_subset_1(B_375, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_393])).
% 3.75/1.67  tff(c_395, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_394])).
% 3.75/1.67  tff(c_398, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_395])).
% 3.75/1.67  tff(c_402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_398])).
% 3.75/1.67  tff(c_404, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_394])).
% 3.75/1.67  tff(c_38, plain, (v3_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_36, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.75/1.67  tff(c_227, plain, (![C_422, A_423, B_424, D_425]: (m1_connsp_2(C_422, A_423, B_424) | ~r2_hidden(B_424, D_425) | ~r1_tarski(D_425, C_422) | ~v3_pre_topc(D_425, A_423) | ~m1_subset_1(D_425, k1_zfmisc_1(u1_struct_0(A_423))) | ~m1_subset_1(C_422, k1_zfmisc_1(u1_struct_0(A_423))) | ~m1_subset_1(B_424, u1_struct_0(A_423)) | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423) | v2_struct_0(A_423))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.75/1.67  tff(c_237, plain, (![C_426, A_427]: (m1_connsp_2(C_426, A_427, '#skF_8') | ~r1_tarski('#skF_7', C_426) | ~v3_pre_topc('#skF_7', A_427) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_427))) | ~m1_subset_1(C_426, k1_zfmisc_1(u1_struct_0(A_427))) | ~m1_subset_1('#skF_8', u1_struct_0(A_427)) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(resolution, [status(thm)], [c_36, c_227])).
% 3.75/1.67  tff(c_239, plain, (![C_426]: (m1_connsp_2(C_426, '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', C_426) | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(C_426, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_237])).
% 3.75/1.67  tff(c_242, plain, (![C_426]: (m1_connsp_2(C_426, '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', C_426) | ~m1_subset_1(C_426, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_38, c_239])).
% 3.75/1.67  tff(c_243, plain, (![C_426]: (m1_connsp_2(C_426, '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', C_426) | ~m1_subset_1(C_426, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_242])).
% 3.75/1.67  tff(c_414, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_404, c_243])).
% 3.75/1.67  tff(c_434, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_414])).
% 3.75/1.67  tff(c_157, plain, (![A_392, B_393, C_394]: (m1_connsp_2('#skF_1'(A_392, B_393, C_394), A_392, B_393) | ~m1_connsp_2(C_394, A_392, B_393) | ~m1_subset_1(C_394, k1_zfmisc_1(u1_struct_0(A_392))) | ~m1_subset_1(B_393, u1_struct_0(A_392)) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.75/1.67  tff(c_162, plain, (![A_40, B_393, B_42]: (m1_connsp_2('#skF_1'(A_40, B_393, u1_struct_0(B_42)), A_40, B_393) | ~m1_connsp_2(u1_struct_0(B_42), A_40, B_393) | ~m1_subset_1(B_393, u1_struct_0(A_40)) | ~v2_pre_topc(A_40) | v2_struct_0(A_40) | ~m1_pre_topc(B_42, A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_24, c_157])).
% 3.75/1.67  tff(c_482, plain, (![B_473]: (~m1_connsp_2('#skF_1'('#skF_4', B_473, u1_struct_0('#skF_6')), '#skF_4', '#skF_8') | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_473) | ~m1_subset_1(B_473, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_394])).
% 3.75/1.67  tff(c_490, plain, (~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_162, c_482])).
% 3.75/1.67  tff(c_496, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_58, c_42, c_434, c_490])).
% 3.75/1.67  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_496])).
% 3.75/1.67  tff(c_499, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_75])).
% 3.75/1.67  tff(c_703, plain, (![C_544, B_547, D_548, A_546, F_545]: (r1_tmap_1(D_548, A_546, k2_tmap_1(B_547, A_546, C_544, D_548), F_545) | ~r1_tmap_1(B_547, A_546, C_544, F_545) | ~m1_subset_1(F_545, u1_struct_0(D_548)) | ~m1_subset_1(F_545, u1_struct_0(B_547)) | ~m1_pre_topc(D_548, B_547) | v2_struct_0(D_548) | ~m1_subset_1(C_544, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_547), u1_struct_0(A_546)))) | ~v1_funct_2(C_544, u1_struct_0(B_547), u1_struct_0(A_546)) | ~v1_funct_1(C_544) | ~l1_pre_topc(B_547) | ~v2_pre_topc(B_547) | v2_struct_0(B_547) | ~l1_pre_topc(A_546) | ~v2_pre_topc(A_546) | v2_struct_0(A_546))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.75/1.67  tff(c_705, plain, (![D_548, F_545]: (r1_tmap_1(D_548, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_548), F_545) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_545) | ~m1_subset_1(F_545, u1_struct_0(D_548)) | ~m1_subset_1(F_545, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_548, '#skF_4') | v2_struct_0(D_548) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_703])).
% 3.75/1.67  tff(c_708, plain, (![D_548, F_545]: (r1_tmap_1(D_548, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_548), F_545) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_545) | ~m1_subset_1(F_545, u1_struct_0(D_548)) | ~m1_subset_1(F_545, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_548, '#skF_4') | v2_struct_0(D_548) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_54, c_52, c_705])).
% 3.75/1.67  tff(c_735, plain, (![D_552, F_553]: (r1_tmap_1(D_552, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_552), F_553) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_553) | ~m1_subset_1(F_553, u1_struct_0(D_552)) | ~m1_subset_1(F_553, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_552, '#skF_4') | v2_struct_0(D_552))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_708])).
% 3.75/1.67  tff(c_500, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_75])).
% 3.75/1.67  tff(c_738, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_735, c_500])).
% 3.75/1.67  tff(c_741, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_77, c_499, c_738])).
% 3.75/1.67  tff(c_743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_741])).
% 3.75/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.67  
% 3.75/1.67  Inference rules
% 3.75/1.67  ----------------------
% 3.75/1.67  #Ref     : 0
% 3.75/1.67  #Sup     : 123
% 3.75/1.67  #Fact    : 0
% 3.75/1.67  #Define  : 0
% 3.75/1.67  #Split   : 4
% 3.75/1.67  #Chain   : 0
% 3.75/1.67  #Close   : 0
% 3.75/1.67  
% 3.75/1.67  Ordering : KBO
% 3.75/1.67  
% 3.75/1.67  Simplification rules
% 3.75/1.67  ----------------------
% 3.75/1.67  #Subsume      : 2
% 3.75/1.67  #Demod        : 140
% 3.75/1.67  #Tautology    : 12
% 3.75/1.67  #SimpNegUnit  : 44
% 3.75/1.67  #BackRed      : 0
% 3.75/1.67  
% 3.75/1.67  #Partial instantiations: 0
% 3.75/1.67  #Strategies tried      : 1
% 3.75/1.67  
% 3.75/1.67  Timing (in seconds)
% 3.75/1.67  ----------------------
% 3.75/1.67  Preprocessing        : 0.40
% 3.75/1.67  Parsing              : 0.21
% 3.75/1.67  CNF conversion       : 0.05
% 3.75/1.67  Main loop            : 0.43
% 3.75/1.67  Inferencing          : 0.17
% 3.75/1.67  Reduction            : 0.13
% 3.75/1.67  Demodulation         : 0.09
% 3.75/1.67  BG Simplification    : 0.03
% 3.75/1.67  Subsumption          : 0.07
% 3.75/1.67  Abstraction          : 0.02
% 3.75/1.67  MUC search           : 0.00
% 3.75/1.67  Cooper               : 0.00
% 3.75/1.67  Total                : 0.88
% 3.75/1.67  Index Insertion      : 0.00
% 3.75/1.67  Index Deletion       : 0.00
% 3.75/1.67  Index Matching       : 0.00
% 3.75/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
