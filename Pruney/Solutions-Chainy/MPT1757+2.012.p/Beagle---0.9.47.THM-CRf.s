%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:05 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 485 expanded)
%              Number of leaves         :   42 ( 204 expanded)
%              Depth                    :   20
%              Number of atoms          :  395 (3550 expanded)
%              Number of equality atoms :    5 ( 172 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_288,negated_conjecture,(
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
                      & v1_tsep_1(D,B)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ( E = F
                             => ( r1_tmap_1(B,A,C,E)
                              <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_54,axiom,(
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
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_158,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_151,axiom,(
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

tff(f_133,axiom,(
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

tff(f_245,axiom,(
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

tff(f_198,axiom,(
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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_50,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_44,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_82,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_62,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_101,plain,(
    ! [B_317,A_318] :
      ( v2_pre_topc(B_317)
      | ~ m1_pre_topc(B_317,A_318)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_101])).

tff(c_107,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_104])).

tff(c_88,plain,(
    ! [B_310,A_311] :
      ( l1_pre_topc(B_310)
      | ~ m1_pre_topc(B_310,A_311)
      | ~ l1_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_94,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91])).

tff(c_16,plain,(
    ! [B_27,A_25] :
      ( r2_hidden(B_27,k1_connsp_2(A_25,B_27))
      | ~ m1_subset_1(B_27,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_117,plain,(
    ! [A_326,B_327] :
      ( m1_subset_1(k1_connsp_2(A_326,B_327),k1_zfmisc_1(u1_struct_0(A_326)))
      | ~ m1_subset_1(B_327,u1_struct_0(A_326))
      | ~ l1_pre_topc(A_326)
      | ~ v2_pre_topc(A_326)
      | v2_struct_0(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_140,plain,(
    ! [A_333,A_334,B_335] :
      ( ~ v1_xboole_0(u1_struct_0(A_333))
      | ~ r2_hidden(A_334,k1_connsp_2(A_333,B_335))
      | ~ m1_subset_1(B_335,u1_struct_0(A_333))
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | v2_struct_0(A_333) ) ),
    inference(resolution,[status(thm)],[c_117,c_4])).

tff(c_150,plain,(
    ! [A_336,B_337] :
      ( ~ v1_xboole_0(u1_struct_0(A_336))
      | ~ m1_subset_1(B_337,u1_struct_0(A_336))
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(resolution,[status(thm)],[c_16,c_140])).

tff(c_162,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_150])).

tff(c_171,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_94,c_162])).

tff(c_172,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_171])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_52,plain,(
    v1_tsep_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_36,plain,(
    ! [B_62,A_60] :
      ( m1_subset_1(u1_struct_0(B_62),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_pre_topc(B_62,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_197,plain,(
    ! [B_349,A_350] :
      ( v3_pre_topc(u1_struct_0(B_349),A_350)
      | ~ v1_tsep_1(B_349,A_350)
      | ~ m1_subset_1(u1_struct_0(B_349),k1_zfmisc_1(u1_struct_0(A_350)))
      | ~ m1_pre_topc(B_349,A_350)
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_201,plain,(
    ! [B_62,A_60] :
      ( v3_pre_topc(u1_struct_0(B_62),A_60)
      | ~ v1_tsep_1(B_62,A_60)
      | ~ v2_pre_topc(A_60)
      | ~ m1_pre_topc(B_62,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_36,c_197])).

tff(c_226,plain,(
    ! [A_361,B_362,C_363] :
      ( r1_tarski('#skF_1'(A_361,B_362,C_363),B_362)
      | ~ r2_hidden(C_363,B_362)
      | ~ m1_subset_1(C_363,u1_struct_0(A_361))
      | ~ v3_pre_topc(B_362,A_361)
      | ~ m1_subset_1(B_362,k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ l1_pre_topc(A_361)
      | ~ v2_pre_topc(A_361)
      | v2_struct_0(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_232,plain,(
    ! [A_60,B_62,C_363] :
      ( r1_tarski('#skF_1'(A_60,u1_struct_0(B_62),C_363),u1_struct_0(B_62))
      | ~ r2_hidden(C_363,u1_struct_0(B_62))
      | ~ m1_subset_1(C_363,u1_struct_0(A_60))
      | ~ v3_pre_topc(u1_struct_0(B_62),A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_62,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_36,c_226])).

tff(c_28,plain,(
    ! [A_28,B_42,C_49] :
      ( m1_subset_1('#skF_1'(A_28,B_42,C_49),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ r2_hidden(C_49,B_42)
      | ~ m1_subset_1(C_49,u1_struct_0(A_28))
      | ~ v3_pre_topc(B_42,A_28)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_7')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_81,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_80])).

tff(c_113,plain,(
    r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_74,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_83,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_74])).

tff(c_115,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_83])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_288])).

tff(c_384,plain,(
    ! [B_438,D_435,A_436,E_437,G_439,C_440] :
      ( r1_tmap_1(B_438,A_436,C_440,G_439)
      | ~ r1_tmap_1(D_435,A_436,k2_tmap_1(B_438,A_436,C_440,D_435),G_439)
      | ~ m1_connsp_2(E_437,B_438,G_439)
      | ~ r1_tarski(E_437,u1_struct_0(D_435))
      | ~ m1_subset_1(G_439,u1_struct_0(D_435))
      | ~ m1_subset_1(G_439,u1_struct_0(B_438))
      | ~ m1_subset_1(E_437,k1_zfmisc_1(u1_struct_0(B_438)))
      | ~ m1_pre_topc(D_435,B_438)
      | v2_struct_0(D_435)
      | ~ m1_subset_1(C_440,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_438),u1_struct_0(A_436))))
      | ~ v1_funct_2(C_440,u1_struct_0(B_438),u1_struct_0(A_436))
      | ~ v1_funct_1(C_440)
      | ~ l1_pre_topc(B_438)
      | ~ v2_pre_topc(B_438)
      | v2_struct_0(B_438)
      | ~ l1_pre_topc(A_436)
      | ~ v2_pre_topc(A_436)
      | v2_struct_0(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_388,plain,(
    ! [E_437] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_437,'#skF_4','#skF_8')
      | ~ r1_tarski(E_437,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_437,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_113,c_384])).

tff(c_395,plain,(
    ! [E_437] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_437,'#skF_4','#skF_8')
      | ~ r1_tarski(E_437,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_437,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_56,c_50,c_82,c_46,c_388])).

tff(c_397,plain,(
    ! [E_441] :
      ( ~ m1_connsp_2(E_441,'#skF_4','#skF_8')
      | ~ r1_tarski(E_441,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_441,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_54,c_115,c_395])).

tff(c_409,plain,(
    ! [B_42,C_49] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_42,C_49),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4',B_42,C_49),u1_struct_0('#skF_6'))
      | ~ r2_hidden(C_49,B_42)
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(B_42,'#skF_4')
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_397])).

tff(c_428,plain,(
    ! [B_42,C_49] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_42,C_49),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4',B_42,C_49),u1_struct_0('#skF_6'))
      | ~ r2_hidden(C_49,B_42)
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(B_42,'#skF_4')
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_409])).

tff(c_439,plain,(
    ! [B_444,C_445] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_444,C_445),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4',B_444,C_445),u1_struct_0('#skF_6'))
      | ~ r2_hidden(C_445,B_444)
      | ~ m1_subset_1(C_445,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(B_444,'#skF_4')
      | ~ m1_subset_1(B_444,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_428])).

tff(c_443,plain,(
    ! [C_363] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_363),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_363,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_363,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_232,c_439])).

tff(c_446,plain,(
    ! [C_363] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_363),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_363,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_363,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_443])).

tff(c_447,plain,(
    ! [C_363] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_363),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_363,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_363,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_446])).

tff(c_448,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_454,plain,
    ( ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_201,c_448])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_52,c_454])).

tff(c_464,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_255,plain,(
    ! [A_381,B_382,C_383] :
      ( m1_connsp_2('#skF_1'(A_381,B_382,C_383),A_381,C_383)
      | ~ r2_hidden(C_383,B_382)
      | ~ m1_subset_1(C_383,u1_struct_0(A_381))
      | ~ v3_pre_topc(B_382,A_381)
      | ~ m1_subset_1(B_382,k1_zfmisc_1(u1_struct_0(A_381)))
      | ~ l1_pre_topc(A_381)
      | ~ v2_pre_topc(A_381)
      | v2_struct_0(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_261,plain,(
    ! [A_60,B_62,C_383] :
      ( m1_connsp_2('#skF_1'(A_60,u1_struct_0(B_62),C_383),A_60,C_383)
      | ~ r2_hidden(C_383,u1_struct_0(B_62))
      | ~ m1_subset_1(C_383,u1_struct_0(A_60))
      | ~ v3_pre_topc(u1_struct_0(B_62),A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_62,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_36,c_255])).

tff(c_463,plain,(
    ! [C_363] :
      ( ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_363),'#skF_4','#skF_8')
      | ~ r2_hidden(C_363,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_363,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_471,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_463])).

tff(c_474,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_471])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_474])).

tff(c_529,plain,(
    ! [C_451] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_451),'#skF_4','#skF_8')
      | ~ r2_hidden(C_451,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_451,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_537,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_261,c_529])).

tff(c_543,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_464,c_82,c_537])).

tff(c_544,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_543])).

tff(c_547,plain,
    ( v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2,c_544])).

tff(c_550,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_547])).

tff(c_552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_550])).

tff(c_553,plain,(
    r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_729,plain,(
    ! [D_521,C_525,F_522,B_523,A_524] :
      ( r1_tmap_1(D_521,A_524,k2_tmap_1(B_523,A_524,C_525,D_521),F_522)
      | ~ r1_tmap_1(B_523,A_524,C_525,F_522)
      | ~ m1_subset_1(F_522,u1_struct_0(D_521))
      | ~ m1_subset_1(F_522,u1_struct_0(B_523))
      | ~ m1_pre_topc(D_521,B_523)
      | v2_struct_0(D_521)
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_523),u1_struct_0(A_524))))
      | ~ v1_funct_2(C_525,u1_struct_0(B_523),u1_struct_0(A_524))
      | ~ v1_funct_1(C_525)
      | ~ l1_pre_topc(B_523)
      | ~ v2_pre_topc(B_523)
      | v2_struct_0(B_523)
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | v2_struct_0(A_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_731,plain,(
    ! [D_521,F_522] :
      ( r1_tmap_1(D_521,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_521),F_522)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_522)
      | ~ m1_subset_1(F_522,u1_struct_0(D_521))
      | ~ m1_subset_1(F_522,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_521,'#skF_4')
      | v2_struct_0(D_521)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_729])).

tff(c_734,plain,(
    ! [D_521,F_522] :
      ( r1_tmap_1(D_521,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_521),F_522)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_522)
      | ~ m1_subset_1(F_522,u1_struct_0(D_521))
      | ~ m1_subset_1(F_522,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_521,'#skF_4')
      | v2_struct_0(D_521)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_731])).

tff(c_736,plain,(
    ! [D_526,F_527] :
      ( r1_tmap_1(D_526,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_526),F_527)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_527)
      | ~ m1_subset_1(F_527,u1_struct_0(D_526))
      | ~ m1_subset_1(F_527,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_526,'#skF_4')
      | v2_struct_0(D_526) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_734])).

tff(c_554,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_739,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_736,c_554])).

tff(c_742,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_82,c_46,c_553,c_739])).

tff(c_744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_742])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:03:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.61  
% 3.91/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.61  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 3.91/1.61  
% 3.91/1.61  %Foreground sorts:
% 3.91/1.61  
% 3.91/1.61  
% 3.91/1.61  %Background operators:
% 3.91/1.61  
% 3.91/1.61  
% 3.91/1.61  %Foreground operators:
% 3.91/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.91/1.61  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.91/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.91/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.91/1.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.91/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.61  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 3.91/1.61  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.91/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.91/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.91/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.91/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.91/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.91/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.91/1.61  tff('#skF_8', type, '#skF_8': $i).
% 3.91/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.91/1.61  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.91/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.91/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.91/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.91/1.61  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.91/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.91/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.91/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.61  
% 3.91/1.63  tff(f_288, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.91/1.63  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.91/1.63  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.91/1.63  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 3.91/1.63  tff(f_81, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 3.91/1.63  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.91/1.63  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.91/1.63  tff(f_158, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.91/1.63  tff(f_151, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.91/1.63  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 3.91/1.63  tff(f_245, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.91/1.63  tff(f_198, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.91/1.63  tff(c_54, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_50, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_44, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_82, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48])).
% 3.91/1.63  tff(c_46, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_62, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_101, plain, (![B_317, A_318]: (v2_pre_topc(B_317) | ~m1_pre_topc(B_317, A_318) | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.91/1.63  tff(c_104, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_101])).
% 3.91/1.63  tff(c_107, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_104])).
% 3.91/1.63  tff(c_88, plain, (![B_310, A_311]: (l1_pre_topc(B_310) | ~m1_pre_topc(B_310, A_311) | ~l1_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.91/1.63  tff(c_91, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_88])).
% 3.91/1.63  tff(c_94, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91])).
% 3.91/1.63  tff(c_16, plain, (![B_27, A_25]: (r2_hidden(B_27, k1_connsp_2(A_25, B_27)) | ~m1_subset_1(B_27, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.91/1.63  tff(c_117, plain, (![A_326, B_327]: (m1_subset_1(k1_connsp_2(A_326, B_327), k1_zfmisc_1(u1_struct_0(A_326))) | ~m1_subset_1(B_327, u1_struct_0(A_326)) | ~l1_pre_topc(A_326) | ~v2_pre_topc(A_326) | v2_struct_0(A_326))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.91/1.63  tff(c_4, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.91/1.63  tff(c_140, plain, (![A_333, A_334, B_335]: (~v1_xboole_0(u1_struct_0(A_333)) | ~r2_hidden(A_334, k1_connsp_2(A_333, B_335)) | ~m1_subset_1(B_335, u1_struct_0(A_333)) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333) | v2_struct_0(A_333))), inference(resolution, [status(thm)], [c_117, c_4])).
% 3.91/1.63  tff(c_150, plain, (![A_336, B_337]: (~v1_xboole_0(u1_struct_0(A_336)) | ~m1_subset_1(B_337, u1_struct_0(A_336)) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(resolution, [status(thm)], [c_16, c_140])).
% 3.91/1.63  tff(c_162, plain, (~v1_xboole_0(u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_46, c_150])).
% 3.91/1.63  tff(c_171, plain, (~v1_xboole_0(u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_94, c_162])).
% 3.91/1.63  tff(c_172, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_54, c_171])).
% 3.91/1.63  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.63  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_52, plain, (v1_tsep_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_36, plain, (![B_62, A_60]: (m1_subset_1(u1_struct_0(B_62), k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_pre_topc(B_62, A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.91/1.63  tff(c_197, plain, (![B_349, A_350]: (v3_pre_topc(u1_struct_0(B_349), A_350) | ~v1_tsep_1(B_349, A_350) | ~m1_subset_1(u1_struct_0(B_349), k1_zfmisc_1(u1_struct_0(A_350))) | ~m1_pre_topc(B_349, A_350) | ~l1_pre_topc(A_350) | ~v2_pre_topc(A_350))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.91/1.63  tff(c_201, plain, (![B_62, A_60]: (v3_pre_topc(u1_struct_0(B_62), A_60) | ~v1_tsep_1(B_62, A_60) | ~v2_pre_topc(A_60) | ~m1_pre_topc(B_62, A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_36, c_197])).
% 3.91/1.63  tff(c_226, plain, (![A_361, B_362, C_363]: (r1_tarski('#skF_1'(A_361, B_362, C_363), B_362) | ~r2_hidden(C_363, B_362) | ~m1_subset_1(C_363, u1_struct_0(A_361)) | ~v3_pre_topc(B_362, A_361) | ~m1_subset_1(B_362, k1_zfmisc_1(u1_struct_0(A_361))) | ~l1_pre_topc(A_361) | ~v2_pre_topc(A_361) | v2_struct_0(A_361))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.91/1.63  tff(c_232, plain, (![A_60, B_62, C_363]: (r1_tarski('#skF_1'(A_60, u1_struct_0(B_62), C_363), u1_struct_0(B_62)) | ~r2_hidden(C_363, u1_struct_0(B_62)) | ~m1_subset_1(C_363, u1_struct_0(A_60)) | ~v3_pre_topc(u1_struct_0(B_62), A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_62, A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_36, c_226])).
% 3.91/1.63  tff(c_28, plain, (![A_28, B_42, C_49]: (m1_subset_1('#skF_1'(A_28, B_42, C_49), k1_zfmisc_1(u1_struct_0(A_28))) | ~r2_hidden(C_49, B_42) | ~m1_subset_1(C_49, u1_struct_0(A_28)) | ~v3_pre_topc(B_42, A_28) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.91/1.63  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_80, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_81, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_80])).
% 3.91/1.63  tff(c_113, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_81])).
% 3.91/1.63  tff(c_74, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_83, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_74])).
% 3.91/1.63  tff(c_115, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_83])).
% 3.91/1.63  tff(c_70, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_68, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_58, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_288])).
% 3.91/1.63  tff(c_384, plain, (![B_438, D_435, A_436, E_437, G_439, C_440]: (r1_tmap_1(B_438, A_436, C_440, G_439) | ~r1_tmap_1(D_435, A_436, k2_tmap_1(B_438, A_436, C_440, D_435), G_439) | ~m1_connsp_2(E_437, B_438, G_439) | ~r1_tarski(E_437, u1_struct_0(D_435)) | ~m1_subset_1(G_439, u1_struct_0(D_435)) | ~m1_subset_1(G_439, u1_struct_0(B_438)) | ~m1_subset_1(E_437, k1_zfmisc_1(u1_struct_0(B_438))) | ~m1_pre_topc(D_435, B_438) | v2_struct_0(D_435) | ~m1_subset_1(C_440, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_438), u1_struct_0(A_436)))) | ~v1_funct_2(C_440, u1_struct_0(B_438), u1_struct_0(A_436)) | ~v1_funct_1(C_440) | ~l1_pre_topc(B_438) | ~v2_pre_topc(B_438) | v2_struct_0(B_438) | ~l1_pre_topc(A_436) | ~v2_pre_topc(A_436) | v2_struct_0(A_436))), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.91/1.63  tff(c_388, plain, (![E_437]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_437, '#skF_4', '#skF_8') | ~r1_tarski(E_437, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_437, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_113, c_384])).
% 3.91/1.63  tff(c_395, plain, (![E_437]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_437, '#skF_4', '#skF_8') | ~r1_tarski(E_437, u1_struct_0('#skF_6')) | ~m1_subset_1(E_437, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_56, c_50, c_82, c_46, c_388])).
% 3.91/1.63  tff(c_397, plain, (![E_441]: (~m1_connsp_2(E_441, '#skF_4', '#skF_8') | ~r1_tarski(E_441, u1_struct_0('#skF_6')) | ~m1_subset_1(E_441, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_54, c_115, c_395])).
% 3.91/1.63  tff(c_409, plain, (![B_42, C_49]: (~m1_connsp_2('#skF_1'('#skF_4', B_42, C_49), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', B_42, C_49), u1_struct_0('#skF_6')) | ~r2_hidden(C_49, B_42) | ~m1_subset_1(C_49, u1_struct_0('#skF_4')) | ~v3_pre_topc(B_42, '#skF_4') | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_397])).
% 3.91/1.63  tff(c_428, plain, (![B_42, C_49]: (~m1_connsp_2('#skF_1'('#skF_4', B_42, C_49), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', B_42, C_49), u1_struct_0('#skF_6')) | ~r2_hidden(C_49, B_42) | ~m1_subset_1(C_49, u1_struct_0('#skF_4')) | ~v3_pre_topc(B_42, '#skF_4') | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_409])).
% 3.91/1.63  tff(c_439, plain, (![B_444, C_445]: (~m1_connsp_2('#skF_1'('#skF_4', B_444, C_445), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', B_444, C_445), u1_struct_0('#skF_6')) | ~r2_hidden(C_445, B_444) | ~m1_subset_1(C_445, u1_struct_0('#skF_4')) | ~v3_pre_topc(B_444, '#skF_4') | ~m1_subset_1(B_444, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_428])).
% 3.91/1.63  tff(c_443, plain, (![C_363]: (~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_363), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_363, u1_struct_0('#skF_6')) | ~m1_subset_1(C_363, u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_232, c_439])).
% 3.91/1.63  tff(c_446, plain, (![C_363]: (~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_363), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_363, u1_struct_0('#skF_6')) | ~m1_subset_1(C_363, u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_443])).
% 3.91/1.63  tff(c_447, plain, (![C_363]: (~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_363), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_363, u1_struct_0('#skF_6')) | ~m1_subset_1(C_363, u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_446])).
% 3.91/1.63  tff(c_448, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_447])).
% 3.91/1.63  tff(c_454, plain, (~v1_tsep_1('#skF_6', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_201, c_448])).
% 3.91/1.63  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_52, c_454])).
% 3.91/1.63  tff(c_464, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_447])).
% 3.91/1.63  tff(c_255, plain, (![A_381, B_382, C_383]: (m1_connsp_2('#skF_1'(A_381, B_382, C_383), A_381, C_383) | ~r2_hidden(C_383, B_382) | ~m1_subset_1(C_383, u1_struct_0(A_381)) | ~v3_pre_topc(B_382, A_381) | ~m1_subset_1(B_382, k1_zfmisc_1(u1_struct_0(A_381))) | ~l1_pre_topc(A_381) | ~v2_pre_topc(A_381) | v2_struct_0(A_381))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.91/1.63  tff(c_261, plain, (![A_60, B_62, C_383]: (m1_connsp_2('#skF_1'(A_60, u1_struct_0(B_62), C_383), A_60, C_383) | ~r2_hidden(C_383, u1_struct_0(B_62)) | ~m1_subset_1(C_383, u1_struct_0(A_60)) | ~v3_pre_topc(u1_struct_0(B_62), A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_62, A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_36, c_255])).
% 3.91/1.63  tff(c_463, plain, (![C_363]: (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_363), '#skF_4', '#skF_8') | ~r2_hidden(C_363, u1_struct_0('#skF_6')) | ~m1_subset_1(C_363, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_447])).
% 3.91/1.63  tff(c_471, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_463])).
% 3.91/1.63  tff(c_474, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_471])).
% 3.91/1.63  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_474])).
% 3.91/1.63  tff(c_529, plain, (![C_451]: (~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_451), '#skF_4', '#skF_8') | ~r2_hidden(C_451, u1_struct_0('#skF_6')) | ~m1_subset_1(C_451, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_463])).
% 3.91/1.63  tff(c_537, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_261, c_529])).
% 3.91/1.63  tff(c_543, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_464, c_82, c_537])).
% 3.91/1.63  tff(c_544, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_543])).
% 3.91/1.63  tff(c_547, plain, (v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_2, c_544])).
% 3.91/1.63  tff(c_550, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_547])).
% 3.91/1.63  tff(c_552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_550])).
% 3.91/1.63  tff(c_553, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 3.91/1.63  tff(c_729, plain, (![D_521, C_525, F_522, B_523, A_524]: (r1_tmap_1(D_521, A_524, k2_tmap_1(B_523, A_524, C_525, D_521), F_522) | ~r1_tmap_1(B_523, A_524, C_525, F_522) | ~m1_subset_1(F_522, u1_struct_0(D_521)) | ~m1_subset_1(F_522, u1_struct_0(B_523)) | ~m1_pre_topc(D_521, B_523) | v2_struct_0(D_521) | ~m1_subset_1(C_525, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_523), u1_struct_0(A_524)))) | ~v1_funct_2(C_525, u1_struct_0(B_523), u1_struct_0(A_524)) | ~v1_funct_1(C_525) | ~l1_pre_topc(B_523) | ~v2_pre_topc(B_523) | v2_struct_0(B_523) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | v2_struct_0(A_524))), inference(cnfTransformation, [status(thm)], [f_198])).
% 3.91/1.63  tff(c_731, plain, (![D_521, F_522]: (r1_tmap_1(D_521, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_521), F_522) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_522) | ~m1_subset_1(F_522, u1_struct_0(D_521)) | ~m1_subset_1(F_522, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_521, '#skF_4') | v2_struct_0(D_521) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_729])).
% 3.91/1.63  tff(c_734, plain, (![D_521, F_522]: (r1_tmap_1(D_521, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_521), F_522) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_522) | ~m1_subset_1(F_522, u1_struct_0(D_521)) | ~m1_subset_1(F_522, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_521, '#skF_4') | v2_struct_0(D_521) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_731])).
% 3.91/1.63  tff(c_736, plain, (![D_526, F_527]: (r1_tmap_1(D_526, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_526), F_527) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_527) | ~m1_subset_1(F_527, u1_struct_0(D_526)) | ~m1_subset_1(F_527, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_526, '#skF_4') | v2_struct_0(D_526))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_734])).
% 3.91/1.63  tff(c_554, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 3.91/1.63  tff(c_739, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_736, c_554])).
% 3.91/1.63  tff(c_742, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_82, c_46, c_553, c_739])).
% 3.91/1.63  tff(c_744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_742])).
% 3.91/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.63  
% 3.91/1.63  Inference rules
% 3.91/1.63  ----------------------
% 3.91/1.63  #Ref     : 0
% 3.91/1.63  #Sup     : 124
% 3.91/1.63  #Fact    : 0
% 3.91/1.63  #Define  : 0
% 3.91/1.63  #Split   : 5
% 3.91/1.63  #Chain   : 0
% 3.91/1.63  #Close   : 0
% 3.91/1.63  
% 3.91/1.63  Ordering : KBO
% 3.91/1.63  
% 3.91/1.63  Simplification rules
% 3.91/1.64  ----------------------
% 3.91/1.64  #Subsume      : 26
% 3.91/1.64  #Demod        : 115
% 3.91/1.64  #Tautology    : 14
% 3.91/1.64  #SimpNegUnit  : 35
% 3.91/1.64  #BackRed      : 0
% 3.91/1.64  
% 3.91/1.64  #Partial instantiations: 0
% 3.91/1.64  #Strategies tried      : 1
% 3.91/1.64  
% 3.91/1.64  Timing (in seconds)
% 3.91/1.64  ----------------------
% 3.91/1.64  Preprocessing        : 0.40
% 3.91/1.64  Parsing              : 0.20
% 3.91/1.64  CNF conversion       : 0.05
% 3.91/1.64  Main loop            : 0.46
% 3.91/1.64  Inferencing          : 0.18
% 3.91/1.64  Reduction            : 0.13
% 3.91/1.64  Demodulation         : 0.09
% 3.91/1.64  BG Simplification    : 0.03
% 3.91/1.64  Subsumption          : 0.09
% 3.91/1.64  Abstraction          : 0.02
% 3.91/1.64  MUC search           : 0.00
% 3.91/1.64  Cooper               : 0.00
% 3.91/1.64  Total                : 0.90
% 3.91/1.64  Index Insertion      : 0.00
% 3.91/1.64  Index Deletion       : 0.00
% 3.91/1.64  Index Matching       : 0.00
% 3.91/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
