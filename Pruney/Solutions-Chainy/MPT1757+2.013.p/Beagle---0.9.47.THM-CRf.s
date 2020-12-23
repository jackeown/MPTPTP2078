%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:05 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 489 expanded)
%              Number of leaves         :   41 ( 205 expanded)
%              Depth                    :   20
%              Number of atoms          :  416 (3590 expanded)
%              Number of equality atoms :    5 ( 171 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_294,negated_conjecture,(
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

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_164,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_157,axiom,(
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

tff(f_139,axiom,(
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

tff(f_251,axiom,(
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

tff(f_204,axiom,(
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
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_50,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_48,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_44,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_46,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_81,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_64,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_62,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_95,plain,(
    ! [B_319,A_320] :
      ( v2_pre_topc(B_319)
      | ~ m1_pre_topc(B_319,A_320)
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,
    ( v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_95])).

tff(c_101,plain,(
    v2_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_98])).

tff(c_88,plain,(
    ! [B_317,A_318] :
      ( l1_pre_topc(B_317)
      | ~ m1_pre_topc(B_317,A_318)
      | ~ l1_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_94,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91])).

tff(c_14,plain,(
    ! [A_25,B_26] :
      ( m1_connsp_2('#skF_1'(A_25,B_26),A_25,B_26)
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_154,plain,(
    ! [C_346,A_347,B_348] :
      ( m1_subset_1(C_346,k1_zfmisc_1(u1_struct_0(A_347)))
      | ~ m1_connsp_2(C_346,A_347,B_348)
      | ~ m1_subset_1(B_348,u1_struct_0(A_347))
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_157,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1('#skF_1'(A_25,B_26),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_14,c_154])).

tff(c_193,plain,(
    ! [C_366,B_367,A_368] :
      ( r2_hidden(C_366,B_367)
      | ~ m1_connsp_2(B_367,A_368,C_366)
      | ~ m1_subset_1(C_366,u1_struct_0(A_368))
      | ~ m1_subset_1(B_367,k1_zfmisc_1(u1_struct_0(A_368)))
      | ~ l1_pre_topc(A_368)
      | ~ v2_pre_topc(A_368)
      | v2_struct_0(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_197,plain,(
    ! [B_369,A_370] :
      ( r2_hidden(B_369,'#skF_1'(A_370,B_369))
      | ~ m1_subset_1('#skF_1'(A_370,B_369),k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ m1_subset_1(B_369,u1_struct_0(A_370))
      | ~ l1_pre_topc(A_370)
      | ~ v2_pre_topc(A_370)
      | v2_struct_0(A_370) ) ),
    inference(resolution,[status(thm)],[c_14,c_193])).

tff(c_208,plain,(
    ! [B_374,A_375] :
      ( r2_hidden(B_374,'#skF_1'(A_375,B_374))
      | ~ m1_subset_1(B_374,u1_struct_0(A_375))
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(resolution,[status(thm)],[c_157,c_197])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_216,plain,(
    ! [B_376,A_377,A_378] :
      ( r2_hidden(B_376,A_377)
      | ~ m1_subset_1('#skF_1'(A_378,B_376),k1_zfmisc_1(A_377))
      | ~ m1_subset_1(B_376,u1_struct_0(A_378))
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378) ) ),
    inference(resolution,[status(thm)],[c_208,c_2])).

tff(c_220,plain,(
    ! [B_26,A_25] :
      ( r2_hidden(B_26,u1_struct_0(A_25))
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_157,c_216])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_52,plain,(
    v1_tsep_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_36,plain,(
    ! [B_69,A_67] :
      ( m1_subset_1(u1_struct_0(B_69),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_pre_topc(B_69,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_176,plain,(
    ! [B_360,A_361] :
      ( v3_pre_topc(u1_struct_0(B_360),A_361)
      | ~ v1_tsep_1(B_360,A_361)
      | ~ m1_subset_1(u1_struct_0(B_360),k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ m1_pre_topc(B_360,A_361)
      | ~ l1_pre_topc(A_361)
      | ~ v2_pre_topc(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_180,plain,(
    ! [B_69,A_67] :
      ( v3_pre_topc(u1_struct_0(B_69),A_67)
      | ~ v1_tsep_1(B_69,A_67)
      | ~ v2_pre_topc(A_67)
      | ~ m1_pre_topc(B_69,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_36,c_176])).

tff(c_201,plain,(
    ! [A_371,B_372,C_373] :
      ( r1_tarski('#skF_2'(A_371,B_372,C_373),B_372)
      | ~ r2_hidden(C_373,B_372)
      | ~ m1_subset_1(C_373,u1_struct_0(A_371))
      | ~ v3_pre_topc(B_372,A_371)
      | ~ m1_subset_1(B_372,k1_zfmisc_1(u1_struct_0(A_371)))
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371)
      | v2_struct_0(A_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_207,plain,(
    ! [A_67,B_69,C_373] :
      ( r1_tarski('#skF_2'(A_67,u1_struct_0(B_69),C_373),u1_struct_0(B_69))
      | ~ r2_hidden(C_373,u1_struct_0(B_69))
      | ~ m1_subset_1(C_373,u1_struct_0(A_67))
      | ~ v3_pre_topc(u1_struct_0(B_69),A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67)
      | ~ m1_pre_topc(B_69,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_36,c_201])).

tff(c_28,plain,(
    ! [A_35,B_49,C_56] :
      ( m1_subset_1('#skF_2'(A_35,B_49,C_56),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ r2_hidden(C_56,B_49)
      | ~ m1_subset_1(C_56,u1_struct_0(A_35))
      | ~ v3_pre_topc(B_49,A_35)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
    | r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
    | r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_80])).

tff(c_102,plain,(
    r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_74,plain,
    ( ~ r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_83,plain,
    ( ~ r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_74])).

tff(c_114,plain,(
    ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_83])).

tff(c_70,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_58,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_534,plain,(
    ! [G_466,D_465,A_464,E_461,B_463,C_462] :
      ( r1_tmap_1(B_463,A_464,C_462,G_466)
      | ~ r1_tmap_1(D_465,A_464,k2_tmap_1(B_463,A_464,C_462,D_465),G_466)
      | ~ m1_connsp_2(E_461,B_463,G_466)
      | ~ r1_tarski(E_461,u1_struct_0(D_465))
      | ~ m1_subset_1(G_466,u1_struct_0(D_465))
      | ~ m1_subset_1(G_466,u1_struct_0(B_463))
      | ~ m1_subset_1(E_461,k1_zfmisc_1(u1_struct_0(B_463)))
      | ~ m1_pre_topc(D_465,B_463)
      | v2_struct_0(D_465)
      | ~ m1_subset_1(C_462,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_463),u1_struct_0(A_464))))
      | ~ v1_funct_2(C_462,u1_struct_0(B_463),u1_struct_0(A_464))
      | ~ v1_funct_1(C_462)
      | ~ l1_pre_topc(B_463)
      | ~ v2_pre_topc(B_463)
      | v2_struct_0(B_463)
      | ~ l1_pre_topc(A_464)
      | ~ v2_pre_topc(A_464)
      | v2_struct_0(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_538,plain,(
    ! [E_461] :
      ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
      | ~ m1_connsp_2(E_461,'#skF_5','#skF_8')
      | ~ r1_tarski(E_461,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_461,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_7','#skF_5')
      | v2_struct_0('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_102,c_534])).

tff(c_545,plain,(
    ! [E_461] :
      ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
      | ~ m1_connsp_2(E_461,'#skF_5','#skF_8')
      | ~ r1_tarski(E_461,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(E_461,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_56,c_50,c_48,c_81,c_538])).

tff(c_547,plain,(
    ! [E_467] :
      ( ~ m1_connsp_2(E_467,'#skF_5','#skF_8')
      | ~ r1_tarski(E_467,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(E_467,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_54,c_114,c_545])).

tff(c_551,plain,(
    ! [B_49,C_56] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_49,C_56),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_5',B_49,C_56),u1_struct_0('#skF_7'))
      | ~ r2_hidden(C_56,B_49)
      | ~ m1_subset_1(C_56,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(B_49,'#skF_5')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_547])).

tff(c_562,plain,(
    ! [B_49,C_56] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_49,C_56),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_5',B_49,C_56),u1_struct_0('#skF_7'))
      | ~ r2_hidden(C_56,B_49)
      | ~ m1_subset_1(C_56,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(B_49,'#skF_5')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_551])).

tff(c_644,plain,(
    ! [B_499,C_500] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_499,C_500),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_5',B_499,C_500),u1_struct_0('#skF_7'))
      | ~ r2_hidden(C_500,B_499)
      | ~ m1_subset_1(C_500,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(B_499,'#skF_5')
      | ~ m1_subset_1(B_499,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_562])).

tff(c_648,plain,(
    ! [C_373] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',u1_struct_0('#skF_7'),C_373),'#skF_5','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_373,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_373,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_7','#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_207,c_644])).

tff(c_651,plain,(
    ! [C_373] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',u1_struct_0('#skF_7'),C_373),'#skF_5','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_373,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_373,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_648])).

tff(c_652,plain,(
    ! [C_373] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',u1_struct_0('#skF_7'),C_373),'#skF_5','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_373,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_373,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_651])).

tff(c_653,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_652])).

tff(c_656,plain,
    ( ~ v1_tsep_1('#skF_7','#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_180,c_653])).

tff(c_660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_52,c_656])).

tff(c_662,plain,(
    v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_228,plain,(
    ! [A_381,B_382,C_383] :
      ( m1_connsp_2('#skF_2'(A_381,B_382,C_383),A_381,C_383)
      | ~ r2_hidden(C_383,B_382)
      | ~ m1_subset_1(C_383,u1_struct_0(A_381))
      | ~ v3_pre_topc(B_382,A_381)
      | ~ m1_subset_1(B_382,k1_zfmisc_1(u1_struct_0(A_381)))
      | ~ l1_pre_topc(A_381)
      | ~ v2_pre_topc(A_381)
      | v2_struct_0(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_234,plain,(
    ! [A_67,B_69,C_383] :
      ( m1_connsp_2('#skF_2'(A_67,u1_struct_0(B_69),C_383),A_67,C_383)
      | ~ r2_hidden(C_383,u1_struct_0(B_69))
      | ~ m1_subset_1(C_383,u1_struct_0(A_67))
      | ~ v3_pre_topc(u1_struct_0(B_69),A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67)
      | ~ m1_pre_topc(B_69,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_36,c_228])).

tff(c_661,plain,(
    ! [C_373] :
      ( ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_connsp_2('#skF_2'('#skF_5',u1_struct_0('#skF_7'),C_373),'#skF_5','#skF_8')
      | ~ r2_hidden(C_373,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_373,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_669,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_661])).

tff(c_672,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_669])).

tff(c_676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_672])).

tff(c_963,plain,(
    ! [C_518] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',u1_struct_0('#skF_7'),C_518),'#skF_5','#skF_8')
      | ~ r2_hidden(C_518,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_518,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_661])).

tff(c_971,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_234,c_963])).

tff(c_977,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_662,c_48,c_971])).

tff(c_978,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_977])).

tff(c_990,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_220,c_978])).

tff(c_1002,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_94,c_81,c_990])).

tff(c_1004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1002])).

tff(c_1005,plain,(
    r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1411,plain,(
    ! [B_650,F_648,D_649,A_647,C_646] :
      ( r1_tmap_1(D_649,A_647,k2_tmap_1(B_650,A_647,C_646,D_649),F_648)
      | ~ r1_tmap_1(B_650,A_647,C_646,F_648)
      | ~ m1_subset_1(F_648,u1_struct_0(D_649))
      | ~ m1_subset_1(F_648,u1_struct_0(B_650))
      | ~ m1_pre_topc(D_649,B_650)
      | v2_struct_0(D_649)
      | ~ m1_subset_1(C_646,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_650),u1_struct_0(A_647))))
      | ~ v1_funct_2(C_646,u1_struct_0(B_650),u1_struct_0(A_647))
      | ~ v1_funct_1(C_646)
      | ~ l1_pre_topc(B_650)
      | ~ v2_pre_topc(B_650)
      | v2_struct_0(B_650)
      | ~ l1_pre_topc(A_647)
      | ~ v2_pre_topc(A_647)
      | v2_struct_0(A_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_1413,plain,(
    ! [D_649,F_648] :
      ( r1_tmap_1(D_649,'#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6',D_649),F_648)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6',F_648)
      | ~ m1_subset_1(F_648,u1_struct_0(D_649))
      | ~ m1_subset_1(F_648,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_649,'#skF_5')
      | v2_struct_0(D_649)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_1411])).

tff(c_1416,plain,(
    ! [D_649,F_648] :
      ( r1_tmap_1(D_649,'#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6',D_649),F_648)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6',F_648)
      | ~ m1_subset_1(F_648,u1_struct_0(D_649))
      | ~ m1_subset_1(F_648,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_649,'#skF_5')
      | v2_struct_0(D_649)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_1413])).

tff(c_1449,plain,(
    ! [D_659,F_660] :
      ( r1_tmap_1(D_659,'#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6',D_659),F_660)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6',F_660)
      | ~ m1_subset_1(F_660,u1_struct_0(D_659))
      | ~ m1_subset_1(F_660,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_659,'#skF_5')
      | v2_struct_0(D_659) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_1416])).

tff(c_1006,plain,(
    ~ r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1452,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1449,c_1006])).

tff(c_1455,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_81,c_1005,c_1452])).

tff(c_1457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1455])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:05:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.91  
% 4.68/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.91  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 4.68/1.91  
% 4.68/1.91  %Foreground sorts:
% 4.68/1.91  
% 4.68/1.91  
% 4.68/1.91  %Background operators:
% 4.68/1.91  
% 4.68/1.91  
% 4.68/1.91  %Foreground operators:
% 4.68/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.68/1.91  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.68/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.68/1.91  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.91  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.68/1.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.68/1.91  tff('#skF_7', type, '#skF_7': $i).
% 4.68/1.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.68/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.68/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.68/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.68/1.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.68/1.91  tff('#skF_9', type, '#skF_9': $i).
% 4.68/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.91  tff('#skF_8', type, '#skF_8': $i).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.68/1.91  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.68/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.91  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.68/1.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.68/1.91  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.68/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.68/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.68/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.91  
% 5.02/1.93  tff(f_294, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 5.02/1.93  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.02/1.93  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.02/1.93  tff(f_96, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 5.02/1.93  tff(f_84, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 5.02/1.93  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 5.02/1.93  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.02/1.93  tff(f_164, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.02/1.93  tff(f_157, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 5.02/1.93  tff(f_139, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 5.02/1.93  tff(f_251, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 5.02/1.93  tff(f_204, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 5.02/1.93  tff(c_54, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_50, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_48, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_44, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_46, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_81, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 5.02/1.93  tff(c_64, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_62, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_95, plain, (![B_319, A_320]: (v2_pre_topc(B_319) | ~m1_pre_topc(B_319, A_320) | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.02/1.93  tff(c_98, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_50, c_95])).
% 5.02/1.93  tff(c_101, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_98])).
% 5.02/1.93  tff(c_88, plain, (![B_317, A_318]: (l1_pre_topc(B_317) | ~m1_pre_topc(B_317, A_318) | ~l1_pre_topc(A_318))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.02/1.93  tff(c_91, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_50, c_88])).
% 5.02/1.93  tff(c_94, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91])).
% 5.02/1.93  tff(c_14, plain, (![A_25, B_26]: (m1_connsp_2('#skF_1'(A_25, B_26), A_25, B_26) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.02/1.93  tff(c_154, plain, (![C_346, A_347, B_348]: (m1_subset_1(C_346, k1_zfmisc_1(u1_struct_0(A_347))) | ~m1_connsp_2(C_346, A_347, B_348) | ~m1_subset_1(B_348, u1_struct_0(A_347)) | ~l1_pre_topc(A_347) | ~v2_pre_topc(A_347) | v2_struct_0(A_347))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.02/1.93  tff(c_157, plain, (![A_25, B_26]: (m1_subset_1('#skF_1'(A_25, B_26), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_14, c_154])).
% 5.02/1.93  tff(c_193, plain, (![C_366, B_367, A_368]: (r2_hidden(C_366, B_367) | ~m1_connsp_2(B_367, A_368, C_366) | ~m1_subset_1(C_366, u1_struct_0(A_368)) | ~m1_subset_1(B_367, k1_zfmisc_1(u1_struct_0(A_368))) | ~l1_pre_topc(A_368) | ~v2_pre_topc(A_368) | v2_struct_0(A_368))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.02/1.93  tff(c_197, plain, (![B_369, A_370]: (r2_hidden(B_369, '#skF_1'(A_370, B_369)) | ~m1_subset_1('#skF_1'(A_370, B_369), k1_zfmisc_1(u1_struct_0(A_370))) | ~m1_subset_1(B_369, u1_struct_0(A_370)) | ~l1_pre_topc(A_370) | ~v2_pre_topc(A_370) | v2_struct_0(A_370))), inference(resolution, [status(thm)], [c_14, c_193])).
% 5.02/1.93  tff(c_208, plain, (![B_374, A_375]: (r2_hidden(B_374, '#skF_1'(A_375, B_374)) | ~m1_subset_1(B_374, u1_struct_0(A_375)) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375))), inference(resolution, [status(thm)], [c_157, c_197])).
% 5.02/1.93  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.02/1.93  tff(c_216, plain, (![B_376, A_377, A_378]: (r2_hidden(B_376, A_377) | ~m1_subset_1('#skF_1'(A_378, B_376), k1_zfmisc_1(A_377)) | ~m1_subset_1(B_376, u1_struct_0(A_378)) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378))), inference(resolution, [status(thm)], [c_208, c_2])).
% 5.02/1.93  tff(c_220, plain, (![B_26, A_25]: (r2_hidden(B_26, u1_struct_0(A_25)) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_157, c_216])).
% 5.02/1.93  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_52, plain, (v1_tsep_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_36, plain, (![B_69, A_67]: (m1_subset_1(u1_struct_0(B_69), k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_pre_topc(B_69, A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.02/1.93  tff(c_176, plain, (![B_360, A_361]: (v3_pre_topc(u1_struct_0(B_360), A_361) | ~v1_tsep_1(B_360, A_361) | ~m1_subset_1(u1_struct_0(B_360), k1_zfmisc_1(u1_struct_0(A_361))) | ~m1_pre_topc(B_360, A_361) | ~l1_pre_topc(A_361) | ~v2_pre_topc(A_361))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.02/1.93  tff(c_180, plain, (![B_69, A_67]: (v3_pre_topc(u1_struct_0(B_69), A_67) | ~v1_tsep_1(B_69, A_67) | ~v2_pre_topc(A_67) | ~m1_pre_topc(B_69, A_67) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_36, c_176])).
% 5.02/1.93  tff(c_201, plain, (![A_371, B_372, C_373]: (r1_tarski('#skF_2'(A_371, B_372, C_373), B_372) | ~r2_hidden(C_373, B_372) | ~m1_subset_1(C_373, u1_struct_0(A_371)) | ~v3_pre_topc(B_372, A_371) | ~m1_subset_1(B_372, k1_zfmisc_1(u1_struct_0(A_371))) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371) | v2_struct_0(A_371))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.02/1.93  tff(c_207, plain, (![A_67, B_69, C_373]: (r1_tarski('#skF_2'(A_67, u1_struct_0(B_69), C_373), u1_struct_0(B_69)) | ~r2_hidden(C_373, u1_struct_0(B_69)) | ~m1_subset_1(C_373, u1_struct_0(A_67)) | ~v3_pre_topc(u1_struct_0(B_69), A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67) | ~m1_pre_topc(B_69, A_67) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_36, c_201])).
% 5.02/1.93  tff(c_28, plain, (![A_35, B_49, C_56]: (m1_subset_1('#skF_2'(A_35, B_49, C_56), k1_zfmisc_1(u1_struct_0(A_35))) | ~r2_hidden(C_56, B_49) | ~m1_subset_1(C_56, u1_struct_0(A_35)) | ~v3_pre_topc(B_49, A_35) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.02/1.93  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_80, plain, (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_82, plain, (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_80])).
% 5.02/1.93  tff(c_102, plain, (r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_82])).
% 5.02/1.93  tff(c_74, plain, (~r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_83, plain, (~r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_74])).
% 5.02/1.93  tff(c_114, plain, (~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_83])).
% 5.02/1.93  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_58, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.02/1.93  tff(c_534, plain, (![G_466, D_465, A_464, E_461, B_463, C_462]: (r1_tmap_1(B_463, A_464, C_462, G_466) | ~r1_tmap_1(D_465, A_464, k2_tmap_1(B_463, A_464, C_462, D_465), G_466) | ~m1_connsp_2(E_461, B_463, G_466) | ~r1_tarski(E_461, u1_struct_0(D_465)) | ~m1_subset_1(G_466, u1_struct_0(D_465)) | ~m1_subset_1(G_466, u1_struct_0(B_463)) | ~m1_subset_1(E_461, k1_zfmisc_1(u1_struct_0(B_463))) | ~m1_pre_topc(D_465, B_463) | v2_struct_0(D_465) | ~m1_subset_1(C_462, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_463), u1_struct_0(A_464)))) | ~v1_funct_2(C_462, u1_struct_0(B_463), u1_struct_0(A_464)) | ~v1_funct_1(C_462) | ~l1_pre_topc(B_463) | ~v2_pre_topc(B_463) | v2_struct_0(B_463) | ~l1_pre_topc(A_464) | ~v2_pre_topc(A_464) | v2_struct_0(A_464))), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.02/1.93  tff(c_538, plain, (![E_461]: (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | ~m1_connsp_2(E_461, '#skF_5', '#skF_8') | ~r1_tarski(E_461, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(E_461, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_102, c_534])).
% 5.02/1.93  tff(c_545, plain, (![E_461]: (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | ~m1_connsp_2(E_461, '#skF_5', '#skF_8') | ~r1_tarski(E_461, u1_struct_0('#skF_7')) | ~m1_subset_1(E_461, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_7') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_56, c_50, c_48, c_81, c_538])).
% 5.02/1.93  tff(c_547, plain, (![E_467]: (~m1_connsp_2(E_467, '#skF_5', '#skF_8') | ~r1_tarski(E_467, u1_struct_0('#skF_7')) | ~m1_subset_1(E_467, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_54, c_114, c_545])).
% 5.02/1.93  tff(c_551, plain, (![B_49, C_56]: (~m1_connsp_2('#skF_2'('#skF_5', B_49, C_56), '#skF_5', '#skF_8') | ~r1_tarski('#skF_2'('#skF_5', B_49, C_56), u1_struct_0('#skF_7')) | ~r2_hidden(C_56, B_49) | ~m1_subset_1(C_56, u1_struct_0('#skF_5')) | ~v3_pre_topc(B_49, '#skF_5') | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_547])).
% 5.02/1.93  tff(c_562, plain, (![B_49, C_56]: (~m1_connsp_2('#skF_2'('#skF_5', B_49, C_56), '#skF_5', '#skF_8') | ~r1_tarski('#skF_2'('#skF_5', B_49, C_56), u1_struct_0('#skF_7')) | ~r2_hidden(C_56, B_49) | ~m1_subset_1(C_56, u1_struct_0('#skF_5')) | ~v3_pre_topc(B_49, '#skF_5') | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_551])).
% 5.02/1.93  tff(c_644, plain, (![B_499, C_500]: (~m1_connsp_2('#skF_2'('#skF_5', B_499, C_500), '#skF_5', '#skF_8') | ~r1_tarski('#skF_2'('#skF_5', B_499, C_500), u1_struct_0('#skF_7')) | ~r2_hidden(C_500, B_499) | ~m1_subset_1(C_500, u1_struct_0('#skF_5')) | ~v3_pre_topc(B_499, '#skF_5') | ~m1_subset_1(B_499, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_562])).
% 5.02/1.93  tff(c_648, plain, (![C_373]: (~m1_connsp_2('#skF_2'('#skF_5', u1_struct_0('#skF_7'), C_373), '#skF_5', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_373, u1_struct_0('#skF_7')) | ~m1_subset_1(C_373, u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_207, c_644])).
% 5.02/1.93  tff(c_651, plain, (![C_373]: (~m1_connsp_2('#skF_2'('#skF_5', u1_struct_0('#skF_7'), C_373), '#skF_5', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_373, u1_struct_0('#skF_7')) | ~m1_subset_1(C_373, u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_648])).
% 5.02/1.93  tff(c_652, plain, (![C_373]: (~m1_connsp_2('#skF_2'('#skF_5', u1_struct_0('#skF_7'), C_373), '#skF_5', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_373, u1_struct_0('#skF_7')) | ~m1_subset_1(C_373, u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_651])).
% 5.02/1.93  tff(c_653, plain, (~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_652])).
% 5.02/1.93  tff(c_656, plain, (~v1_tsep_1('#skF_7', '#skF_5') | ~v2_pre_topc('#skF_5') | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_180, c_653])).
% 5.02/1.93  tff(c_660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_52, c_656])).
% 5.02/1.93  tff(c_662, plain, (v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_652])).
% 5.02/1.93  tff(c_228, plain, (![A_381, B_382, C_383]: (m1_connsp_2('#skF_2'(A_381, B_382, C_383), A_381, C_383) | ~r2_hidden(C_383, B_382) | ~m1_subset_1(C_383, u1_struct_0(A_381)) | ~v3_pre_topc(B_382, A_381) | ~m1_subset_1(B_382, k1_zfmisc_1(u1_struct_0(A_381))) | ~l1_pre_topc(A_381) | ~v2_pre_topc(A_381) | v2_struct_0(A_381))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.02/1.93  tff(c_234, plain, (![A_67, B_69, C_383]: (m1_connsp_2('#skF_2'(A_67, u1_struct_0(B_69), C_383), A_67, C_383) | ~r2_hidden(C_383, u1_struct_0(B_69)) | ~m1_subset_1(C_383, u1_struct_0(A_67)) | ~v3_pre_topc(u1_struct_0(B_69), A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67) | ~m1_pre_topc(B_69, A_67) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_36, c_228])).
% 5.02/1.93  tff(c_661, plain, (![C_373]: (~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_connsp_2('#skF_2'('#skF_5', u1_struct_0('#skF_7'), C_373), '#skF_5', '#skF_8') | ~r2_hidden(C_373, u1_struct_0('#skF_7')) | ~m1_subset_1(C_373, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_652])).
% 5.02/1.93  tff(c_669, plain, (~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_661])).
% 5.02/1.93  tff(c_672, plain, (~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_36, c_669])).
% 5.02/1.93  tff(c_676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_672])).
% 5.02/1.93  tff(c_963, plain, (![C_518]: (~m1_connsp_2('#skF_2'('#skF_5', u1_struct_0('#skF_7'), C_518), '#skF_5', '#skF_8') | ~r2_hidden(C_518, u1_struct_0('#skF_7')) | ~m1_subset_1(C_518, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_661])).
% 5.02/1.93  tff(c_971, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_234, c_963])).
% 5.02/1.93  tff(c_977, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_662, c_48, c_971])).
% 5.02/1.93  tff(c_978, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_66, c_977])).
% 5.02/1.93  tff(c_990, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_220, c_978])).
% 5.02/1.93  tff(c_1002, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_94, c_81, c_990])).
% 5.02/1.93  tff(c_1004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1002])).
% 5.02/1.93  tff(c_1005, plain, (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_82])).
% 5.02/1.93  tff(c_1411, plain, (![B_650, F_648, D_649, A_647, C_646]: (r1_tmap_1(D_649, A_647, k2_tmap_1(B_650, A_647, C_646, D_649), F_648) | ~r1_tmap_1(B_650, A_647, C_646, F_648) | ~m1_subset_1(F_648, u1_struct_0(D_649)) | ~m1_subset_1(F_648, u1_struct_0(B_650)) | ~m1_pre_topc(D_649, B_650) | v2_struct_0(D_649) | ~m1_subset_1(C_646, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_650), u1_struct_0(A_647)))) | ~v1_funct_2(C_646, u1_struct_0(B_650), u1_struct_0(A_647)) | ~v1_funct_1(C_646) | ~l1_pre_topc(B_650) | ~v2_pre_topc(B_650) | v2_struct_0(B_650) | ~l1_pre_topc(A_647) | ~v2_pre_topc(A_647) | v2_struct_0(A_647))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.02/1.93  tff(c_1413, plain, (![D_649, F_648]: (r1_tmap_1(D_649, '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', D_649), F_648) | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', F_648) | ~m1_subset_1(F_648, u1_struct_0(D_649)) | ~m1_subset_1(F_648, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_649, '#skF_5') | v2_struct_0(D_649) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_1411])).
% 5.02/1.93  tff(c_1416, plain, (![D_649, F_648]: (r1_tmap_1(D_649, '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', D_649), F_648) | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', F_648) | ~m1_subset_1(F_648, u1_struct_0(D_649)) | ~m1_subset_1(F_648, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_649, '#skF_5') | v2_struct_0(D_649) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_1413])).
% 5.02/1.93  tff(c_1449, plain, (![D_659, F_660]: (r1_tmap_1(D_659, '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', D_659), F_660) | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', F_660) | ~m1_subset_1(F_660, u1_struct_0(D_659)) | ~m1_subset_1(F_660, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_659, '#skF_5') | v2_struct_0(D_659))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_1416])).
% 5.02/1.93  tff(c_1006, plain, (~r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_82])).
% 5.02/1.93  tff(c_1452, plain, (~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1449, c_1006])).
% 5.02/1.93  tff(c_1455, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_81, c_1005, c_1452])).
% 5.02/1.93  tff(c_1457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1455])).
% 5.02/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/1.93  
% 5.02/1.93  Inference rules
% 5.02/1.93  ----------------------
% 5.02/1.93  #Ref     : 0
% 5.02/1.93  #Sup     : 269
% 5.02/1.93  #Fact    : 0
% 5.02/1.93  #Define  : 0
% 5.02/1.93  #Split   : 6
% 5.02/1.93  #Chain   : 0
% 5.02/1.93  #Close   : 0
% 5.02/1.93  
% 5.02/1.93  Ordering : KBO
% 5.02/1.93  
% 5.02/1.93  Simplification rules
% 5.02/1.93  ----------------------
% 5.02/1.93  #Subsume      : 46
% 5.02/1.93  #Demod        : 207
% 5.02/1.93  #Tautology    : 26
% 5.02/1.93  #SimpNegUnit  : 69
% 5.02/1.93  #BackRed      : 0
% 5.02/1.93  
% 5.02/1.93  #Partial instantiations: 0
% 5.02/1.93  #Strategies tried      : 1
% 5.02/1.93  
% 5.02/1.93  Timing (in seconds)
% 5.02/1.93  ----------------------
% 5.02/1.94  Preprocessing        : 0.43
% 5.02/1.94  Parsing              : 0.23
% 5.02/1.94  CNF conversion       : 0.05
% 5.02/1.94  Main loop            : 0.66
% 5.02/1.94  Inferencing          : 0.25
% 5.02/1.94  Reduction            : 0.18
% 5.02/1.94  Demodulation         : 0.12
% 5.02/1.94  BG Simplification    : 0.03
% 5.02/1.94  Subsumption          : 0.16
% 5.02/1.94  Abstraction          : 0.02
% 5.02/1.94  MUC search           : 0.00
% 5.02/1.94  Cooper               : 0.00
% 5.02/1.94  Total                : 1.13
% 5.02/1.94  Index Insertion      : 0.00
% 5.02/1.94  Index Deletion       : 0.00
% 5.02/1.94  Index Matching       : 0.00
% 5.02/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
