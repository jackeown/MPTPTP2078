%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:06 EST 2020

% Result     : Theorem 5.38s
% Output     : CNFRefutation 5.64s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 500 expanded)
%              Number of leaves         :   43 ( 209 expanded)
%              Depth                    :   21
%              Number of atoms          :  432 (3638 expanded)
%              Number of equality atoms :    5 ( 174 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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

tff(c_96,plain,(
    ! [B_319,A_320] :
      ( v2_pre_topc(B_319)
      | ~ m1_pre_topc(B_319,A_320)
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_99,plain,
    ( v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_96])).

tff(c_102,plain,(
    v2_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_99])).

tff(c_88,plain,(
    ! [B_315,A_316] :
      ( l1_pre_topc(B_315)
      | ~ m1_pre_topc(B_315,A_316)
      | ~ l1_pre_topc(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_94,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91])).

tff(c_14,plain,(
    ! [A_23,B_24] :
      ( m1_connsp_2('#skF_1'(A_23,B_24),A_23,B_24)
      | ~ m1_subset_1(B_24,u1_struct_0(A_23))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_153,plain,(
    ! [C_342,A_343,B_344] :
      ( m1_subset_1(C_342,k1_zfmisc_1(u1_struct_0(A_343)))
      | ~ m1_connsp_2(C_342,A_343,B_344)
      | ~ m1_subset_1(B_344,u1_struct_0(A_343))
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_156,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1('#skF_1'(A_23,B_24),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_24,u1_struct_0(A_23))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_14,c_153])).

tff(c_191,plain,(
    ! [C_362,B_363,A_364] :
      ( r2_hidden(C_362,B_363)
      | ~ m1_connsp_2(B_363,A_364,C_362)
      | ~ m1_subset_1(C_362,u1_struct_0(A_364))
      | ~ m1_subset_1(B_363,k1_zfmisc_1(u1_struct_0(A_364)))
      | ~ l1_pre_topc(A_364)
      | ~ v2_pre_topc(A_364)
      | v2_struct_0(A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_202,plain,(
    ! [B_368,A_369] :
      ( r2_hidden(B_368,'#skF_1'(A_369,B_368))
      | ~ m1_subset_1('#skF_1'(A_369,B_368),k1_zfmisc_1(u1_struct_0(A_369)))
      | ~ m1_subset_1(B_368,u1_struct_0(A_369))
      | ~ l1_pre_topc(A_369)
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(resolution,[status(thm)],[c_14,c_191])).

tff(c_206,plain,(
    ! [B_370,A_371] :
      ( r2_hidden(B_370,'#skF_1'(A_371,B_370))
      | ~ m1_subset_1(B_370,u1_struct_0(A_371))
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371)
      | v2_struct_0(A_371) ) ),
    inference(resolution,[status(thm)],[c_156,c_202])).

tff(c_157,plain,(
    ! [A_345,B_346] :
      ( m1_subset_1('#skF_1'(A_345,B_346),k1_zfmisc_1(u1_struct_0(A_345)))
      | ~ m1_subset_1(B_346,u1_struct_0(A_345))
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(resolution,[status(thm)],[c_14,c_153])).

tff(c_4,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_163,plain,(
    ! [A_345,A_3,B_346] :
      ( ~ v1_xboole_0(u1_struct_0(A_345))
      | ~ r2_hidden(A_3,'#skF_1'(A_345,B_346))
      | ~ m1_subset_1(B_346,u1_struct_0(A_345))
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(resolution,[status(thm)],[c_157,c_4])).

tff(c_211,plain,(
    ! [A_372,B_373] :
      ( ~ v1_xboole_0(u1_struct_0(A_372))
      | ~ m1_subset_1(B_373,u1_struct_0(A_372))
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(resolution,[status(thm)],[c_206,c_163])).

tff(c_223,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_7'))
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_81,c_211])).

tff(c_232,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_94,c_223])).

tff(c_233,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_232])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_52,plain,(
    v1_tsep_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_36,plain,(
    ! [B_67,A_65] :
      ( m1_subset_1(u1_struct_0(B_67),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_pre_topc(B_67,A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_175,plain,(
    ! [B_352,A_353] :
      ( v3_pre_topc(u1_struct_0(B_352),A_353)
      | ~ v1_tsep_1(B_352,A_353)
      | ~ m1_subset_1(u1_struct_0(B_352),k1_zfmisc_1(u1_struct_0(A_353)))
      | ~ m1_pre_topc(B_352,A_353)
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_179,plain,(
    ! [B_67,A_65] :
      ( v3_pre_topc(u1_struct_0(B_67),A_65)
      | ~ v1_tsep_1(B_67,A_65)
      | ~ v2_pre_topc(A_65)
      | ~ m1_pre_topc(B_67,A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_36,c_175])).

tff(c_195,plain,(
    ! [A_365,B_366,C_367] :
      ( r1_tarski('#skF_2'(A_365,B_366,C_367),B_366)
      | ~ r2_hidden(C_367,B_366)
      | ~ m1_subset_1(C_367,u1_struct_0(A_365))
      | ~ v3_pre_topc(B_366,A_365)
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_201,plain,(
    ! [A_65,B_67,C_367] :
      ( r1_tarski('#skF_2'(A_65,u1_struct_0(B_67),C_367),u1_struct_0(B_67))
      | ~ r2_hidden(C_367,u1_struct_0(B_67))
      | ~ m1_subset_1(C_367,u1_struct_0(A_65))
      | ~ v3_pre_topc(u1_struct_0(B_67),A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65)
      | ~ m1_pre_topc(B_67,A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_36,c_195])).

tff(c_28,plain,(
    ! [A_33,B_47,C_54] :
      ( m1_subset_1('#skF_2'(A_33,B_47,C_54),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ r2_hidden(C_54,B_47)
      | ~ m1_subset_1(C_54,u1_struct_0(A_33))
      | ~ v3_pre_topc(B_47,A_33)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_74,plain,
    ( ~ r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_83,plain,
    ( ~ r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_74])).

tff(c_103,plain,(
    ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_83])).

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

tff(c_80,plain,
    ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
    | r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
    | r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_80])).

tff(c_114,plain,(
    r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_82])).

tff(c_342,plain,(
    ! [B_420,C_421,E_419,A_418,D_423,G_422] :
      ( r1_tmap_1(B_420,A_418,C_421,G_422)
      | ~ r1_tmap_1(D_423,A_418,k2_tmap_1(B_420,A_418,C_421,D_423),G_422)
      | ~ m1_connsp_2(E_419,B_420,G_422)
      | ~ r1_tarski(E_419,u1_struct_0(D_423))
      | ~ m1_subset_1(G_422,u1_struct_0(D_423))
      | ~ m1_subset_1(G_422,u1_struct_0(B_420))
      | ~ m1_subset_1(E_419,k1_zfmisc_1(u1_struct_0(B_420)))
      | ~ m1_pre_topc(D_423,B_420)
      | v2_struct_0(D_423)
      | ~ m1_subset_1(C_421,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_420),u1_struct_0(A_418))))
      | ~ v1_funct_2(C_421,u1_struct_0(B_420),u1_struct_0(A_418))
      | ~ v1_funct_1(C_421)
      | ~ l1_pre_topc(B_420)
      | ~ v2_pre_topc(B_420)
      | v2_struct_0(B_420)
      | ~ l1_pre_topc(A_418)
      | ~ v2_pre_topc(A_418)
      | v2_struct_0(A_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_346,plain,(
    ! [E_419] :
      ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
      | ~ m1_connsp_2(E_419,'#skF_5','#skF_8')
      | ~ r1_tarski(E_419,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_419,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_114,c_342])).

tff(c_353,plain,(
    ! [E_419] :
      ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
      | ~ m1_connsp_2(E_419,'#skF_5','#skF_8')
      | ~ r1_tarski(E_419,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(E_419,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_56,c_50,c_48,c_81,c_346])).

tff(c_355,plain,(
    ! [E_424] :
      ( ~ m1_connsp_2(E_424,'#skF_5','#skF_8')
      | ~ r1_tarski(E_424,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(E_424,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_54,c_103,c_353])).

tff(c_363,plain,(
    ! [B_47,C_54] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_47,C_54),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_5',B_47,C_54),u1_struct_0('#skF_7'))
      | ~ r2_hidden(C_54,B_47)
      | ~ m1_subset_1(C_54,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(B_47,'#skF_5')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_355])).

tff(c_378,plain,(
    ! [B_47,C_54] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_47,C_54),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_5',B_47,C_54),u1_struct_0('#skF_7'))
      | ~ r2_hidden(C_54,B_47)
      | ~ m1_subset_1(C_54,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(B_47,'#skF_5')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_363])).

tff(c_389,plain,(
    ! [B_427,C_428] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_427,C_428),'#skF_5','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_5',B_427,C_428),u1_struct_0('#skF_7'))
      | ~ r2_hidden(C_428,B_427)
      | ~ m1_subset_1(C_428,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(B_427,'#skF_5')
      | ~ m1_subset_1(B_427,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_378])).

tff(c_393,plain,(
    ! [C_367] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',u1_struct_0('#skF_7'),C_367),'#skF_5','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_367,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_367,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_7','#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_201,c_389])).

tff(c_396,plain,(
    ! [C_367] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',u1_struct_0('#skF_7'),C_367),'#skF_5','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_367,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_367,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_393])).

tff(c_397,plain,(
    ! [C_367] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',u1_struct_0('#skF_7'),C_367),'#skF_5','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_367,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_367,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_396])).

tff(c_398,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_397])).

tff(c_405,plain,
    ( ~ v1_tsep_1('#skF_7','#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_179,c_398])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_52,c_405])).

tff(c_415,plain,(
    v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_397])).

tff(c_254,plain,(
    ! [A_380,B_381,C_382] :
      ( m1_connsp_2('#skF_2'(A_380,B_381,C_382),A_380,C_382)
      | ~ r2_hidden(C_382,B_381)
      | ~ m1_subset_1(C_382,u1_struct_0(A_380))
      | ~ v3_pre_topc(B_381,A_380)
      | ~ m1_subset_1(B_381,k1_zfmisc_1(u1_struct_0(A_380)))
      | ~ l1_pre_topc(A_380)
      | ~ v2_pre_topc(A_380)
      | v2_struct_0(A_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_260,plain,(
    ! [A_65,B_67,C_382] :
      ( m1_connsp_2('#skF_2'(A_65,u1_struct_0(B_67),C_382),A_65,C_382)
      | ~ r2_hidden(C_382,u1_struct_0(B_67))
      | ~ m1_subset_1(C_382,u1_struct_0(A_65))
      | ~ v3_pre_topc(u1_struct_0(B_67),A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65)
      | ~ m1_pre_topc(B_67,A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_36,c_254])).

tff(c_414,plain,(
    ! [C_367] :
      ( ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_connsp_2('#skF_2'('#skF_5',u1_struct_0('#skF_7'),C_367),'#skF_5','#skF_8')
      | ~ r2_hidden(C_367,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_367,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_397])).

tff(c_422,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_434,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_422])).

tff(c_438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_434])).

tff(c_474,plain,(
    ! [C_433] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',u1_struct_0('#skF_7'),C_433),'#skF_5','#skF_8')
      | ~ r2_hidden(C_433,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_433,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_478,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_7'),'#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_260,c_474])).

tff(c_481,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_415,c_48,c_478])).

tff(c_482,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_481])).

tff(c_486,plain,
    ( v1_xboole_0(u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2,c_482])).

tff(c_489,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_486])).

tff(c_491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_489])).

tff(c_493,plain,(
    r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_724,plain,(
    ! [D_529,B_527,A_530,C_526,F_528] :
      ( r1_tmap_1(D_529,A_530,k2_tmap_1(B_527,A_530,C_526,D_529),F_528)
      | ~ r1_tmap_1(B_527,A_530,C_526,F_528)
      | ~ m1_subset_1(F_528,u1_struct_0(D_529))
      | ~ m1_subset_1(F_528,u1_struct_0(B_527))
      | ~ m1_pre_topc(D_529,B_527)
      | v2_struct_0(D_529)
      | ~ m1_subset_1(C_526,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_527),u1_struct_0(A_530))))
      | ~ v1_funct_2(C_526,u1_struct_0(B_527),u1_struct_0(A_530))
      | ~ v1_funct_1(C_526)
      | ~ l1_pre_topc(B_527)
      | ~ v2_pre_topc(B_527)
      | v2_struct_0(B_527)
      | ~ l1_pre_topc(A_530)
      | ~ v2_pre_topc(A_530)
      | v2_struct_0(A_530) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_726,plain,(
    ! [D_529,F_528] :
      ( r1_tmap_1(D_529,'#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6',D_529),F_528)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6',F_528)
      | ~ m1_subset_1(F_528,u1_struct_0(D_529))
      | ~ m1_subset_1(F_528,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_529,'#skF_5')
      | v2_struct_0(D_529)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_724])).

tff(c_729,plain,(
    ! [D_529,F_528] :
      ( r1_tmap_1(D_529,'#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6',D_529),F_528)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6',F_528)
      | ~ m1_subset_1(F_528,u1_struct_0(D_529))
      | ~ m1_subset_1(F_528,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_529,'#skF_5')
      | v2_struct_0(D_529)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_726])).

tff(c_731,plain,(
    ! [D_531,F_532] :
      ( r1_tmap_1(D_531,'#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6',D_531),F_532)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6',F_532)
      | ~ m1_subset_1(F_532,u1_struct_0(D_531))
      | ~ m1_subset_1(F_532,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_531,'#skF_5')
      | v2_struct_0(D_531) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_729])).

tff(c_492,plain,(
    ~ r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_734,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_731,c_492])).

tff(c_737,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_81,c_493,c_734])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:44:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.38/2.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.30  
% 5.64/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.30  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 5.64/2.30  
% 5.64/2.30  %Foreground sorts:
% 5.64/2.30  
% 5.64/2.30  
% 5.64/2.30  %Background operators:
% 5.64/2.30  
% 5.64/2.30  
% 5.64/2.30  %Foreground operators:
% 5.64/2.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.64/2.30  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.64/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.64/2.30  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.64/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.64/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.64/2.30  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.64/2.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.64/2.30  tff('#skF_7', type, '#skF_7': $i).
% 5.64/2.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.64/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.64/2.30  tff('#skF_5', type, '#skF_5': $i).
% 5.64/2.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.64/2.30  tff('#skF_6', type, '#skF_6': $i).
% 5.64/2.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.64/2.30  tff('#skF_9', type, '#skF_9': $i).
% 5.64/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.64/2.30  tff('#skF_8', type, '#skF_8': $i).
% 5.64/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.64/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.64/2.30  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.64/2.30  tff('#skF_4', type, '#skF_4': $i).
% 5.64/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.64/2.30  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.64/2.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.64/2.30  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.64/2.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.64/2.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.64/2.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.64/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.64/2.30  
% 5.64/2.34  tff(f_294, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 5.64/2.34  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.64/2.34  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.64/2.34  tff(f_96, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 5.64/2.34  tff(f_84, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 5.64/2.34  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 5.64/2.34  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.64/2.34  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.64/2.34  tff(f_164, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.64/2.34  tff(f_157, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 5.64/2.34  tff(f_139, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 5.64/2.34  tff(f_251, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 5.64/2.34  tff(f_204, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 5.64/2.34  tff(c_54, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_50, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_48, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_44, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_46, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_81, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 5.64/2.34  tff(c_64, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_62, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_96, plain, (![B_319, A_320]: (v2_pre_topc(B_319) | ~m1_pre_topc(B_319, A_320) | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.64/2.34  tff(c_99, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_50, c_96])).
% 5.64/2.34  tff(c_102, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_99])).
% 5.64/2.34  tff(c_88, plain, (![B_315, A_316]: (l1_pre_topc(B_315) | ~m1_pre_topc(B_315, A_316) | ~l1_pre_topc(A_316))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.64/2.34  tff(c_91, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_50, c_88])).
% 5.64/2.34  tff(c_94, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91])).
% 5.64/2.34  tff(c_14, plain, (![A_23, B_24]: (m1_connsp_2('#skF_1'(A_23, B_24), A_23, B_24) | ~m1_subset_1(B_24, u1_struct_0(A_23)) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.64/2.34  tff(c_153, plain, (![C_342, A_343, B_344]: (m1_subset_1(C_342, k1_zfmisc_1(u1_struct_0(A_343))) | ~m1_connsp_2(C_342, A_343, B_344) | ~m1_subset_1(B_344, u1_struct_0(A_343)) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.64/2.34  tff(c_156, plain, (![A_23, B_24]: (m1_subset_1('#skF_1'(A_23, B_24), k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_24, u1_struct_0(A_23)) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_14, c_153])).
% 5.64/2.34  tff(c_191, plain, (![C_362, B_363, A_364]: (r2_hidden(C_362, B_363) | ~m1_connsp_2(B_363, A_364, C_362) | ~m1_subset_1(C_362, u1_struct_0(A_364)) | ~m1_subset_1(B_363, k1_zfmisc_1(u1_struct_0(A_364))) | ~l1_pre_topc(A_364) | ~v2_pre_topc(A_364) | v2_struct_0(A_364))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.64/2.34  tff(c_202, plain, (![B_368, A_369]: (r2_hidden(B_368, '#skF_1'(A_369, B_368)) | ~m1_subset_1('#skF_1'(A_369, B_368), k1_zfmisc_1(u1_struct_0(A_369))) | ~m1_subset_1(B_368, u1_struct_0(A_369)) | ~l1_pre_topc(A_369) | ~v2_pre_topc(A_369) | v2_struct_0(A_369))), inference(resolution, [status(thm)], [c_14, c_191])).
% 5.64/2.34  tff(c_206, plain, (![B_370, A_371]: (r2_hidden(B_370, '#skF_1'(A_371, B_370)) | ~m1_subset_1(B_370, u1_struct_0(A_371)) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371) | v2_struct_0(A_371))), inference(resolution, [status(thm)], [c_156, c_202])).
% 5.64/2.34  tff(c_157, plain, (![A_345, B_346]: (m1_subset_1('#skF_1'(A_345, B_346), k1_zfmisc_1(u1_struct_0(A_345))) | ~m1_subset_1(B_346, u1_struct_0(A_345)) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(resolution, [status(thm)], [c_14, c_153])).
% 5.64/2.34  tff(c_4, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.64/2.34  tff(c_163, plain, (![A_345, A_3, B_346]: (~v1_xboole_0(u1_struct_0(A_345)) | ~r2_hidden(A_3, '#skF_1'(A_345, B_346)) | ~m1_subset_1(B_346, u1_struct_0(A_345)) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(resolution, [status(thm)], [c_157, c_4])).
% 5.64/2.34  tff(c_211, plain, (![A_372, B_373]: (~v1_xboole_0(u1_struct_0(A_372)) | ~m1_subset_1(B_373, u1_struct_0(A_372)) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372) | v2_struct_0(A_372))), inference(resolution, [status(thm)], [c_206, c_163])).
% 5.64/2.34  tff(c_223, plain, (~v1_xboole_0(u1_struct_0('#skF_7')) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_81, c_211])).
% 5.64/2.34  tff(c_232, plain, (~v1_xboole_0(u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_94, c_223])).
% 5.64/2.34  tff(c_233, plain, (~v1_xboole_0(u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_54, c_232])).
% 5.64/2.34  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.64/2.34  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_52, plain, (v1_tsep_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_36, plain, (![B_67, A_65]: (m1_subset_1(u1_struct_0(B_67), k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_pre_topc(B_67, A_65) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.64/2.34  tff(c_175, plain, (![B_352, A_353]: (v3_pre_topc(u1_struct_0(B_352), A_353) | ~v1_tsep_1(B_352, A_353) | ~m1_subset_1(u1_struct_0(B_352), k1_zfmisc_1(u1_struct_0(A_353))) | ~m1_pre_topc(B_352, A_353) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.64/2.34  tff(c_179, plain, (![B_67, A_65]: (v3_pre_topc(u1_struct_0(B_67), A_65) | ~v1_tsep_1(B_67, A_65) | ~v2_pre_topc(A_65) | ~m1_pre_topc(B_67, A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_36, c_175])).
% 5.64/2.34  tff(c_195, plain, (![A_365, B_366, C_367]: (r1_tarski('#skF_2'(A_365, B_366, C_367), B_366) | ~r2_hidden(C_367, B_366) | ~m1_subset_1(C_367, u1_struct_0(A_365)) | ~v3_pre_topc(B_366, A_365) | ~m1_subset_1(B_366, k1_zfmisc_1(u1_struct_0(A_365))) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | v2_struct_0(A_365))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.64/2.34  tff(c_201, plain, (![A_65, B_67, C_367]: (r1_tarski('#skF_2'(A_65, u1_struct_0(B_67), C_367), u1_struct_0(B_67)) | ~r2_hidden(C_367, u1_struct_0(B_67)) | ~m1_subset_1(C_367, u1_struct_0(A_65)) | ~v3_pre_topc(u1_struct_0(B_67), A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65) | ~m1_pre_topc(B_67, A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_36, c_195])).
% 5.64/2.34  tff(c_28, plain, (![A_33, B_47, C_54]: (m1_subset_1('#skF_2'(A_33, B_47, C_54), k1_zfmisc_1(u1_struct_0(A_33))) | ~r2_hidden(C_54, B_47) | ~m1_subset_1(C_54, u1_struct_0(A_33)) | ~v3_pre_topc(B_47, A_33) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.64/2.34  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_74, plain, (~r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_83, plain, (~r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_74])).
% 5.64/2.34  tff(c_103, plain, (~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_83])).
% 5.64/2.34  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_58, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_80, plain, (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_294])).
% 5.64/2.34  tff(c_82, plain, (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_80])).
% 5.64/2.34  tff(c_114, plain, (r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_103, c_82])).
% 5.64/2.34  tff(c_342, plain, (![B_420, C_421, E_419, A_418, D_423, G_422]: (r1_tmap_1(B_420, A_418, C_421, G_422) | ~r1_tmap_1(D_423, A_418, k2_tmap_1(B_420, A_418, C_421, D_423), G_422) | ~m1_connsp_2(E_419, B_420, G_422) | ~r1_tarski(E_419, u1_struct_0(D_423)) | ~m1_subset_1(G_422, u1_struct_0(D_423)) | ~m1_subset_1(G_422, u1_struct_0(B_420)) | ~m1_subset_1(E_419, k1_zfmisc_1(u1_struct_0(B_420))) | ~m1_pre_topc(D_423, B_420) | v2_struct_0(D_423) | ~m1_subset_1(C_421, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_420), u1_struct_0(A_418)))) | ~v1_funct_2(C_421, u1_struct_0(B_420), u1_struct_0(A_418)) | ~v1_funct_1(C_421) | ~l1_pre_topc(B_420) | ~v2_pre_topc(B_420) | v2_struct_0(B_420) | ~l1_pre_topc(A_418) | ~v2_pre_topc(A_418) | v2_struct_0(A_418))), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.64/2.34  tff(c_346, plain, (![E_419]: (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | ~m1_connsp_2(E_419, '#skF_5', '#skF_8') | ~r1_tarski(E_419, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(E_419, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_114, c_342])).
% 5.64/2.34  tff(c_353, plain, (![E_419]: (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | ~m1_connsp_2(E_419, '#skF_5', '#skF_8') | ~r1_tarski(E_419, u1_struct_0('#skF_7')) | ~m1_subset_1(E_419, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_7') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_56, c_50, c_48, c_81, c_346])).
% 5.64/2.34  tff(c_355, plain, (![E_424]: (~m1_connsp_2(E_424, '#skF_5', '#skF_8') | ~r1_tarski(E_424, u1_struct_0('#skF_7')) | ~m1_subset_1(E_424, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_54, c_103, c_353])).
% 5.64/2.34  tff(c_363, plain, (![B_47, C_54]: (~m1_connsp_2('#skF_2'('#skF_5', B_47, C_54), '#skF_5', '#skF_8') | ~r1_tarski('#skF_2'('#skF_5', B_47, C_54), u1_struct_0('#skF_7')) | ~r2_hidden(C_54, B_47) | ~m1_subset_1(C_54, u1_struct_0('#skF_5')) | ~v3_pre_topc(B_47, '#skF_5') | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_355])).
% 5.64/2.34  tff(c_378, plain, (![B_47, C_54]: (~m1_connsp_2('#skF_2'('#skF_5', B_47, C_54), '#skF_5', '#skF_8') | ~r1_tarski('#skF_2'('#skF_5', B_47, C_54), u1_struct_0('#skF_7')) | ~r2_hidden(C_54, B_47) | ~m1_subset_1(C_54, u1_struct_0('#skF_5')) | ~v3_pre_topc(B_47, '#skF_5') | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_363])).
% 5.64/2.34  tff(c_389, plain, (![B_427, C_428]: (~m1_connsp_2('#skF_2'('#skF_5', B_427, C_428), '#skF_5', '#skF_8') | ~r1_tarski('#skF_2'('#skF_5', B_427, C_428), u1_struct_0('#skF_7')) | ~r2_hidden(C_428, B_427) | ~m1_subset_1(C_428, u1_struct_0('#skF_5')) | ~v3_pre_topc(B_427, '#skF_5') | ~m1_subset_1(B_427, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_378])).
% 5.64/2.34  tff(c_393, plain, (![C_367]: (~m1_connsp_2('#skF_2'('#skF_5', u1_struct_0('#skF_7'), C_367), '#skF_5', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_367, u1_struct_0('#skF_7')) | ~m1_subset_1(C_367, u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_201, c_389])).
% 5.64/2.34  tff(c_396, plain, (![C_367]: (~m1_connsp_2('#skF_2'('#skF_5', u1_struct_0('#skF_7'), C_367), '#skF_5', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_367, u1_struct_0('#skF_7')) | ~m1_subset_1(C_367, u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_393])).
% 5.64/2.34  tff(c_397, plain, (![C_367]: (~m1_connsp_2('#skF_2'('#skF_5', u1_struct_0('#skF_7'), C_367), '#skF_5', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_367, u1_struct_0('#skF_7')) | ~m1_subset_1(C_367, u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_396])).
% 5.64/2.34  tff(c_398, plain, (~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_397])).
% 5.64/2.34  tff(c_405, plain, (~v1_tsep_1('#skF_7', '#skF_5') | ~v2_pre_topc('#skF_5') | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_179, c_398])).
% 5.64/2.34  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_52, c_405])).
% 5.64/2.34  tff(c_415, plain, (v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_397])).
% 5.64/2.34  tff(c_254, plain, (![A_380, B_381, C_382]: (m1_connsp_2('#skF_2'(A_380, B_381, C_382), A_380, C_382) | ~r2_hidden(C_382, B_381) | ~m1_subset_1(C_382, u1_struct_0(A_380)) | ~v3_pre_topc(B_381, A_380) | ~m1_subset_1(B_381, k1_zfmisc_1(u1_struct_0(A_380))) | ~l1_pre_topc(A_380) | ~v2_pre_topc(A_380) | v2_struct_0(A_380))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.64/2.34  tff(c_260, plain, (![A_65, B_67, C_382]: (m1_connsp_2('#skF_2'(A_65, u1_struct_0(B_67), C_382), A_65, C_382) | ~r2_hidden(C_382, u1_struct_0(B_67)) | ~m1_subset_1(C_382, u1_struct_0(A_65)) | ~v3_pre_topc(u1_struct_0(B_67), A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65) | ~m1_pre_topc(B_67, A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_36, c_254])).
% 5.64/2.34  tff(c_414, plain, (![C_367]: (~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_connsp_2('#skF_2'('#skF_5', u1_struct_0('#skF_7'), C_367), '#skF_5', '#skF_8') | ~r2_hidden(C_367, u1_struct_0('#skF_7')) | ~m1_subset_1(C_367, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_397])).
% 5.64/2.34  tff(c_422, plain, (~m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_414])).
% 5.64/2.34  tff(c_434, plain, (~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_36, c_422])).
% 5.64/2.34  tff(c_438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_434])).
% 5.64/2.34  tff(c_474, plain, (![C_433]: (~m1_connsp_2('#skF_2'('#skF_5', u1_struct_0('#skF_7'), C_433), '#skF_5', '#skF_8') | ~r2_hidden(C_433, u1_struct_0('#skF_7')) | ~m1_subset_1(C_433, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_414])).
% 5.64/2.34  tff(c_478, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_7'), '#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_260, c_474])).
% 5.64/2.34  tff(c_481, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_415, c_48, c_478])).
% 5.64/2.34  tff(c_482, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_66, c_481])).
% 5.64/2.34  tff(c_486, plain, (v1_xboole_0(u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_2, c_482])).
% 5.64/2.34  tff(c_489, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_486])).
% 5.64/2.34  tff(c_491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_233, c_489])).
% 5.64/2.34  tff(c_493, plain, (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_83])).
% 5.64/2.34  tff(c_724, plain, (![D_529, B_527, A_530, C_526, F_528]: (r1_tmap_1(D_529, A_530, k2_tmap_1(B_527, A_530, C_526, D_529), F_528) | ~r1_tmap_1(B_527, A_530, C_526, F_528) | ~m1_subset_1(F_528, u1_struct_0(D_529)) | ~m1_subset_1(F_528, u1_struct_0(B_527)) | ~m1_pre_topc(D_529, B_527) | v2_struct_0(D_529) | ~m1_subset_1(C_526, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_527), u1_struct_0(A_530)))) | ~v1_funct_2(C_526, u1_struct_0(B_527), u1_struct_0(A_530)) | ~v1_funct_1(C_526) | ~l1_pre_topc(B_527) | ~v2_pre_topc(B_527) | v2_struct_0(B_527) | ~l1_pre_topc(A_530) | ~v2_pre_topc(A_530) | v2_struct_0(A_530))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.64/2.34  tff(c_726, plain, (![D_529, F_528]: (r1_tmap_1(D_529, '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', D_529), F_528) | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', F_528) | ~m1_subset_1(F_528, u1_struct_0(D_529)) | ~m1_subset_1(F_528, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_529, '#skF_5') | v2_struct_0(D_529) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_724])).
% 5.64/2.34  tff(c_729, plain, (![D_529, F_528]: (r1_tmap_1(D_529, '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', D_529), F_528) | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', F_528) | ~m1_subset_1(F_528, u1_struct_0(D_529)) | ~m1_subset_1(F_528, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_529, '#skF_5') | v2_struct_0(D_529) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_726])).
% 5.64/2.34  tff(c_731, plain, (![D_531, F_532]: (r1_tmap_1(D_531, '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', D_531), F_532) | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', F_532) | ~m1_subset_1(F_532, u1_struct_0(D_531)) | ~m1_subset_1(F_532, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_531, '#skF_5') | v2_struct_0(D_531))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_729])).
% 5.64/2.34  tff(c_492, plain, (~r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_83])).
% 5.64/2.34  tff(c_734, plain, (~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_731, c_492])).
% 5.64/2.34  tff(c_737, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_81, c_493, c_734])).
% 5.64/2.34  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_737])).
% 5.64/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.34  
% 5.64/2.34  Inference rules
% 5.64/2.34  ----------------------
% 5.64/2.34  #Ref     : 0
% 5.64/2.34  #Sup     : 129
% 5.64/2.34  #Fact    : 0
% 5.64/2.34  #Define  : 0
% 5.64/2.34  #Split   : 6
% 5.64/2.34  #Chain   : 0
% 5.64/2.34  #Close   : 0
% 5.64/2.34  
% 5.64/2.34  Ordering : KBO
% 5.64/2.34  
% 5.64/2.35  Simplification rules
% 5.64/2.35  ----------------------
% 5.64/2.35  #Subsume      : 24
% 5.64/2.35  #Demod        : 105
% 5.64/2.35  #Tautology    : 15
% 5.64/2.35  #SimpNegUnit  : 30
% 5.64/2.35  #BackRed      : 0
% 5.64/2.35  
% 5.64/2.35  #Partial instantiations: 0
% 5.64/2.35  #Strategies tried      : 1
% 5.64/2.35  
% 5.64/2.35  Timing (in seconds)
% 5.64/2.35  ----------------------
% 5.64/2.35  Preprocessing        : 0.63
% 5.64/2.35  Parsing              : 0.31
% 5.64/2.35  CNF conversion       : 0.08
% 5.64/2.35  Main loop            : 0.75
% 5.64/2.35  Inferencing          : 0.29
% 5.64/2.35  Reduction            : 0.21
% 5.64/2.35  Demodulation         : 0.15
% 5.64/2.35  BG Simplification    : 0.04
% 5.64/2.35  Subsumption          : 0.15
% 5.64/2.35  Abstraction          : 0.03
% 5.64/2.35  MUC search           : 0.00
% 5.64/2.35  Cooper               : 0.00
% 5.64/2.35  Total                : 1.46
% 5.64/2.35  Index Insertion      : 0.00
% 5.64/2.35  Index Deletion       : 0.00
% 5.64/2.35  Index Matching       : 0.00
% 5.64/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
