%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:06 EST 2020

% Result     : Theorem 7.21s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 738 expanded)
%              Number of leaves         :   44 ( 297 expanded)
%              Depth                    :   21
%              Number of atoms          :  519 (5533 expanded)
%              Number of equality atoms :    5 ( 257 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4 > #skF_1

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

tff(f_313,negated_conjecture,(
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

tff(f_132,axiom,(
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

tff(f_181,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_174,axiom,(
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

tff(f_156,axiom,(
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

tff(f_270,axiom,(
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
                             => ( ( v3_pre_topc(E,B)
                                  & r2_hidden(F,E)
                                  & r1_tarski(E,u1_struct_0(D))
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_115,axiom,(
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

tff(f_221,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_50,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_44,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_82,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_62,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_101,plain,(
    ! [B_326,A_327] :
      ( v2_pre_topc(B_326)
      | ~ m1_pre_topc(B_326,A_327)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327) ) ),
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
    ! [B_319,A_320] :
      ( l1_pre_topc(B_319)
      | ~ m1_pre_topc(B_319,A_320)
      | ~ l1_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_94,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91])).

tff(c_14,plain,(
    ! [A_23,B_24] :
      ( m1_connsp_2('#skF_1'(A_23,B_24),A_23,B_24)
      | ~ m1_subset_1(B_24,u1_struct_0(A_23))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_150,plain,(
    ! [C_344,A_345,B_346] :
      ( m1_subset_1(C_344,k1_zfmisc_1(u1_struct_0(A_345)))
      | ~ m1_connsp_2(C_344,A_345,B_346)
      | ~ m1_subset_1(B_346,u1_struct_0(A_345))
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_153,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1('#skF_1'(A_23,B_24),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_24,u1_struct_0(A_23))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_14,c_150])).

tff(c_180,plain,(
    ! [C_360,B_361,A_362] :
      ( r2_hidden(C_360,B_361)
      | ~ m1_connsp_2(B_361,A_362,C_360)
      | ~ m1_subset_1(C_360,u1_struct_0(A_362))
      | ~ m1_subset_1(B_361,k1_zfmisc_1(u1_struct_0(A_362)))
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_184,plain,(
    ! [B_363,A_364] :
      ( r2_hidden(B_363,'#skF_1'(A_364,B_363))
      | ~ m1_subset_1('#skF_1'(A_364,B_363),k1_zfmisc_1(u1_struct_0(A_364)))
      | ~ m1_subset_1(B_363,u1_struct_0(A_364))
      | ~ l1_pre_topc(A_364)
      | ~ v2_pre_topc(A_364)
      | v2_struct_0(A_364) ) ),
    inference(resolution,[status(thm)],[c_14,c_180])).

tff(c_188,plain,(
    ! [B_365,A_366] :
      ( r2_hidden(B_365,'#skF_1'(A_366,B_365))
      | ~ m1_subset_1(B_365,u1_struct_0(A_366))
      | ~ l1_pre_topc(A_366)
      | ~ v2_pre_topc(A_366)
      | v2_struct_0(A_366) ) ),
    inference(resolution,[status(thm)],[c_153,c_184])).

tff(c_160,plain,(
    ! [A_351,B_352] :
      ( m1_subset_1('#skF_1'(A_351,B_352),k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ m1_subset_1(B_352,u1_struct_0(A_351))
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351)
      | v2_struct_0(A_351) ) ),
    inference(resolution,[status(thm)],[c_14,c_150])).

tff(c_4,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_163,plain,(
    ! [A_351,A_3,B_352] :
      ( ~ v1_xboole_0(u1_struct_0(A_351))
      | ~ r2_hidden(A_3,'#skF_1'(A_351,B_352))
      | ~ m1_subset_1(B_352,u1_struct_0(A_351))
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351)
      | v2_struct_0(A_351) ) ),
    inference(resolution,[status(thm)],[c_160,c_4])).

tff(c_193,plain,(
    ! [A_367,B_368] :
      ( ~ v1_xboole_0(u1_struct_0(A_367))
      | ~ m1_subset_1(B_368,u1_struct_0(A_367))
      | ~ l1_pre_topc(A_367)
      | ~ v2_pre_topc(A_367)
      | v2_struct_0(A_367) ) ),
    inference(resolution,[status(thm)],[c_188,c_163])).

tff(c_205,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_193])).

tff(c_214,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_94,c_205])).

tff(c_215,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_214])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    v1_tsep_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_36,plain,(
    ! [B_71,A_69] :
      ( m1_subset_1(u1_struct_0(B_71),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_pre_topc(B_71,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_170,plain,(
    ! [B_356,A_357] :
      ( v3_pre_topc(u1_struct_0(B_356),A_357)
      | ~ v1_tsep_1(B_356,A_357)
      | ~ m1_subset_1(u1_struct_0(B_356),k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ m1_pre_topc(B_356,A_357)
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_174,plain,(
    ! [B_71,A_69] :
      ( v3_pre_topc(u1_struct_0(B_71),A_69)
      | ~ v1_tsep_1(B_71,A_69)
      | ~ v2_pre_topc(A_69)
      | ~ m1_pre_topc(B_71,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_36,c_170])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_232,plain,(
    ! [A_377,B_378,C_379] :
      ( r1_tarski('#skF_2'(A_377,B_378,C_379),C_379)
      | ~ m1_connsp_2(C_379,A_377,B_378)
      | ~ m1_subset_1(C_379,k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ m1_subset_1(B_378,u1_struct_0(A_377))
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_238,plain,(
    ! [A_69,B_378,B_71] :
      ( r1_tarski('#skF_2'(A_69,B_378,u1_struct_0(B_71)),u1_struct_0(B_71))
      | ~ m1_connsp_2(u1_struct_0(B_71),A_69,B_378)
      | ~ m1_subset_1(B_378,u1_struct_0(A_69))
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69)
      | ~ m1_pre_topc(B_71,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_36,c_232])).

tff(c_28,plain,(
    ! [A_40,B_52,C_58] :
      ( m1_subset_1('#skF_2'(A_40,B_52,C_58),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_connsp_2(C_58,A_40,B_52)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_52,u1_struct_0(A_40))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_7')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

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
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_83,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_74])).

tff(c_115,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_83])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_313])).

tff(c_623,plain,(
    ! [A_449,C_447,B_450,D_448,E_451,G_446] :
      ( r1_tmap_1(B_450,A_449,C_447,G_446)
      | ~ r1_tmap_1(D_448,A_449,k2_tmap_1(B_450,A_449,C_447,D_448),G_446)
      | ~ r1_tarski(E_451,u1_struct_0(D_448))
      | ~ r2_hidden(G_446,E_451)
      | ~ v3_pre_topc(E_451,B_450)
      | ~ m1_subset_1(G_446,u1_struct_0(D_448))
      | ~ m1_subset_1(G_446,u1_struct_0(B_450))
      | ~ m1_subset_1(E_451,k1_zfmisc_1(u1_struct_0(B_450)))
      | ~ m1_pre_topc(D_448,B_450)
      | v2_struct_0(D_448)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_450),u1_struct_0(A_449))))
      | ~ v1_funct_2(C_447,u1_struct_0(B_450),u1_struct_0(A_449))
      | ~ v1_funct_1(C_447)
      | ~ l1_pre_topc(B_450)
      | ~ v2_pre_topc(B_450)
      | v2_struct_0(B_450)
      | ~ l1_pre_topc(A_449)
      | ~ v2_pre_topc(A_449)
      | v2_struct_0(A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_627,plain,(
    ! [E_451] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ r1_tarski(E_451,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',E_451)
      | ~ v3_pre_topc(E_451,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_451,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_113,c_623])).

tff(c_634,plain,(
    ! [E_451] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ r1_tarski(E_451,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',E_451)
      | ~ v3_pre_topc(E_451,'#skF_4')
      | ~ m1_subset_1(E_451,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_56,c_50,c_82,c_46,c_627])).

tff(c_636,plain,(
    ! [E_452] :
      ( ~ r1_tarski(E_452,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',E_452)
      | ~ v3_pre_topc(E_452,'#skF_4')
      | ~ m1_subset_1(E_452,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_54,c_115,c_634])).

tff(c_646,plain,(
    ! [B_52,C_58] :
      ( ~ r1_tarski('#skF_2'('#skF_4',B_52,C_58),u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_52,C_58))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_52,C_58),'#skF_4')
      | ~ m1_connsp_2(C_58,'#skF_4',B_52)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_636])).

tff(c_659,plain,(
    ! [B_52,C_58] :
      ( ~ r1_tarski('#skF_2'('#skF_4',B_52,C_58),u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_52,C_58))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_52,C_58),'#skF_4')
      | ~ m1_connsp_2(C_58,'#skF_4',B_52)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_646])).

tff(c_725,plain,(
    ! [B_462,C_463] :
      ( ~ r1_tarski('#skF_2'('#skF_4',B_462,C_463),u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_462,C_463))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_462,C_463),'#skF_4')
      | ~ m1_connsp_2(C_463,'#skF_4',B_462)
      | ~ m1_subset_1(C_463,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_462,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_659])).

tff(c_733,plain,(
    ! [B_378] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_378,u1_struct_0('#skF_6')))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_378,u1_struct_0('#skF_6')),'#skF_4')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_378)
      | ~ m1_subset_1(B_378,u1_struct_0('#skF_4'))
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_238,c_725])).

tff(c_739,plain,(
    ! [B_378] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_378,u1_struct_0('#skF_6')))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_378,u1_struct_0('#skF_6')),'#skF_4')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_378)
      | ~ m1_subset_1(B_378,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_733])).

tff(c_740,plain,(
    ! [B_378] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_378,u1_struct_0('#skF_6')))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_378,u1_struct_0('#skF_6')),'#skF_4')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_378)
      | ~ m1_subset_1(B_378,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_739])).

tff(c_754,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_740])).

tff(c_760,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_754])).

tff(c_767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_760])).

tff(c_769,plain,(
    m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_740])).

tff(c_117,plain,(
    ! [C_335,A_336,B_337] :
      ( m1_subset_1(C_335,u1_struct_0(A_336))
      | ~ m1_subset_1(C_335,u1_struct_0(B_337))
      | ~ m1_pre_topc(B_337,A_336)
      | v2_struct_0(B_337)
      | ~ l1_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_121,plain,(
    ! [A_336] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_336))
      | ~ m1_pre_topc('#skF_6',A_336)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(resolution,[status(thm)],[c_46,c_117])).

tff(c_127,plain,(
    ! [A_336] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_336))
      | ~ m1_pre_topc('#skF_6',A_336)
      | ~ l1_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_121])).

tff(c_239,plain,(
    ! [B_380,A_381,C_382] :
      ( m1_connsp_2(B_380,A_381,C_382)
      | ~ r2_hidden(C_382,B_380)
      | ~ v3_pre_topc(B_380,A_381)
      | ~ m1_subset_1(C_382,u1_struct_0(A_381))
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0(A_381)))
      | ~ l1_pre_topc(A_381)
      | ~ v2_pre_topc(A_381)
      | v2_struct_0(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_248,plain,(
    ! [B_380,A_336] :
      ( m1_connsp_2(B_380,A_336,'#skF_8')
      | ~ r2_hidden('#skF_8',B_380)
      | ~ v3_pre_topc(B_380,A_336)
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0(A_336)))
      | ~ v2_pre_topc(A_336)
      | ~ m1_pre_topc('#skF_6',A_336)
      | ~ l1_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(resolution,[status(thm)],[c_127,c_239])).

tff(c_780,plain,
    ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_769,c_248])).

tff(c_800,plain,
    ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_780])).

tff(c_801,plain,
    ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_800])).

tff(c_816,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_801])).

tff(c_819,plain,
    ( ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_174,c_816])).

tff(c_823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_52,c_819])).

tff(c_824,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_801])).

tff(c_832,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_824])).

tff(c_835,plain,
    ( v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2,c_832])).

tff(c_838,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_835])).

tff(c_840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_838])).

tff(c_841,plain,(
    m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_824])).

tff(c_22,plain,(
    ! [B_52,A_40,C_58] :
      ( r2_hidden(B_52,'#skF_2'(A_40,B_52,C_58))
      | ~ m1_connsp_2(C_58,A_40,B_52)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_52,u1_struct_0(A_40))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_787,plain,(
    ! [B_52] :
      ( r2_hidden(B_52,'#skF_2'('#skF_4',B_52,u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_769,c_22])).

tff(c_809,plain,(
    ! [B_52] :
      ( r2_hidden(B_52,'#skF_2'('#skF_4',B_52,u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_787])).

tff(c_810,plain,(
    ! [B_52] :
      ( r2_hidden(B_52,'#skF_2'('#skF_4',B_52,u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_809])).

tff(c_216,plain,(
    ! [A_369,B_370,C_371] :
      ( v3_pre_topc('#skF_2'(A_369,B_370,C_371),A_369)
      | ~ m1_connsp_2(C_371,A_369,B_370)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(u1_struct_0(A_369)))
      | ~ m1_subset_1(B_370,u1_struct_0(A_369))
      | ~ l1_pre_topc(A_369)
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_222,plain,(
    ! [A_69,B_370,B_71] :
      ( v3_pre_topc('#skF_2'(A_69,B_370,u1_struct_0(B_71)),A_69)
      | ~ m1_connsp_2(u1_struct_0(B_71),A_69,B_370)
      | ~ m1_subset_1(B_370,u1_struct_0(A_69))
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69)
      | ~ m1_pre_topc(B_71,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_36,c_216])).

tff(c_880,plain,(
    ! [B_475] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_475,u1_struct_0('#skF_6')))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_475,u1_struct_0('#skF_6')),'#skF_4')
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_475)
      | ~ m1_subset_1(B_475,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_740])).

tff(c_891,plain,(
    ! [B_370] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_370,u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_370)
      | ~ m1_subset_1(B_370,u1_struct_0('#skF_4'))
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_222,c_880])).

tff(c_898,plain,(
    ! [B_370] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_370,u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_370)
      | ~ m1_subset_1(B_370,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_891])).

tff(c_900,plain,(
    ! [B_476] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_476,u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_476)
      | ~ m1_subset_1(B_476,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_898])).

tff(c_904,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_810,c_900])).

tff(c_919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_841,c_904])).

tff(c_920,plain,(
    r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_1451,plain,(
    ! [D_590,A_589,C_588,F_592,B_591] :
      ( r1_tmap_1(D_590,A_589,k2_tmap_1(B_591,A_589,C_588,D_590),F_592)
      | ~ r1_tmap_1(B_591,A_589,C_588,F_592)
      | ~ m1_subset_1(F_592,u1_struct_0(D_590))
      | ~ m1_subset_1(F_592,u1_struct_0(B_591))
      | ~ m1_pre_topc(D_590,B_591)
      | v2_struct_0(D_590)
      | ~ m1_subset_1(C_588,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_591),u1_struct_0(A_589))))
      | ~ v1_funct_2(C_588,u1_struct_0(B_591),u1_struct_0(A_589))
      | ~ v1_funct_1(C_588)
      | ~ l1_pre_topc(B_591)
      | ~ v2_pre_topc(B_591)
      | v2_struct_0(B_591)
      | ~ l1_pre_topc(A_589)
      | ~ v2_pre_topc(A_589)
      | v2_struct_0(A_589) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_1453,plain,(
    ! [D_590,F_592] :
      ( r1_tmap_1(D_590,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_590),F_592)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_592)
      | ~ m1_subset_1(F_592,u1_struct_0(D_590))
      | ~ m1_subset_1(F_592,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_590,'#skF_4')
      | v2_struct_0(D_590)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_1451])).

tff(c_1456,plain,(
    ! [D_590,F_592] :
      ( r1_tmap_1(D_590,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_590),F_592)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_592)
      | ~ m1_subset_1(F_592,u1_struct_0(D_590))
      | ~ m1_subset_1(F_592,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_590,'#skF_4')
      | v2_struct_0(D_590)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_1453])).

tff(c_1458,plain,(
    ! [D_593,F_594] :
      ( r1_tmap_1(D_593,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_593),F_594)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_594)
      | ~ m1_subset_1(F_594,u1_struct_0(D_593))
      | ~ m1_subset_1(F_594,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_593,'#skF_4')
      | v2_struct_0(D_593) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_1456])).

tff(c_921,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_1461,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1458,c_921])).

tff(c_1464,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_82,c_46,c_920,c_1461])).

tff(c_1466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1464])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.21/2.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/2.69  
% 7.31/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/2.70  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4 > #skF_1
% 7.31/2.70  
% 7.31/2.70  %Foreground sorts:
% 7.31/2.70  
% 7.31/2.70  
% 7.31/2.70  %Background operators:
% 7.31/2.70  
% 7.31/2.70  
% 7.31/2.70  %Foreground operators:
% 7.31/2.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.31/2.70  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 7.31/2.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.31/2.70  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.31/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.31/2.70  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 7.31/2.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.31/2.70  tff('#skF_7', type, '#skF_7': $i).
% 7.31/2.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.31/2.70  tff('#skF_5', type, '#skF_5': $i).
% 7.31/2.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.31/2.70  tff('#skF_6', type, '#skF_6': $i).
% 7.31/2.70  tff('#skF_3', type, '#skF_3': $i).
% 7.31/2.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.31/2.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.31/2.70  tff('#skF_8', type, '#skF_8': $i).
% 7.31/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.31/2.70  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 7.31/2.70  tff('#skF_4', type, '#skF_4': $i).
% 7.31/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.70  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.31/2.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.31/2.70  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.31/2.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.31/2.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.31/2.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.31/2.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.31/2.70  
% 7.49/2.74  tff(f_313, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 7.49/2.74  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 7.49/2.74  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.49/2.74  tff(f_96, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 7.49/2.74  tff(f_84, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 7.49/2.74  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 7.49/2.74  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 7.49/2.74  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 7.49/2.74  tff(f_181, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 7.49/2.74  tff(f_174, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 7.49/2.74  tff(f_156, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 7.49/2.74  tff(f_270, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 7.49/2.74  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 7.49/2.74  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 7.49/2.74  tff(f_221, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 7.49/2.74  tff(c_54, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_50, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_44, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_82, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48])).
% 7.49/2.74  tff(c_46, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_62, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_101, plain, (![B_326, A_327]: (v2_pre_topc(B_326) | ~m1_pre_topc(B_326, A_327) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.49/2.74  tff(c_104, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_101])).
% 7.49/2.74  tff(c_107, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_104])).
% 7.49/2.74  tff(c_88, plain, (![B_319, A_320]: (l1_pre_topc(B_319) | ~m1_pre_topc(B_319, A_320) | ~l1_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.49/2.74  tff(c_91, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_88])).
% 7.49/2.74  tff(c_94, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91])).
% 7.49/2.74  tff(c_14, plain, (![A_23, B_24]: (m1_connsp_2('#skF_1'(A_23, B_24), A_23, B_24) | ~m1_subset_1(B_24, u1_struct_0(A_23)) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.49/2.74  tff(c_150, plain, (![C_344, A_345, B_346]: (m1_subset_1(C_344, k1_zfmisc_1(u1_struct_0(A_345))) | ~m1_connsp_2(C_344, A_345, B_346) | ~m1_subset_1(B_346, u1_struct_0(A_345)) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.49/2.74  tff(c_153, plain, (![A_23, B_24]: (m1_subset_1('#skF_1'(A_23, B_24), k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_24, u1_struct_0(A_23)) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_14, c_150])).
% 7.49/2.74  tff(c_180, plain, (![C_360, B_361, A_362]: (r2_hidden(C_360, B_361) | ~m1_connsp_2(B_361, A_362, C_360) | ~m1_subset_1(C_360, u1_struct_0(A_362)) | ~m1_subset_1(B_361, k1_zfmisc_1(u1_struct_0(A_362))) | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362) | v2_struct_0(A_362))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.49/2.74  tff(c_184, plain, (![B_363, A_364]: (r2_hidden(B_363, '#skF_1'(A_364, B_363)) | ~m1_subset_1('#skF_1'(A_364, B_363), k1_zfmisc_1(u1_struct_0(A_364))) | ~m1_subset_1(B_363, u1_struct_0(A_364)) | ~l1_pre_topc(A_364) | ~v2_pre_topc(A_364) | v2_struct_0(A_364))), inference(resolution, [status(thm)], [c_14, c_180])).
% 7.49/2.74  tff(c_188, plain, (![B_365, A_366]: (r2_hidden(B_365, '#skF_1'(A_366, B_365)) | ~m1_subset_1(B_365, u1_struct_0(A_366)) | ~l1_pre_topc(A_366) | ~v2_pre_topc(A_366) | v2_struct_0(A_366))), inference(resolution, [status(thm)], [c_153, c_184])).
% 7.49/2.74  tff(c_160, plain, (![A_351, B_352]: (m1_subset_1('#skF_1'(A_351, B_352), k1_zfmisc_1(u1_struct_0(A_351))) | ~m1_subset_1(B_352, u1_struct_0(A_351)) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351) | v2_struct_0(A_351))), inference(resolution, [status(thm)], [c_14, c_150])).
% 7.49/2.74  tff(c_4, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.49/2.74  tff(c_163, plain, (![A_351, A_3, B_352]: (~v1_xboole_0(u1_struct_0(A_351)) | ~r2_hidden(A_3, '#skF_1'(A_351, B_352)) | ~m1_subset_1(B_352, u1_struct_0(A_351)) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351) | v2_struct_0(A_351))), inference(resolution, [status(thm)], [c_160, c_4])).
% 7.49/2.74  tff(c_193, plain, (![A_367, B_368]: (~v1_xboole_0(u1_struct_0(A_367)) | ~m1_subset_1(B_368, u1_struct_0(A_367)) | ~l1_pre_topc(A_367) | ~v2_pre_topc(A_367) | v2_struct_0(A_367))), inference(resolution, [status(thm)], [c_188, c_163])).
% 7.49/2.74  tff(c_205, plain, (~v1_xboole_0(u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_46, c_193])).
% 7.49/2.74  tff(c_214, plain, (~v1_xboole_0(u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_94, c_205])).
% 7.49/2.74  tff(c_215, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_54, c_214])).
% 7.49/2.74  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.49/2.74  tff(c_52, plain, (v1_tsep_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_36, plain, (![B_71, A_69]: (m1_subset_1(u1_struct_0(B_71), k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_pre_topc(B_71, A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.49/2.74  tff(c_170, plain, (![B_356, A_357]: (v3_pre_topc(u1_struct_0(B_356), A_357) | ~v1_tsep_1(B_356, A_357) | ~m1_subset_1(u1_struct_0(B_356), k1_zfmisc_1(u1_struct_0(A_357))) | ~m1_pre_topc(B_356, A_357) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357))), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.49/2.74  tff(c_174, plain, (![B_71, A_69]: (v3_pre_topc(u1_struct_0(B_71), A_69) | ~v1_tsep_1(B_71, A_69) | ~v2_pre_topc(A_69) | ~m1_pre_topc(B_71, A_69) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_36, c_170])).
% 7.49/2.74  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_232, plain, (![A_377, B_378, C_379]: (r1_tarski('#skF_2'(A_377, B_378, C_379), C_379) | ~m1_connsp_2(C_379, A_377, B_378) | ~m1_subset_1(C_379, k1_zfmisc_1(u1_struct_0(A_377))) | ~m1_subset_1(B_378, u1_struct_0(A_377)) | ~l1_pre_topc(A_377) | ~v2_pre_topc(A_377) | v2_struct_0(A_377))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.49/2.74  tff(c_238, plain, (![A_69, B_378, B_71]: (r1_tarski('#skF_2'(A_69, B_378, u1_struct_0(B_71)), u1_struct_0(B_71)) | ~m1_connsp_2(u1_struct_0(B_71), A_69, B_378) | ~m1_subset_1(B_378, u1_struct_0(A_69)) | ~v2_pre_topc(A_69) | v2_struct_0(A_69) | ~m1_pre_topc(B_71, A_69) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_36, c_232])).
% 7.49/2.74  tff(c_28, plain, (![A_40, B_52, C_58]: (m1_subset_1('#skF_2'(A_40, B_52, C_58), k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_connsp_2(C_58, A_40, B_52) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_52, u1_struct_0(A_40)) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.49/2.74  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_80, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_81, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_80])).
% 7.49/2.74  tff(c_113, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_81])).
% 7.49/2.74  tff(c_74, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_83, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_74])).
% 7.49/2.74  tff(c_115, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_83])).
% 7.49/2.74  tff(c_70, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_68, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_58, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_313])).
% 7.49/2.74  tff(c_623, plain, (![A_449, C_447, B_450, D_448, E_451, G_446]: (r1_tmap_1(B_450, A_449, C_447, G_446) | ~r1_tmap_1(D_448, A_449, k2_tmap_1(B_450, A_449, C_447, D_448), G_446) | ~r1_tarski(E_451, u1_struct_0(D_448)) | ~r2_hidden(G_446, E_451) | ~v3_pre_topc(E_451, B_450) | ~m1_subset_1(G_446, u1_struct_0(D_448)) | ~m1_subset_1(G_446, u1_struct_0(B_450)) | ~m1_subset_1(E_451, k1_zfmisc_1(u1_struct_0(B_450))) | ~m1_pre_topc(D_448, B_450) | v2_struct_0(D_448) | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_450), u1_struct_0(A_449)))) | ~v1_funct_2(C_447, u1_struct_0(B_450), u1_struct_0(A_449)) | ~v1_funct_1(C_447) | ~l1_pre_topc(B_450) | ~v2_pre_topc(B_450) | v2_struct_0(B_450) | ~l1_pre_topc(A_449) | ~v2_pre_topc(A_449) | v2_struct_0(A_449))), inference(cnfTransformation, [status(thm)], [f_270])).
% 7.49/2.74  tff(c_627, plain, (![E_451]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~r1_tarski(E_451, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', E_451) | ~v3_pre_topc(E_451, '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_451, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_113, c_623])).
% 7.49/2.74  tff(c_634, plain, (![E_451]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~r1_tarski(E_451, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', E_451) | ~v3_pre_topc(E_451, '#skF_4') | ~m1_subset_1(E_451, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_56, c_50, c_82, c_46, c_627])).
% 7.49/2.74  tff(c_636, plain, (![E_452]: (~r1_tarski(E_452, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', E_452) | ~v3_pre_topc(E_452, '#skF_4') | ~m1_subset_1(E_452, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_54, c_115, c_634])).
% 7.49/2.74  tff(c_646, plain, (![B_52, C_58]: (~r1_tarski('#skF_2'('#skF_4', B_52, C_58), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_52, C_58)) | ~v3_pre_topc('#skF_2'('#skF_4', B_52, C_58), '#skF_4') | ~m1_connsp_2(C_58, '#skF_4', B_52) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_52, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_636])).
% 7.49/2.74  tff(c_659, plain, (![B_52, C_58]: (~r1_tarski('#skF_2'('#skF_4', B_52, C_58), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_52, C_58)) | ~v3_pre_topc('#skF_2'('#skF_4', B_52, C_58), '#skF_4') | ~m1_connsp_2(C_58, '#skF_4', B_52) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_52, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_646])).
% 7.49/2.74  tff(c_725, plain, (![B_462, C_463]: (~r1_tarski('#skF_2'('#skF_4', B_462, C_463), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_462, C_463)) | ~v3_pre_topc('#skF_2'('#skF_4', B_462, C_463), '#skF_4') | ~m1_connsp_2(C_463, '#skF_4', B_462) | ~m1_subset_1(C_463, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_462, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_659])).
% 7.49/2.74  tff(c_733, plain, (![B_378]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_378, u1_struct_0('#skF_6'))) | ~v3_pre_topc('#skF_2'('#skF_4', B_378, u1_struct_0('#skF_6')), '#skF_4') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_378) | ~m1_subset_1(B_378, u1_struct_0('#skF_4')) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_238, c_725])).
% 7.49/2.74  tff(c_739, plain, (![B_378]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_378, u1_struct_0('#skF_6'))) | ~v3_pre_topc('#skF_2'('#skF_4', B_378, u1_struct_0('#skF_6')), '#skF_4') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_378) | ~m1_subset_1(B_378, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_733])).
% 7.49/2.74  tff(c_740, plain, (![B_378]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_378, u1_struct_0('#skF_6'))) | ~v3_pre_topc('#skF_2'('#skF_4', B_378, u1_struct_0('#skF_6')), '#skF_4') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_378) | ~m1_subset_1(B_378, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_739])).
% 7.49/2.74  tff(c_754, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_740])).
% 7.49/2.74  tff(c_760, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_754])).
% 7.49/2.74  tff(c_767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_760])).
% 7.49/2.74  tff(c_769, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_740])).
% 7.49/2.74  tff(c_117, plain, (![C_335, A_336, B_337]: (m1_subset_1(C_335, u1_struct_0(A_336)) | ~m1_subset_1(C_335, u1_struct_0(B_337)) | ~m1_pre_topc(B_337, A_336) | v2_struct_0(B_337) | ~l1_pre_topc(A_336) | v2_struct_0(A_336))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.49/2.74  tff(c_121, plain, (![A_336]: (m1_subset_1('#skF_8', u1_struct_0(A_336)) | ~m1_pre_topc('#skF_6', A_336) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_336) | v2_struct_0(A_336))), inference(resolution, [status(thm)], [c_46, c_117])).
% 7.49/2.74  tff(c_127, plain, (![A_336]: (m1_subset_1('#skF_8', u1_struct_0(A_336)) | ~m1_pre_topc('#skF_6', A_336) | ~l1_pre_topc(A_336) | v2_struct_0(A_336))), inference(negUnitSimplification, [status(thm)], [c_54, c_121])).
% 7.49/2.74  tff(c_239, plain, (![B_380, A_381, C_382]: (m1_connsp_2(B_380, A_381, C_382) | ~r2_hidden(C_382, B_380) | ~v3_pre_topc(B_380, A_381) | ~m1_subset_1(C_382, u1_struct_0(A_381)) | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0(A_381))) | ~l1_pre_topc(A_381) | ~v2_pre_topc(A_381) | v2_struct_0(A_381))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.49/2.74  tff(c_248, plain, (![B_380, A_336]: (m1_connsp_2(B_380, A_336, '#skF_8') | ~r2_hidden('#skF_8', B_380) | ~v3_pre_topc(B_380, A_336) | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0(A_336))) | ~v2_pre_topc(A_336) | ~m1_pre_topc('#skF_6', A_336) | ~l1_pre_topc(A_336) | v2_struct_0(A_336))), inference(resolution, [status(thm)], [c_127, c_239])).
% 7.49/2.74  tff(c_780, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_769, c_248])).
% 7.49/2.74  tff(c_800, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_780])).
% 7.49/2.74  tff(c_801, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_800])).
% 7.49/2.74  tff(c_816, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_801])).
% 7.49/2.74  tff(c_819, plain, (~v1_tsep_1('#skF_6', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_174, c_816])).
% 7.49/2.74  tff(c_823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_52, c_819])).
% 7.49/2.74  tff(c_824, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_801])).
% 7.49/2.74  tff(c_832, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_824])).
% 7.49/2.74  tff(c_835, plain, (v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_2, c_832])).
% 7.49/2.74  tff(c_838, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_835])).
% 7.49/2.74  tff(c_840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215, c_838])).
% 7.49/2.74  tff(c_841, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_824])).
% 7.49/2.74  tff(c_22, plain, (![B_52, A_40, C_58]: (r2_hidden(B_52, '#skF_2'(A_40, B_52, C_58)) | ~m1_connsp_2(C_58, A_40, B_52) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_52, u1_struct_0(A_40)) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.49/2.74  tff(c_787, plain, (![B_52]: (r2_hidden(B_52, '#skF_2'('#skF_4', B_52, u1_struct_0('#skF_6'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_769, c_22])).
% 7.49/2.74  tff(c_809, plain, (![B_52]: (r2_hidden(B_52, '#skF_2'('#skF_4', B_52, u1_struct_0('#skF_6'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_787])).
% 7.49/2.74  tff(c_810, plain, (![B_52]: (r2_hidden(B_52, '#skF_2'('#skF_4', B_52, u1_struct_0('#skF_6'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_809])).
% 7.49/2.74  tff(c_216, plain, (![A_369, B_370, C_371]: (v3_pre_topc('#skF_2'(A_369, B_370, C_371), A_369) | ~m1_connsp_2(C_371, A_369, B_370) | ~m1_subset_1(C_371, k1_zfmisc_1(u1_struct_0(A_369))) | ~m1_subset_1(B_370, u1_struct_0(A_369)) | ~l1_pre_topc(A_369) | ~v2_pre_topc(A_369) | v2_struct_0(A_369))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.49/2.74  tff(c_222, plain, (![A_69, B_370, B_71]: (v3_pre_topc('#skF_2'(A_69, B_370, u1_struct_0(B_71)), A_69) | ~m1_connsp_2(u1_struct_0(B_71), A_69, B_370) | ~m1_subset_1(B_370, u1_struct_0(A_69)) | ~v2_pre_topc(A_69) | v2_struct_0(A_69) | ~m1_pre_topc(B_71, A_69) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_36, c_216])).
% 7.49/2.74  tff(c_880, plain, (![B_475]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_475, u1_struct_0('#skF_6'))) | ~v3_pre_topc('#skF_2'('#skF_4', B_475, u1_struct_0('#skF_6')), '#skF_4') | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_475) | ~m1_subset_1(B_475, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_740])).
% 7.49/2.74  tff(c_891, plain, (![B_370]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_370, u1_struct_0('#skF_6'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_370) | ~m1_subset_1(B_370, u1_struct_0('#skF_4')) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_222, c_880])).
% 7.49/2.74  tff(c_898, plain, (![B_370]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_370, u1_struct_0('#skF_6'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_370) | ~m1_subset_1(B_370, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_891])).
% 7.49/2.74  tff(c_900, plain, (![B_476]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_476, u1_struct_0('#skF_6'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_476) | ~m1_subset_1(B_476, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_898])).
% 7.49/2.74  tff(c_904, plain, (~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_810, c_900])).
% 7.49/2.74  tff(c_919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_841, c_904])).
% 7.49/2.74  tff(c_920, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 7.49/2.74  tff(c_1451, plain, (![D_590, A_589, C_588, F_592, B_591]: (r1_tmap_1(D_590, A_589, k2_tmap_1(B_591, A_589, C_588, D_590), F_592) | ~r1_tmap_1(B_591, A_589, C_588, F_592) | ~m1_subset_1(F_592, u1_struct_0(D_590)) | ~m1_subset_1(F_592, u1_struct_0(B_591)) | ~m1_pre_topc(D_590, B_591) | v2_struct_0(D_590) | ~m1_subset_1(C_588, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_591), u1_struct_0(A_589)))) | ~v1_funct_2(C_588, u1_struct_0(B_591), u1_struct_0(A_589)) | ~v1_funct_1(C_588) | ~l1_pre_topc(B_591) | ~v2_pre_topc(B_591) | v2_struct_0(B_591) | ~l1_pre_topc(A_589) | ~v2_pre_topc(A_589) | v2_struct_0(A_589))), inference(cnfTransformation, [status(thm)], [f_221])).
% 7.49/2.74  tff(c_1453, plain, (![D_590, F_592]: (r1_tmap_1(D_590, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_590), F_592) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_592) | ~m1_subset_1(F_592, u1_struct_0(D_590)) | ~m1_subset_1(F_592, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_590, '#skF_4') | v2_struct_0(D_590) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_1451])).
% 7.49/2.74  tff(c_1456, plain, (![D_590, F_592]: (r1_tmap_1(D_590, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_590), F_592) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_592) | ~m1_subset_1(F_592, u1_struct_0(D_590)) | ~m1_subset_1(F_592, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_590, '#skF_4') | v2_struct_0(D_590) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_1453])).
% 7.49/2.74  tff(c_1458, plain, (![D_593, F_594]: (r1_tmap_1(D_593, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_593), F_594) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_594) | ~m1_subset_1(F_594, u1_struct_0(D_593)) | ~m1_subset_1(F_594, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_593, '#skF_4') | v2_struct_0(D_593))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_1456])).
% 7.49/2.74  tff(c_921, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 7.49/2.74  tff(c_1461, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1458, c_921])).
% 7.49/2.74  tff(c_1464, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_82, c_46, c_920, c_1461])).
% 7.49/2.74  tff(c_1466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1464])).
% 7.49/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/2.74  
% 7.49/2.74  Inference rules
% 7.49/2.74  ----------------------
% 7.49/2.74  #Ref     : 0
% 7.49/2.74  #Sup     : 254
% 7.49/2.74  #Fact    : 0
% 7.49/2.74  #Define  : 0
% 7.49/2.74  #Split   : 5
% 7.49/2.74  #Chain   : 0
% 7.49/2.74  #Close   : 0
% 7.49/2.74  
% 7.49/2.74  Ordering : KBO
% 7.49/2.74  
% 7.49/2.74  Simplification rules
% 7.49/2.74  ----------------------
% 7.49/2.74  #Subsume      : 58
% 7.49/2.74  #Demod        : 294
% 7.49/2.74  #Tautology    : 33
% 7.49/2.74  #SimpNegUnit  : 103
% 7.49/2.74  #BackRed      : 0
% 7.49/2.74  
% 7.49/2.74  #Partial instantiations: 0
% 7.49/2.74  #Strategies tried      : 1
% 7.49/2.74  
% 7.49/2.74  Timing (in seconds)
% 7.49/2.74  ----------------------
% 7.49/2.75  Preprocessing        : 0.67
% 7.49/2.75  Parsing              : 0.33
% 7.49/2.75  CNF conversion       : 0.09
% 7.49/2.75  Main loop            : 1.13
% 7.49/2.75  Inferencing          : 0.45
% 7.49/2.75  Reduction            : 0.34
% 7.49/2.75  Demodulation         : 0.23
% 7.49/2.75  BG Simplification    : 0.05
% 7.49/2.75  Subsumption          : 0.21
% 7.49/2.75  Abstraction          : 0.04
% 7.49/2.75  MUC search           : 0.00
% 7.49/2.75  Cooper               : 0.00
% 7.49/2.75  Total                : 1.88
% 7.49/2.75  Index Insertion      : 0.00
% 7.49/2.75  Index Deletion       : 0.00
% 7.49/2.75  Index Matching       : 0.00
% 7.49/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
