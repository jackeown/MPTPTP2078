%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:06 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 5.25s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 768 expanded)
%              Number of leaves         :   44 ( 308 expanded)
%              Depth                    :   24
%              Number of atoms          :  582 (5765 expanded)
%              Number of equality atoms :    5 ( 264 expanded)
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

tff(f_318,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_186,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_179,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_161,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_275,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_226,axiom,(
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

tff(c_54,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_50,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_44,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_82,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_62,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_101,plain,(
    ! [B_318,A_319] :
      ( v2_pre_topc(B_318)
      | ~ m1_pre_topc(B_318,A_319)
      | ~ l1_pre_topc(A_319)
      | ~ v2_pre_topc(A_319) ) ),
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
    ! [B_311,A_312] :
      ( l1_pre_topc(B_311)
      | ~ m1_pre_topc(B_311,A_312)
      | ~ l1_pre_topc(A_312) ) ),
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
    ! [C_336,A_337,B_338] :
      ( m1_subset_1(C_336,k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ m1_connsp_2(C_336,A_337,B_338)
      | ~ m1_subset_1(B_338,u1_struct_0(A_337))
      | ~ l1_pre_topc(A_337)
      | ~ v2_pre_topc(A_337)
      | v2_struct_0(A_337) ) ),
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
    ! [C_352,B_353,A_354] :
      ( r2_hidden(C_352,B_353)
      | ~ m1_connsp_2(B_353,A_354,C_352)
      | ~ m1_subset_1(C_352,u1_struct_0(A_354))
      | ~ m1_subset_1(B_353,k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354)
      | v2_struct_0(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_184,plain,(
    ! [B_355,A_356] :
      ( r2_hidden(B_355,'#skF_1'(A_356,B_355))
      | ~ m1_subset_1('#skF_1'(A_356,B_355),k1_zfmisc_1(u1_struct_0(A_356)))
      | ~ m1_subset_1(B_355,u1_struct_0(A_356))
      | ~ l1_pre_topc(A_356)
      | ~ v2_pre_topc(A_356)
      | v2_struct_0(A_356) ) ),
    inference(resolution,[status(thm)],[c_14,c_180])).

tff(c_188,plain,(
    ! [B_357,A_358] :
      ( r2_hidden(B_357,'#skF_1'(A_358,B_357))
      | ~ m1_subset_1(B_357,u1_struct_0(A_358))
      | ~ l1_pre_topc(A_358)
      | ~ v2_pre_topc(A_358)
      | v2_struct_0(A_358) ) ),
    inference(resolution,[status(thm)],[c_153,c_184])).

tff(c_160,plain,(
    ! [A_343,B_344] :
      ( m1_subset_1('#skF_1'(A_343,B_344),k1_zfmisc_1(u1_struct_0(A_343)))
      | ~ m1_subset_1(B_344,u1_struct_0(A_343))
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(resolution,[status(thm)],[c_14,c_150])).

tff(c_4,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_163,plain,(
    ! [A_343,A_3,B_344] :
      ( ~ v1_xboole_0(u1_struct_0(A_343))
      | ~ r2_hidden(A_3,'#skF_1'(A_343,B_344))
      | ~ m1_subset_1(B_344,u1_struct_0(A_343))
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(resolution,[status(thm)],[c_160,c_4])).

tff(c_193,plain,(
    ! [A_359,B_360] :
      ( ~ v1_xboole_0(u1_struct_0(A_359))
      | ~ m1_subset_1(B_360,u1_struct_0(A_359))
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
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
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_36,plain,(
    ! [B_63,A_61] :
      ( m1_subset_1(u1_struct_0(B_63),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_pre_topc(B_63,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_170,plain,(
    ! [B_348,A_349] :
      ( v3_pre_topc(u1_struct_0(B_348),A_349)
      | ~ v1_tsep_1(B_348,A_349)
      | ~ m1_subset_1(u1_struct_0(B_348),k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ m1_pre_topc(B_348,A_349)
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_174,plain,(
    ! [B_63,A_61] :
      ( v3_pre_topc(u1_struct_0(B_63),A_61)
      | ~ v1_tsep_1(B_63,A_61)
      | ~ v2_pre_topc(A_61)
      | ~ m1_pre_topc(B_63,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_36,c_170])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_283,plain,(
    ! [A_372,B_373,C_374] :
      ( r1_tarski('#skF_2'(A_372,B_373,C_374),C_374)
      | ~ m1_connsp_2(C_374,A_372,B_373)
      | ~ m1_subset_1(C_374,k1_zfmisc_1(u1_struct_0(A_372)))
      | ~ m1_subset_1(B_373,u1_struct_0(A_372))
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_289,plain,(
    ! [A_61,B_373,B_63] :
      ( r1_tarski('#skF_2'(A_61,B_373,u1_struct_0(B_63)),u1_struct_0(B_63))
      | ~ m1_connsp_2(u1_struct_0(B_63),A_61,B_373)
      | ~ m1_subset_1(B_373,u1_struct_0(A_61))
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61)
      | ~ m1_pre_topc(B_63,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_36,c_283])).

tff(c_26,plain,(
    ! [A_40,B_48,C_52] :
      ( m1_subset_1('#skF_2'(A_40,B_48,C_52),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_connsp_2(C_52,A_40,B_48)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_48,u1_struct_0(A_40))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_7')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

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
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_83,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_74])).

tff(c_115,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_83])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_671,plain,(
    ! [B_442,A_443,E_441,D_440,G_439,C_438] :
      ( r1_tmap_1(B_442,A_443,C_438,G_439)
      | ~ r1_tmap_1(D_440,A_443,k2_tmap_1(B_442,A_443,C_438,D_440),G_439)
      | ~ r1_tarski(E_441,u1_struct_0(D_440))
      | ~ r2_hidden(G_439,E_441)
      | ~ v3_pre_topc(E_441,B_442)
      | ~ m1_subset_1(G_439,u1_struct_0(D_440))
      | ~ m1_subset_1(G_439,u1_struct_0(B_442))
      | ~ m1_subset_1(E_441,k1_zfmisc_1(u1_struct_0(B_442)))
      | ~ m1_pre_topc(D_440,B_442)
      | v2_struct_0(D_440)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_442),u1_struct_0(A_443))))
      | ~ v1_funct_2(C_438,u1_struct_0(B_442),u1_struct_0(A_443))
      | ~ v1_funct_1(C_438)
      | ~ l1_pre_topc(B_442)
      | ~ v2_pre_topc(B_442)
      | v2_struct_0(B_442)
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443)
      | v2_struct_0(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_275])).

tff(c_675,plain,(
    ! [E_441] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ r1_tarski(E_441,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',E_441)
      | ~ v3_pre_topc(E_441,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_441,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_113,c_671])).

tff(c_682,plain,(
    ! [E_441] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ r1_tarski(E_441,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',E_441)
      | ~ v3_pre_topc(E_441,'#skF_4')
      | ~ m1_subset_1(E_441,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_56,c_50,c_82,c_46,c_675])).

tff(c_684,plain,(
    ! [E_444] :
      ( ~ r1_tarski(E_444,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',E_444)
      | ~ v3_pre_topc(E_444,'#skF_4')
      | ~ m1_subset_1(E_444,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_54,c_115,c_682])).

tff(c_692,plain,(
    ! [B_48,C_52] :
      ( ~ r1_tarski('#skF_2'('#skF_4',B_48,C_52),u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_48,C_52))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_48,C_52),'#skF_4')
      | ~ m1_connsp_2(C_52,'#skF_4',B_48)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_684])).

tff(c_713,plain,(
    ! [B_48,C_52] :
      ( ~ r1_tarski('#skF_2'('#skF_4',B_48,C_52),u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_48,C_52))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_48,C_52),'#skF_4')
      | ~ m1_connsp_2(C_52,'#skF_4',B_48)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_692])).

tff(c_952,plain,(
    ! [B_467,C_468] :
      ( ~ r1_tarski('#skF_2'('#skF_4',B_467,C_468),u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_467,C_468))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_467,C_468),'#skF_4')
      | ~ m1_connsp_2(C_468,'#skF_4',B_467)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_467,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_713])).

tff(c_960,plain,(
    ! [B_373] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_373,u1_struct_0('#skF_6')))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_373,u1_struct_0('#skF_6')),'#skF_4')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_373)
      | ~ m1_subset_1(B_373,u1_struct_0('#skF_4'))
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_289,c_952])).

tff(c_966,plain,(
    ! [B_373] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_373,u1_struct_0('#skF_6')))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_373,u1_struct_0('#skF_6')),'#skF_4')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_373)
      | ~ m1_subset_1(B_373,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_960])).

tff(c_967,plain,(
    ! [B_373] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_373,u1_struct_0('#skF_6')))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_373,u1_struct_0('#skF_6')),'#skF_4')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_373)
      | ~ m1_subset_1(B_373,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_966])).

tff(c_968,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_967])).

tff(c_974,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_968])).

tff(c_981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_974])).

tff(c_983,plain,(
    m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_117,plain,(
    ! [C_327,A_328,B_329] :
      ( m1_subset_1(C_327,u1_struct_0(A_328))
      | ~ m1_subset_1(C_327,u1_struct_0(B_329))
      | ~ m1_pre_topc(B_329,A_328)
      | v2_struct_0(B_329)
      | ~ l1_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_121,plain,(
    ! [A_328] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_328))
      | ~ m1_pre_topc('#skF_6',A_328)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(resolution,[status(thm)],[c_46,c_117])).

tff(c_127,plain,(
    ! [A_328] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_328))
      | ~ m1_pre_topc('#skF_6',A_328)
      | ~ l1_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_121])).

tff(c_219,plain,(
    ! [B_366,A_367,C_368] :
      ( m1_connsp_2(B_366,A_367,C_368)
      | ~ r2_hidden(C_368,B_366)
      | ~ v3_pre_topc(B_366,A_367)
      | ~ m1_subset_1(C_368,u1_struct_0(A_367))
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0(A_367)))
      | ~ l1_pre_topc(A_367)
      | ~ v2_pre_topc(A_367)
      | v2_struct_0(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_228,plain,(
    ! [B_366,A_328] :
      ( m1_connsp_2(B_366,A_328,'#skF_8')
      | ~ r2_hidden('#skF_8',B_366)
      | ~ v3_pre_topc(B_366,A_328)
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ v2_pre_topc(A_328)
      | ~ m1_pre_topc('#skF_6',A_328)
      | ~ l1_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(resolution,[status(thm)],[c_127,c_219])).

tff(c_998,plain,
    ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_983,c_228])).

tff(c_1022,plain,
    ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_998])).

tff(c_1023,plain,
    ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1022])).

tff(c_1030,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1023])).

tff(c_1033,plain,
    ( ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_174,c_1030])).

tff(c_1037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_52,c_1033])).

tff(c_1038,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1023])).

tff(c_1053,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1038])).

tff(c_1056,plain,
    ( v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2,c_1053])).

tff(c_1059,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1056])).

tff(c_1061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_1059])).

tff(c_1062,plain,(
    m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1038])).

tff(c_24,plain,(
    ! [A_40,B_48,C_52] :
      ( m1_connsp_2('#skF_2'(A_40,B_48,C_52),A_40,B_48)
      | ~ m1_connsp_2(C_52,A_40,B_48)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_48,u1_struct_0(A_40))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_990,plain,(
    ! [B_48] :
      ( m1_connsp_2('#skF_2'('#skF_4',B_48,u1_struct_0('#skF_6')),'#skF_4',B_48)
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_48)
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_983,c_24])).

tff(c_1010,plain,(
    ! [B_48] :
      ( m1_connsp_2('#skF_2'('#skF_4',B_48,u1_struct_0('#skF_6')),'#skF_4',B_48)
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_48)
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_990])).

tff(c_1092,plain,(
    ! [B_479] :
      ( m1_connsp_2('#skF_2'('#skF_4',B_479,u1_struct_0('#skF_6')),'#skF_4',B_479)
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_479)
      | ~ m1_subset_1(B_479,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1010])).

tff(c_12,plain,(
    ! [C_22,A_19,B_20] :
      ( m1_subset_1(C_22,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_connsp_2(C_22,A_19,B_20)
      | ~ m1_subset_1(B_20,u1_struct_0(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1096,plain,(
    ! [B_479] :
      ( m1_subset_1('#skF_2'('#skF_4',B_479,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_479)
      | ~ m1_subset_1(B_479,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1092,c_12])).

tff(c_1103,plain,(
    ! [B_479] :
      ( m1_subset_1('#skF_2'('#skF_4',B_479,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_479)
      | ~ m1_subset_1(B_479,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1096])).

tff(c_1104,plain,(
    ! [B_479] :
      ( m1_subset_1('#skF_2'('#skF_4',B_479,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_479)
      | ~ m1_subset_1(B_479,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1103])).

tff(c_506,plain,(
    ! [A_398,B_399,C_400] :
      ( m1_connsp_2('#skF_2'(A_398,B_399,C_400),A_398,B_399)
      | ~ m1_connsp_2(C_400,A_398,B_399)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(u1_struct_0(A_398)))
      | ~ m1_subset_1(B_399,u1_struct_0(A_398))
      | ~ l1_pre_topc(A_398)
      | ~ v2_pre_topc(A_398)
      | v2_struct_0(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_538,plain,(
    ! [A_404,B_405,B_406] :
      ( m1_connsp_2('#skF_2'(A_404,B_405,u1_struct_0(B_406)),A_404,B_405)
      | ~ m1_connsp_2(u1_struct_0(B_406),A_404,B_405)
      | ~ m1_subset_1(B_405,u1_struct_0(A_404))
      | ~ v2_pre_topc(A_404)
      | v2_struct_0(A_404)
      | ~ m1_pre_topc(B_406,A_404)
      | ~ l1_pre_topc(A_404) ) ),
    inference(resolution,[status(thm)],[c_36,c_506])).

tff(c_18,plain,(
    ! [C_39,B_37,A_33] :
      ( r2_hidden(C_39,B_37)
      | ~ m1_connsp_2(B_37,A_33,C_39)
      | ~ m1_subset_1(C_39,u1_struct_0(A_33))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1178,plain,(
    ! [B_484,A_485,B_486] :
      ( r2_hidden(B_484,'#skF_2'(A_485,B_484,u1_struct_0(B_486)))
      | ~ m1_subset_1('#skF_2'(A_485,B_484,u1_struct_0(B_486)),k1_zfmisc_1(u1_struct_0(A_485)))
      | ~ m1_connsp_2(u1_struct_0(B_486),A_485,B_484)
      | ~ m1_subset_1(B_484,u1_struct_0(A_485))
      | ~ v2_pre_topc(A_485)
      | v2_struct_0(A_485)
      | ~ m1_pre_topc(B_486,A_485)
      | ~ l1_pre_topc(A_485) ) ),
    inference(resolution,[status(thm)],[c_538,c_18])).

tff(c_1180,plain,(
    ! [B_479] :
      ( r2_hidden(B_479,'#skF_2'('#skF_4',B_479,u1_struct_0('#skF_6')))
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_479)
      | ~ m1_subset_1(B_479,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1104,c_1178])).

tff(c_1192,plain,(
    ! [B_479] :
      ( r2_hidden(B_479,'#skF_2'('#skF_4',B_479,u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_4')
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_479)
      | ~ m1_subset_1(B_479,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_1180])).

tff(c_1204,plain,(
    ! [B_487] :
      ( r2_hidden(B_487,'#skF_2'('#skF_4',B_487,u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_487)
      | ~ m1_subset_1(B_487,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1192])).

tff(c_459,plain,(
    ! [A_386,B_387,C_388] :
      ( v3_pre_topc('#skF_2'(A_386,B_387,C_388),A_386)
      | ~ m1_connsp_2(C_388,A_386,B_387)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ m1_subset_1(B_387,u1_struct_0(A_386))
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386)
      | v2_struct_0(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_489,plain,(
    ! [A_61,B_387,B_63] :
      ( v3_pre_topc('#skF_2'(A_61,B_387,u1_struct_0(B_63)),A_61)
      | ~ m1_connsp_2(u1_struct_0(B_63),A_61,B_387)
      | ~ m1_subset_1(B_387,u1_struct_0(A_61))
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61)
      | ~ m1_pre_topc(B_63,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_36,c_459])).

tff(c_1152,plain,(
    ! [B_481] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_481,u1_struct_0('#skF_6')))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_481,u1_struct_0('#skF_6')),'#skF_4')
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_481)
      | ~ m1_subset_1(B_481,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_1163,plain,(
    ! [B_387] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_387,u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_387)
      | ~ m1_subset_1(B_387,u1_struct_0('#skF_4'))
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_489,c_1152])).

tff(c_1170,plain,(
    ! [B_387] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_387,u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_387)
      | ~ m1_subset_1(B_387,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_1163])).

tff(c_1171,plain,(
    ! [B_387] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_387,u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_387)
      | ~ m1_subset_1(B_387,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1170])).

tff(c_1208,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1204,c_1171])).

tff(c_1212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1062,c_1208])).

tff(c_1213,plain,(
    r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_1764,plain,(
    ! [A_598,F_594,C_596,D_595,B_597] :
      ( r1_tmap_1(D_595,A_598,k2_tmap_1(B_597,A_598,C_596,D_595),F_594)
      | ~ r1_tmap_1(B_597,A_598,C_596,F_594)
      | ~ m1_subset_1(F_594,u1_struct_0(D_595))
      | ~ m1_subset_1(F_594,u1_struct_0(B_597))
      | ~ m1_pre_topc(D_595,B_597)
      | v2_struct_0(D_595)
      | ~ m1_subset_1(C_596,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_597),u1_struct_0(A_598))))
      | ~ v1_funct_2(C_596,u1_struct_0(B_597),u1_struct_0(A_598))
      | ~ v1_funct_1(C_596)
      | ~ l1_pre_topc(B_597)
      | ~ v2_pre_topc(B_597)
      | v2_struct_0(B_597)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_1766,plain,(
    ! [D_595,F_594] :
      ( r1_tmap_1(D_595,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_595),F_594)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_594)
      | ~ m1_subset_1(F_594,u1_struct_0(D_595))
      | ~ m1_subset_1(F_594,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_595,'#skF_4')
      | v2_struct_0(D_595)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_1764])).

tff(c_1769,plain,(
    ! [D_595,F_594] :
      ( r1_tmap_1(D_595,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_595),F_594)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_594)
      | ~ m1_subset_1(F_594,u1_struct_0(D_595))
      | ~ m1_subset_1(F_594,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_595,'#skF_4')
      | v2_struct_0(D_595)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_1766])).

tff(c_1771,plain,(
    ! [D_599,F_600] :
      ( r1_tmap_1(D_599,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_599),F_600)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_600)
      | ~ m1_subset_1(F_600,u1_struct_0(D_599))
      | ~ m1_subset_1(F_600,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_599,'#skF_4')
      | v2_struct_0(D_599) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_1769])).

tff(c_1214,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_1774,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1771,c_1214])).

tff(c_1777,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_82,c_46,c_1213,c_1774])).

tff(c_1779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1777])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.25/1.99  
% 5.25/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.25/2.00  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4 > #skF_1
% 5.25/2.00  
% 5.25/2.00  %Foreground sorts:
% 5.25/2.00  
% 5.25/2.00  
% 5.25/2.00  %Background operators:
% 5.25/2.00  
% 5.25/2.00  
% 5.25/2.00  %Foreground operators:
% 5.25/2.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.25/2.00  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.25/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.25/2.00  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.25/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.25/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.25/2.00  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.25/2.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.25/2.00  tff('#skF_7', type, '#skF_7': $i).
% 5.25/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.25/2.00  tff('#skF_5', type, '#skF_5': $i).
% 5.25/2.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.25/2.00  tff('#skF_6', type, '#skF_6': $i).
% 5.25/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.25/2.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.25/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.25/2.00  tff('#skF_8', type, '#skF_8': $i).
% 5.25/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.25/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.25/2.00  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.25/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.25/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.25/2.00  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.25/2.00  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.25/2.00  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.25/2.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.25/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.25/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.25/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.25/2.00  
% 5.25/2.03  tff(f_318, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 5.25/2.03  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.25/2.03  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.25/2.03  tff(f_96, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 5.25/2.03  tff(f_84, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 5.25/2.03  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 5.25/2.03  tff(f_38, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.25/2.03  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.25/2.03  tff(f_186, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.25/2.03  tff(f_179, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 5.25/2.03  tff(f_161, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 5.25/2.03  tff(f_275, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tmap_1)).
% 5.25/2.03  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 5.25/2.03  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 5.25/2.03  tff(f_226, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 5.25/2.03  tff(c_54, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_50, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_44, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_82, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48])).
% 5.25/2.03  tff(c_46, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_62, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_101, plain, (![B_318, A_319]: (v2_pre_topc(B_318) | ~m1_pre_topc(B_318, A_319) | ~l1_pre_topc(A_319) | ~v2_pre_topc(A_319))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.25/2.03  tff(c_104, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_101])).
% 5.25/2.03  tff(c_107, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_104])).
% 5.25/2.03  tff(c_88, plain, (![B_311, A_312]: (l1_pre_topc(B_311) | ~m1_pre_topc(B_311, A_312) | ~l1_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.25/2.03  tff(c_91, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_88])).
% 5.25/2.03  tff(c_94, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91])).
% 5.25/2.03  tff(c_14, plain, (![A_23, B_24]: (m1_connsp_2('#skF_1'(A_23, B_24), A_23, B_24) | ~m1_subset_1(B_24, u1_struct_0(A_23)) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.25/2.03  tff(c_150, plain, (![C_336, A_337, B_338]: (m1_subset_1(C_336, k1_zfmisc_1(u1_struct_0(A_337))) | ~m1_connsp_2(C_336, A_337, B_338) | ~m1_subset_1(B_338, u1_struct_0(A_337)) | ~l1_pre_topc(A_337) | ~v2_pre_topc(A_337) | v2_struct_0(A_337))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.25/2.03  tff(c_153, plain, (![A_23, B_24]: (m1_subset_1('#skF_1'(A_23, B_24), k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_24, u1_struct_0(A_23)) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_14, c_150])).
% 5.25/2.03  tff(c_180, plain, (![C_352, B_353, A_354]: (r2_hidden(C_352, B_353) | ~m1_connsp_2(B_353, A_354, C_352) | ~m1_subset_1(C_352, u1_struct_0(A_354)) | ~m1_subset_1(B_353, k1_zfmisc_1(u1_struct_0(A_354))) | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354) | v2_struct_0(A_354))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.25/2.03  tff(c_184, plain, (![B_355, A_356]: (r2_hidden(B_355, '#skF_1'(A_356, B_355)) | ~m1_subset_1('#skF_1'(A_356, B_355), k1_zfmisc_1(u1_struct_0(A_356))) | ~m1_subset_1(B_355, u1_struct_0(A_356)) | ~l1_pre_topc(A_356) | ~v2_pre_topc(A_356) | v2_struct_0(A_356))), inference(resolution, [status(thm)], [c_14, c_180])).
% 5.25/2.03  tff(c_188, plain, (![B_357, A_358]: (r2_hidden(B_357, '#skF_1'(A_358, B_357)) | ~m1_subset_1(B_357, u1_struct_0(A_358)) | ~l1_pre_topc(A_358) | ~v2_pre_topc(A_358) | v2_struct_0(A_358))), inference(resolution, [status(thm)], [c_153, c_184])).
% 5.25/2.03  tff(c_160, plain, (![A_343, B_344]: (m1_subset_1('#skF_1'(A_343, B_344), k1_zfmisc_1(u1_struct_0(A_343))) | ~m1_subset_1(B_344, u1_struct_0(A_343)) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(resolution, [status(thm)], [c_14, c_150])).
% 5.25/2.03  tff(c_4, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.25/2.03  tff(c_163, plain, (![A_343, A_3, B_344]: (~v1_xboole_0(u1_struct_0(A_343)) | ~r2_hidden(A_3, '#skF_1'(A_343, B_344)) | ~m1_subset_1(B_344, u1_struct_0(A_343)) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(resolution, [status(thm)], [c_160, c_4])).
% 5.25/2.03  tff(c_193, plain, (![A_359, B_360]: (~v1_xboole_0(u1_struct_0(A_359)) | ~m1_subset_1(B_360, u1_struct_0(A_359)) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(resolution, [status(thm)], [c_188, c_163])).
% 5.25/2.03  tff(c_205, plain, (~v1_xboole_0(u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_46, c_193])).
% 5.25/2.03  tff(c_214, plain, (~v1_xboole_0(u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_94, c_205])).
% 5.25/2.03  tff(c_215, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_54, c_214])).
% 5.25/2.03  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.25/2.03  tff(c_52, plain, (v1_tsep_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_36, plain, (![B_63, A_61]: (m1_subset_1(u1_struct_0(B_63), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_pre_topc(B_63, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.25/2.03  tff(c_170, plain, (![B_348, A_349]: (v3_pre_topc(u1_struct_0(B_348), A_349) | ~v1_tsep_1(B_348, A_349) | ~m1_subset_1(u1_struct_0(B_348), k1_zfmisc_1(u1_struct_0(A_349))) | ~m1_pre_topc(B_348, A_349) | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.25/2.03  tff(c_174, plain, (![B_63, A_61]: (v3_pre_topc(u1_struct_0(B_63), A_61) | ~v1_tsep_1(B_63, A_61) | ~v2_pre_topc(A_61) | ~m1_pre_topc(B_63, A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_36, c_170])).
% 5.25/2.03  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_283, plain, (![A_372, B_373, C_374]: (r1_tarski('#skF_2'(A_372, B_373, C_374), C_374) | ~m1_connsp_2(C_374, A_372, B_373) | ~m1_subset_1(C_374, k1_zfmisc_1(u1_struct_0(A_372))) | ~m1_subset_1(B_373, u1_struct_0(A_372)) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372) | v2_struct_0(A_372))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.25/2.03  tff(c_289, plain, (![A_61, B_373, B_63]: (r1_tarski('#skF_2'(A_61, B_373, u1_struct_0(B_63)), u1_struct_0(B_63)) | ~m1_connsp_2(u1_struct_0(B_63), A_61, B_373) | ~m1_subset_1(B_373, u1_struct_0(A_61)) | ~v2_pre_topc(A_61) | v2_struct_0(A_61) | ~m1_pre_topc(B_63, A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_36, c_283])).
% 5.25/2.03  tff(c_26, plain, (![A_40, B_48, C_52]: (m1_subset_1('#skF_2'(A_40, B_48, C_52), k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_connsp_2(C_52, A_40, B_48) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_48, u1_struct_0(A_40)) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.25/2.03  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_80, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_81, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_80])).
% 5.25/2.03  tff(c_113, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_81])).
% 5.25/2.03  tff(c_74, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_83, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_74])).
% 5.25/2.03  tff(c_115, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_83])).
% 5.25/2.03  tff(c_70, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_68, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_58, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_318])).
% 5.25/2.03  tff(c_671, plain, (![B_442, A_443, E_441, D_440, G_439, C_438]: (r1_tmap_1(B_442, A_443, C_438, G_439) | ~r1_tmap_1(D_440, A_443, k2_tmap_1(B_442, A_443, C_438, D_440), G_439) | ~r1_tarski(E_441, u1_struct_0(D_440)) | ~r2_hidden(G_439, E_441) | ~v3_pre_topc(E_441, B_442) | ~m1_subset_1(G_439, u1_struct_0(D_440)) | ~m1_subset_1(G_439, u1_struct_0(B_442)) | ~m1_subset_1(E_441, k1_zfmisc_1(u1_struct_0(B_442))) | ~m1_pre_topc(D_440, B_442) | v2_struct_0(D_440) | ~m1_subset_1(C_438, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_442), u1_struct_0(A_443)))) | ~v1_funct_2(C_438, u1_struct_0(B_442), u1_struct_0(A_443)) | ~v1_funct_1(C_438) | ~l1_pre_topc(B_442) | ~v2_pre_topc(B_442) | v2_struct_0(B_442) | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443) | v2_struct_0(A_443))), inference(cnfTransformation, [status(thm)], [f_275])).
% 5.25/2.03  tff(c_675, plain, (![E_441]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~r1_tarski(E_441, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', E_441) | ~v3_pre_topc(E_441, '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_441, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_113, c_671])).
% 5.25/2.03  tff(c_682, plain, (![E_441]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~r1_tarski(E_441, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', E_441) | ~v3_pre_topc(E_441, '#skF_4') | ~m1_subset_1(E_441, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_56, c_50, c_82, c_46, c_675])).
% 5.25/2.03  tff(c_684, plain, (![E_444]: (~r1_tarski(E_444, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', E_444) | ~v3_pre_topc(E_444, '#skF_4') | ~m1_subset_1(E_444, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_54, c_115, c_682])).
% 5.25/2.03  tff(c_692, plain, (![B_48, C_52]: (~r1_tarski('#skF_2'('#skF_4', B_48, C_52), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_48, C_52)) | ~v3_pre_topc('#skF_2'('#skF_4', B_48, C_52), '#skF_4') | ~m1_connsp_2(C_52, '#skF_4', B_48) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_48, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_684])).
% 5.25/2.03  tff(c_713, plain, (![B_48, C_52]: (~r1_tarski('#skF_2'('#skF_4', B_48, C_52), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_48, C_52)) | ~v3_pre_topc('#skF_2'('#skF_4', B_48, C_52), '#skF_4') | ~m1_connsp_2(C_52, '#skF_4', B_48) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_48, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_692])).
% 5.25/2.03  tff(c_952, plain, (![B_467, C_468]: (~r1_tarski('#skF_2'('#skF_4', B_467, C_468), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_467, C_468)) | ~v3_pre_topc('#skF_2'('#skF_4', B_467, C_468), '#skF_4') | ~m1_connsp_2(C_468, '#skF_4', B_467) | ~m1_subset_1(C_468, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_467, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_713])).
% 5.25/2.03  tff(c_960, plain, (![B_373]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_373, u1_struct_0('#skF_6'))) | ~v3_pre_topc('#skF_2'('#skF_4', B_373, u1_struct_0('#skF_6')), '#skF_4') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_373) | ~m1_subset_1(B_373, u1_struct_0('#skF_4')) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_289, c_952])).
% 5.25/2.03  tff(c_966, plain, (![B_373]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_373, u1_struct_0('#skF_6'))) | ~v3_pre_topc('#skF_2'('#skF_4', B_373, u1_struct_0('#skF_6')), '#skF_4') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_373) | ~m1_subset_1(B_373, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_960])).
% 5.25/2.03  tff(c_967, plain, (![B_373]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_373, u1_struct_0('#skF_6'))) | ~v3_pre_topc('#skF_2'('#skF_4', B_373, u1_struct_0('#skF_6')), '#skF_4') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_373) | ~m1_subset_1(B_373, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_966])).
% 5.25/2.03  tff(c_968, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_967])).
% 5.25/2.03  tff(c_974, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_968])).
% 5.25/2.03  tff(c_981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_974])).
% 5.25/2.03  tff(c_983, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_967])).
% 5.25/2.03  tff(c_117, plain, (![C_327, A_328, B_329]: (m1_subset_1(C_327, u1_struct_0(A_328)) | ~m1_subset_1(C_327, u1_struct_0(B_329)) | ~m1_pre_topc(B_329, A_328) | v2_struct_0(B_329) | ~l1_pre_topc(A_328) | v2_struct_0(A_328))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.25/2.03  tff(c_121, plain, (![A_328]: (m1_subset_1('#skF_8', u1_struct_0(A_328)) | ~m1_pre_topc('#skF_6', A_328) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_328) | v2_struct_0(A_328))), inference(resolution, [status(thm)], [c_46, c_117])).
% 5.25/2.03  tff(c_127, plain, (![A_328]: (m1_subset_1('#skF_8', u1_struct_0(A_328)) | ~m1_pre_topc('#skF_6', A_328) | ~l1_pre_topc(A_328) | v2_struct_0(A_328))), inference(negUnitSimplification, [status(thm)], [c_54, c_121])).
% 5.25/2.03  tff(c_219, plain, (![B_366, A_367, C_368]: (m1_connsp_2(B_366, A_367, C_368) | ~r2_hidden(C_368, B_366) | ~v3_pre_topc(B_366, A_367) | ~m1_subset_1(C_368, u1_struct_0(A_367)) | ~m1_subset_1(B_366, k1_zfmisc_1(u1_struct_0(A_367))) | ~l1_pre_topc(A_367) | ~v2_pre_topc(A_367) | v2_struct_0(A_367))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.25/2.03  tff(c_228, plain, (![B_366, A_328]: (m1_connsp_2(B_366, A_328, '#skF_8') | ~r2_hidden('#skF_8', B_366) | ~v3_pre_topc(B_366, A_328) | ~m1_subset_1(B_366, k1_zfmisc_1(u1_struct_0(A_328))) | ~v2_pre_topc(A_328) | ~m1_pre_topc('#skF_6', A_328) | ~l1_pre_topc(A_328) | v2_struct_0(A_328))), inference(resolution, [status(thm)], [c_127, c_219])).
% 5.25/2.03  tff(c_998, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_983, c_228])).
% 5.25/2.03  tff(c_1022, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_998])).
% 5.25/2.03  tff(c_1023, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_1022])).
% 5.25/2.03  tff(c_1030, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1023])).
% 5.25/2.03  tff(c_1033, plain, (~v1_tsep_1('#skF_6', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_174, c_1030])).
% 5.25/2.03  tff(c_1037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_52, c_1033])).
% 5.25/2.03  tff(c_1038, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_1023])).
% 5.25/2.03  tff(c_1053, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1038])).
% 5.25/2.03  tff(c_1056, plain, (v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_2, c_1053])).
% 5.25/2.03  tff(c_1059, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1056])).
% 5.25/2.03  tff(c_1061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215, c_1059])).
% 5.25/2.03  tff(c_1062, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_1038])).
% 5.25/2.03  tff(c_24, plain, (![A_40, B_48, C_52]: (m1_connsp_2('#skF_2'(A_40, B_48, C_52), A_40, B_48) | ~m1_connsp_2(C_52, A_40, B_48) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_48, u1_struct_0(A_40)) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.25/2.03  tff(c_990, plain, (![B_48]: (m1_connsp_2('#skF_2'('#skF_4', B_48, u1_struct_0('#skF_6')), '#skF_4', B_48) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_48) | ~m1_subset_1(B_48, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_983, c_24])).
% 5.25/2.03  tff(c_1010, plain, (![B_48]: (m1_connsp_2('#skF_2'('#skF_4', B_48, u1_struct_0('#skF_6')), '#skF_4', B_48) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_48) | ~m1_subset_1(B_48, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_990])).
% 5.25/2.03  tff(c_1092, plain, (![B_479]: (m1_connsp_2('#skF_2'('#skF_4', B_479, u1_struct_0('#skF_6')), '#skF_4', B_479) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_479) | ~m1_subset_1(B_479, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1010])).
% 5.25/2.03  tff(c_12, plain, (![C_22, A_19, B_20]: (m1_subset_1(C_22, k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_connsp_2(C_22, A_19, B_20) | ~m1_subset_1(B_20, u1_struct_0(A_19)) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.25/2.03  tff(c_1096, plain, (![B_479]: (m1_subset_1('#skF_2'('#skF_4', B_479, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_479) | ~m1_subset_1(B_479, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1092, c_12])).
% 5.25/2.03  tff(c_1103, plain, (![B_479]: (m1_subset_1('#skF_2'('#skF_4', B_479, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_479) | ~m1_subset_1(B_479, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1096])).
% 5.25/2.03  tff(c_1104, plain, (![B_479]: (m1_subset_1('#skF_2'('#skF_4', B_479, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_479) | ~m1_subset_1(B_479, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1103])).
% 5.25/2.03  tff(c_506, plain, (![A_398, B_399, C_400]: (m1_connsp_2('#skF_2'(A_398, B_399, C_400), A_398, B_399) | ~m1_connsp_2(C_400, A_398, B_399) | ~m1_subset_1(C_400, k1_zfmisc_1(u1_struct_0(A_398))) | ~m1_subset_1(B_399, u1_struct_0(A_398)) | ~l1_pre_topc(A_398) | ~v2_pre_topc(A_398) | v2_struct_0(A_398))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.25/2.03  tff(c_538, plain, (![A_404, B_405, B_406]: (m1_connsp_2('#skF_2'(A_404, B_405, u1_struct_0(B_406)), A_404, B_405) | ~m1_connsp_2(u1_struct_0(B_406), A_404, B_405) | ~m1_subset_1(B_405, u1_struct_0(A_404)) | ~v2_pre_topc(A_404) | v2_struct_0(A_404) | ~m1_pre_topc(B_406, A_404) | ~l1_pre_topc(A_404))), inference(resolution, [status(thm)], [c_36, c_506])).
% 5.25/2.03  tff(c_18, plain, (![C_39, B_37, A_33]: (r2_hidden(C_39, B_37) | ~m1_connsp_2(B_37, A_33, C_39) | ~m1_subset_1(C_39, u1_struct_0(A_33)) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.25/2.03  tff(c_1178, plain, (![B_484, A_485, B_486]: (r2_hidden(B_484, '#skF_2'(A_485, B_484, u1_struct_0(B_486))) | ~m1_subset_1('#skF_2'(A_485, B_484, u1_struct_0(B_486)), k1_zfmisc_1(u1_struct_0(A_485))) | ~m1_connsp_2(u1_struct_0(B_486), A_485, B_484) | ~m1_subset_1(B_484, u1_struct_0(A_485)) | ~v2_pre_topc(A_485) | v2_struct_0(A_485) | ~m1_pre_topc(B_486, A_485) | ~l1_pre_topc(A_485))), inference(resolution, [status(thm)], [c_538, c_18])).
% 5.25/2.03  tff(c_1180, plain, (![B_479]: (r2_hidden(B_479, '#skF_2'('#skF_4', B_479, u1_struct_0('#skF_6'))) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_479) | ~m1_subset_1(B_479, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1104, c_1178])).
% 5.25/2.03  tff(c_1192, plain, (![B_479]: (r2_hidden(B_479, '#skF_2'('#skF_4', B_479, u1_struct_0('#skF_6'))) | v2_struct_0('#skF_4') | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_479) | ~m1_subset_1(B_479, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_1180])).
% 5.25/2.03  tff(c_1204, plain, (![B_487]: (r2_hidden(B_487, '#skF_2'('#skF_4', B_487, u1_struct_0('#skF_6'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_487) | ~m1_subset_1(B_487, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1192])).
% 5.25/2.03  tff(c_459, plain, (![A_386, B_387, C_388]: (v3_pre_topc('#skF_2'(A_386, B_387, C_388), A_386) | ~m1_connsp_2(C_388, A_386, B_387) | ~m1_subset_1(C_388, k1_zfmisc_1(u1_struct_0(A_386))) | ~m1_subset_1(B_387, u1_struct_0(A_386)) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386) | v2_struct_0(A_386))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.25/2.03  tff(c_489, plain, (![A_61, B_387, B_63]: (v3_pre_topc('#skF_2'(A_61, B_387, u1_struct_0(B_63)), A_61) | ~m1_connsp_2(u1_struct_0(B_63), A_61, B_387) | ~m1_subset_1(B_387, u1_struct_0(A_61)) | ~v2_pre_topc(A_61) | v2_struct_0(A_61) | ~m1_pre_topc(B_63, A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_36, c_459])).
% 5.25/2.03  tff(c_1152, plain, (![B_481]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_481, u1_struct_0('#skF_6'))) | ~v3_pre_topc('#skF_2'('#skF_4', B_481, u1_struct_0('#skF_6')), '#skF_4') | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_481) | ~m1_subset_1(B_481, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_967])).
% 5.25/2.03  tff(c_1163, plain, (![B_387]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_387, u1_struct_0('#skF_6'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_387) | ~m1_subset_1(B_387, u1_struct_0('#skF_4')) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_489, c_1152])).
% 5.25/2.03  tff(c_1170, plain, (![B_387]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_387, u1_struct_0('#skF_6'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_387) | ~m1_subset_1(B_387, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_1163])).
% 5.25/2.03  tff(c_1171, plain, (![B_387]: (~r2_hidden('#skF_8', '#skF_2'('#skF_4', B_387, u1_struct_0('#skF_6'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_387) | ~m1_subset_1(B_387, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1170])).
% 5.25/2.03  tff(c_1208, plain, (~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1204, c_1171])).
% 5.25/2.03  tff(c_1212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_1062, c_1208])).
% 5.25/2.03  tff(c_1213, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 5.25/2.03  tff(c_1764, plain, (![A_598, F_594, C_596, D_595, B_597]: (r1_tmap_1(D_595, A_598, k2_tmap_1(B_597, A_598, C_596, D_595), F_594) | ~r1_tmap_1(B_597, A_598, C_596, F_594) | ~m1_subset_1(F_594, u1_struct_0(D_595)) | ~m1_subset_1(F_594, u1_struct_0(B_597)) | ~m1_pre_topc(D_595, B_597) | v2_struct_0(D_595) | ~m1_subset_1(C_596, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_597), u1_struct_0(A_598)))) | ~v1_funct_2(C_596, u1_struct_0(B_597), u1_struct_0(A_598)) | ~v1_funct_1(C_596) | ~l1_pre_topc(B_597) | ~v2_pre_topc(B_597) | v2_struct_0(B_597) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598))), inference(cnfTransformation, [status(thm)], [f_226])).
% 5.25/2.03  tff(c_1766, plain, (![D_595, F_594]: (r1_tmap_1(D_595, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_595), F_594) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_594) | ~m1_subset_1(F_594, u1_struct_0(D_595)) | ~m1_subset_1(F_594, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_595, '#skF_4') | v2_struct_0(D_595) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_1764])).
% 5.25/2.03  tff(c_1769, plain, (![D_595, F_594]: (r1_tmap_1(D_595, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_595), F_594) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_594) | ~m1_subset_1(F_594, u1_struct_0(D_595)) | ~m1_subset_1(F_594, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_595, '#skF_4') | v2_struct_0(D_595) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_1766])).
% 5.25/2.03  tff(c_1771, plain, (![D_599, F_600]: (r1_tmap_1(D_599, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_599), F_600) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_600) | ~m1_subset_1(F_600, u1_struct_0(D_599)) | ~m1_subset_1(F_600, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_599, '#skF_4') | v2_struct_0(D_599))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_1769])).
% 5.25/2.03  tff(c_1214, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 5.25/2.03  tff(c_1774, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1771, c_1214])).
% 5.25/2.03  tff(c_1777, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_82, c_46, c_1213, c_1774])).
% 5.25/2.03  tff(c_1779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1777])).
% 5.25/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.25/2.03  
% 5.25/2.03  Inference rules
% 5.25/2.03  ----------------------
% 5.25/2.03  #Ref     : 0
% 5.25/2.03  #Sup     : 307
% 5.25/2.03  #Fact    : 0
% 5.25/2.03  #Define  : 0
% 5.25/2.03  #Split   : 6
% 5.25/2.03  #Chain   : 0
% 5.25/2.03  #Close   : 0
% 5.25/2.03  
% 5.25/2.03  Ordering : KBO
% 5.25/2.03  
% 5.25/2.03  Simplification rules
% 5.25/2.03  ----------------------
% 5.25/2.03  #Subsume      : 66
% 5.25/2.03  #Demod        : 370
% 5.25/2.03  #Tautology    : 31
% 5.25/2.03  #SimpNegUnit  : 141
% 5.25/2.03  #BackRed      : 0
% 5.25/2.03  
% 5.25/2.03  #Partial instantiations: 0
% 5.25/2.03  #Strategies tried      : 1
% 5.25/2.03  
% 5.25/2.03  Timing (in seconds)
% 5.25/2.03  ----------------------
% 5.25/2.03  Preprocessing        : 0.50
% 5.25/2.03  Parsing              : 0.27
% 5.25/2.03  CNF conversion       : 0.06
% 5.25/2.03  Main loop            : 0.67
% 5.25/2.03  Inferencing          : 0.27
% 5.25/2.03  Reduction            : 0.20
% 5.25/2.03  Demodulation         : 0.14
% 5.25/2.03  BG Simplification    : 0.04
% 5.25/2.03  Subsumption          : 0.12
% 5.25/2.03  Abstraction          : 0.03
% 5.25/2.03  MUC search           : 0.00
% 5.25/2.03  Cooper               : 0.00
% 5.25/2.03  Total                : 1.23
% 5.25/2.03  Index Insertion      : 0.00
% 5.25/2.03  Index Deletion       : 0.00
% 5.25/2.03  Index Matching       : 0.00
% 5.25/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
