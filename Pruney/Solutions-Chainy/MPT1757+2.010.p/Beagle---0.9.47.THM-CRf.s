%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:05 EST 2020

% Result     : Theorem 5.31s
% Output     : CNFRefutation 5.64s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 602 expanded)
%              Number of leaves         :   41 ( 247 expanded)
%              Depth                    :   19
%              Number of atoms          :  407 (4459 expanded)
%              Number of equality atoms :    5 ( 215 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_310,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_180,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_173,axiom,(
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

tff(f_155,axiom,(
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

tff(f_267,axiom,(
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

tff(f_126,axiom,(
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

tff(f_220,axiom,(
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
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_50,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_44,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_81,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_95,plain,(
    ! [B_310,A_311] :
      ( v2_pre_topc(B_310)
      | ~ m1_pre_topc(B_310,A_311)
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_95])).

tff(c_101,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_98])).

tff(c_88,plain,(
    ! [B_308,A_309] :
      ( l1_pre_topc(B_308)
      | ~ m1_pre_topc(B_308,A_309)
      | ~ l1_pre_topc(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_94,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91])).

tff(c_12,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k1_connsp_2(A_21,B_22),k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_22,u1_struct_0(A_21))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_116,plain,(
    ! [B_324,A_325] :
      ( r2_hidden(B_324,k1_connsp_2(A_325,B_324))
      | ~ m1_subset_1(B_324,u1_struct_0(A_325))
      | ~ l1_pre_topc(A_325)
      | ~ v2_pre_topc(A_325)
      | v2_struct_0(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_164,plain,(
    ! [B_344,A_345,A_346] :
      ( r2_hidden(B_344,A_345)
      | ~ m1_subset_1(k1_connsp_2(A_346,B_344),k1_zfmisc_1(A_345))
      | ~ m1_subset_1(B_344,u1_struct_0(A_346))
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_168,plain,(
    ! [B_22,A_21] :
      ( r2_hidden(B_22,u1_struct_0(A_21))
      | ~ m1_subset_1(B_22,u1_struct_0(A_21))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_12,c_164])).

tff(c_52,plain,(
    v1_tsep_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_36,plain,(
    ! [B_60,A_58] :
      ( m1_subset_1(u1_struct_0(B_60),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_pre_topc(B_60,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_158,plain,(
    ! [B_340,A_341] :
      ( v3_pre_topc(u1_struct_0(B_340),A_341)
      | ~ v1_tsep_1(B_340,A_341)
      | ~ m1_subset_1(u1_struct_0(B_340),k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ m1_pre_topc(B_340,A_341)
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_162,plain,(
    ! [B_60,A_58] :
      ( v3_pre_topc(u1_struct_0(B_60),A_58)
      | ~ v1_tsep_1(B_60,A_58)
      | ~ v2_pre_topc(A_58)
      | ~ m1_pre_topc(B_60,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_36,c_158])).

tff(c_287,plain,(
    ! [A_383,B_384,C_385] :
      ( r1_tarski('#skF_1'(A_383,B_384,C_385),C_385)
      | ~ m1_connsp_2(C_385,A_383,B_384)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(u1_struct_0(A_383)))
      | ~ m1_subset_1(B_384,u1_struct_0(A_383))
      | ~ l1_pre_topc(A_383)
      | ~ v2_pre_topc(A_383)
      | v2_struct_0(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_853,plain,(
    ! [A_459,B_460,B_461] :
      ( r1_tarski('#skF_1'(A_459,B_460,u1_struct_0(B_461)),u1_struct_0(B_461))
      | ~ m1_connsp_2(u1_struct_0(B_461),A_459,B_460)
      | ~ m1_subset_1(B_460,u1_struct_0(A_459))
      | ~ v2_pre_topc(A_459)
      | v2_struct_0(A_459)
      | ~ m1_pre_topc(B_461,A_459)
      | ~ l1_pre_topc(A_459) ) ),
    inference(resolution,[status(thm)],[c_36,c_287])).

tff(c_26,plain,(
    ! [A_37,B_45,C_49] :
      ( m1_subset_1('#skF_1'(A_37,B_45,C_49),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_connsp_2(C_49,A_37,B_45)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(B_45,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_80])).

tff(c_102,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_74,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_83,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_74])).

tff(c_114,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_83])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_755,plain,(
    ! [A_440,B_439,C_441,D_443,E_444,G_442] :
      ( r1_tmap_1(B_439,A_440,C_441,G_442)
      | ~ r1_tmap_1(D_443,A_440,k2_tmap_1(B_439,A_440,C_441,D_443),G_442)
      | ~ m1_connsp_2(E_444,B_439,G_442)
      | ~ r1_tarski(E_444,u1_struct_0(D_443))
      | ~ m1_subset_1(G_442,u1_struct_0(D_443))
      | ~ m1_subset_1(G_442,u1_struct_0(B_439))
      | ~ m1_subset_1(E_444,k1_zfmisc_1(u1_struct_0(B_439)))
      | ~ m1_pre_topc(D_443,B_439)
      | v2_struct_0(D_443)
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_439),u1_struct_0(A_440))))
      | ~ v1_funct_2(C_441,u1_struct_0(B_439),u1_struct_0(A_440))
      | ~ v1_funct_1(C_441)
      | ~ l1_pre_topc(B_439)
      | ~ v2_pre_topc(B_439)
      | v2_struct_0(B_439)
      | ~ l1_pre_topc(A_440)
      | ~ v2_pre_topc(A_440)
      | v2_struct_0(A_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_759,plain,(
    ! [E_444] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_444,'#skF_3','#skF_6')
      | ~ r1_tarski(E_444,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_444,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_102,c_755])).

tff(c_766,plain,(
    ! [E_444] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_444,'#skF_3','#skF_6')
      | ~ r1_tarski(E_444,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_444,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_56,c_50,c_48,c_81,c_759])).

tff(c_768,plain,(
    ! [E_445] :
      ( ~ m1_connsp_2(E_445,'#skF_3','#skF_6')
      | ~ r1_tarski(E_445,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_445,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_54,c_114,c_766])).

tff(c_775,plain,(
    ! [B_45,C_49] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_45,C_49),'#skF_3','#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_3',B_45,C_49),u1_struct_0('#skF_5'))
      | ~ m1_connsp_2(C_49,'#skF_3',B_45)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_768])).

tff(c_790,plain,(
    ! [B_45,C_49] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_45,C_49),'#skF_3','#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_3',B_45,C_49),u1_struct_0('#skF_5'))
      | ~ m1_connsp_2(C_49,'#skF_3',B_45)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_775])).

tff(c_791,plain,(
    ! [B_45,C_49] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_45,C_49),'#skF_3','#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_3',B_45,C_49),u1_struct_0('#skF_5'))
      | ~ m1_connsp_2(C_49,'#skF_3',B_45)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_790])).

tff(c_857,plain,(
    ! [B_460] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_460,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_460)
      | ~ m1_subset_1(B_460,u1_struct_0('#skF_3'))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_853,c_791])).

tff(c_860,plain,(
    ! [B_460] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_460,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_460)
      | ~ m1_subset_1(B_460,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_857])).

tff(c_861,plain,(
    ! [B_460] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_460,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_460)
      | ~ m1_subset_1(B_460,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_860])).

tff(c_862,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_861])).

tff(c_868,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_862])).

tff(c_875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_868])).

tff(c_877,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_861])).

tff(c_294,plain,(
    ! [B_386,A_387,C_388] :
      ( m1_connsp_2(B_386,A_387,C_388)
      | ~ r2_hidden(C_388,B_386)
      | ~ v3_pre_topc(B_386,A_387)
      | ~ m1_subset_1(C_388,u1_struct_0(A_387))
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0(A_387)))
      | ~ l1_pre_topc(A_387)
      | ~ v2_pre_topc(A_387)
      | v2_struct_0(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_302,plain,(
    ! [B_386] :
      ( m1_connsp_2(B_386,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_386)
      | ~ v3_pre_topc(B_386,'#skF_3')
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_294])).

tff(c_311,plain,(
    ! [B_386] :
      ( m1_connsp_2(B_386,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_386)
      | ~ v3_pre_topc(B_386,'#skF_3')
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_302])).

tff(c_312,plain,(
    ! [B_386] :
      ( m1_connsp_2(B_386,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_386)
      | ~ v3_pre_topc(B_386,'#skF_3')
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_311])).

tff(c_923,plain,
    ( m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6')
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_877,c_312])).

tff(c_989,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_923])).

tff(c_996,plain,
    ( ~ v1_tsep_1('#skF_5','#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_989])).

tff(c_1000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_52,c_996])).

tff(c_1001,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_923])).

tff(c_1021,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1001])).

tff(c_1033,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_168,c_1021])).

tff(c_1042,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_94,c_81,c_1033])).

tff(c_1044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1042])).

tff(c_1045,plain,(
    m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1001])).

tff(c_490,plain,(
    ! [A_407,B_408,C_409] :
      ( m1_connsp_2('#skF_1'(A_407,B_408,C_409),A_407,B_408)
      | ~ m1_connsp_2(C_409,A_407,B_408)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(u1_struct_0(A_407)))
      | ~ m1_subset_1(B_408,u1_struct_0(A_407))
      | ~ l1_pre_topc(A_407)
      | ~ v2_pre_topc(A_407)
      | v2_struct_0(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_508,plain,(
    ! [A_58,B_408,B_60] :
      ( m1_connsp_2('#skF_1'(A_58,B_408,u1_struct_0(B_60)),A_58,B_408)
      | ~ m1_connsp_2(u1_struct_0(B_60),A_58,B_408)
      | ~ m1_subset_1(B_408,u1_struct_0(A_58))
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58)
      | ~ m1_pre_topc(B_60,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_36,c_490])).

tff(c_1215,plain,(
    ! [B_484] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_484,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_484)
      | ~ m1_subset_1(B_484,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_861])).

tff(c_1219,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_508,c_1215])).

tff(c_1222,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_64,c_48,c_1045,c_1219])).

tff(c_1224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1222])).

tff(c_1225,plain,(
    r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1915,plain,(
    ! [C_614,A_616,D_617,F_615,B_618] :
      ( r1_tmap_1(D_617,A_616,k2_tmap_1(B_618,A_616,C_614,D_617),F_615)
      | ~ r1_tmap_1(B_618,A_616,C_614,F_615)
      | ~ m1_subset_1(F_615,u1_struct_0(D_617))
      | ~ m1_subset_1(F_615,u1_struct_0(B_618))
      | ~ m1_pre_topc(D_617,B_618)
      | v2_struct_0(D_617)
      | ~ m1_subset_1(C_614,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_618),u1_struct_0(A_616))))
      | ~ v1_funct_2(C_614,u1_struct_0(B_618),u1_struct_0(A_616))
      | ~ v1_funct_1(C_614)
      | ~ l1_pre_topc(B_618)
      | ~ v2_pre_topc(B_618)
      | v2_struct_0(B_618)
      | ~ l1_pre_topc(A_616)
      | ~ v2_pre_topc(A_616)
      | v2_struct_0(A_616) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_1917,plain,(
    ! [D_617,F_615] :
      ( r1_tmap_1(D_617,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_617),F_615)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_615)
      | ~ m1_subset_1(F_615,u1_struct_0(D_617))
      | ~ m1_subset_1(F_615,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_617,'#skF_3')
      | v2_struct_0(D_617)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_1915])).

tff(c_1920,plain,(
    ! [D_617,F_615] :
      ( r1_tmap_1(D_617,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_617),F_615)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_615)
      | ~ m1_subset_1(F_615,u1_struct_0(D_617))
      | ~ m1_subset_1(F_615,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_617,'#skF_3')
      | v2_struct_0(D_617)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_58,c_1917])).

tff(c_1949,plain,(
    ! [D_625,F_626] :
      ( r1_tmap_1(D_625,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_625),F_626)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_626)
      | ~ m1_subset_1(F_626,u1_struct_0(D_625))
      | ~ m1_subset_1(F_626,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_625,'#skF_3')
      | v2_struct_0(D_625) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_1920])).

tff(c_1226,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1952,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1949,c_1226])).

tff(c_1955,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_81,c_1225,c_1952])).

tff(c_1957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1955])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:24:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.31/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.31/1.95  
% 5.31/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.31/1.96  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 5.31/1.96  
% 5.31/1.96  %Foreground sorts:
% 5.31/1.96  
% 5.31/1.96  
% 5.31/1.96  %Background operators:
% 5.31/1.96  
% 5.31/1.96  
% 5.31/1.96  %Foreground operators:
% 5.31/1.96  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.31/1.96  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.31/1.96  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.31/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.31/1.96  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.31/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.31/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.31/1.96  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 5.31/1.96  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.31/1.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.31/1.96  tff('#skF_7', type, '#skF_7': $i).
% 5.31/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.31/1.96  tff('#skF_5', type, '#skF_5': $i).
% 5.31/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.31/1.96  tff('#skF_6', type, '#skF_6': $i).
% 5.31/1.96  tff('#skF_2', type, '#skF_2': $i).
% 5.31/1.96  tff('#skF_3', type, '#skF_3': $i).
% 5.31/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.31/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.31/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.31/1.96  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.31/1.96  tff('#skF_4', type, '#skF_4': $i).
% 5.31/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.31/1.96  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.31/1.96  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.31/1.96  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.31/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.31/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.31/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.31/1.96  
% 5.64/1.98  tff(f_310, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 5.64/1.98  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.64/1.98  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.64/1.98  tff(f_81, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 5.64/1.98  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 5.64/1.98  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.64/1.98  tff(f_180, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.64/1.98  tff(f_173, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 5.64/1.98  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 5.64/1.98  tff(f_267, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 5.64/1.98  tff(f_126, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 5.64/1.98  tff(f_220, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 5.64/1.98  tff(c_54, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_50, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_44, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_81, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 5.64/1.98  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_95, plain, (![B_310, A_311]: (v2_pre_topc(B_310) | ~m1_pre_topc(B_310, A_311) | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.64/1.98  tff(c_98, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_95])).
% 5.64/1.98  tff(c_101, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_98])).
% 5.64/1.98  tff(c_88, plain, (![B_308, A_309]: (l1_pre_topc(B_308) | ~m1_pre_topc(B_308, A_309) | ~l1_pre_topc(A_309))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.64/1.98  tff(c_91, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_88])).
% 5.64/1.98  tff(c_94, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91])).
% 5.64/1.98  tff(c_12, plain, (![A_21, B_22]: (m1_subset_1(k1_connsp_2(A_21, B_22), k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_22, u1_struct_0(A_21)) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.64/1.98  tff(c_116, plain, (![B_324, A_325]: (r2_hidden(B_324, k1_connsp_2(A_325, B_324)) | ~m1_subset_1(B_324, u1_struct_0(A_325)) | ~l1_pre_topc(A_325) | ~v2_pre_topc(A_325) | v2_struct_0(A_325))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.64/1.98  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.64/1.98  tff(c_164, plain, (![B_344, A_345, A_346]: (r2_hidden(B_344, A_345) | ~m1_subset_1(k1_connsp_2(A_346, B_344), k1_zfmisc_1(A_345)) | ~m1_subset_1(B_344, u1_struct_0(A_346)) | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346) | v2_struct_0(A_346))), inference(resolution, [status(thm)], [c_116, c_2])).
% 5.64/1.98  tff(c_168, plain, (![B_22, A_21]: (r2_hidden(B_22, u1_struct_0(A_21)) | ~m1_subset_1(B_22, u1_struct_0(A_21)) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(resolution, [status(thm)], [c_12, c_164])).
% 5.64/1.98  tff(c_52, plain, (v1_tsep_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_36, plain, (![B_60, A_58]: (m1_subset_1(u1_struct_0(B_60), k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_pre_topc(B_60, A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_180])).
% 5.64/1.98  tff(c_158, plain, (![B_340, A_341]: (v3_pre_topc(u1_struct_0(B_340), A_341) | ~v1_tsep_1(B_340, A_341) | ~m1_subset_1(u1_struct_0(B_340), k1_zfmisc_1(u1_struct_0(A_341))) | ~m1_pre_topc(B_340, A_341) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.64/1.98  tff(c_162, plain, (![B_60, A_58]: (v3_pre_topc(u1_struct_0(B_60), A_58) | ~v1_tsep_1(B_60, A_58) | ~v2_pre_topc(A_58) | ~m1_pre_topc(B_60, A_58) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_36, c_158])).
% 5.64/1.98  tff(c_287, plain, (![A_383, B_384, C_385]: (r1_tarski('#skF_1'(A_383, B_384, C_385), C_385) | ~m1_connsp_2(C_385, A_383, B_384) | ~m1_subset_1(C_385, k1_zfmisc_1(u1_struct_0(A_383))) | ~m1_subset_1(B_384, u1_struct_0(A_383)) | ~l1_pre_topc(A_383) | ~v2_pre_topc(A_383) | v2_struct_0(A_383))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.64/1.98  tff(c_853, plain, (![A_459, B_460, B_461]: (r1_tarski('#skF_1'(A_459, B_460, u1_struct_0(B_461)), u1_struct_0(B_461)) | ~m1_connsp_2(u1_struct_0(B_461), A_459, B_460) | ~m1_subset_1(B_460, u1_struct_0(A_459)) | ~v2_pre_topc(A_459) | v2_struct_0(A_459) | ~m1_pre_topc(B_461, A_459) | ~l1_pre_topc(A_459))), inference(resolution, [status(thm)], [c_36, c_287])).
% 5.64/1.98  tff(c_26, plain, (![A_37, B_45, C_49]: (m1_subset_1('#skF_1'(A_37, B_45, C_49), k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_connsp_2(C_49, A_37, B_45) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(B_45, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.64/1.98  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_80, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_82, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_80])).
% 5.64/1.98  tff(c_102, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_82])).
% 5.64/1.98  tff(c_74, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_83, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_74])).
% 5.64/1.98  tff(c_114, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_83])).
% 5.64/1.98  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_58, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_310])).
% 5.64/1.98  tff(c_755, plain, (![A_440, B_439, C_441, D_443, E_444, G_442]: (r1_tmap_1(B_439, A_440, C_441, G_442) | ~r1_tmap_1(D_443, A_440, k2_tmap_1(B_439, A_440, C_441, D_443), G_442) | ~m1_connsp_2(E_444, B_439, G_442) | ~r1_tarski(E_444, u1_struct_0(D_443)) | ~m1_subset_1(G_442, u1_struct_0(D_443)) | ~m1_subset_1(G_442, u1_struct_0(B_439)) | ~m1_subset_1(E_444, k1_zfmisc_1(u1_struct_0(B_439))) | ~m1_pre_topc(D_443, B_439) | v2_struct_0(D_443) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_439), u1_struct_0(A_440)))) | ~v1_funct_2(C_441, u1_struct_0(B_439), u1_struct_0(A_440)) | ~v1_funct_1(C_441) | ~l1_pre_topc(B_439) | ~v2_pre_topc(B_439) | v2_struct_0(B_439) | ~l1_pre_topc(A_440) | ~v2_pre_topc(A_440) | v2_struct_0(A_440))), inference(cnfTransformation, [status(thm)], [f_267])).
% 5.64/1.98  tff(c_759, plain, (![E_444]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_444, '#skF_3', '#skF_6') | ~r1_tarski(E_444, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1(E_444, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_102, c_755])).
% 5.64/1.98  tff(c_766, plain, (![E_444]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_444, '#skF_3', '#skF_6') | ~r1_tarski(E_444, u1_struct_0('#skF_5')) | ~m1_subset_1(E_444, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_56, c_50, c_48, c_81, c_759])).
% 5.64/1.98  tff(c_768, plain, (![E_445]: (~m1_connsp_2(E_445, '#skF_3', '#skF_6') | ~r1_tarski(E_445, u1_struct_0('#skF_5')) | ~m1_subset_1(E_445, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_54, c_114, c_766])).
% 5.64/1.98  tff(c_775, plain, (![B_45, C_49]: (~m1_connsp_2('#skF_1'('#skF_3', B_45, C_49), '#skF_3', '#skF_6') | ~r1_tarski('#skF_1'('#skF_3', B_45, C_49), u1_struct_0('#skF_5')) | ~m1_connsp_2(C_49, '#skF_3', B_45) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_768])).
% 5.64/1.98  tff(c_790, plain, (![B_45, C_49]: (~m1_connsp_2('#skF_1'('#skF_3', B_45, C_49), '#skF_3', '#skF_6') | ~r1_tarski('#skF_1'('#skF_3', B_45, C_49), u1_struct_0('#skF_5')) | ~m1_connsp_2(C_49, '#skF_3', B_45) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_775])).
% 5.64/1.98  tff(c_791, plain, (![B_45, C_49]: (~m1_connsp_2('#skF_1'('#skF_3', B_45, C_49), '#skF_3', '#skF_6') | ~r1_tarski('#skF_1'('#skF_3', B_45, C_49), u1_struct_0('#skF_5')) | ~m1_connsp_2(C_49, '#skF_3', B_45) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_45, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_790])).
% 5.64/1.98  tff(c_857, plain, (![B_460]: (~m1_connsp_2('#skF_1'('#skF_3', B_460, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_460) | ~m1_subset_1(B_460, u1_struct_0('#skF_3')) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_853, c_791])).
% 5.64/1.98  tff(c_860, plain, (![B_460]: (~m1_connsp_2('#skF_1'('#skF_3', B_460, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_460) | ~m1_subset_1(B_460, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_857])).
% 5.64/1.98  tff(c_861, plain, (![B_460]: (~m1_connsp_2('#skF_1'('#skF_3', B_460, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_460) | ~m1_subset_1(B_460, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_860])).
% 5.64/1.98  tff(c_862, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_861])).
% 5.64/1.98  tff(c_868, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_862])).
% 5.64/1.98  tff(c_875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_868])).
% 5.64/1.98  tff(c_877, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_861])).
% 5.64/1.98  tff(c_294, plain, (![B_386, A_387, C_388]: (m1_connsp_2(B_386, A_387, C_388) | ~r2_hidden(C_388, B_386) | ~v3_pre_topc(B_386, A_387) | ~m1_subset_1(C_388, u1_struct_0(A_387)) | ~m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0(A_387))) | ~l1_pre_topc(A_387) | ~v2_pre_topc(A_387) | v2_struct_0(A_387))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.64/1.98  tff(c_302, plain, (![B_386]: (m1_connsp_2(B_386, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_386) | ~v3_pre_topc(B_386, '#skF_3') | ~m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_294])).
% 5.64/1.98  tff(c_311, plain, (![B_386]: (m1_connsp_2(B_386, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_386) | ~v3_pre_topc(B_386, '#skF_3') | ~m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_302])).
% 5.64/1.98  tff(c_312, plain, (![B_386]: (m1_connsp_2(B_386, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_386) | ~v3_pre_topc(B_386, '#skF_3') | ~m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_311])).
% 5.64/1.98  tff(c_923, plain, (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_877, c_312])).
% 5.64/1.98  tff(c_989, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_923])).
% 5.64/1.98  tff(c_996, plain, (~v1_tsep_1('#skF_5', '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_162, c_989])).
% 5.64/1.98  tff(c_1000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_52, c_996])).
% 5.64/1.98  tff(c_1001, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_923])).
% 5.64/1.98  tff(c_1021, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1001])).
% 5.64/1.98  tff(c_1033, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_168, c_1021])).
% 5.64/1.98  tff(c_1042, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_94, c_81, c_1033])).
% 5.64/1.98  tff(c_1044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1042])).
% 5.64/1.98  tff(c_1045, plain, (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_1001])).
% 5.64/1.98  tff(c_490, plain, (![A_407, B_408, C_409]: (m1_connsp_2('#skF_1'(A_407, B_408, C_409), A_407, B_408) | ~m1_connsp_2(C_409, A_407, B_408) | ~m1_subset_1(C_409, k1_zfmisc_1(u1_struct_0(A_407))) | ~m1_subset_1(B_408, u1_struct_0(A_407)) | ~l1_pre_topc(A_407) | ~v2_pre_topc(A_407) | v2_struct_0(A_407))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.64/1.98  tff(c_508, plain, (![A_58, B_408, B_60]: (m1_connsp_2('#skF_1'(A_58, B_408, u1_struct_0(B_60)), A_58, B_408) | ~m1_connsp_2(u1_struct_0(B_60), A_58, B_408) | ~m1_subset_1(B_408, u1_struct_0(A_58)) | ~v2_pre_topc(A_58) | v2_struct_0(A_58) | ~m1_pre_topc(B_60, A_58) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_36, c_490])).
% 5.64/1.98  tff(c_1215, plain, (![B_484]: (~m1_connsp_2('#skF_1'('#skF_3', B_484, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_484) | ~m1_subset_1(B_484, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_861])).
% 5.64/1.98  tff(c_1219, plain, (~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_508, c_1215])).
% 5.64/1.98  tff(c_1222, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_64, c_48, c_1045, c_1219])).
% 5.64/1.98  tff(c_1224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1222])).
% 5.64/1.98  tff(c_1225, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_82])).
% 5.64/1.98  tff(c_1915, plain, (![C_614, A_616, D_617, F_615, B_618]: (r1_tmap_1(D_617, A_616, k2_tmap_1(B_618, A_616, C_614, D_617), F_615) | ~r1_tmap_1(B_618, A_616, C_614, F_615) | ~m1_subset_1(F_615, u1_struct_0(D_617)) | ~m1_subset_1(F_615, u1_struct_0(B_618)) | ~m1_pre_topc(D_617, B_618) | v2_struct_0(D_617) | ~m1_subset_1(C_614, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_618), u1_struct_0(A_616)))) | ~v1_funct_2(C_614, u1_struct_0(B_618), u1_struct_0(A_616)) | ~v1_funct_1(C_614) | ~l1_pre_topc(B_618) | ~v2_pre_topc(B_618) | v2_struct_0(B_618) | ~l1_pre_topc(A_616) | ~v2_pre_topc(A_616) | v2_struct_0(A_616))), inference(cnfTransformation, [status(thm)], [f_220])).
% 5.64/1.98  tff(c_1917, plain, (![D_617, F_615]: (r1_tmap_1(D_617, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_617), F_615) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_615) | ~m1_subset_1(F_615, u1_struct_0(D_617)) | ~m1_subset_1(F_615, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_617, '#skF_3') | v2_struct_0(D_617) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_1915])).
% 5.64/1.98  tff(c_1920, plain, (![D_617, F_615]: (r1_tmap_1(D_617, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_617), F_615) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_615) | ~m1_subset_1(F_615, u1_struct_0(D_617)) | ~m1_subset_1(F_615, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_617, '#skF_3') | v2_struct_0(D_617) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_58, c_1917])).
% 5.64/1.98  tff(c_1949, plain, (![D_625, F_626]: (r1_tmap_1(D_625, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_625), F_626) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_626) | ~m1_subset_1(F_626, u1_struct_0(D_625)) | ~m1_subset_1(F_626, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_625, '#skF_3') | v2_struct_0(D_625))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_1920])).
% 5.64/1.98  tff(c_1226, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_82])).
% 5.64/1.98  tff(c_1952, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1949, c_1226])).
% 5.64/1.98  tff(c_1955, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_81, c_1225, c_1952])).
% 5.64/1.98  tff(c_1957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1955])).
% 5.64/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/1.98  
% 5.64/1.98  Inference rules
% 5.64/1.98  ----------------------
% 5.64/1.98  #Ref     : 0
% 5.64/1.98  #Sup     : 343
% 5.64/1.98  #Fact    : 0
% 5.64/1.98  #Define  : 0
% 5.64/1.99  #Split   : 14
% 5.64/1.99  #Chain   : 0
% 5.64/1.99  #Close   : 0
% 5.64/1.99  
% 5.64/1.99  Ordering : KBO
% 5.64/1.99  
% 5.64/1.99  Simplification rules
% 5.64/1.99  ----------------------
% 5.64/1.99  #Subsume      : 108
% 5.64/1.99  #Demod        : 372
% 5.64/1.99  #Tautology    : 45
% 5.64/1.99  #SimpNegUnit  : 106
% 5.64/1.99  #BackRed      : 0
% 5.64/1.99  
% 5.64/1.99  #Partial instantiations: 0
% 5.64/1.99  #Strategies tried      : 1
% 5.64/1.99  
% 5.64/1.99  Timing (in seconds)
% 5.64/1.99  ----------------------
% 5.64/1.99  Preprocessing        : 0.43
% 5.64/1.99  Parsing              : 0.22
% 5.64/1.99  CNF conversion       : 0.06
% 5.64/1.99  Main loop            : 0.77
% 5.64/1.99  Inferencing          : 0.29
% 5.64/1.99  Reduction            : 0.24
% 5.64/1.99  Demodulation         : 0.15
% 5.64/1.99  BG Simplification    : 0.04
% 5.64/1.99  Subsumption          : 0.16
% 5.64/1.99  Abstraction          : 0.03
% 5.64/1.99  MUC search           : 0.00
% 5.64/1.99  Cooper               : 0.00
% 5.64/1.99  Total                : 1.27
% 5.64/1.99  Index Insertion      : 0.00
% 5.64/1.99  Index Deletion       : 0.00
% 5.64/1.99  Index Matching       : 0.00
% 5.64/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
