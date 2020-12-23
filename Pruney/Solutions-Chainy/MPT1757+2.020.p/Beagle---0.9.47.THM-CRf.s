%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:06 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 513 expanded)
%              Number of leaves         :   41 ( 211 expanded)
%              Depth                    :   20
%              Number of atoms          :  403 (3577 expanded)
%              Number of equality atoms :    6 ( 174 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_134,axiom,(
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

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_116,axiom,(
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

tff(f_228,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_181,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_52,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_46,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_83,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_54,plain,(
    v1_tsep_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_38,plain,(
    ! [B_55,A_53] :
      ( m1_subset_1(u1_struct_0(B_55),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_pre_topc(B_55,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_204,plain,(
    ! [B_340,A_341] :
      ( v3_pre_topc(u1_struct_0(B_340),A_341)
      | ~ v1_tsep_1(B_340,A_341)
      | ~ m1_subset_1(u1_struct_0(B_340),k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ m1_pre_topc(B_340,A_341)
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_208,plain,(
    ! [B_55,A_53] :
      ( v3_pre_topc(u1_struct_0(B_55),A_53)
      | ~ v1_tsep_1(B_55,A_53)
      | ~ v2_pre_topc(A_53)
      | ~ m1_pre_topc(B_55,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_38,c_204])).

tff(c_94,plain,(
    ! [B_306,A_307] :
      ( l1_pre_topc(B_306)
      | ~ m1_pre_topc(B_306,A_307)
      | ~ l1_pre_topc(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_94])).

tff(c_100,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_97])).

tff(c_12,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,(
    ! [B_316,A_317] :
      ( m1_subset_1(u1_struct_0(B_316),k1_zfmisc_1(u1_struct_0(A_317)))
      | ~ m1_pre_topc(B_316,A_317)
      | ~ l1_pre_topc(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( m1_subset_1(A_5,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_119,plain,(
    ! [A_318,A_319,B_320] :
      ( m1_subset_1(A_318,u1_struct_0(A_319))
      | ~ r2_hidden(A_318,u1_struct_0(B_320))
      | ~ m1_pre_topc(B_320,A_319)
      | ~ l1_pre_topc(A_319) ) ),
    inference(resolution,[status(thm)],[c_114,c_10])).

tff(c_144,plain,(
    ! [A_326,A_327,B_328] :
      ( m1_subset_1(A_326,u1_struct_0(A_327))
      | ~ m1_pre_topc(B_328,A_327)
      | ~ l1_pre_topc(A_327)
      | v1_xboole_0(u1_struct_0(B_328))
      | ~ m1_subset_1(A_326,u1_struct_0(B_328)) ) ),
    inference(resolution,[status(thm)],[c_8,c_119])).

tff(c_146,plain,(
    ! [A_326] :
      ( m1_subset_1(A_326,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_326,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_52,c_144])).

tff(c_149,plain,(
    ! [A_326] :
      ( m1_subset_1(A_326,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_326,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_146])).

tff(c_150,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_16,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_153,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_150,c_16])).

tff(c_156,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_153])).

tff(c_160,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_156])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_160])).

tff(c_166,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_215,plain,(
    ! [A_346,B_347,C_348] :
      ( r1_tarski('#skF_1'(A_346,B_347,C_348),C_348)
      | ~ m1_connsp_2(C_348,A_346,B_347)
      | ~ m1_subset_1(C_348,k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ m1_subset_1(B_347,u1_struct_0(A_346))
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_218,plain,(
    ! [A_53,B_347,B_55] :
      ( r1_tarski('#skF_1'(A_53,B_347,u1_struct_0(B_55)),u1_struct_0(B_55))
      | ~ m1_connsp_2(u1_struct_0(B_55),A_53,B_347)
      | ~ m1_subset_1(B_347,u1_struct_0(A_53))
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53)
      | ~ m1_pre_topc(B_55,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_38,c_215])).

tff(c_30,plain,(
    ! [A_24,B_36,C_42] :
      ( m1_subset_1('#skF_1'(A_24,B_36,C_42),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_connsp_2(C_42,A_24,B_36)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_36,u1_struct_0(A_24))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_85,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_76])).

tff(c_118,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_60,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_84,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_82])).

tff(c_124,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_84])).

tff(c_282,plain,(
    ! [D_392,B_393,C_396,A_391,G_395,E_394] :
      ( r1_tmap_1(B_393,A_391,C_396,G_395)
      | ~ r1_tmap_1(D_392,A_391,k2_tmap_1(B_393,A_391,C_396,D_392),G_395)
      | ~ m1_connsp_2(E_394,B_393,G_395)
      | ~ r1_tarski(E_394,u1_struct_0(D_392))
      | ~ m1_subset_1(G_395,u1_struct_0(D_392))
      | ~ m1_subset_1(G_395,u1_struct_0(B_393))
      | ~ m1_subset_1(E_394,k1_zfmisc_1(u1_struct_0(B_393)))
      | ~ m1_pre_topc(D_392,B_393)
      | v2_struct_0(D_392)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_393),u1_struct_0(A_391))))
      | ~ v1_funct_2(C_396,u1_struct_0(B_393),u1_struct_0(A_391))
      | ~ v1_funct_1(C_396)
      | ~ l1_pre_topc(B_393)
      | ~ v2_pre_topc(B_393)
      | v2_struct_0(B_393)
      | ~ l1_pre_topc(A_391)
      | ~ v2_pre_topc(A_391)
      | v2_struct_0(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_286,plain,(
    ! [E_394] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_394,'#skF_3','#skF_6')
      | ~ r1_tarski(E_394,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_394,k1_zfmisc_1(u1_struct_0('#skF_3')))
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
    inference(resolution,[status(thm)],[c_124,c_282])).

tff(c_293,plain,(
    ! [E_394] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_394,'#skF_3','#skF_6')
      | ~ r1_tarski(E_394,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_394,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_60,c_58,c_52,c_50,c_83,c_286])).

tff(c_295,plain,(
    ! [E_397] :
      ( ~ m1_connsp_2(E_397,'#skF_3','#skF_6')
      | ~ r1_tarski(E_397,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_397,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_56,c_118,c_293])).

tff(c_299,plain,(
    ! [B_36,C_42] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_36,C_42),'#skF_3','#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_3',B_36,C_42),u1_struct_0('#skF_5'))
      | ~ m1_connsp_2(C_42,'#skF_3',B_36)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_295])).

tff(c_306,plain,(
    ! [B_36,C_42] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_36,C_42),'#skF_3','#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_3',B_36,C_42),u1_struct_0('#skF_5'))
      | ~ m1_connsp_2(C_42,'#skF_3',B_36)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_36,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_299])).

tff(c_319,plain,(
    ! [B_399,C_400] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_399,C_400),'#skF_3','#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_3',B_399,C_400),u1_struct_0('#skF_5'))
      | ~ m1_connsp_2(C_400,'#skF_3',B_399)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_399,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_306])).

tff(c_323,plain,(
    ! [B_347] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_347,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_347)
      | ~ m1_subset_1(B_347,u1_struct_0('#skF_3'))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_218,c_319])).

tff(c_326,plain,(
    ! [B_347] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_347,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_347)
      | ~ m1_subset_1(B_347,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_52,c_66,c_323])).

tff(c_327,plain,(
    ! [B_347] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_347,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_347)
      | ~ m1_subset_1(B_347,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_326])).

tff(c_328,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_338,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_328])).

tff(c_342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_52,c_338])).

tff(c_344,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_259,plain,(
    ! [C_373,A_374,B_375,D_376] :
      ( m1_connsp_2(C_373,A_374,B_375)
      | ~ r2_hidden(B_375,D_376)
      | ~ r1_tarski(D_376,C_373)
      | ~ v3_pre_topc(D_376,A_374)
      | ~ m1_subset_1(D_376,k1_zfmisc_1(u1_struct_0(A_374)))
      | ~ m1_subset_1(C_373,k1_zfmisc_1(u1_struct_0(A_374)))
      | ~ m1_subset_1(B_375,u1_struct_0(A_374))
      | ~ l1_pre_topc(A_374)
      | ~ v2_pre_topc(A_374)
      | v2_struct_0(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_409,plain,(
    ! [C_413,A_414,A_415,B_416] :
      ( m1_connsp_2(C_413,A_414,A_415)
      | ~ r1_tarski(B_416,C_413)
      | ~ v3_pre_topc(B_416,A_414)
      | ~ m1_subset_1(B_416,k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ m1_subset_1(C_413,k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ m1_subset_1(A_415,u1_struct_0(A_414))
      | ~ l1_pre_topc(A_414)
      | ~ v2_pre_topc(A_414)
      | v2_struct_0(A_414)
      | v1_xboole_0(B_416)
      | ~ m1_subset_1(A_415,B_416) ) ),
    inference(resolution,[status(thm)],[c_8,c_259])).

tff(c_419,plain,(
    ! [B_417,A_418,A_419] :
      ( m1_connsp_2(B_417,A_418,A_419)
      | ~ v3_pre_topc(B_417,A_418)
      | ~ m1_subset_1(B_417,k1_zfmisc_1(u1_struct_0(A_418)))
      | ~ m1_subset_1(A_419,u1_struct_0(A_418))
      | ~ l1_pre_topc(A_418)
      | ~ v2_pre_topc(A_418)
      | v2_struct_0(A_418)
      | v1_xboole_0(B_417)
      | ~ m1_subset_1(A_419,B_417) ) ),
    inference(resolution,[status(thm)],[c_6,c_409])).

tff(c_421,plain,(
    ! [A_419] :
      ( m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',A_419)
      | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3')
      | ~ m1_subset_1(A_419,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_419,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_344,c_419])).

tff(c_428,plain,(
    ! [A_419] :
      ( m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',A_419)
      | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3')
      | ~ m1_subset_1(A_419,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_419,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_421])).

tff(c_429,plain,(
    ! [A_419] :
      ( m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',A_419)
      | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3')
      | ~ m1_subset_1(A_419,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_419,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_68,c_428])).

tff(c_432,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_435,plain,
    ( ~ v1_tsep_1('#skF_5','#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_208,c_432])).

tff(c_439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_52,c_66,c_54,c_435])).

tff(c_448,plain,(
    ! [A_420] :
      ( m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',A_420)
      | ~ m1_subset_1(A_420,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_420,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_303,plain,(
    ! [B_55] :
      ( ~ m1_connsp_2(u1_struct_0(B_55),'#skF_3','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_55),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_55,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_295])).

tff(c_311,plain,(
    ! [B_398] :
      ( ~ m1_connsp_2(u1_struct_0(B_398),'#skF_3','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_398),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_398,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_303])).

tff(c_315,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_311])).

tff(c_318,plain,(
    ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_315])).

tff(c_451,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_448,c_318])).

tff(c_457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_50,c_451])).

tff(c_459,plain,(
    r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_633,plain,(
    ! [A_498,B_497,F_496,C_494,D_495] :
      ( r1_tmap_1(D_495,A_498,k2_tmap_1(B_497,A_498,C_494,D_495),F_496)
      | ~ r1_tmap_1(B_497,A_498,C_494,F_496)
      | ~ m1_subset_1(F_496,u1_struct_0(D_495))
      | ~ m1_subset_1(F_496,u1_struct_0(B_497))
      | ~ m1_pre_topc(D_495,B_497)
      | v2_struct_0(D_495)
      | ~ m1_subset_1(C_494,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_497),u1_struct_0(A_498))))
      | ~ v1_funct_2(C_494,u1_struct_0(B_497),u1_struct_0(A_498))
      | ~ v1_funct_1(C_494)
      | ~ l1_pre_topc(B_497)
      | ~ v2_pre_topc(B_497)
      | v2_struct_0(B_497)
      | ~ l1_pre_topc(A_498)
      | ~ v2_pre_topc(A_498)
      | v2_struct_0(A_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_635,plain,(
    ! [D_495,F_496] :
      ( r1_tmap_1(D_495,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_495),F_496)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_496)
      | ~ m1_subset_1(F_496,u1_struct_0(D_495))
      | ~ m1_subset_1(F_496,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_495,'#skF_3')
      | v2_struct_0(D_495)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_633])).

tff(c_638,plain,(
    ! [D_495,F_496] :
      ( r1_tmap_1(D_495,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_495),F_496)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_496)
      | ~ m1_subset_1(F_496,u1_struct_0(D_495))
      | ~ m1_subset_1(F_496,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_495,'#skF_3')
      | v2_struct_0(D_495)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_60,c_635])).

tff(c_640,plain,(
    ! [D_499,F_500] :
      ( r1_tmap_1(D_499,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_499),F_500)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_500)
      | ~ m1_subset_1(F_500,u1_struct_0(D_499))
      | ~ m1_subset_1(F_500,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_499,'#skF_3')
      | v2_struct_0(D_499) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_638])).

tff(c_458,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_643,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_640,c_458])).

tff(c_646,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_83,c_459,c_643])).

tff(c_648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_646])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.56  
% 3.77/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.57  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.77/1.57  
% 3.77/1.57  %Foreground sorts:
% 3.77/1.57  
% 3.77/1.57  
% 3.77/1.57  %Background operators:
% 3.77/1.57  
% 3.77/1.57  
% 3.77/1.57  %Foreground operators:
% 3.77/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.77/1.57  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.77/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.77/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.77/1.57  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.77/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.57  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.77/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.77/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.77/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.77/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.77/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.77/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.77/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.77/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.77/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.77/1.57  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.77/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.77/1.57  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.77/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.77/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.77/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.77/1.57  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.77/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.77/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.77/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.57  
% 3.77/1.59  tff(f_271, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.77/1.59  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.77/1.59  tff(f_134, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.77/1.59  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.77/1.59  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.77/1.59  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.77/1.59  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.77/1.59  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.77/1.59  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 3.77/1.59  tff(f_228, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.77/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.77/1.59  tff(f_181, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.77/1.59  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_52, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_46, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_83, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 3.77/1.59  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_54, plain, (v1_tsep_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_38, plain, (![B_55, A_53]: (m1_subset_1(u1_struct_0(B_55), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc(B_55, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.77/1.59  tff(c_204, plain, (![B_340, A_341]: (v3_pre_topc(u1_struct_0(B_340), A_341) | ~v1_tsep_1(B_340, A_341) | ~m1_subset_1(u1_struct_0(B_340), k1_zfmisc_1(u1_struct_0(A_341))) | ~m1_pre_topc(B_340, A_341) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.77/1.59  tff(c_208, plain, (![B_55, A_53]: (v3_pre_topc(u1_struct_0(B_55), A_53) | ~v1_tsep_1(B_55, A_53) | ~v2_pre_topc(A_53) | ~m1_pre_topc(B_55, A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_38, c_204])).
% 3.77/1.59  tff(c_94, plain, (![B_306, A_307]: (l1_pre_topc(B_306) | ~m1_pre_topc(B_306, A_307) | ~l1_pre_topc(A_307))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.77/1.59  tff(c_97, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_94])).
% 3.77/1.59  tff(c_100, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_97])).
% 3.77/1.59  tff(c_12, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.77/1.59  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.77/1.59  tff(c_114, plain, (![B_316, A_317]: (m1_subset_1(u1_struct_0(B_316), k1_zfmisc_1(u1_struct_0(A_317))) | ~m1_pre_topc(B_316, A_317) | ~l1_pre_topc(A_317))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.77/1.59  tff(c_10, plain, (![A_5, C_7, B_6]: (m1_subset_1(A_5, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.77/1.59  tff(c_119, plain, (![A_318, A_319, B_320]: (m1_subset_1(A_318, u1_struct_0(A_319)) | ~r2_hidden(A_318, u1_struct_0(B_320)) | ~m1_pre_topc(B_320, A_319) | ~l1_pre_topc(A_319))), inference(resolution, [status(thm)], [c_114, c_10])).
% 3.77/1.59  tff(c_144, plain, (![A_326, A_327, B_328]: (m1_subset_1(A_326, u1_struct_0(A_327)) | ~m1_pre_topc(B_328, A_327) | ~l1_pre_topc(A_327) | v1_xboole_0(u1_struct_0(B_328)) | ~m1_subset_1(A_326, u1_struct_0(B_328)))), inference(resolution, [status(thm)], [c_8, c_119])).
% 3.77/1.59  tff(c_146, plain, (![A_326]: (m1_subset_1(A_326, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_326, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_52, c_144])).
% 3.77/1.59  tff(c_149, plain, (![A_326]: (m1_subset_1(A_326, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_326, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_146])).
% 3.77/1.59  tff(c_150, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_149])).
% 3.77/1.59  tff(c_16, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.77/1.59  tff(c_153, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_150, c_16])).
% 3.77/1.59  tff(c_156, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_153])).
% 3.77/1.59  tff(c_160, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12, c_156])).
% 3.77/1.59  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_160])).
% 3.77/1.59  tff(c_166, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_149])).
% 3.77/1.59  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_215, plain, (![A_346, B_347, C_348]: (r1_tarski('#skF_1'(A_346, B_347, C_348), C_348) | ~m1_connsp_2(C_348, A_346, B_347) | ~m1_subset_1(C_348, k1_zfmisc_1(u1_struct_0(A_346))) | ~m1_subset_1(B_347, u1_struct_0(A_346)) | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346) | v2_struct_0(A_346))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.77/1.59  tff(c_218, plain, (![A_53, B_347, B_55]: (r1_tarski('#skF_1'(A_53, B_347, u1_struct_0(B_55)), u1_struct_0(B_55)) | ~m1_connsp_2(u1_struct_0(B_55), A_53, B_347) | ~m1_subset_1(B_347, u1_struct_0(A_53)) | ~v2_pre_topc(A_53) | v2_struct_0(A_53) | ~m1_pre_topc(B_55, A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_38, c_215])).
% 3.77/1.59  tff(c_30, plain, (![A_24, B_36, C_42]: (m1_subset_1('#skF_1'(A_24, B_36, C_42), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_connsp_2(C_42, A_24, B_36) | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_36, u1_struct_0(A_24)) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.77/1.59  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_76, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_85, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_76])).
% 3.77/1.59  tff(c_118, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_85])).
% 3.77/1.59  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_60, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_82, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_271])).
% 3.77/1.59  tff(c_84, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_82])).
% 3.77/1.59  tff(c_124, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_118, c_84])).
% 3.77/1.59  tff(c_282, plain, (![D_392, B_393, C_396, A_391, G_395, E_394]: (r1_tmap_1(B_393, A_391, C_396, G_395) | ~r1_tmap_1(D_392, A_391, k2_tmap_1(B_393, A_391, C_396, D_392), G_395) | ~m1_connsp_2(E_394, B_393, G_395) | ~r1_tarski(E_394, u1_struct_0(D_392)) | ~m1_subset_1(G_395, u1_struct_0(D_392)) | ~m1_subset_1(G_395, u1_struct_0(B_393)) | ~m1_subset_1(E_394, k1_zfmisc_1(u1_struct_0(B_393))) | ~m1_pre_topc(D_392, B_393) | v2_struct_0(D_392) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_393), u1_struct_0(A_391)))) | ~v1_funct_2(C_396, u1_struct_0(B_393), u1_struct_0(A_391)) | ~v1_funct_1(C_396) | ~l1_pre_topc(B_393) | ~v2_pre_topc(B_393) | v2_struct_0(B_393) | ~l1_pre_topc(A_391) | ~v2_pre_topc(A_391) | v2_struct_0(A_391))), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.77/1.59  tff(c_286, plain, (![E_394]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_394, '#skF_3', '#skF_6') | ~r1_tarski(E_394, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1(E_394, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_124, c_282])).
% 3.77/1.59  tff(c_293, plain, (![E_394]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_394, '#skF_3', '#skF_6') | ~r1_tarski(E_394, u1_struct_0('#skF_5')) | ~m1_subset_1(E_394, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_60, c_58, c_52, c_50, c_83, c_286])).
% 3.77/1.59  tff(c_295, plain, (![E_397]: (~m1_connsp_2(E_397, '#skF_3', '#skF_6') | ~r1_tarski(E_397, u1_struct_0('#skF_5')) | ~m1_subset_1(E_397, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_56, c_118, c_293])).
% 3.77/1.59  tff(c_299, plain, (![B_36, C_42]: (~m1_connsp_2('#skF_1'('#skF_3', B_36, C_42), '#skF_3', '#skF_6') | ~r1_tarski('#skF_1'('#skF_3', B_36, C_42), u1_struct_0('#skF_5')) | ~m1_connsp_2(C_42, '#skF_3', B_36) | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_36, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_295])).
% 3.77/1.59  tff(c_306, plain, (![B_36, C_42]: (~m1_connsp_2('#skF_1'('#skF_3', B_36, C_42), '#skF_3', '#skF_6') | ~r1_tarski('#skF_1'('#skF_3', B_36, C_42), u1_struct_0('#skF_5')) | ~m1_connsp_2(C_42, '#skF_3', B_36) | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_36, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_299])).
% 3.77/1.59  tff(c_319, plain, (![B_399, C_400]: (~m1_connsp_2('#skF_1'('#skF_3', B_399, C_400), '#skF_3', '#skF_6') | ~r1_tarski('#skF_1'('#skF_3', B_399, C_400), u1_struct_0('#skF_5')) | ~m1_connsp_2(C_400, '#skF_3', B_399) | ~m1_subset_1(C_400, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_399, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_68, c_306])).
% 3.77/1.59  tff(c_323, plain, (![B_347]: (~m1_connsp_2('#skF_1'('#skF_3', B_347, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_347) | ~m1_subset_1(B_347, u1_struct_0('#skF_3')) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_218, c_319])).
% 3.77/1.59  tff(c_326, plain, (![B_347]: (~m1_connsp_2('#skF_1'('#skF_3', B_347, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_347) | ~m1_subset_1(B_347, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_52, c_66, c_323])).
% 3.77/1.59  tff(c_327, plain, (![B_347]: (~m1_connsp_2('#skF_1'('#skF_3', B_347, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_347) | ~m1_subset_1(B_347, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_68, c_326])).
% 3.77/1.59  tff(c_328, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_327])).
% 3.77/1.59  tff(c_338, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_328])).
% 3.77/1.59  tff(c_342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_52, c_338])).
% 3.77/1.59  tff(c_344, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_327])).
% 3.77/1.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.59  tff(c_259, plain, (![C_373, A_374, B_375, D_376]: (m1_connsp_2(C_373, A_374, B_375) | ~r2_hidden(B_375, D_376) | ~r1_tarski(D_376, C_373) | ~v3_pre_topc(D_376, A_374) | ~m1_subset_1(D_376, k1_zfmisc_1(u1_struct_0(A_374))) | ~m1_subset_1(C_373, k1_zfmisc_1(u1_struct_0(A_374))) | ~m1_subset_1(B_375, u1_struct_0(A_374)) | ~l1_pre_topc(A_374) | ~v2_pre_topc(A_374) | v2_struct_0(A_374))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.77/1.59  tff(c_409, plain, (![C_413, A_414, A_415, B_416]: (m1_connsp_2(C_413, A_414, A_415) | ~r1_tarski(B_416, C_413) | ~v3_pre_topc(B_416, A_414) | ~m1_subset_1(B_416, k1_zfmisc_1(u1_struct_0(A_414))) | ~m1_subset_1(C_413, k1_zfmisc_1(u1_struct_0(A_414))) | ~m1_subset_1(A_415, u1_struct_0(A_414)) | ~l1_pre_topc(A_414) | ~v2_pre_topc(A_414) | v2_struct_0(A_414) | v1_xboole_0(B_416) | ~m1_subset_1(A_415, B_416))), inference(resolution, [status(thm)], [c_8, c_259])).
% 3.77/1.59  tff(c_419, plain, (![B_417, A_418, A_419]: (m1_connsp_2(B_417, A_418, A_419) | ~v3_pre_topc(B_417, A_418) | ~m1_subset_1(B_417, k1_zfmisc_1(u1_struct_0(A_418))) | ~m1_subset_1(A_419, u1_struct_0(A_418)) | ~l1_pre_topc(A_418) | ~v2_pre_topc(A_418) | v2_struct_0(A_418) | v1_xboole_0(B_417) | ~m1_subset_1(A_419, B_417))), inference(resolution, [status(thm)], [c_6, c_409])).
% 3.77/1.59  tff(c_421, plain, (![A_419]: (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', A_419) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3') | ~m1_subset_1(A_419, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_419, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_344, c_419])).
% 3.77/1.59  tff(c_428, plain, (![A_419]: (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', A_419) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3') | ~m1_subset_1(A_419, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_419, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_421])).
% 3.77/1.59  tff(c_429, plain, (![A_419]: (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', A_419) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3') | ~m1_subset_1(A_419, u1_struct_0('#skF_3')) | ~m1_subset_1(A_419, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_166, c_68, c_428])).
% 3.77/1.59  tff(c_432, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_429])).
% 3.77/1.59  tff(c_435, plain, (~v1_tsep_1('#skF_5', '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_208, c_432])).
% 3.77/1.59  tff(c_439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_52, c_66, c_54, c_435])).
% 3.77/1.59  tff(c_448, plain, (![A_420]: (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', A_420) | ~m1_subset_1(A_420, u1_struct_0('#skF_3')) | ~m1_subset_1(A_420, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_429])).
% 3.77/1.59  tff(c_303, plain, (![B_55]: (~m1_connsp_2(u1_struct_0(B_55), '#skF_3', '#skF_6') | ~r1_tarski(u1_struct_0(B_55), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_55, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_295])).
% 3.77/1.59  tff(c_311, plain, (![B_398]: (~m1_connsp_2(u1_struct_0(B_398), '#skF_3', '#skF_6') | ~r1_tarski(u1_struct_0(B_398), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_398, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_303])).
% 3.77/1.59  tff(c_315, plain, (~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_311])).
% 3.77/1.59  tff(c_318, plain, (~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_315])).
% 3.77/1.59  tff(c_451, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_448, c_318])).
% 3.77/1.59  tff(c_457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_50, c_451])).
% 3.77/1.59  tff(c_459, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_85])).
% 3.77/1.59  tff(c_633, plain, (![A_498, B_497, F_496, C_494, D_495]: (r1_tmap_1(D_495, A_498, k2_tmap_1(B_497, A_498, C_494, D_495), F_496) | ~r1_tmap_1(B_497, A_498, C_494, F_496) | ~m1_subset_1(F_496, u1_struct_0(D_495)) | ~m1_subset_1(F_496, u1_struct_0(B_497)) | ~m1_pre_topc(D_495, B_497) | v2_struct_0(D_495) | ~m1_subset_1(C_494, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_497), u1_struct_0(A_498)))) | ~v1_funct_2(C_494, u1_struct_0(B_497), u1_struct_0(A_498)) | ~v1_funct_1(C_494) | ~l1_pre_topc(B_497) | ~v2_pre_topc(B_497) | v2_struct_0(B_497) | ~l1_pre_topc(A_498) | ~v2_pre_topc(A_498) | v2_struct_0(A_498))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.77/1.59  tff(c_635, plain, (![D_495, F_496]: (r1_tmap_1(D_495, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_495), F_496) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_496) | ~m1_subset_1(F_496, u1_struct_0(D_495)) | ~m1_subset_1(F_496, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_495, '#skF_3') | v2_struct_0(D_495) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_633])).
% 3.77/1.59  tff(c_638, plain, (![D_495, F_496]: (r1_tmap_1(D_495, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_495), F_496) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_496) | ~m1_subset_1(F_496, u1_struct_0(D_495)) | ~m1_subset_1(F_496, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_495, '#skF_3') | v2_struct_0(D_495) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_60, c_635])).
% 3.77/1.59  tff(c_640, plain, (![D_499, F_500]: (r1_tmap_1(D_499, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_499), F_500) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_500) | ~m1_subset_1(F_500, u1_struct_0(D_499)) | ~m1_subset_1(F_500, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_499, '#skF_3') | v2_struct_0(D_499))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_638])).
% 3.77/1.59  tff(c_458, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_85])).
% 3.77/1.59  tff(c_643, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_640, c_458])).
% 3.77/1.59  tff(c_646, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_83, c_459, c_643])).
% 3.77/1.59  tff(c_648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_646])).
% 3.77/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.59  
% 3.77/1.59  Inference rules
% 3.77/1.59  ----------------------
% 3.77/1.59  #Ref     : 0
% 3.77/1.59  #Sup     : 104
% 3.77/1.59  #Fact    : 0
% 3.77/1.59  #Define  : 0
% 3.77/1.59  #Split   : 5
% 3.77/1.59  #Chain   : 0
% 3.77/1.59  #Close   : 0
% 3.77/1.59  
% 3.77/1.59  Ordering : KBO
% 3.77/1.59  
% 3.77/1.59  Simplification rules
% 3.77/1.59  ----------------------
% 3.77/1.59  #Subsume      : 9
% 3.77/1.59  #Demod        : 100
% 3.77/1.59  #Tautology    : 25
% 3.77/1.59  #SimpNegUnit  : 30
% 3.77/1.59  #BackRed      : 0
% 3.77/1.59  
% 3.77/1.59  #Partial instantiations: 0
% 3.77/1.59  #Strategies tried      : 1
% 3.77/1.59  
% 3.77/1.59  Timing (in seconds)
% 3.77/1.59  ----------------------
% 3.77/1.59  Preprocessing        : 0.40
% 3.77/1.59  Parsing              : 0.20
% 3.77/1.59  CNF conversion       : 0.05
% 3.77/1.59  Main loop            : 0.39
% 3.77/1.59  Inferencing          : 0.15
% 3.77/1.59  Reduction            : 0.11
% 3.77/1.59  Demodulation         : 0.08
% 3.77/1.59  BG Simplification    : 0.03
% 3.77/1.59  Subsumption          : 0.08
% 3.77/1.59  Abstraction          : 0.02
% 3.77/1.60  MUC search           : 0.00
% 3.77/1.60  Cooper               : 0.00
% 3.77/1.60  Total                : 0.84
% 3.77/1.60  Index Insertion      : 0.00
% 3.77/1.60  Index Deletion       : 0.00
% 3.77/1.60  Index Matching       : 0.00
% 3.77/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
