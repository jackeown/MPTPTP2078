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
% DateTime   : Thu Dec  3 10:27:04 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 358 expanded)
%              Number of leaves         :   42 ( 151 expanded)
%              Depth                    :   14
%              Number of atoms          :  392 (2293 expanded)
%              Number of equality atoms :    6 ( 108 expanded)
%              Maximal formula depth    :   26 (   5 average)
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

tff(f_283,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_144,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_240,axiom,(
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

tff(f_126,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_191,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_52,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_46,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_84,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50])).

tff(c_48,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_66,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_112,plain,(
    ! [B_317,A_318] :
      ( v2_pre_topc(B_317)
      | ~ m1_pre_topc(B_317,A_318)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_115,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_112])).

tff(c_118,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_115])).

tff(c_92,plain,(
    ! [B_308,A_309] :
      ( l1_pre_topc(B_308)
      | ~ m1_pre_topc(B_308,A_309)
      | ~ l1_pre_topc(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_95,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_92])).

tff(c_98,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_95])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_25,B_26] :
      ( m1_connsp_2('#skF_1'(A_25,B_26),A_25,B_26)
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_154,plain,(
    ! [C_333,A_334,B_335] :
      ( m1_subset_1(C_333,k1_zfmisc_1(u1_struct_0(A_334)))
      | ~ m1_connsp_2(C_333,A_334,B_335)
      | ~ m1_subset_1(B_335,u1_struct_0(A_334))
      | ~ l1_pre_topc(A_334)
      | ~ v2_pre_topc(A_334)
      | v2_struct_0(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_158,plain,(
    ! [A_336,B_337] :
      ( m1_subset_1('#skF_1'(A_336,B_337),k1_zfmisc_1(u1_struct_0(A_336)))
      | ~ m1_subset_1(B_337,u1_struct_0(A_336))
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(resolution,[status(thm)],[c_20,c_154])).

tff(c_10,plain,(
    ! [C_7,B_6,A_5] :
      ( ~ v1_xboole_0(C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_169,plain,(
    ! [A_340,A_341,B_342] :
      ( ~ v1_xboole_0(u1_struct_0(A_340))
      | ~ r2_hidden(A_341,'#skF_1'(A_340,B_342))
      | ~ m1_subset_1(B_342,u1_struct_0(A_340))
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(resolution,[status(thm)],[c_158,c_10])).

tff(c_191,plain,(
    ! [A_351,B_352,A_353] :
      ( ~ v1_xboole_0(u1_struct_0(A_351))
      | ~ m1_subset_1(B_352,u1_struct_0(A_351))
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351)
      | v2_struct_0(A_351)
      | v1_xboole_0('#skF_1'(A_351,B_352))
      | ~ m1_subset_1(A_353,'#skF_1'(A_351,B_352)) ) ),
    inference(resolution,[status(thm)],[c_8,c_169])).

tff(c_197,plain,(
    ! [A_353] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | v1_xboole_0('#skF_1'('#skF_6','#skF_8'))
      | ~ m1_subset_1(A_353,'#skF_1'('#skF_6','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_48,c_191])).

tff(c_204,plain,(
    ! [A_353] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | v1_xboole_0('#skF_1'('#skF_6','#skF_8'))
      | ~ m1_subset_1(A_353,'#skF_1'('#skF_6','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_98,c_197])).

tff(c_205,plain,(
    ! [A_353] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
      | v1_xboole_0('#skF_1'('#skF_6','#skF_8'))
      | ~ m1_subset_1(A_353,'#skF_1'('#skF_6','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_204])).

tff(c_210,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_54,plain,(
    v1_tsep_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_38,plain,(
    ! [B_59,A_57] :
      ( m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_pre_topc(B_59,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_181,plain,(
    ! [B_347,A_348] :
      ( v3_pre_topc(u1_struct_0(B_347),A_348)
      | ~ v1_tsep_1(B_347,A_348)
      | ~ m1_subset_1(u1_struct_0(B_347),k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ m1_pre_topc(B_347,A_348)
      | ~ l1_pre_topc(A_348)
      | ~ v2_pre_topc(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_185,plain,(
    ! [B_59,A_57] :
      ( v3_pre_topc(u1_struct_0(B_59),A_57)
      | ~ v1_tsep_1(B_59,A_57)
      | ~ v2_pre_topc(A_57)
      | ~ m1_pre_topc(B_59,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_38,c_181])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_7')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_83,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_82])).

tff(c_106,plain,(
    r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_85,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_76])).

tff(c_126,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_85])).

tff(c_72,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_60,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_349,plain,(
    ! [G_434,A_433,B_429,D_432,E_431,C_430] :
      ( r1_tmap_1(B_429,A_433,C_430,G_434)
      | ~ r1_tmap_1(D_432,A_433,k2_tmap_1(B_429,A_433,C_430,D_432),G_434)
      | ~ r1_tarski(E_431,u1_struct_0(D_432))
      | ~ r2_hidden(G_434,E_431)
      | ~ v3_pre_topc(E_431,B_429)
      | ~ m1_subset_1(G_434,u1_struct_0(D_432))
      | ~ m1_subset_1(G_434,u1_struct_0(B_429))
      | ~ m1_subset_1(E_431,k1_zfmisc_1(u1_struct_0(B_429)))
      | ~ m1_pre_topc(D_432,B_429)
      | v2_struct_0(D_432)
      | ~ m1_subset_1(C_430,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_429),u1_struct_0(A_433))))
      | ~ v1_funct_2(C_430,u1_struct_0(B_429),u1_struct_0(A_433))
      | ~ v1_funct_1(C_430)
      | ~ l1_pre_topc(B_429)
      | ~ v2_pre_topc(B_429)
      | v2_struct_0(B_429)
      | ~ l1_pre_topc(A_433)
      | ~ v2_pre_topc(A_433)
      | v2_struct_0(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_353,plain,(
    ! [E_431] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ r1_tarski(E_431,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',E_431)
      | ~ v3_pre_topc(E_431,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_431,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_106,c_349])).

tff(c_360,plain,(
    ! [E_431] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ r1_tarski(E_431,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',E_431)
      | ~ v3_pre_topc(E_431,'#skF_4')
      | ~ m1_subset_1(E_431,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_60,c_58,c_52,c_84,c_48,c_353])).

tff(c_362,plain,(
    ! [E_435] :
      ( ~ r1_tarski(E_435,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',E_435)
      | ~ v3_pre_topc(E_435,'#skF_4')
      | ~ m1_subset_1(E_435,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_56,c_126,c_360])).

tff(c_374,plain,(
    ! [B_59] :
      ( ~ r1_tarski(u1_struct_0(B_59),u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_59))
      | ~ v3_pre_topc(u1_struct_0(B_59),'#skF_4')
      | ~ m1_pre_topc(B_59,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_362])).

tff(c_386,plain,(
    ! [B_436] :
      ( ~ r1_tarski(u1_struct_0(B_436),u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_436))
      | ~ v3_pre_topc(u1_struct_0(B_436),'#skF_4')
      | ~ m1_pre_topc(B_436,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_374])).

tff(c_390,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_386])).

tff(c_393,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_390])).

tff(c_394,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_393])).

tff(c_398,plain,
    ( ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_185,c_394])).

tff(c_402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_52,c_66,c_54,c_398])).

tff(c_403,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_413,plain,
    ( v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_8,c_403])).

tff(c_416,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_413])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_416])).

tff(c_420,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_157,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1('#skF_1'(A_25,B_26),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_20,c_154])).

tff(c_432,plain,(
    ! [B_440,A_441,C_442] :
      ( r2_hidden(B_440,'#skF_2'(A_441,B_440,C_442))
      | ~ m1_connsp_2(C_442,A_441,B_440)
      | ~ m1_subset_1(C_442,k1_zfmisc_1(u1_struct_0(A_441)))
      | ~ m1_subset_1(B_440,u1_struct_0(A_441))
      | ~ l1_pre_topc(A_441)
      | ~ v2_pre_topc(A_441)
      | v2_struct_0(A_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_563,plain,(
    ! [B_499,A_500,B_501] :
      ( r2_hidden(B_499,'#skF_2'(A_500,B_499,'#skF_1'(A_500,B_501)))
      | ~ m1_connsp_2('#skF_1'(A_500,B_501),A_500,B_499)
      | ~ m1_subset_1(B_499,u1_struct_0(A_500))
      | ~ m1_subset_1(B_501,u1_struct_0(A_500))
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500) ) ),
    inference(resolution,[status(thm)],[c_157,c_432])).

tff(c_529,plain,(
    ! [A_479,B_480,C_481] :
      ( m1_subset_1('#skF_2'(A_479,B_480,C_481),k1_zfmisc_1(u1_struct_0(A_479)))
      | ~ m1_connsp_2(C_481,A_479,B_480)
      | ~ m1_subset_1(C_481,k1_zfmisc_1(u1_struct_0(A_479)))
      | ~ m1_subset_1(B_480,u1_struct_0(A_479))
      | ~ l1_pre_topc(A_479)
      | ~ v2_pre_topc(A_479)
      | v2_struct_0(A_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_541,plain,(
    ! [A_479,A_5,B_480,C_481] :
      ( ~ v1_xboole_0(u1_struct_0(A_479))
      | ~ r2_hidden(A_5,'#skF_2'(A_479,B_480,C_481))
      | ~ m1_connsp_2(C_481,A_479,B_480)
      | ~ m1_subset_1(C_481,k1_zfmisc_1(u1_struct_0(A_479)))
      | ~ m1_subset_1(B_480,u1_struct_0(A_479))
      | ~ l1_pre_topc(A_479)
      | ~ v2_pre_topc(A_479)
      | v2_struct_0(A_479) ) ),
    inference(resolution,[status(thm)],[c_529,c_10])).

tff(c_574,plain,(
    ! [A_505,B_506,B_507] :
      ( ~ v1_xboole_0(u1_struct_0(A_505))
      | ~ m1_subset_1('#skF_1'(A_505,B_506),k1_zfmisc_1(u1_struct_0(A_505)))
      | ~ m1_connsp_2('#skF_1'(A_505,B_506),A_505,B_507)
      | ~ m1_subset_1(B_507,u1_struct_0(A_505))
      | ~ m1_subset_1(B_506,u1_struct_0(A_505))
      | ~ l1_pre_topc(A_505)
      | ~ v2_pre_topc(A_505)
      | v2_struct_0(A_505) ) ),
    inference(resolution,[status(thm)],[c_563,c_541])).

tff(c_578,plain,(
    ! [A_508,B_509,B_510] :
      ( ~ v1_xboole_0(u1_struct_0(A_508))
      | ~ m1_connsp_2('#skF_1'(A_508,B_509),A_508,B_510)
      | ~ m1_subset_1(B_510,u1_struct_0(A_508))
      | ~ m1_subset_1(B_509,u1_struct_0(A_508))
      | ~ l1_pre_topc(A_508)
      | ~ v2_pre_topc(A_508)
      | v2_struct_0(A_508) ) ),
    inference(resolution,[status(thm)],[c_157,c_574])).

tff(c_590,plain,(
    ! [A_516,B_517] :
      ( ~ v1_xboole_0(u1_struct_0(A_516))
      | ~ m1_subset_1(B_517,u1_struct_0(A_516))
      | ~ l1_pre_topc(A_516)
      | ~ v2_pre_topc(A_516)
      | v2_struct_0(A_516) ) ),
    inference(resolution,[status(thm)],[c_20,c_578])).

tff(c_599,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_590])).

tff(c_607,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_98,c_420,c_599])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_607])).

tff(c_610,plain,(
    r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_779,plain,(
    ! [B_601,A_603,F_600,D_599,C_602] :
      ( r1_tmap_1(D_599,A_603,k2_tmap_1(B_601,A_603,C_602,D_599),F_600)
      | ~ r1_tmap_1(B_601,A_603,C_602,F_600)
      | ~ m1_subset_1(F_600,u1_struct_0(D_599))
      | ~ m1_subset_1(F_600,u1_struct_0(B_601))
      | ~ m1_pre_topc(D_599,B_601)
      | v2_struct_0(D_599)
      | ~ m1_subset_1(C_602,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_601),u1_struct_0(A_603))))
      | ~ v1_funct_2(C_602,u1_struct_0(B_601),u1_struct_0(A_603))
      | ~ v1_funct_1(C_602)
      | ~ l1_pre_topc(B_601)
      | ~ v2_pre_topc(B_601)
      | v2_struct_0(B_601)
      | ~ l1_pre_topc(A_603)
      | ~ v2_pre_topc(A_603)
      | v2_struct_0(A_603) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_781,plain,(
    ! [D_599,F_600] :
      ( r1_tmap_1(D_599,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_599),F_600)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_600)
      | ~ m1_subset_1(F_600,u1_struct_0(D_599))
      | ~ m1_subset_1(F_600,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_599,'#skF_4')
      | v2_struct_0(D_599)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_779])).

tff(c_784,plain,(
    ! [D_599,F_600] :
      ( r1_tmap_1(D_599,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_599),F_600)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_600)
      | ~ m1_subset_1(F_600,u1_struct_0(D_599))
      | ~ m1_subset_1(F_600,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_599,'#skF_4')
      | v2_struct_0(D_599)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_60,c_781])).

tff(c_786,plain,(
    ! [D_604,F_605] :
      ( r1_tmap_1(D_604,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_604),F_605)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_605)
      | ~ m1_subset_1(F_605,u1_struct_0(D_604))
      | ~ m1_subset_1(F_605,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_604,'#skF_4')
      | v2_struct_0(D_604) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_784])).

tff(c_614,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_85])).

tff(c_789,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_786,c_614])).

tff(c_792,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_48,c_610,c_789])).

tff(c_794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_792])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.62  
% 3.75/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.62  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4 > #skF_1
% 3.75/1.62  
% 3.75/1.62  %Foreground sorts:
% 3.75/1.62  
% 3.75/1.62  
% 3.75/1.62  %Background operators:
% 3.75/1.62  
% 3.75/1.62  
% 3.75/1.62  %Foreground operators:
% 3.75/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.75/1.62  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.75/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.75/1.62  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.75/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.75/1.62  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.75/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.75/1.62  tff('#skF_7', type, '#skF_7': $i).
% 3.75/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.75/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.75/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.75/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.75/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/1.62  tff('#skF_8', type, '#skF_8': $i).
% 3.75/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.75/1.62  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.75/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.75/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.62  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.75/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.75/1.62  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.75/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.75/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.75/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.75/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.62  
% 4.08/1.64  tff(f_283, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 4.08/1.64  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.08/1.64  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.08/1.64  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.08/1.64  tff(f_102, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 4.08/1.64  tff(f_90, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 4.08/1.64  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.08/1.64  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.08/1.64  tff(f_144, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.08/1.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.08/1.64  tff(f_240, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tmap_1)).
% 4.08/1.64  tff(f_126, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 4.08/1.64  tff(f_191, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 4.08/1.64  tff(c_56, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_52, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_46, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_84, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50])).
% 4.08/1.64  tff(c_48, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_66, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_112, plain, (![B_317, A_318]: (v2_pre_topc(B_317) | ~m1_pre_topc(B_317, A_318) | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.08/1.64  tff(c_115, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_112])).
% 4.08/1.64  tff(c_118, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_115])).
% 4.08/1.64  tff(c_92, plain, (![B_308, A_309]: (l1_pre_topc(B_308) | ~m1_pre_topc(B_308, A_309) | ~l1_pre_topc(A_309))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.08/1.64  tff(c_95, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_92])).
% 4.08/1.64  tff(c_98, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_95])).
% 4.08/1.64  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.08/1.64  tff(c_20, plain, (![A_25, B_26]: (m1_connsp_2('#skF_1'(A_25, B_26), A_25, B_26) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.08/1.64  tff(c_154, plain, (![C_333, A_334, B_335]: (m1_subset_1(C_333, k1_zfmisc_1(u1_struct_0(A_334))) | ~m1_connsp_2(C_333, A_334, B_335) | ~m1_subset_1(B_335, u1_struct_0(A_334)) | ~l1_pre_topc(A_334) | ~v2_pre_topc(A_334) | v2_struct_0(A_334))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.08/1.64  tff(c_158, plain, (![A_336, B_337]: (m1_subset_1('#skF_1'(A_336, B_337), k1_zfmisc_1(u1_struct_0(A_336))) | ~m1_subset_1(B_337, u1_struct_0(A_336)) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(resolution, [status(thm)], [c_20, c_154])).
% 4.08/1.64  tff(c_10, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.08/1.64  tff(c_169, plain, (![A_340, A_341, B_342]: (~v1_xboole_0(u1_struct_0(A_340)) | ~r2_hidden(A_341, '#skF_1'(A_340, B_342)) | ~m1_subset_1(B_342, u1_struct_0(A_340)) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(resolution, [status(thm)], [c_158, c_10])).
% 4.08/1.64  tff(c_191, plain, (![A_351, B_352, A_353]: (~v1_xboole_0(u1_struct_0(A_351)) | ~m1_subset_1(B_352, u1_struct_0(A_351)) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351) | v2_struct_0(A_351) | v1_xboole_0('#skF_1'(A_351, B_352)) | ~m1_subset_1(A_353, '#skF_1'(A_351, B_352)))), inference(resolution, [status(thm)], [c_8, c_169])).
% 4.08/1.64  tff(c_197, plain, (![A_353]: (~v1_xboole_0(u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | v1_xboole_0('#skF_1'('#skF_6', '#skF_8')) | ~m1_subset_1(A_353, '#skF_1'('#skF_6', '#skF_8')))), inference(resolution, [status(thm)], [c_48, c_191])).
% 4.08/1.64  tff(c_204, plain, (![A_353]: (~v1_xboole_0(u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | v1_xboole_0('#skF_1'('#skF_6', '#skF_8')) | ~m1_subset_1(A_353, '#skF_1'('#skF_6', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_98, c_197])).
% 4.08/1.64  tff(c_205, plain, (![A_353]: (~v1_xboole_0(u1_struct_0('#skF_6')) | v1_xboole_0('#skF_1'('#skF_6', '#skF_8')) | ~m1_subset_1(A_353, '#skF_1'('#skF_6', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_56, c_204])).
% 4.08/1.64  tff(c_210, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_205])).
% 4.08/1.64  tff(c_54, plain, (v1_tsep_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_38, plain, (![B_59, A_57]: (m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_pre_topc(B_59, A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.08/1.64  tff(c_181, plain, (![B_347, A_348]: (v3_pre_topc(u1_struct_0(B_347), A_348) | ~v1_tsep_1(B_347, A_348) | ~m1_subset_1(u1_struct_0(B_347), k1_zfmisc_1(u1_struct_0(A_348))) | ~m1_pre_topc(B_347, A_348) | ~l1_pre_topc(A_348) | ~v2_pre_topc(A_348))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.08/1.64  tff(c_185, plain, (![B_59, A_57]: (v3_pre_topc(u1_struct_0(B_59), A_57) | ~v1_tsep_1(B_59, A_57) | ~v2_pre_topc(A_57) | ~m1_pre_topc(B_59, A_57) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_38, c_181])).
% 4.08/1.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.08/1.64  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_82, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_83, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_82])).
% 4.08/1.64  tff(c_106, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_83])).
% 4.08/1.64  tff(c_76, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_85, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_76])).
% 4.08/1.64  tff(c_126, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_85])).
% 4.08/1.64  tff(c_72, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_60, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.08/1.64  tff(c_349, plain, (![G_434, A_433, B_429, D_432, E_431, C_430]: (r1_tmap_1(B_429, A_433, C_430, G_434) | ~r1_tmap_1(D_432, A_433, k2_tmap_1(B_429, A_433, C_430, D_432), G_434) | ~r1_tarski(E_431, u1_struct_0(D_432)) | ~r2_hidden(G_434, E_431) | ~v3_pre_topc(E_431, B_429) | ~m1_subset_1(G_434, u1_struct_0(D_432)) | ~m1_subset_1(G_434, u1_struct_0(B_429)) | ~m1_subset_1(E_431, k1_zfmisc_1(u1_struct_0(B_429))) | ~m1_pre_topc(D_432, B_429) | v2_struct_0(D_432) | ~m1_subset_1(C_430, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_429), u1_struct_0(A_433)))) | ~v1_funct_2(C_430, u1_struct_0(B_429), u1_struct_0(A_433)) | ~v1_funct_1(C_430) | ~l1_pre_topc(B_429) | ~v2_pre_topc(B_429) | v2_struct_0(B_429) | ~l1_pre_topc(A_433) | ~v2_pre_topc(A_433) | v2_struct_0(A_433))), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.08/1.64  tff(c_353, plain, (![E_431]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~r1_tarski(E_431, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', E_431) | ~v3_pre_topc(E_431, '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_431, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_106, c_349])).
% 4.08/1.64  tff(c_360, plain, (![E_431]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~r1_tarski(E_431, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', E_431) | ~v3_pre_topc(E_431, '#skF_4') | ~m1_subset_1(E_431, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_60, c_58, c_52, c_84, c_48, c_353])).
% 4.08/1.64  tff(c_362, plain, (![E_435]: (~r1_tarski(E_435, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', E_435) | ~v3_pre_topc(E_435, '#skF_4') | ~m1_subset_1(E_435, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_56, c_126, c_360])).
% 4.08/1.64  tff(c_374, plain, (![B_59]: (~r1_tarski(u1_struct_0(B_59), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', u1_struct_0(B_59)) | ~v3_pre_topc(u1_struct_0(B_59), '#skF_4') | ~m1_pre_topc(B_59, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_362])).
% 4.08/1.64  tff(c_386, plain, (![B_436]: (~r1_tarski(u1_struct_0(B_436), u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', u1_struct_0(B_436)) | ~v3_pre_topc(u1_struct_0(B_436), '#skF_4') | ~m1_pre_topc(B_436, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_374])).
% 4.08/1.64  tff(c_390, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_6, c_386])).
% 4.08/1.64  tff(c_393, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_390])).
% 4.08/1.64  tff(c_394, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_393])).
% 4.08/1.64  tff(c_398, plain, (~v1_tsep_1('#skF_6', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_185, c_394])).
% 4.08/1.64  tff(c_402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_52, c_66, c_54, c_398])).
% 4.08/1.64  tff(c_403, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_393])).
% 4.08/1.64  tff(c_413, plain, (v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_8, c_403])).
% 4.08/1.64  tff(c_416, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_413])).
% 4.08/1.64  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210, c_416])).
% 4.08/1.64  tff(c_420, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_205])).
% 4.08/1.64  tff(c_157, plain, (![A_25, B_26]: (m1_subset_1('#skF_1'(A_25, B_26), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_20, c_154])).
% 4.08/1.64  tff(c_432, plain, (![B_440, A_441, C_442]: (r2_hidden(B_440, '#skF_2'(A_441, B_440, C_442)) | ~m1_connsp_2(C_442, A_441, B_440) | ~m1_subset_1(C_442, k1_zfmisc_1(u1_struct_0(A_441))) | ~m1_subset_1(B_440, u1_struct_0(A_441)) | ~l1_pre_topc(A_441) | ~v2_pre_topc(A_441) | v2_struct_0(A_441))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.08/1.64  tff(c_563, plain, (![B_499, A_500, B_501]: (r2_hidden(B_499, '#skF_2'(A_500, B_499, '#skF_1'(A_500, B_501))) | ~m1_connsp_2('#skF_1'(A_500, B_501), A_500, B_499) | ~m1_subset_1(B_499, u1_struct_0(A_500)) | ~m1_subset_1(B_501, u1_struct_0(A_500)) | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500))), inference(resolution, [status(thm)], [c_157, c_432])).
% 4.08/1.64  tff(c_529, plain, (![A_479, B_480, C_481]: (m1_subset_1('#skF_2'(A_479, B_480, C_481), k1_zfmisc_1(u1_struct_0(A_479))) | ~m1_connsp_2(C_481, A_479, B_480) | ~m1_subset_1(C_481, k1_zfmisc_1(u1_struct_0(A_479))) | ~m1_subset_1(B_480, u1_struct_0(A_479)) | ~l1_pre_topc(A_479) | ~v2_pre_topc(A_479) | v2_struct_0(A_479))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.08/1.64  tff(c_541, plain, (![A_479, A_5, B_480, C_481]: (~v1_xboole_0(u1_struct_0(A_479)) | ~r2_hidden(A_5, '#skF_2'(A_479, B_480, C_481)) | ~m1_connsp_2(C_481, A_479, B_480) | ~m1_subset_1(C_481, k1_zfmisc_1(u1_struct_0(A_479))) | ~m1_subset_1(B_480, u1_struct_0(A_479)) | ~l1_pre_topc(A_479) | ~v2_pre_topc(A_479) | v2_struct_0(A_479))), inference(resolution, [status(thm)], [c_529, c_10])).
% 4.08/1.64  tff(c_574, plain, (![A_505, B_506, B_507]: (~v1_xboole_0(u1_struct_0(A_505)) | ~m1_subset_1('#skF_1'(A_505, B_506), k1_zfmisc_1(u1_struct_0(A_505))) | ~m1_connsp_2('#skF_1'(A_505, B_506), A_505, B_507) | ~m1_subset_1(B_507, u1_struct_0(A_505)) | ~m1_subset_1(B_506, u1_struct_0(A_505)) | ~l1_pre_topc(A_505) | ~v2_pre_topc(A_505) | v2_struct_0(A_505))), inference(resolution, [status(thm)], [c_563, c_541])).
% 4.08/1.64  tff(c_578, plain, (![A_508, B_509, B_510]: (~v1_xboole_0(u1_struct_0(A_508)) | ~m1_connsp_2('#skF_1'(A_508, B_509), A_508, B_510) | ~m1_subset_1(B_510, u1_struct_0(A_508)) | ~m1_subset_1(B_509, u1_struct_0(A_508)) | ~l1_pre_topc(A_508) | ~v2_pre_topc(A_508) | v2_struct_0(A_508))), inference(resolution, [status(thm)], [c_157, c_574])).
% 4.08/1.64  tff(c_590, plain, (![A_516, B_517]: (~v1_xboole_0(u1_struct_0(A_516)) | ~m1_subset_1(B_517, u1_struct_0(A_516)) | ~l1_pre_topc(A_516) | ~v2_pre_topc(A_516) | v2_struct_0(A_516))), inference(resolution, [status(thm)], [c_20, c_578])).
% 4.08/1.64  tff(c_599, plain, (~v1_xboole_0(u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_48, c_590])).
% 4.08/1.64  tff(c_607, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_98, c_420, c_599])).
% 4.08/1.64  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_607])).
% 4.08/1.64  tff(c_610, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_83])).
% 4.08/1.64  tff(c_779, plain, (![B_601, A_603, F_600, D_599, C_602]: (r1_tmap_1(D_599, A_603, k2_tmap_1(B_601, A_603, C_602, D_599), F_600) | ~r1_tmap_1(B_601, A_603, C_602, F_600) | ~m1_subset_1(F_600, u1_struct_0(D_599)) | ~m1_subset_1(F_600, u1_struct_0(B_601)) | ~m1_pre_topc(D_599, B_601) | v2_struct_0(D_599) | ~m1_subset_1(C_602, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_601), u1_struct_0(A_603)))) | ~v1_funct_2(C_602, u1_struct_0(B_601), u1_struct_0(A_603)) | ~v1_funct_1(C_602) | ~l1_pre_topc(B_601) | ~v2_pre_topc(B_601) | v2_struct_0(B_601) | ~l1_pre_topc(A_603) | ~v2_pre_topc(A_603) | v2_struct_0(A_603))), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.08/1.64  tff(c_781, plain, (![D_599, F_600]: (r1_tmap_1(D_599, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_599), F_600) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_600) | ~m1_subset_1(F_600, u1_struct_0(D_599)) | ~m1_subset_1(F_600, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_599, '#skF_4') | v2_struct_0(D_599) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_779])).
% 4.08/1.64  tff(c_784, plain, (![D_599, F_600]: (r1_tmap_1(D_599, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_599), F_600) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_600) | ~m1_subset_1(F_600, u1_struct_0(D_599)) | ~m1_subset_1(F_600, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_599, '#skF_4') | v2_struct_0(D_599) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_60, c_781])).
% 4.08/1.64  tff(c_786, plain, (![D_604, F_605]: (r1_tmap_1(D_604, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_604), F_605) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_605) | ~m1_subset_1(F_605, u1_struct_0(D_604)) | ~m1_subset_1(F_605, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_604, '#skF_4') | v2_struct_0(D_604))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_784])).
% 4.08/1.64  tff(c_614, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_610, c_85])).
% 4.08/1.64  tff(c_789, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_786, c_614])).
% 4.08/1.64  tff(c_792, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_48, c_610, c_789])).
% 4.08/1.64  tff(c_794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_792])).
% 4.08/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.64  
% 4.08/1.65  Inference rules
% 4.08/1.65  ----------------------
% 4.08/1.65  #Ref     : 0
% 4.08/1.65  #Sup     : 141
% 4.08/1.65  #Fact    : 0
% 4.08/1.65  #Define  : 0
% 4.08/1.65  #Split   : 10
% 4.08/1.65  #Chain   : 0
% 4.08/1.65  #Close   : 0
% 4.08/1.65  
% 4.08/1.65  Ordering : KBO
% 4.08/1.65  
% 4.08/1.65  Simplification rules
% 4.08/1.65  ----------------------
% 4.08/1.65  #Subsume      : 30
% 4.08/1.65  #Demod        : 103
% 4.08/1.65  #Tautology    : 16
% 4.08/1.65  #SimpNegUnit  : 29
% 4.08/1.65  #BackRed      : 0
% 4.08/1.65  
% 4.08/1.65  #Partial instantiations: 0
% 4.08/1.65  #Strategies tried      : 1
% 4.08/1.65  
% 4.08/1.65  Timing (in seconds)
% 4.08/1.65  ----------------------
% 4.08/1.65  Preprocessing        : 0.40
% 4.08/1.65  Parsing              : 0.21
% 4.08/1.65  CNF conversion       : 0.05
% 4.08/1.65  Main loop            : 0.47
% 4.08/1.65  Inferencing          : 0.18
% 4.08/1.65  Reduction            : 0.13
% 4.08/1.65  Demodulation         : 0.09
% 4.08/1.65  BG Simplification    : 0.03
% 4.08/1.65  Subsumption          : 0.10
% 4.08/1.65  Abstraction          : 0.02
% 4.08/1.65  MUC search           : 0.00
% 4.08/1.65  Cooper               : 0.00
% 4.08/1.65  Total                : 0.91
% 4.08/1.65  Index Insertion      : 0.00
% 4.08/1.65  Index Deletion       : 0.00
% 4.08/1.65  Index Matching       : 0.00
% 4.08/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
