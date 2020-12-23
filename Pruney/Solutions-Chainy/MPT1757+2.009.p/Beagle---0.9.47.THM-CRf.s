%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:05 EST 2020

% Result     : Theorem 6.25s
% Output     : CNFRefutation 6.60s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 692 expanded)
%              Number of leaves         :   43 ( 279 expanded)
%              Depth                    :   26
%              Number of atoms          :  466 (5119 expanded)
%              Number of equality atoms :    5 ( 240 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_292,negated_conjecture,(
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

tff(f_162,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_155,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_111,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_137,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

tff(f_249,axiom,(
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

tff(f_202,axiom,(
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

tff(c_60,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_56,plain,(
    m1_pre_topc('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_54,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_50,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_52,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_87,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52])).

tff(c_68,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_70,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_58,plain,(
    v1_tsep_1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_42,plain,(
    ! [B_69,A_67] :
      ( m1_subset_1(u1_struct_0(B_69),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_pre_topc(B_69,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_290,plain,(
    ! [B_386,A_387] :
      ( v3_pre_topc(u1_struct_0(B_386),A_387)
      | ~ v1_tsep_1(B_386,A_387)
      | ~ m1_subset_1(u1_struct_0(B_386),k1_zfmisc_1(u1_struct_0(A_387)))
      | ~ m1_pre_topc(B_386,A_387)
      | ~ l1_pre_topc(A_387)
      | ~ v2_pre_topc(A_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_297,plain,(
    ! [B_69,A_67] :
      ( v3_pre_topc(u1_struct_0(B_69),A_67)
      | ~ v1_tsep_1(B_69,A_67)
      | ~ v2_pre_topc(A_67)
      | ~ m1_pre_topc(B_69,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_42,c_290])).

tff(c_123,plain,(
    ! [B_331,A_332] :
      ( v2_pre_topc(B_331)
      | ~ m1_pre_topc(B_331,A_332)
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,
    ( v2_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_123])).

tff(c_129,plain,(
    v2_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_126])).

tff(c_94,plain,(
    ! [B_317,A_318] :
      ( l1_pre_topc(B_317)
      | ~ m1_pre_topc(B_317,A_318)
      | ~ l1_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_94])).

tff(c_100,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_97])).

tff(c_20,plain,(
    ! [A_25,B_26] :
      ( m1_connsp_2('#skF_2'(A_25,B_26),A_25,B_26)
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_255,plain,(
    ! [C_375,A_376,B_377] :
      ( m1_subset_1(C_375,k1_zfmisc_1(u1_struct_0(A_376)))
      | ~ m1_connsp_2(C_375,A_376,B_377)
      | ~ m1_subset_1(B_377,u1_struct_0(A_376))
      | ~ l1_pre_topc(A_376)
      | ~ v2_pre_topc(A_376)
      | v2_struct_0(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_259,plain,(
    ! [A_378,B_379] :
      ( m1_subset_1('#skF_2'(A_378,B_379),k1_zfmisc_1(u1_struct_0(A_378)))
      | ~ m1_subset_1(B_379,u1_struct_0(A_378))
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378) ) ),
    inference(resolution,[status(thm)],[c_20,c_255])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_266,plain,(
    ! [A_378,B_379] :
      ( r1_tarski('#skF_2'(A_378,B_379),u1_struct_0(A_378))
      | ~ m1_subset_1(B_379,u1_struct_0(A_378))
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378) ) ),
    inference(resolution,[status(thm)],[c_259,c_8])).

tff(c_258,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1('#skF_2'(A_25,B_26),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_20,c_255])).

tff(c_333,plain,(
    ! [C_404,B_405,A_406] :
      ( r2_hidden(C_404,B_405)
      | ~ m1_connsp_2(B_405,A_406,C_404)
      | ~ m1_subset_1(C_404,u1_struct_0(A_406))
      | ~ m1_subset_1(B_405,k1_zfmisc_1(u1_struct_0(A_406)))
      | ~ l1_pre_topc(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_491,plain,(
    ! [B_441,A_442] :
      ( r2_hidden(B_441,'#skF_2'(A_442,B_441))
      | ~ m1_subset_1('#skF_2'(A_442,B_441),k1_zfmisc_1(u1_struct_0(A_442)))
      | ~ m1_subset_1(B_441,u1_struct_0(A_442))
      | ~ l1_pre_topc(A_442)
      | ~ v2_pre_topc(A_442)
      | v2_struct_0(A_442) ) ),
    inference(resolution,[status(thm)],[c_20,c_333])).

tff(c_499,plain,(
    ! [B_443,A_444] :
      ( r2_hidden(B_443,'#skF_2'(A_444,B_443))
      | ~ m1_subset_1(B_443,u1_struct_0(A_444))
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(resolution,[status(thm)],[c_258,c_491])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_503,plain,(
    ! [B_445,B_446,A_447] :
      ( r2_hidden(B_445,B_446)
      | ~ r1_tarski('#skF_2'(A_447,B_445),B_446)
      | ~ m1_subset_1(B_445,u1_struct_0(A_447))
      | ~ l1_pre_topc(A_447)
      | ~ v2_pre_topc(A_447)
      | v2_struct_0(A_447) ) ),
    inference(resolution,[status(thm)],[c_499,c_2])).

tff(c_515,plain,(
    ! [B_379,A_378] :
      ( r2_hidden(B_379,u1_struct_0(A_378))
      | ~ m1_subset_1(B_379,u1_struct_0(A_378))
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378) ) ),
    inference(resolution,[status(thm)],[c_266,c_503])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_130,plain,(
    ! [B_333,A_334] :
      ( m1_subset_1(u1_struct_0(B_333),k1_zfmisc_1(u1_struct_0(A_334)))
      | ~ m1_pre_topc(B_333,A_334)
      | ~ l1_pre_topc(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_134,plain,(
    ! [B_333,A_334] :
      ( r1_tarski(u1_struct_0(B_333),u1_struct_0(A_334))
      | ~ m1_pre_topc(B_333,A_334)
      | ~ l1_pre_topc(A_334) ) ),
    inference(resolution,[status(thm)],[c_130,c_8])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_440,plain,(
    ! [A_430,B_431,C_432] :
      ( r1_tarski('#skF_3'(A_430,B_431,C_432),B_431)
      | ~ r2_hidden(C_432,B_431)
      | ~ m1_subset_1(C_432,u1_struct_0(A_430))
      | ~ v3_pre_topc(B_431,A_430)
      | ~ m1_subset_1(B_431,k1_zfmisc_1(u1_struct_0(A_430)))
      | ~ l1_pre_topc(A_430)
      | ~ v2_pre_topc(A_430)
      | v2_struct_0(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_450,plain,(
    ! [A_430,A_6,C_432] :
      ( r1_tarski('#skF_3'(A_430,A_6,C_432),A_6)
      | ~ r2_hidden(C_432,A_6)
      | ~ m1_subset_1(C_432,u1_struct_0(A_430))
      | ~ v3_pre_topc(A_6,A_430)
      | ~ l1_pre_topc(A_430)
      | ~ v2_pre_topc(A_430)
      | v2_struct_0(A_430)
      | ~ r1_tarski(A_6,u1_struct_0(A_430)) ) ),
    inference(resolution,[status(thm)],[c_10,c_440])).

tff(c_34,plain,(
    ! [A_35,B_49,C_56] :
      ( m1_subset_1('#skF_3'(A_35,B_49,C_56),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ r2_hidden(C_56,B_49)
      | ~ m1_subset_1(C_56,u1_struct_0(A_35))
      | ~ v3_pre_topc(B_49,A_35)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_80,plain,
    ( ~ r1_tmap_1('#skF_8','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_7','#skF_8'),'#skF_10')
    | ~ r1_tmap_1('#skF_6','#skF_5','#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_89,plain,
    ( ~ r1_tmap_1('#skF_8','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_7','#skF_8'),'#skF_9')
    | ~ r1_tmap_1('#skF_6','#skF_5','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_80])).

tff(c_145,plain,(
    ~ r1_tmap_1('#skF_6','#skF_5','#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_76,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_74,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_66,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_64,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_86,plain,
    ( r1_tmap_1('#skF_6','#skF_5','#skF_7','#skF_9')
    | r1_tmap_1('#skF_8','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_7','#skF_8'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_292])).

tff(c_88,plain,
    ( r1_tmap_1('#skF_6','#skF_5','#skF_7','#skF_9')
    | r1_tmap_1('#skF_8','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_7','#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_86])).

tff(c_146,plain,(
    r1_tmap_1('#skF_8','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_7','#skF_8'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_88])).

tff(c_836,plain,(
    ! [G_520,D_519,E_515,A_518,C_516,B_517] :
      ( r1_tmap_1(B_517,A_518,C_516,G_520)
      | ~ r1_tmap_1(D_519,A_518,k2_tmap_1(B_517,A_518,C_516,D_519),G_520)
      | ~ m1_connsp_2(E_515,B_517,G_520)
      | ~ r1_tarski(E_515,u1_struct_0(D_519))
      | ~ m1_subset_1(G_520,u1_struct_0(D_519))
      | ~ m1_subset_1(G_520,u1_struct_0(B_517))
      | ~ m1_subset_1(E_515,k1_zfmisc_1(u1_struct_0(B_517)))
      | ~ m1_pre_topc(D_519,B_517)
      | v2_struct_0(D_519)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_517),u1_struct_0(A_518))))
      | ~ v1_funct_2(C_516,u1_struct_0(B_517),u1_struct_0(A_518))
      | ~ v1_funct_1(C_516)
      | ~ l1_pre_topc(B_517)
      | ~ v2_pre_topc(B_517)
      | v2_struct_0(B_517)
      | ~ l1_pre_topc(A_518)
      | ~ v2_pre_topc(A_518)
      | v2_struct_0(A_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_840,plain,(
    ! [E_515] :
      ( r1_tmap_1('#skF_6','#skF_5','#skF_7','#skF_9')
      | ~ m1_connsp_2(E_515,'#skF_6','#skF_9')
      | ~ r1_tarski(E_515,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_515,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_8','#skF_6')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_146,c_836])).

tff(c_847,plain,(
    ! [E_515] :
      ( r1_tmap_1('#skF_6','#skF_5','#skF_7','#skF_9')
      | ~ m1_connsp_2(E_515,'#skF_6','#skF_9')
      | ~ r1_tarski(E_515,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(E_515,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_8')
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_66,c_64,c_62,c_56,c_54,c_87,c_840])).

tff(c_849,plain,(
    ! [E_521] :
      ( ~ m1_connsp_2(E_521,'#skF_6','#skF_9')
      | ~ r1_tarski(E_521,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(E_521,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_60,c_145,c_847])).

tff(c_853,plain,(
    ! [B_49,C_56] :
      ( ~ m1_connsp_2('#skF_3'('#skF_6',B_49,C_56),'#skF_6','#skF_9')
      | ~ r1_tarski('#skF_3'('#skF_6',B_49,C_56),u1_struct_0('#skF_8'))
      | ~ r2_hidden(C_56,B_49)
      | ~ m1_subset_1(C_56,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(B_49,'#skF_6')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_849])).

tff(c_868,plain,(
    ! [B_49,C_56] :
      ( ~ m1_connsp_2('#skF_3'('#skF_6',B_49,C_56),'#skF_6','#skF_9')
      | ~ r1_tarski('#skF_3'('#skF_6',B_49,C_56),u1_struct_0('#skF_8'))
      | ~ r2_hidden(C_56,B_49)
      | ~ m1_subset_1(C_56,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(B_49,'#skF_6')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_853])).

tff(c_1002,plain,(
    ! [B_531,C_532] :
      ( ~ m1_connsp_2('#skF_3'('#skF_6',B_531,C_532),'#skF_6','#skF_9')
      | ~ r1_tarski('#skF_3'('#skF_6',B_531,C_532),u1_struct_0('#skF_8'))
      | ~ r2_hidden(C_532,B_531)
      | ~ m1_subset_1(C_532,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(B_531,'#skF_6')
      | ~ m1_subset_1(B_531,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_868])).

tff(c_1006,plain,(
    ! [C_432] :
      ( ~ m1_connsp_2('#skF_3'('#skF_6',u1_struct_0('#skF_8'),C_432),'#skF_6','#skF_9')
      | ~ m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(C_432,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(C_432,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(u1_struct_0('#skF_8'),'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(u1_struct_0('#skF_8'),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_450,c_1002])).

tff(c_1009,plain,(
    ! [C_432] :
      ( ~ m1_connsp_2('#skF_3'('#skF_6',u1_struct_0('#skF_8'),C_432),'#skF_6','#skF_9')
      | ~ m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(C_432,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(C_432,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(u1_struct_0('#skF_8'),'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(u1_struct_0('#skF_8'),u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1006])).

tff(c_1010,plain,(
    ! [C_432] :
      ( ~ m1_connsp_2('#skF_3'('#skF_6',u1_struct_0('#skF_8'),C_432),'#skF_6','#skF_9')
      | ~ m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(C_432,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(C_432,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(u1_struct_0('#skF_8'),'#skF_6')
      | ~ r1_tarski(u1_struct_0('#skF_8'),u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1009])).

tff(c_1086,plain,(
    ~ r1_tarski(u1_struct_0('#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1010])).

tff(c_1095,plain,
    ( ~ m1_pre_topc('#skF_8','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_134,c_1086])).

tff(c_1103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_56,c_1095])).

tff(c_1104,plain,(
    ! [C_432] :
      ( ~ v3_pre_topc(u1_struct_0('#skF_8'),'#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_connsp_2('#skF_3'('#skF_6',u1_struct_0('#skF_8'),C_432),'#skF_6','#skF_9')
      | ~ r2_hidden(C_432,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(C_432,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1010])).

tff(c_2129,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1104])).

tff(c_2136,plain,
    ( ~ m1_pre_topc('#skF_8','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_2129])).

tff(c_2143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_56,c_2136])).

tff(c_2145,plain,(
    m1_subset_1(u1_struct_0('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1104])).

tff(c_26,plain,(
    ! [A_35,B_49] :
      ( r2_hidden('#skF_4'(A_35,B_49),B_49)
      | v3_pre_topc(B_49,A_35)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2151,plain,
    ( r2_hidden('#skF_4'('#skF_6',u1_struct_0('#skF_8')),u1_struct_0('#skF_8'))
    | v3_pre_topc(u1_struct_0('#skF_8'),'#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2145,c_26])).

tff(c_2165,plain,
    ( r2_hidden('#skF_4'('#skF_6',u1_struct_0('#skF_8')),u1_struct_0('#skF_8'))
    | v3_pre_topc(u1_struct_0('#skF_8'),'#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_2151])).

tff(c_2166,plain,
    ( r2_hidden('#skF_4'('#skF_6',u1_struct_0('#skF_8')),u1_struct_0('#skF_8'))
    | v3_pre_topc(u1_struct_0('#skF_8'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2165])).

tff(c_2169,plain,(
    v3_pre_topc(u1_struct_0('#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2166])).

tff(c_518,plain,(
    ! [A_448,B_449,C_450] :
      ( m1_connsp_2('#skF_3'(A_448,B_449,C_450),A_448,C_450)
      | ~ r2_hidden(C_450,B_449)
      | ~ m1_subset_1(C_450,u1_struct_0(A_448))
      | ~ v3_pre_topc(B_449,A_448)
      | ~ m1_subset_1(B_449,k1_zfmisc_1(u1_struct_0(A_448)))
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448)
      | v2_struct_0(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_527,plain,(
    ! [A_67,B_69,C_450] :
      ( m1_connsp_2('#skF_3'(A_67,u1_struct_0(B_69),C_450),A_67,C_450)
      | ~ r2_hidden(C_450,u1_struct_0(B_69))
      | ~ m1_subset_1(C_450,u1_struct_0(A_67))
      | ~ v3_pre_topc(u1_struct_0(B_69),A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67)
      | ~ m1_pre_topc(B_69,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_42,c_518])).

tff(c_2144,plain,(
    ! [C_432] :
      ( ~ v3_pre_topc(u1_struct_0('#skF_8'),'#skF_6')
      | ~ m1_connsp_2('#skF_3'('#skF_6',u1_struct_0('#skF_8'),C_432),'#skF_6','#skF_9')
      | ~ r2_hidden(C_432,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(C_432,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_1104])).

tff(c_2178,plain,(
    ! [C_677] :
      ( ~ m1_connsp_2('#skF_3'('#skF_6',u1_struct_0('#skF_8'),C_677),'#skF_6','#skF_9')
      | ~ r2_hidden(C_677,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(C_677,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2169,c_2144])).

tff(c_2182,plain,
    ( ~ r2_hidden('#skF_9',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ v3_pre_topc(u1_struct_0('#skF_8'),'#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_8','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_527,c_2178])).

tff(c_2189,plain,
    ( ~ r2_hidden('#skF_9',u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_56,c_70,c_2169,c_54,c_2182])).

tff(c_2190,plain,(
    ~ r2_hidden('#skF_9',u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2189])).

tff(c_2228,plain,
    ( ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_515,c_2190])).

tff(c_2240,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_100,c_87,c_2228])).

tff(c_2242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2240])).

tff(c_2244,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2166])).

tff(c_2247,plain,
    ( ~ v1_tsep_1('#skF_8','#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | ~ m1_pre_topc('#skF_8','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_297,c_2244])).

tff(c_2251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_56,c_70,c_58,c_2247])).

tff(c_2253,plain,(
    r1_tmap_1('#skF_6','#skF_5','#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_2879,plain,(
    ! [B_833,C_829,D_832,A_830,F_831] :
      ( r1_tmap_1(D_832,A_830,k2_tmap_1(B_833,A_830,C_829,D_832),F_831)
      | ~ r1_tmap_1(B_833,A_830,C_829,F_831)
      | ~ m1_subset_1(F_831,u1_struct_0(D_832))
      | ~ m1_subset_1(F_831,u1_struct_0(B_833))
      | ~ m1_pre_topc(D_832,B_833)
      | v2_struct_0(D_832)
      | ~ m1_subset_1(C_829,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_833),u1_struct_0(A_830))))
      | ~ v1_funct_2(C_829,u1_struct_0(B_833),u1_struct_0(A_830))
      | ~ v1_funct_1(C_829)
      | ~ l1_pre_topc(B_833)
      | ~ v2_pre_topc(B_833)
      | v2_struct_0(B_833)
      | ~ l1_pre_topc(A_830)
      | ~ v2_pre_topc(A_830)
      | v2_struct_0(A_830) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_2881,plain,(
    ! [D_832,F_831] :
      ( r1_tmap_1(D_832,'#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_7',D_832),F_831)
      | ~ r1_tmap_1('#skF_6','#skF_5','#skF_7',F_831)
      | ~ m1_subset_1(F_831,u1_struct_0(D_832))
      | ~ m1_subset_1(F_831,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_832,'#skF_6')
      | v2_struct_0(D_832)
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_2879])).

tff(c_2887,plain,(
    ! [D_832,F_831] :
      ( r1_tmap_1(D_832,'#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_7',D_832),F_831)
      | ~ r1_tmap_1('#skF_6','#skF_5','#skF_7',F_831)
      | ~ m1_subset_1(F_831,u1_struct_0(D_832))
      | ~ m1_subset_1(F_831,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_832,'#skF_6')
      | v2_struct_0(D_832)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_66,c_64,c_2881])).

tff(c_2934,plain,(
    ! [D_844,F_845] :
      ( r1_tmap_1(D_844,'#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_7',D_844),F_845)
      | ~ r1_tmap_1('#skF_6','#skF_5','#skF_7',F_845)
      | ~ m1_subset_1(F_845,u1_struct_0(D_844))
      | ~ m1_subset_1(F_845,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_844,'#skF_6')
      | v2_struct_0(D_844) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_2887])).

tff(c_2252,plain,(
    ~ r1_tmap_1('#skF_8','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_7','#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_2937,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_5','#skF_7','#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_8','#skF_6')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2934,c_2252])).

tff(c_2940,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_87,c_2253,c_2937])).

tff(c_2942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2940])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:50:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.25/2.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.60/2.33  
% 6.60/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.60/2.33  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 6.60/2.33  
% 6.60/2.33  %Foreground sorts:
% 6.60/2.33  
% 6.60/2.33  
% 6.60/2.33  %Background operators:
% 6.60/2.33  
% 6.60/2.33  
% 6.60/2.33  %Foreground operators:
% 6.60/2.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.60/2.33  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 6.60/2.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.60/2.33  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.60/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.60/2.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.60/2.33  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 6.60/2.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.60/2.33  tff('#skF_7', type, '#skF_7': $i).
% 6.60/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.60/2.33  tff('#skF_10', type, '#skF_10': $i).
% 6.60/2.33  tff('#skF_5', type, '#skF_5': $i).
% 6.60/2.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.60/2.33  tff('#skF_6', type, '#skF_6': $i).
% 6.60/2.33  tff('#skF_9', type, '#skF_9': $i).
% 6.60/2.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.60/2.33  tff('#skF_8', type, '#skF_8': $i).
% 6.60/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.60/2.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.60/2.33  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 6.60/2.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.60/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.60/2.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.60/2.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.60/2.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.60/2.33  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.60/2.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.60/2.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.60/2.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.60/2.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.60/2.33  
% 6.60/2.37  tff(f_292, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 6.60/2.37  tff(f_162, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.60/2.37  tff(f_155, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 6.60/2.37  tff(f_45, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 6.60/2.37  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.60/2.37  tff(f_94, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 6.60/2.37  tff(f_82, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 6.60/2.37  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.60/2.37  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 6.60/2.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.60/2.37  tff(f_137, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_connsp_2)).
% 6.60/2.37  tff(f_249, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 6.60/2.37  tff(f_202, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 6.60/2.37  tff(c_60, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_56, plain, (m1_pre_topc('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_54, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_50, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_52, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_87, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52])).
% 6.60/2.37  tff(c_68, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_70, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_58, plain, (v1_tsep_1('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_42, plain, (![B_69, A_67]: (m1_subset_1(u1_struct_0(B_69), k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_pre_topc(B_69, A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.60/2.37  tff(c_290, plain, (![B_386, A_387]: (v3_pre_topc(u1_struct_0(B_386), A_387) | ~v1_tsep_1(B_386, A_387) | ~m1_subset_1(u1_struct_0(B_386), k1_zfmisc_1(u1_struct_0(A_387))) | ~m1_pre_topc(B_386, A_387) | ~l1_pre_topc(A_387) | ~v2_pre_topc(A_387))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.60/2.37  tff(c_297, plain, (![B_69, A_67]: (v3_pre_topc(u1_struct_0(B_69), A_67) | ~v1_tsep_1(B_69, A_67) | ~v2_pre_topc(A_67) | ~m1_pre_topc(B_69, A_67) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_42, c_290])).
% 6.60/2.37  tff(c_123, plain, (![B_331, A_332]: (v2_pre_topc(B_331) | ~m1_pre_topc(B_331, A_332) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.60/2.37  tff(c_126, plain, (v2_pre_topc('#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_56, c_123])).
% 6.60/2.37  tff(c_129, plain, (v2_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_126])).
% 6.60/2.37  tff(c_94, plain, (![B_317, A_318]: (l1_pre_topc(B_317) | ~m1_pre_topc(B_317, A_318) | ~l1_pre_topc(A_318))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.60/2.37  tff(c_97, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_56, c_94])).
% 6.60/2.37  tff(c_100, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_97])).
% 6.60/2.37  tff(c_20, plain, (![A_25, B_26]: (m1_connsp_2('#skF_2'(A_25, B_26), A_25, B_26) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.60/2.37  tff(c_255, plain, (![C_375, A_376, B_377]: (m1_subset_1(C_375, k1_zfmisc_1(u1_struct_0(A_376))) | ~m1_connsp_2(C_375, A_376, B_377) | ~m1_subset_1(B_377, u1_struct_0(A_376)) | ~l1_pre_topc(A_376) | ~v2_pre_topc(A_376) | v2_struct_0(A_376))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.60/2.37  tff(c_259, plain, (![A_378, B_379]: (m1_subset_1('#skF_2'(A_378, B_379), k1_zfmisc_1(u1_struct_0(A_378))) | ~m1_subset_1(B_379, u1_struct_0(A_378)) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378))), inference(resolution, [status(thm)], [c_20, c_255])).
% 6.60/2.37  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.60/2.37  tff(c_266, plain, (![A_378, B_379]: (r1_tarski('#skF_2'(A_378, B_379), u1_struct_0(A_378)) | ~m1_subset_1(B_379, u1_struct_0(A_378)) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378))), inference(resolution, [status(thm)], [c_259, c_8])).
% 6.60/2.37  tff(c_258, plain, (![A_25, B_26]: (m1_subset_1('#skF_2'(A_25, B_26), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_20, c_255])).
% 6.60/2.37  tff(c_333, plain, (![C_404, B_405, A_406]: (r2_hidden(C_404, B_405) | ~m1_connsp_2(B_405, A_406, C_404) | ~m1_subset_1(C_404, u1_struct_0(A_406)) | ~m1_subset_1(B_405, k1_zfmisc_1(u1_struct_0(A_406))) | ~l1_pre_topc(A_406) | ~v2_pre_topc(A_406) | v2_struct_0(A_406))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.60/2.37  tff(c_491, plain, (![B_441, A_442]: (r2_hidden(B_441, '#skF_2'(A_442, B_441)) | ~m1_subset_1('#skF_2'(A_442, B_441), k1_zfmisc_1(u1_struct_0(A_442))) | ~m1_subset_1(B_441, u1_struct_0(A_442)) | ~l1_pre_topc(A_442) | ~v2_pre_topc(A_442) | v2_struct_0(A_442))), inference(resolution, [status(thm)], [c_20, c_333])).
% 6.60/2.37  tff(c_499, plain, (![B_443, A_444]: (r2_hidden(B_443, '#skF_2'(A_444, B_443)) | ~m1_subset_1(B_443, u1_struct_0(A_444)) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(resolution, [status(thm)], [c_258, c_491])).
% 6.60/2.37  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.60/2.37  tff(c_503, plain, (![B_445, B_446, A_447]: (r2_hidden(B_445, B_446) | ~r1_tarski('#skF_2'(A_447, B_445), B_446) | ~m1_subset_1(B_445, u1_struct_0(A_447)) | ~l1_pre_topc(A_447) | ~v2_pre_topc(A_447) | v2_struct_0(A_447))), inference(resolution, [status(thm)], [c_499, c_2])).
% 6.60/2.37  tff(c_515, plain, (![B_379, A_378]: (r2_hidden(B_379, u1_struct_0(A_378)) | ~m1_subset_1(B_379, u1_struct_0(A_378)) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378))), inference(resolution, [status(thm)], [c_266, c_503])).
% 6.60/2.37  tff(c_72, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_130, plain, (![B_333, A_334]: (m1_subset_1(u1_struct_0(B_333), k1_zfmisc_1(u1_struct_0(A_334))) | ~m1_pre_topc(B_333, A_334) | ~l1_pre_topc(A_334))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.60/2.37  tff(c_134, plain, (![B_333, A_334]: (r1_tarski(u1_struct_0(B_333), u1_struct_0(A_334)) | ~m1_pre_topc(B_333, A_334) | ~l1_pre_topc(A_334))), inference(resolution, [status(thm)], [c_130, c_8])).
% 6.60/2.37  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.60/2.37  tff(c_440, plain, (![A_430, B_431, C_432]: (r1_tarski('#skF_3'(A_430, B_431, C_432), B_431) | ~r2_hidden(C_432, B_431) | ~m1_subset_1(C_432, u1_struct_0(A_430)) | ~v3_pre_topc(B_431, A_430) | ~m1_subset_1(B_431, k1_zfmisc_1(u1_struct_0(A_430))) | ~l1_pre_topc(A_430) | ~v2_pre_topc(A_430) | v2_struct_0(A_430))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.60/2.37  tff(c_450, plain, (![A_430, A_6, C_432]: (r1_tarski('#skF_3'(A_430, A_6, C_432), A_6) | ~r2_hidden(C_432, A_6) | ~m1_subset_1(C_432, u1_struct_0(A_430)) | ~v3_pre_topc(A_6, A_430) | ~l1_pre_topc(A_430) | ~v2_pre_topc(A_430) | v2_struct_0(A_430) | ~r1_tarski(A_6, u1_struct_0(A_430)))), inference(resolution, [status(thm)], [c_10, c_440])).
% 6.60/2.37  tff(c_34, plain, (![A_35, B_49, C_56]: (m1_subset_1('#skF_3'(A_35, B_49, C_56), k1_zfmisc_1(u1_struct_0(A_35))) | ~r2_hidden(C_56, B_49) | ~m1_subset_1(C_56, u1_struct_0(A_35)) | ~v3_pre_topc(B_49, A_35) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.60/2.37  tff(c_78, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_80, plain, (~r1_tmap_1('#skF_8', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_8'), '#skF_10') | ~r1_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_89, plain, (~r1_tmap_1('#skF_8', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_8'), '#skF_9') | ~r1_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_80])).
% 6.60/2.37  tff(c_145, plain, (~r1_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_89])).
% 6.60/2.37  tff(c_76, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_74, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_66, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_64, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_62, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_86, plain, (r1_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_9') | r1_tmap_1('#skF_8', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_8'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_292])).
% 6.60/2.37  tff(c_88, plain, (r1_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_9') | r1_tmap_1('#skF_8', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_86])).
% 6.60/2.37  tff(c_146, plain, (r1_tmap_1('#skF_8', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_8'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_145, c_88])).
% 6.60/2.37  tff(c_836, plain, (![G_520, D_519, E_515, A_518, C_516, B_517]: (r1_tmap_1(B_517, A_518, C_516, G_520) | ~r1_tmap_1(D_519, A_518, k2_tmap_1(B_517, A_518, C_516, D_519), G_520) | ~m1_connsp_2(E_515, B_517, G_520) | ~r1_tarski(E_515, u1_struct_0(D_519)) | ~m1_subset_1(G_520, u1_struct_0(D_519)) | ~m1_subset_1(G_520, u1_struct_0(B_517)) | ~m1_subset_1(E_515, k1_zfmisc_1(u1_struct_0(B_517))) | ~m1_pre_topc(D_519, B_517) | v2_struct_0(D_519) | ~m1_subset_1(C_516, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_517), u1_struct_0(A_518)))) | ~v1_funct_2(C_516, u1_struct_0(B_517), u1_struct_0(A_518)) | ~v1_funct_1(C_516) | ~l1_pre_topc(B_517) | ~v2_pre_topc(B_517) | v2_struct_0(B_517) | ~l1_pre_topc(A_518) | ~v2_pre_topc(A_518) | v2_struct_0(A_518))), inference(cnfTransformation, [status(thm)], [f_249])).
% 6.60/2.37  tff(c_840, plain, (![E_515]: (r1_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_9') | ~m1_connsp_2(E_515, '#skF_6', '#skF_9') | ~r1_tarski(E_515, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1(E_515, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc('#skF_8', '#skF_6') | v2_struct_0('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_146, c_836])).
% 6.60/2.37  tff(c_847, plain, (![E_515]: (r1_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_9') | ~m1_connsp_2(E_515, '#skF_6', '#skF_9') | ~r1_tarski(E_515, u1_struct_0('#skF_8')) | ~m1_subset_1(E_515, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_8') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_66, c_64, c_62, c_56, c_54, c_87, c_840])).
% 6.60/2.37  tff(c_849, plain, (![E_521]: (~m1_connsp_2(E_521, '#skF_6', '#skF_9') | ~r1_tarski(E_521, u1_struct_0('#skF_8')) | ~m1_subset_1(E_521, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_60, c_145, c_847])).
% 6.60/2.37  tff(c_853, plain, (![B_49, C_56]: (~m1_connsp_2('#skF_3'('#skF_6', B_49, C_56), '#skF_6', '#skF_9') | ~r1_tarski('#skF_3'('#skF_6', B_49, C_56), u1_struct_0('#skF_8')) | ~r2_hidden(C_56, B_49) | ~m1_subset_1(C_56, u1_struct_0('#skF_6')) | ~v3_pre_topc(B_49, '#skF_6') | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_849])).
% 6.60/2.37  tff(c_868, plain, (![B_49, C_56]: (~m1_connsp_2('#skF_3'('#skF_6', B_49, C_56), '#skF_6', '#skF_9') | ~r1_tarski('#skF_3'('#skF_6', B_49, C_56), u1_struct_0('#skF_8')) | ~r2_hidden(C_56, B_49) | ~m1_subset_1(C_56, u1_struct_0('#skF_6')) | ~v3_pre_topc(B_49, '#skF_6') | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_853])).
% 6.60/2.37  tff(c_1002, plain, (![B_531, C_532]: (~m1_connsp_2('#skF_3'('#skF_6', B_531, C_532), '#skF_6', '#skF_9') | ~r1_tarski('#skF_3'('#skF_6', B_531, C_532), u1_struct_0('#skF_8')) | ~r2_hidden(C_532, B_531) | ~m1_subset_1(C_532, u1_struct_0('#skF_6')) | ~v3_pre_topc(B_531, '#skF_6') | ~m1_subset_1(B_531, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_868])).
% 6.60/2.37  tff(c_1006, plain, (![C_432]: (~m1_connsp_2('#skF_3'('#skF_6', u1_struct_0('#skF_8'), C_432), '#skF_6', '#skF_9') | ~m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_hidden(C_432, u1_struct_0('#skF_8')) | ~m1_subset_1(C_432, u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_8'), '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~r1_tarski(u1_struct_0('#skF_8'), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_450, c_1002])).
% 6.60/2.37  tff(c_1009, plain, (![C_432]: (~m1_connsp_2('#skF_3'('#skF_6', u1_struct_0('#skF_8'), C_432), '#skF_6', '#skF_9') | ~m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_hidden(C_432, u1_struct_0('#skF_8')) | ~m1_subset_1(C_432, u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_8'), '#skF_6') | v2_struct_0('#skF_6') | ~r1_tarski(u1_struct_0('#skF_8'), u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1006])).
% 6.60/2.37  tff(c_1010, plain, (![C_432]: (~m1_connsp_2('#skF_3'('#skF_6', u1_struct_0('#skF_8'), C_432), '#skF_6', '#skF_9') | ~m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_hidden(C_432, u1_struct_0('#skF_8')) | ~m1_subset_1(C_432, u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_8'), '#skF_6') | ~r1_tarski(u1_struct_0('#skF_8'), u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_72, c_1009])).
% 6.60/2.37  tff(c_1086, plain, (~r1_tarski(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1010])).
% 6.60/2.37  tff(c_1095, plain, (~m1_pre_topc('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_134, c_1086])).
% 6.60/2.37  tff(c_1103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_56, c_1095])).
% 6.60/2.37  tff(c_1104, plain, (![C_432]: (~v3_pre_topc(u1_struct_0('#skF_8'), '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_connsp_2('#skF_3'('#skF_6', u1_struct_0('#skF_8'), C_432), '#skF_6', '#skF_9') | ~r2_hidden(C_432, u1_struct_0('#skF_8')) | ~m1_subset_1(C_432, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_1010])).
% 6.60/2.37  tff(c_2129, plain, (~m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_1104])).
% 6.60/2.37  tff(c_2136, plain, (~m1_pre_topc('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_42, c_2129])).
% 6.60/2.37  tff(c_2143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_56, c_2136])).
% 6.60/2.37  tff(c_2145, plain, (m1_subset_1(u1_struct_0('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_1104])).
% 6.60/2.37  tff(c_26, plain, (![A_35, B_49]: (r2_hidden('#skF_4'(A_35, B_49), B_49) | v3_pre_topc(B_49, A_35) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.60/2.37  tff(c_2151, plain, (r2_hidden('#skF_4'('#skF_6', u1_struct_0('#skF_8')), u1_struct_0('#skF_8')) | v3_pre_topc(u1_struct_0('#skF_8'), '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_2145, c_26])).
% 6.60/2.37  tff(c_2165, plain, (r2_hidden('#skF_4'('#skF_6', u1_struct_0('#skF_8')), u1_struct_0('#skF_8')) | v3_pre_topc(u1_struct_0('#skF_8'), '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_2151])).
% 6.60/2.37  tff(c_2166, plain, (r2_hidden('#skF_4'('#skF_6', u1_struct_0('#skF_8')), u1_struct_0('#skF_8')) | v3_pre_topc(u1_struct_0('#skF_8'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_72, c_2165])).
% 6.60/2.37  tff(c_2169, plain, (v3_pre_topc(u1_struct_0('#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_2166])).
% 6.60/2.37  tff(c_518, plain, (![A_448, B_449, C_450]: (m1_connsp_2('#skF_3'(A_448, B_449, C_450), A_448, C_450) | ~r2_hidden(C_450, B_449) | ~m1_subset_1(C_450, u1_struct_0(A_448)) | ~v3_pre_topc(B_449, A_448) | ~m1_subset_1(B_449, k1_zfmisc_1(u1_struct_0(A_448))) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448) | v2_struct_0(A_448))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.60/2.37  tff(c_527, plain, (![A_67, B_69, C_450]: (m1_connsp_2('#skF_3'(A_67, u1_struct_0(B_69), C_450), A_67, C_450) | ~r2_hidden(C_450, u1_struct_0(B_69)) | ~m1_subset_1(C_450, u1_struct_0(A_67)) | ~v3_pre_topc(u1_struct_0(B_69), A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67) | ~m1_pre_topc(B_69, A_67) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_42, c_518])).
% 6.60/2.37  tff(c_2144, plain, (![C_432]: (~v3_pre_topc(u1_struct_0('#skF_8'), '#skF_6') | ~m1_connsp_2('#skF_3'('#skF_6', u1_struct_0('#skF_8'), C_432), '#skF_6', '#skF_9') | ~r2_hidden(C_432, u1_struct_0('#skF_8')) | ~m1_subset_1(C_432, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_1104])).
% 6.60/2.37  tff(c_2178, plain, (![C_677]: (~m1_connsp_2('#skF_3'('#skF_6', u1_struct_0('#skF_8'), C_677), '#skF_6', '#skF_9') | ~r2_hidden(C_677, u1_struct_0('#skF_8')) | ~m1_subset_1(C_677, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2169, c_2144])).
% 6.60/2.37  tff(c_2182, plain, (~r2_hidden('#skF_9', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_8'), '#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_527, c_2178])).
% 6.60/2.37  tff(c_2189, plain, (~r2_hidden('#skF_9', u1_struct_0('#skF_8')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_56, c_70, c_2169, c_54, c_2182])).
% 6.60/2.37  tff(c_2190, plain, (~r2_hidden('#skF_9', u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_72, c_2189])).
% 6.60/2.37  tff(c_2228, plain, (~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_515, c_2190])).
% 6.60/2.37  tff(c_2240, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_100, c_87, c_2228])).
% 6.60/2.37  tff(c_2242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2240])).
% 6.60/2.37  tff(c_2244, plain, (~v3_pre_topc(u1_struct_0('#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_2166])).
% 6.60/2.37  tff(c_2247, plain, (~v1_tsep_1('#skF_8', '#skF_6') | ~v2_pre_topc('#skF_6') | ~m1_pre_topc('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_297, c_2244])).
% 6.60/2.37  tff(c_2251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_56, c_70, c_58, c_2247])).
% 6.60/2.37  tff(c_2253, plain, (r1_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_89])).
% 6.60/2.37  tff(c_2879, plain, (![B_833, C_829, D_832, A_830, F_831]: (r1_tmap_1(D_832, A_830, k2_tmap_1(B_833, A_830, C_829, D_832), F_831) | ~r1_tmap_1(B_833, A_830, C_829, F_831) | ~m1_subset_1(F_831, u1_struct_0(D_832)) | ~m1_subset_1(F_831, u1_struct_0(B_833)) | ~m1_pre_topc(D_832, B_833) | v2_struct_0(D_832) | ~m1_subset_1(C_829, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_833), u1_struct_0(A_830)))) | ~v1_funct_2(C_829, u1_struct_0(B_833), u1_struct_0(A_830)) | ~v1_funct_1(C_829) | ~l1_pre_topc(B_833) | ~v2_pre_topc(B_833) | v2_struct_0(B_833) | ~l1_pre_topc(A_830) | ~v2_pre_topc(A_830) | v2_struct_0(A_830))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.60/2.37  tff(c_2881, plain, (![D_832, F_831]: (r1_tmap_1(D_832, '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_7', D_832), F_831) | ~r1_tmap_1('#skF_6', '#skF_5', '#skF_7', F_831) | ~m1_subset_1(F_831, u1_struct_0(D_832)) | ~m1_subset_1(F_831, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_832, '#skF_6') | v2_struct_0(D_832) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_2879])).
% 6.60/2.37  tff(c_2887, plain, (![D_832, F_831]: (r1_tmap_1(D_832, '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_7', D_832), F_831) | ~r1_tmap_1('#skF_6', '#skF_5', '#skF_7', F_831) | ~m1_subset_1(F_831, u1_struct_0(D_832)) | ~m1_subset_1(F_831, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_832, '#skF_6') | v2_struct_0(D_832) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_66, c_64, c_2881])).
% 6.60/2.37  tff(c_2934, plain, (![D_844, F_845]: (r1_tmap_1(D_844, '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_7', D_844), F_845) | ~r1_tmap_1('#skF_6', '#skF_5', '#skF_7', F_845) | ~m1_subset_1(F_845, u1_struct_0(D_844)) | ~m1_subset_1(F_845, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_844, '#skF_6') | v2_struct_0(D_844))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_2887])).
% 6.60/2.37  tff(c_2252, plain, (~r1_tmap_1('#skF_8', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_89])).
% 6.60/2.37  tff(c_2937, plain, (~r1_tmap_1('#skF_6', '#skF_5', '#skF_7', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_8', '#skF_6') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_2934, c_2252])).
% 6.60/2.37  tff(c_2940, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_87, c_2253, c_2937])).
% 6.60/2.37  tff(c_2942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2940])).
% 6.60/2.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.60/2.37  
% 6.60/2.37  Inference rules
% 6.60/2.37  ----------------------
% 6.60/2.37  #Ref     : 0
% 6.60/2.37  #Sup     : 646
% 6.60/2.37  #Fact    : 0
% 6.60/2.37  #Define  : 0
% 6.60/2.37  #Split   : 25
% 6.60/2.37  #Chain   : 0
% 6.60/2.37  #Close   : 0
% 6.60/2.37  
% 6.60/2.37  Ordering : KBO
% 6.60/2.37  
% 6.60/2.37  Simplification rules
% 6.60/2.37  ----------------------
% 6.60/2.37  #Subsume      : 277
% 6.60/2.37  #Demod        : 236
% 6.60/2.37  #Tautology    : 30
% 6.60/2.37  #SimpNegUnit  : 55
% 6.60/2.37  #BackRed      : 0
% 6.60/2.37  
% 6.60/2.37  #Partial instantiations: 0
% 6.60/2.37  #Strategies tried      : 1
% 6.60/2.37  
% 6.60/2.37  Timing (in seconds)
% 6.60/2.37  ----------------------
% 6.60/2.37  Preprocessing        : 0.47
% 6.60/2.37  Parsing              : 0.24
% 6.60/2.37  CNF conversion       : 0.06
% 6.60/2.37  Main loop            : 1.06
% 6.60/2.37  Inferencing          : 0.36
% 6.60/2.37  Reduction            : 0.29
% 6.60/2.37  Demodulation         : 0.20
% 6.60/2.37  BG Simplification    : 0.04
% 6.60/2.37  Subsumption          : 0.29
% 6.60/2.37  Abstraction          : 0.04
% 6.60/2.37  MUC search           : 0.00
% 6.60/2.37  Cooper               : 0.00
% 6.60/2.37  Total                : 1.58
% 6.60/2.37  Index Insertion      : 0.00
% 6.60/2.37  Index Deletion       : 0.00
% 6.60/2.37  Index Matching       : 0.00
% 6.60/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
