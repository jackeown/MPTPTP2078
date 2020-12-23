%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:04 EST 2020

% Result     : Theorem 5.04s
% Output     : CNFRefutation 5.04s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 368 expanded)
%              Number of leaves         :   42 ( 154 expanded)
%              Depth                    :   16
%              Number of atoms          :  363 (2341 expanded)
%              Number of equality atoms :    6 ( 117 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v4_pre_topc > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(f_311,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_167,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_160,axiom,(
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

tff(f_142,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_268,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_58,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_52,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_89,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54])).

tff(c_72,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_120,plain,(
    ! [B_317,A_318] :
      ( v2_pre_topc(B_317)
      | ~ m1_pre_topc(B_317,A_318)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_123,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_120])).

tff(c_126,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_123])).

tff(c_98,plain,(
    ! [B_309,A_310] :
      ( l1_pre_topc(B_309)
      | ~ m1_pre_topc(B_309,A_310)
      | ~ l1_pre_topc(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_101,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_98])).

tff(c_104,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_101])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_135,plain,(
    ! [B_326,A_327] :
      ( m1_subset_1(u1_struct_0(B_326),k1_zfmisc_1(u1_struct_0(A_327)))
      | ~ m1_pre_topc(B_326,A_327)
      | ~ l1_pre_topc(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( m1_subset_1(A_8,C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_155,plain,(
    ! [A_332,A_333,B_334] :
      ( m1_subset_1(A_332,u1_struct_0(A_333))
      | ~ r2_hidden(A_332,u1_struct_0(B_334))
      | ~ m1_pre_topc(B_334,A_333)
      | ~ l1_pre_topc(A_333) ) ),
    inference(resolution,[status(thm)],[c_135,c_12])).

tff(c_254,plain,(
    ! [A_358,A_359,B_360] :
      ( m1_subset_1(A_358,u1_struct_0(A_359))
      | ~ m1_pre_topc(B_360,A_359)
      | ~ l1_pre_topc(A_359)
      | v1_xboole_0(u1_struct_0(B_360))
      | ~ m1_subset_1(A_358,u1_struct_0(B_360)) ) ),
    inference(resolution,[status(thm)],[c_10,c_155])).

tff(c_256,plain,(
    ! [A_358] :
      ( m1_subset_1(A_358,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_358,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_58,c_254])).

tff(c_259,plain,(
    ! [A_358] :
      ( m1_subset_1(A_358,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_358,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_256])).

tff(c_260,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_144,plain,(
    ! [A_330] :
      ( m1_subset_1('#skF_1'(A_330),k1_zfmisc_1(u1_struct_0(A_330)))
      | ~ l1_pre_topc(A_330)
      | ~ v2_pre_topc(A_330)
      | v2_struct_0(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_xboole_0(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_151,plain,(
    ! [A_330] :
      ( v1_xboole_0('#skF_1'(A_330))
      | ~ v1_xboole_0(u1_struct_0(A_330))
      | ~ l1_pre_topc(A_330)
      | ~ v2_pre_topc(A_330)
      | v2_struct_0(A_330) ) ),
    inference(resolution,[status(thm)],[c_144,c_8])).

tff(c_271,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_260,c_151])).

tff(c_279,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_104,c_271])).

tff(c_280,plain,(
    v1_xboole_0('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_279])).

tff(c_26,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0('#skF_1'(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_286,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_280,c_26])).

tff(c_289,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_104,c_286])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_289])).

tff(c_293,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_60,plain,(
    v1_tsep_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_40,plain,(
    ! [B_53,A_51] :
      ( m1_subset_1(u1_struct_0(B_53),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_798,plain,(
    ! [B_437,A_438] :
      ( v3_pre_topc(u1_struct_0(B_437),A_438)
      | ~ v1_tsep_1(B_437,A_438)
      | ~ m1_subset_1(u1_struct_0(B_437),k1_zfmisc_1(u1_struct_0(A_438)))
      | ~ m1_pre_topc(B_437,A_438)
      | ~ l1_pre_topc(A_438)
      | ~ v2_pre_topc(A_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_822,plain,(
    ! [B_53,A_51] :
      ( v3_pre_topc(u1_struct_0(B_53),A_51)
      | ~ v1_tsep_1(B_53,A_51)
      | ~ v2_pre_topc(A_51)
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_40,c_798])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_887,plain,(
    ! [B_445,A_446,C_447] :
      ( m1_connsp_2(B_445,A_446,C_447)
      | ~ r2_hidden(C_447,B_445)
      | ~ v3_pre_topc(B_445,A_446)
      | ~ m1_subset_1(C_447,u1_struct_0(A_446))
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0(A_446)))
      | ~ l1_pre_topc(A_446)
      | ~ v2_pre_topc(A_446)
      | v2_struct_0(A_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_903,plain,(
    ! [B_445] :
      ( m1_connsp_2(B_445,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_445)
      | ~ v3_pre_topc(B_445,'#skF_3')
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_887])).

tff(c_921,plain,(
    ! [B_445] :
      ( m1_connsp_2(B_445,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_445)
      | ~ v3_pre_topc(B_445,'#skF_3')
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_903])).

tff(c_927,plain,(
    ! [B_448] :
      ( m1_connsp_2(B_448,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_448)
      | ~ v3_pre_topc(B_448,'#skF_3')
      | ~ m1_subset_1(B_448,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_921])).

tff(c_950,plain,(
    ! [B_53] :
      ( m1_connsp_2(u1_struct_0(B_53),'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_53))
      | ~ v3_pre_topc(u1_struct_0(B_53),'#skF_3')
      | ~ m1_pre_topc(B_53,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_927])).

tff(c_1271,plain,(
    ! [B_477] :
      ( m1_connsp_2(u1_struct_0(B_477),'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_477))
      | ~ v3_pre_topc(u1_struct_0(B_477),'#skF_3')
      | ~ m1_pre_topc(B_477,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_950])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_88,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_90,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_88])).

tff(c_106,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_82,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_91,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_82])).

tff(c_153,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_91])).

tff(c_78,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_1100,plain,(
    ! [D_463,C_461,A_460,E_464,B_459,G_462] :
      ( r1_tmap_1(B_459,A_460,C_461,G_462)
      | ~ r1_tmap_1(D_463,A_460,k2_tmap_1(B_459,A_460,C_461,D_463),G_462)
      | ~ m1_connsp_2(E_464,B_459,G_462)
      | ~ r1_tarski(E_464,u1_struct_0(D_463))
      | ~ m1_subset_1(G_462,u1_struct_0(D_463))
      | ~ m1_subset_1(G_462,u1_struct_0(B_459))
      | ~ m1_subset_1(E_464,k1_zfmisc_1(u1_struct_0(B_459)))
      | ~ m1_pre_topc(D_463,B_459)
      | v2_struct_0(D_463)
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_459),u1_struct_0(A_460))))
      | ~ v1_funct_2(C_461,u1_struct_0(B_459),u1_struct_0(A_460))
      | ~ v1_funct_1(C_461)
      | ~ l1_pre_topc(B_459)
      | ~ v2_pre_topc(B_459)
      | v2_struct_0(B_459)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_1102,plain,(
    ! [E_464] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_464,'#skF_3','#skF_6')
      | ~ r1_tarski(E_464,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_464,k1_zfmisc_1(u1_struct_0('#skF_3')))
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
    inference(resolution,[status(thm)],[c_106,c_1100])).

tff(c_1105,plain,(
    ! [E_464] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_464,'#skF_3','#skF_6')
      | ~ r1_tarski(E_464,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_464,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_68,c_66,c_64,c_58,c_56,c_89,c_1102])).

tff(c_1107,plain,(
    ! [E_465] :
      ( ~ m1_connsp_2(E_465,'#skF_3','#skF_6')
      | ~ r1_tarski(E_465,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_465,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_62,c_153,c_1105])).

tff(c_1130,plain,(
    ! [B_53] :
      ( ~ m1_connsp_2(u1_struct_0(B_53),'#skF_3','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_53),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_53,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_1107])).

tff(c_1156,plain,(
    ! [B_467] :
      ( ~ m1_connsp_2(u1_struct_0(B_467),'#skF_3','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_467),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_467,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1130])).

tff(c_1163,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1156])).

tff(c_1167,plain,(
    ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1163])).

tff(c_1277,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_1271,c_1167])).

tff(c_1283,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1277])).

tff(c_1288,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1283])).

tff(c_1291,plain,
    ( ~ v1_tsep_1('#skF_5','#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_822,c_1288])).

tff(c_1298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_58,c_72,c_60,c_1291])).

tff(c_1299,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1283])).

tff(c_1322,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10,c_1299])).

tff(c_1325,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1322])).

tff(c_1327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_1325])).

tff(c_1328,plain,(
    r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2177,plain,(
    ! [A_611,D_612,B_613,C_609,F_610] :
      ( r1_tmap_1(D_612,A_611,k2_tmap_1(B_613,A_611,C_609,D_612),F_610)
      | ~ r1_tmap_1(B_613,A_611,C_609,F_610)
      | ~ m1_subset_1(F_610,u1_struct_0(D_612))
      | ~ m1_subset_1(F_610,u1_struct_0(B_613))
      | ~ m1_pre_topc(D_612,B_613)
      | v2_struct_0(D_612)
      | ~ m1_subset_1(C_609,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_613),u1_struct_0(A_611))))
      | ~ v1_funct_2(C_609,u1_struct_0(B_613),u1_struct_0(A_611))
      | ~ v1_funct_1(C_609)
      | ~ l1_pre_topc(B_613)
      | ~ v2_pre_topc(B_613)
      | v2_struct_0(B_613)
      | ~ l1_pre_topc(A_611)
      | ~ v2_pre_topc(A_611)
      | v2_struct_0(A_611) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_2179,plain,(
    ! [D_612,F_610] :
      ( r1_tmap_1(D_612,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_612),F_610)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_610)
      | ~ m1_subset_1(F_610,u1_struct_0(D_612))
      | ~ m1_subset_1(F_610,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_612,'#skF_3')
      | v2_struct_0(D_612)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_2177])).

tff(c_2182,plain,(
    ! [D_612,F_610] :
      ( r1_tmap_1(D_612,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_612),F_610)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_610)
      | ~ m1_subset_1(F_610,u1_struct_0(D_612))
      | ~ m1_subset_1(F_610,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_612,'#skF_3')
      | v2_struct_0(D_612)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_68,c_66,c_2179])).

tff(c_2320,plain,(
    ! [D_629,F_630] :
      ( r1_tmap_1(D_629,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_629),F_630)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_630)
      | ~ m1_subset_1(F_630,u1_struct_0(D_629))
      | ~ m1_subset_1(F_630,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_629,'#skF_3')
      | v2_struct_0(D_629) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_2182])).

tff(c_1352,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1328,c_91])).

tff(c_2325,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2320,c_1352])).

tff(c_2332,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_89,c_1328,c_2325])).

tff(c_2334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.04/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.04/1.88  
% 5.04/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.04/1.88  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v4_pre_topc > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 5.04/1.88  
% 5.04/1.88  %Foreground sorts:
% 5.04/1.88  
% 5.04/1.88  
% 5.04/1.88  %Background operators:
% 5.04/1.88  
% 5.04/1.88  
% 5.04/1.88  %Foreground operators:
% 5.04/1.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.04/1.88  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.04/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.04/1.88  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.04/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.04/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.04/1.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.04/1.88  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.04/1.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.04/1.88  tff('#skF_7', type, '#skF_7': $i).
% 5.04/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.04/1.88  tff('#skF_5', type, '#skF_5': $i).
% 5.04/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.04/1.88  tff('#skF_6', type, '#skF_6': $i).
% 5.04/1.88  tff('#skF_2', type, '#skF_2': $i).
% 5.04/1.88  tff('#skF_3', type, '#skF_3': $i).
% 5.04/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.04/1.88  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.04/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.04/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.04/1.88  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.04/1.88  tff('#skF_4', type, '#skF_4': $i).
% 5.04/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.04/1.88  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.04/1.88  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.04/1.88  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.04/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.04/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.04/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.04/1.88  
% 5.04/1.91  tff(f_311, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 5.04/1.91  tff(f_59, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.04/1.91  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.04/1.91  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.04/1.91  tff(f_167, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.04/1.91  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.04/1.91  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_tops_1)).
% 5.04/1.91  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.04/1.91  tff(f_160, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 5.04/1.91  tff(f_142, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 5.04/1.91  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.04/1.91  tff(f_268, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 5.04/1.91  tff(f_221, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 5.04/1.91  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_58, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_56, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_52, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_54, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_89, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54])).
% 5.04/1.91  tff(c_72, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_120, plain, (![B_317, A_318]: (v2_pre_topc(B_317) | ~m1_pre_topc(B_317, A_318) | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.04/1.91  tff(c_123, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_58, c_120])).
% 5.04/1.91  tff(c_126, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_123])).
% 5.04/1.91  tff(c_98, plain, (![B_309, A_310]: (l1_pre_topc(B_309) | ~m1_pre_topc(B_309, A_310) | ~l1_pre_topc(A_310))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.04/1.91  tff(c_101, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_58, c_98])).
% 5.04/1.91  tff(c_104, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_101])).
% 5.04/1.91  tff(c_10, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.04/1.91  tff(c_135, plain, (![B_326, A_327]: (m1_subset_1(u1_struct_0(B_326), k1_zfmisc_1(u1_struct_0(A_327))) | ~m1_pre_topc(B_326, A_327) | ~l1_pre_topc(A_327))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.04/1.91  tff(c_12, plain, (![A_8, C_10, B_9]: (m1_subset_1(A_8, C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.04/1.91  tff(c_155, plain, (![A_332, A_333, B_334]: (m1_subset_1(A_332, u1_struct_0(A_333)) | ~r2_hidden(A_332, u1_struct_0(B_334)) | ~m1_pre_topc(B_334, A_333) | ~l1_pre_topc(A_333))), inference(resolution, [status(thm)], [c_135, c_12])).
% 5.04/1.91  tff(c_254, plain, (![A_358, A_359, B_360]: (m1_subset_1(A_358, u1_struct_0(A_359)) | ~m1_pre_topc(B_360, A_359) | ~l1_pre_topc(A_359) | v1_xboole_0(u1_struct_0(B_360)) | ~m1_subset_1(A_358, u1_struct_0(B_360)))), inference(resolution, [status(thm)], [c_10, c_155])).
% 5.04/1.91  tff(c_256, plain, (![A_358]: (m1_subset_1(A_358, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_358, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_58, c_254])).
% 5.04/1.91  tff(c_259, plain, (![A_358]: (m1_subset_1(A_358, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_358, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_256])).
% 5.04/1.91  tff(c_260, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_259])).
% 5.04/1.91  tff(c_144, plain, (![A_330]: (m1_subset_1('#skF_1'(A_330), k1_zfmisc_1(u1_struct_0(A_330))) | ~l1_pre_topc(A_330) | ~v2_pre_topc(A_330) | v2_struct_0(A_330))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.04/1.91  tff(c_8, plain, (![B_5, A_3]: (v1_xboole_0(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.04/1.91  tff(c_151, plain, (![A_330]: (v1_xboole_0('#skF_1'(A_330)) | ~v1_xboole_0(u1_struct_0(A_330)) | ~l1_pre_topc(A_330) | ~v2_pre_topc(A_330) | v2_struct_0(A_330))), inference(resolution, [status(thm)], [c_144, c_8])).
% 5.04/1.91  tff(c_271, plain, (v1_xboole_0('#skF_1'('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_260, c_151])).
% 5.04/1.91  tff(c_279, plain, (v1_xboole_0('#skF_1'('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_104, c_271])).
% 5.04/1.91  tff(c_280, plain, (v1_xboole_0('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_279])).
% 5.04/1.91  tff(c_26, plain, (![A_31]: (~v1_xboole_0('#skF_1'(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.04/1.91  tff(c_286, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_280, c_26])).
% 5.04/1.91  tff(c_289, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_104, c_286])).
% 5.04/1.91  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_289])).
% 5.04/1.91  tff(c_293, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_259])).
% 5.04/1.91  tff(c_60, plain, (v1_tsep_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_40, plain, (![B_53, A_51]: (m1_subset_1(u1_struct_0(B_53), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.04/1.91  tff(c_798, plain, (![B_437, A_438]: (v3_pre_topc(u1_struct_0(B_437), A_438) | ~v1_tsep_1(B_437, A_438) | ~m1_subset_1(u1_struct_0(B_437), k1_zfmisc_1(u1_struct_0(A_438))) | ~m1_pre_topc(B_437, A_438) | ~l1_pre_topc(A_438) | ~v2_pre_topc(A_438))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.04/1.91  tff(c_822, plain, (![B_53, A_51]: (v3_pre_topc(u1_struct_0(B_53), A_51) | ~v1_tsep_1(B_53, A_51) | ~v2_pre_topc(A_51) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_40, c_798])).
% 5.04/1.91  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_887, plain, (![B_445, A_446, C_447]: (m1_connsp_2(B_445, A_446, C_447) | ~r2_hidden(C_447, B_445) | ~v3_pre_topc(B_445, A_446) | ~m1_subset_1(C_447, u1_struct_0(A_446)) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0(A_446))) | ~l1_pre_topc(A_446) | ~v2_pre_topc(A_446) | v2_struct_0(A_446))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.04/1.91  tff(c_903, plain, (![B_445]: (m1_connsp_2(B_445, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_445) | ~v3_pre_topc(B_445, '#skF_3') | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_887])).
% 5.04/1.91  tff(c_921, plain, (![B_445]: (m1_connsp_2(B_445, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_445) | ~v3_pre_topc(B_445, '#skF_3') | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_903])).
% 5.04/1.91  tff(c_927, plain, (![B_448]: (m1_connsp_2(B_448, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_448) | ~v3_pre_topc(B_448, '#skF_3') | ~m1_subset_1(B_448, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_921])).
% 5.04/1.91  tff(c_950, plain, (![B_53]: (m1_connsp_2(u1_struct_0(B_53), '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_53)) | ~v3_pre_topc(u1_struct_0(B_53), '#skF_3') | ~m1_pre_topc(B_53, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_927])).
% 5.04/1.91  tff(c_1271, plain, (![B_477]: (m1_connsp_2(u1_struct_0(B_477), '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_477)) | ~v3_pre_topc(u1_struct_0(B_477), '#skF_3') | ~m1_pre_topc(B_477, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_950])).
% 5.04/1.91  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.04/1.91  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_88, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_90, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_88])).
% 5.04/1.91  tff(c_106, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_90])).
% 5.04/1.91  tff(c_82, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_91, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_82])).
% 5.04/1.91  tff(c_153, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_91])).
% 5.04/1.91  tff(c_78, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_66, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.04/1.91  tff(c_1100, plain, (![D_463, C_461, A_460, E_464, B_459, G_462]: (r1_tmap_1(B_459, A_460, C_461, G_462) | ~r1_tmap_1(D_463, A_460, k2_tmap_1(B_459, A_460, C_461, D_463), G_462) | ~m1_connsp_2(E_464, B_459, G_462) | ~r1_tarski(E_464, u1_struct_0(D_463)) | ~m1_subset_1(G_462, u1_struct_0(D_463)) | ~m1_subset_1(G_462, u1_struct_0(B_459)) | ~m1_subset_1(E_464, k1_zfmisc_1(u1_struct_0(B_459))) | ~m1_pre_topc(D_463, B_459) | v2_struct_0(D_463) | ~m1_subset_1(C_461, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_459), u1_struct_0(A_460)))) | ~v1_funct_2(C_461, u1_struct_0(B_459), u1_struct_0(A_460)) | ~v1_funct_1(C_461) | ~l1_pre_topc(B_459) | ~v2_pre_topc(B_459) | v2_struct_0(B_459) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460))), inference(cnfTransformation, [status(thm)], [f_268])).
% 5.04/1.91  tff(c_1102, plain, (![E_464]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_464, '#skF_3', '#skF_6') | ~r1_tarski(E_464, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1(E_464, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_106, c_1100])).
% 5.04/1.91  tff(c_1105, plain, (![E_464]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_464, '#skF_3', '#skF_6') | ~r1_tarski(E_464, u1_struct_0('#skF_5')) | ~m1_subset_1(E_464, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_68, c_66, c_64, c_58, c_56, c_89, c_1102])).
% 5.04/1.91  tff(c_1107, plain, (![E_465]: (~m1_connsp_2(E_465, '#skF_3', '#skF_6') | ~r1_tarski(E_465, u1_struct_0('#skF_5')) | ~m1_subset_1(E_465, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_62, c_153, c_1105])).
% 5.04/1.91  tff(c_1130, plain, (![B_53]: (~m1_connsp_2(u1_struct_0(B_53), '#skF_3', '#skF_6') | ~r1_tarski(u1_struct_0(B_53), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_53, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_1107])).
% 5.04/1.91  tff(c_1156, plain, (![B_467]: (~m1_connsp_2(u1_struct_0(B_467), '#skF_3', '#skF_6') | ~r1_tarski(u1_struct_0(B_467), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_467, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1130])).
% 5.04/1.91  tff(c_1163, plain, (~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_1156])).
% 5.04/1.91  tff(c_1167, plain, (~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1163])).
% 5.04/1.91  tff(c_1277, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_1271, c_1167])).
% 5.04/1.91  tff(c_1283, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1277])).
% 5.04/1.91  tff(c_1288, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1283])).
% 5.04/1.91  tff(c_1291, plain, (~v1_tsep_1('#skF_5', '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_822, c_1288])).
% 5.04/1.91  tff(c_1298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_58, c_72, c_60, c_1291])).
% 5.04/1.91  tff(c_1299, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1283])).
% 5.04/1.91  tff(c_1322, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_1299])).
% 5.04/1.91  tff(c_1325, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1322])).
% 5.04/1.91  tff(c_1327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_293, c_1325])).
% 5.04/1.91  tff(c_1328, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_90])).
% 5.04/1.91  tff(c_2177, plain, (![A_611, D_612, B_613, C_609, F_610]: (r1_tmap_1(D_612, A_611, k2_tmap_1(B_613, A_611, C_609, D_612), F_610) | ~r1_tmap_1(B_613, A_611, C_609, F_610) | ~m1_subset_1(F_610, u1_struct_0(D_612)) | ~m1_subset_1(F_610, u1_struct_0(B_613)) | ~m1_pre_topc(D_612, B_613) | v2_struct_0(D_612) | ~m1_subset_1(C_609, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_613), u1_struct_0(A_611)))) | ~v1_funct_2(C_609, u1_struct_0(B_613), u1_struct_0(A_611)) | ~v1_funct_1(C_609) | ~l1_pre_topc(B_613) | ~v2_pre_topc(B_613) | v2_struct_0(B_613) | ~l1_pre_topc(A_611) | ~v2_pre_topc(A_611) | v2_struct_0(A_611))), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.04/1.91  tff(c_2179, plain, (![D_612, F_610]: (r1_tmap_1(D_612, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_612), F_610) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_610) | ~m1_subset_1(F_610, u1_struct_0(D_612)) | ~m1_subset_1(F_610, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_612, '#skF_3') | v2_struct_0(D_612) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_2177])).
% 5.04/1.91  tff(c_2182, plain, (![D_612, F_610]: (r1_tmap_1(D_612, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_612), F_610) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_610) | ~m1_subset_1(F_610, u1_struct_0(D_612)) | ~m1_subset_1(F_610, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_612, '#skF_3') | v2_struct_0(D_612) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_68, c_66, c_2179])).
% 5.04/1.91  tff(c_2320, plain, (![D_629, F_630]: (r1_tmap_1(D_629, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_629), F_630) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_630) | ~m1_subset_1(F_630, u1_struct_0(D_629)) | ~m1_subset_1(F_630, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_629, '#skF_3') | v2_struct_0(D_629))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_2182])).
% 5.04/1.91  tff(c_1352, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1328, c_91])).
% 5.04/1.91  tff(c_2325, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2320, c_1352])).
% 5.04/1.91  tff(c_2332, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_89, c_1328, c_2325])).
% 5.04/1.91  tff(c_2334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_2332])).
% 5.04/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.04/1.91  
% 5.04/1.91  Inference rules
% 5.04/1.91  ----------------------
% 5.04/1.91  #Ref     : 0
% 5.04/1.91  #Sup     : 420
% 5.04/1.91  #Fact    : 0
% 5.04/1.91  #Define  : 0
% 5.04/1.91  #Split   : 31
% 5.04/1.91  #Chain   : 0
% 5.04/1.91  #Close   : 0
% 5.04/1.91  
% 5.04/1.91  Ordering : KBO
% 5.04/1.91  
% 5.04/1.91  Simplification rules
% 5.04/1.91  ----------------------
% 5.04/1.91  #Subsume      : 117
% 5.04/1.91  #Demod        : 384
% 5.04/1.91  #Tautology    : 79
% 5.04/1.91  #SimpNegUnit  : 104
% 5.04/1.91  #BackRed      : 0
% 5.04/1.91  
% 5.04/1.91  #Partial instantiations: 0
% 5.04/1.91  #Strategies tried      : 1
% 5.04/1.91  
% 5.04/1.91  Timing (in seconds)
% 5.04/1.91  ----------------------
% 5.04/1.91  Preprocessing        : 0.41
% 5.04/1.91  Parsing              : 0.21
% 5.04/1.91  CNF conversion       : 0.05
% 5.04/1.91  Main loop            : 0.71
% 5.04/1.91  Inferencing          : 0.25
% 5.04/1.91  Reduction            : 0.23
% 5.04/1.91  Demodulation         : 0.15
% 5.04/1.91  BG Simplification    : 0.03
% 5.04/1.91  Subsumption          : 0.16
% 5.04/1.91  Abstraction          : 0.03
% 5.04/1.91  MUC search           : 0.00
% 5.04/1.91  Cooper               : 0.00
% 5.04/1.91  Total                : 1.18
% 5.04/1.91  Index Insertion      : 0.00
% 5.04/1.91  Index Deletion       : 0.00
% 5.04/1.91  Index Matching       : 0.00
% 5.04/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
