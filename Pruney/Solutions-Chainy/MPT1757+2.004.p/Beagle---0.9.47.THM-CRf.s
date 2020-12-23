%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:04 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 326 expanded)
%              Number of leaves         :   42 ( 139 expanded)
%              Depth                    :   16
%              Number of atoms          :  379 (2135 expanded)
%              Number of equality atoms :    6 ( 107 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_293,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_138,axiom,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_163,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_156,axiom,(
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

tff(f_121,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_250,axiom,(
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

tff(f_203,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_46,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_40,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_77,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_106,plain,(
    ! [B_309,A_310] :
      ( v2_pre_topc(B_309)
      | ~ m1_pre_topc(B_309,A_310)
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_109,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_106])).

tff(c_112,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_109])).

tff(c_86,plain,(
    ! [B_300,A_301] :
      ( l1_pre_topc(B_300)
      | ~ m1_pre_topc(B_300,A_301)
      | ~ l1_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_89,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_86])).

tff(c_92,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_89])).

tff(c_20,plain,(
    ! [A_25,B_26] :
      ( m1_connsp_2('#skF_1'(A_25,B_26),A_25,B_26)
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_148,plain,(
    ! [C_325,A_326,B_327] :
      ( m1_subset_1(C_325,k1_zfmisc_1(u1_struct_0(A_326)))
      | ~ m1_connsp_2(C_325,A_326,B_327)
      | ~ m1_subset_1(B_327,u1_struct_0(A_326))
      | ~ l1_pre_topc(A_326)
      | ~ v2_pre_topc(A_326)
      | v2_struct_0(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_151,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1('#skF_1'(A_25,B_26),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_20,c_148])).

tff(c_185,plain,(
    ! [C_343,B_344,A_345] :
      ( r2_hidden(C_343,B_344)
      | ~ m1_connsp_2(B_344,A_345,C_343)
      | ~ m1_subset_1(C_343,u1_struct_0(A_345))
      | ~ m1_subset_1(B_344,k1_zfmisc_1(u1_struct_0(A_345)))
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_189,plain,(
    ! [B_346,A_347] :
      ( r2_hidden(B_346,'#skF_1'(A_347,B_346))
      | ~ m1_subset_1('#skF_1'(A_347,B_346),k1_zfmisc_1(u1_struct_0(A_347)))
      | ~ m1_subset_1(B_346,u1_struct_0(A_347))
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(resolution,[status(thm)],[c_20,c_185])).

tff(c_244,plain,(
    ! [B_353,A_354] :
      ( r2_hidden(B_353,'#skF_1'(A_354,B_353))
      | ~ m1_subset_1(B_353,u1_struct_0(A_354))
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354)
      | v2_struct_0(A_354) ) ),
    inference(resolution,[status(thm)],[c_151,c_189])).

tff(c_152,plain,(
    ! [A_328,B_329] :
      ( m1_subset_1('#skF_1'(A_328,B_329),k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ m1_subset_1(B_329,u1_struct_0(A_328))
      | ~ l1_pre_topc(A_328)
      | ~ v2_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(resolution,[status(thm)],[c_20,c_148])).

tff(c_10,plain,(
    ! [C_7,B_6,A_5] :
      ( ~ v1_xboole_0(C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_155,plain,(
    ! [A_328,A_5,B_329] :
      ( ~ v1_xboole_0(u1_struct_0(A_328))
      | ~ r2_hidden(A_5,'#skF_1'(A_328,B_329))
      | ~ m1_subset_1(B_329,u1_struct_0(A_328))
      | ~ l1_pre_topc(A_328)
      | ~ v2_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(resolution,[status(thm)],[c_152,c_10])).

tff(c_262,plain,(
    ! [A_356,B_357] :
      ( ~ v1_xboole_0(u1_struct_0(A_356))
      | ~ m1_subset_1(B_357,u1_struct_0(A_356))
      | ~ l1_pre_topc(A_356)
      | ~ v2_pre_topc(A_356)
      | v2_struct_0(A_356) ) ),
    inference(resolution,[status(thm)],[c_244,c_155])).

tff(c_271,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_77,c_262])).

tff(c_279,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_92,c_271])).

tff(c_280,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_279])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    v1_tsep_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_32,plain,(
    ! [B_51,A_49] :
      ( m1_subset_1(u1_struct_0(B_51),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_pre_topc(B_51,A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_175,plain,(
    ! [B_339,A_340] :
      ( v3_pre_topc(u1_struct_0(B_339),A_340)
      | ~ v1_tsep_1(B_339,A_340)
      | ~ m1_subset_1(u1_struct_0(B_339),k1_zfmisc_1(u1_struct_0(A_340)))
      | ~ m1_pre_topc(B_339,A_340)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_179,plain,(
    ! [B_51,A_49] :
      ( v3_pre_topc(u1_struct_0(B_51),A_49)
      | ~ v1_tsep_1(B_51,A_49)
      | ~ v2_pre_topc(A_49)
      | ~ m1_pre_topc(B_51,A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(resolution,[status(thm)],[c_32,c_175])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_193,plain,(
    ! [B_348,A_349,C_350] :
      ( m1_connsp_2(B_348,A_349,C_350)
      | ~ r2_hidden(C_350,B_348)
      | ~ v3_pre_topc(B_348,A_349)
      | ~ m1_subset_1(C_350,u1_struct_0(A_349))
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349)
      | v2_struct_0(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_201,plain,(
    ! [B_348] :
      ( m1_connsp_2(B_348,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_348)
      | ~ v3_pre_topc(B_348,'#skF_3')
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_193])).

tff(c_210,plain,(
    ! [B_348] :
      ( m1_connsp_2(B_348,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_348)
      | ~ v3_pre_topc(B_348,'#skF_3')
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_201])).

tff(c_228,plain,(
    ! [B_352] :
      ( m1_connsp_2(B_352,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_352)
      | ~ v3_pre_topc(B_352,'#skF_3')
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_210])).

tff(c_236,plain,(
    ! [B_51] :
      ( m1_connsp_2(u1_struct_0(B_51),'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_51))
      | ~ v3_pre_topc(u1_struct_0(B_51),'#skF_3')
      | ~ m1_pre_topc(B_51,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_228])).

tff(c_243,plain,(
    ! [B_51] :
      ( m1_connsp_2(u1_struct_0(B_51),'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_51))
      | ~ v3_pre_topc(u1_struct_0(B_51),'#skF_3')
      | ~ m1_pre_topc(B_51,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_236])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_78,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76])).

tff(c_94,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_79,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70])).

tff(c_120,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_79])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_293])).

tff(c_402,plain,(
    ! [E_374,C_378,D_377,A_379,G_376,B_375] :
      ( r1_tmap_1(B_375,A_379,C_378,G_376)
      | ~ r1_tmap_1(D_377,A_379,k2_tmap_1(B_375,A_379,C_378,D_377),G_376)
      | ~ m1_connsp_2(E_374,B_375,G_376)
      | ~ r1_tarski(E_374,u1_struct_0(D_377))
      | ~ m1_subset_1(G_376,u1_struct_0(D_377))
      | ~ m1_subset_1(G_376,u1_struct_0(B_375))
      | ~ m1_subset_1(E_374,k1_zfmisc_1(u1_struct_0(B_375)))
      | ~ m1_pre_topc(D_377,B_375)
      | v2_struct_0(D_377)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_375),u1_struct_0(A_379))))
      | ~ v1_funct_2(C_378,u1_struct_0(B_375),u1_struct_0(A_379))
      | ~ v1_funct_1(C_378)
      | ~ l1_pre_topc(B_375)
      | ~ v2_pre_topc(B_375)
      | v2_struct_0(B_375)
      | ~ l1_pre_topc(A_379)
      | ~ v2_pre_topc(A_379)
      | v2_struct_0(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_404,plain,(
    ! [E_374] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_374,'#skF_3','#skF_6')
      | ~ r1_tarski(E_374,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_374,k1_zfmisc_1(u1_struct_0('#skF_3')))
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
    inference(resolution,[status(thm)],[c_94,c_402])).

tff(c_407,plain,(
    ! [E_374] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_374,'#skF_3','#skF_6')
      | ~ r1_tarski(E_374,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_374,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_56,c_54,c_52,c_46,c_44,c_77,c_404])).

tff(c_409,plain,(
    ! [E_380] :
      ( ~ m1_connsp_2(E_380,'#skF_3','#skF_6')
      | ~ r1_tarski(E_380,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_380,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_50,c_120,c_407])).

tff(c_423,plain,(
    ! [B_51] :
      ( ~ m1_connsp_2(u1_struct_0(B_51),'#skF_3','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_51),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_51,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_409])).

tff(c_433,plain,(
    ! [B_381] :
      ( ~ m1_connsp_2(u1_struct_0(B_381),'#skF_3','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_381),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_381,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_423])).

tff(c_437,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_433])).

tff(c_440,plain,(
    ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_437])).

tff(c_443,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_243,c_440])).

tff(c_446,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_443])).

tff(c_448,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_446])).

tff(c_451,plain,
    ( ~ v1_tsep_1('#skF_5','#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_179,c_448])).

tff(c_455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46,c_60,c_48,c_451])).

tff(c_456,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_446])).

tff(c_466,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_8,c_456])).

tff(c_469,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_466])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_469])).

tff(c_472,plain,(
    r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_653,plain,(
    ! [D_436,A_433,F_435,C_434,B_437] :
      ( r1_tmap_1(D_436,A_433,k2_tmap_1(B_437,A_433,C_434,D_436),F_435)
      | ~ r1_tmap_1(B_437,A_433,C_434,F_435)
      | ~ m1_subset_1(F_435,u1_struct_0(D_436))
      | ~ m1_subset_1(F_435,u1_struct_0(B_437))
      | ~ m1_pre_topc(D_436,B_437)
      | v2_struct_0(D_436)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_437),u1_struct_0(A_433))))
      | ~ v1_funct_2(C_434,u1_struct_0(B_437),u1_struct_0(A_433))
      | ~ v1_funct_1(C_434)
      | ~ l1_pre_topc(B_437)
      | ~ v2_pre_topc(B_437)
      | v2_struct_0(B_437)
      | ~ l1_pre_topc(A_433)
      | ~ v2_pre_topc(A_433)
      | v2_struct_0(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_655,plain,(
    ! [D_436,F_435] :
      ( r1_tmap_1(D_436,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_436),F_435)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_435)
      | ~ m1_subset_1(F_435,u1_struct_0(D_436))
      | ~ m1_subset_1(F_435,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_436,'#skF_3')
      | v2_struct_0(D_436)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_653])).

tff(c_658,plain,(
    ! [D_436,F_435] :
      ( r1_tmap_1(D_436,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_436),F_435)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_435)
      | ~ m1_subset_1(F_435,u1_struct_0(D_436))
      | ~ m1_subset_1(F_435,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_436,'#skF_3')
      | v2_struct_0(D_436)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_56,c_54,c_655])).

tff(c_798,plain,(
    ! [D_461,F_462] :
      ( r1_tmap_1(D_461,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_461),F_462)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_462)
      | ~ m1_subset_1(F_462,u1_struct_0(D_461))
      | ~ m1_subset_1(F_462,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_461,'#skF_3')
      | v2_struct_0(D_461) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_658])).

tff(c_473,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_803,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_798,c_473])).

tff(c_810,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_77,c_472,c_803])).

tff(c_812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_810])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.62  
% 3.46/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.63  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.46/1.63  
% 3.46/1.63  %Foreground sorts:
% 3.46/1.63  
% 3.46/1.63  
% 3.46/1.63  %Background operators:
% 3.46/1.63  
% 3.46/1.63  
% 3.46/1.63  %Foreground operators:
% 3.46/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.46/1.63  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.46/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.46/1.63  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.46/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.63  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.46/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.46/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.46/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.46/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.46/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.46/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.46/1.63  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.46/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.46/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.46/1.63  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.46/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.46/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.46/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.46/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.63  
% 3.79/1.65  tff(f_293, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.79/1.65  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.79/1.65  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.79/1.65  tff(f_102, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.79/1.65  tff(f_90, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.79/1.65  tff(f_138, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 3.79/1.65  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.79/1.65  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.79/1.65  tff(f_163, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.79/1.65  tff(f_156, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.79/1.65  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 3.79/1.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.79/1.65  tff(f_250, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.79/1.65  tff(f_203, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.79/1.65  tff(c_50, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_46, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_40, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_42, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_77, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 3.79/1.65  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_106, plain, (![B_309, A_310]: (v2_pre_topc(B_309) | ~m1_pre_topc(B_309, A_310) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.79/1.65  tff(c_109, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_106])).
% 3.79/1.65  tff(c_112, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_109])).
% 3.79/1.65  tff(c_86, plain, (![B_300, A_301]: (l1_pre_topc(B_300) | ~m1_pre_topc(B_300, A_301) | ~l1_pre_topc(A_301))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.79/1.65  tff(c_89, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_86])).
% 3.79/1.65  tff(c_92, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_89])).
% 3.79/1.65  tff(c_20, plain, (![A_25, B_26]: (m1_connsp_2('#skF_1'(A_25, B_26), A_25, B_26) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.79/1.65  tff(c_148, plain, (![C_325, A_326, B_327]: (m1_subset_1(C_325, k1_zfmisc_1(u1_struct_0(A_326))) | ~m1_connsp_2(C_325, A_326, B_327) | ~m1_subset_1(B_327, u1_struct_0(A_326)) | ~l1_pre_topc(A_326) | ~v2_pre_topc(A_326) | v2_struct_0(A_326))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.79/1.65  tff(c_151, plain, (![A_25, B_26]: (m1_subset_1('#skF_1'(A_25, B_26), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_20, c_148])).
% 3.79/1.65  tff(c_185, plain, (![C_343, B_344, A_345]: (r2_hidden(C_343, B_344) | ~m1_connsp_2(B_344, A_345, C_343) | ~m1_subset_1(C_343, u1_struct_0(A_345)) | ~m1_subset_1(B_344, k1_zfmisc_1(u1_struct_0(A_345))) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.79/1.65  tff(c_189, plain, (![B_346, A_347]: (r2_hidden(B_346, '#skF_1'(A_347, B_346)) | ~m1_subset_1('#skF_1'(A_347, B_346), k1_zfmisc_1(u1_struct_0(A_347))) | ~m1_subset_1(B_346, u1_struct_0(A_347)) | ~l1_pre_topc(A_347) | ~v2_pre_topc(A_347) | v2_struct_0(A_347))), inference(resolution, [status(thm)], [c_20, c_185])).
% 3.79/1.65  tff(c_244, plain, (![B_353, A_354]: (r2_hidden(B_353, '#skF_1'(A_354, B_353)) | ~m1_subset_1(B_353, u1_struct_0(A_354)) | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354) | v2_struct_0(A_354))), inference(resolution, [status(thm)], [c_151, c_189])).
% 3.79/1.65  tff(c_152, plain, (![A_328, B_329]: (m1_subset_1('#skF_1'(A_328, B_329), k1_zfmisc_1(u1_struct_0(A_328))) | ~m1_subset_1(B_329, u1_struct_0(A_328)) | ~l1_pre_topc(A_328) | ~v2_pre_topc(A_328) | v2_struct_0(A_328))), inference(resolution, [status(thm)], [c_20, c_148])).
% 3.79/1.65  tff(c_10, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.79/1.65  tff(c_155, plain, (![A_328, A_5, B_329]: (~v1_xboole_0(u1_struct_0(A_328)) | ~r2_hidden(A_5, '#skF_1'(A_328, B_329)) | ~m1_subset_1(B_329, u1_struct_0(A_328)) | ~l1_pre_topc(A_328) | ~v2_pre_topc(A_328) | v2_struct_0(A_328))), inference(resolution, [status(thm)], [c_152, c_10])).
% 3.79/1.65  tff(c_262, plain, (![A_356, B_357]: (~v1_xboole_0(u1_struct_0(A_356)) | ~m1_subset_1(B_357, u1_struct_0(A_356)) | ~l1_pre_topc(A_356) | ~v2_pre_topc(A_356) | v2_struct_0(A_356))), inference(resolution, [status(thm)], [c_244, c_155])).
% 3.79/1.65  tff(c_271, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_77, c_262])).
% 3.79/1.65  tff(c_279, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_92, c_271])).
% 3.79/1.65  tff(c_280, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_50, c_279])).
% 3.79/1.65  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.79/1.65  tff(c_48, plain, (v1_tsep_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_32, plain, (![B_51, A_49]: (m1_subset_1(u1_struct_0(B_51), k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_pre_topc(B_51, A_49) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.79/1.65  tff(c_175, plain, (![B_339, A_340]: (v3_pre_topc(u1_struct_0(B_339), A_340) | ~v1_tsep_1(B_339, A_340) | ~m1_subset_1(u1_struct_0(B_339), k1_zfmisc_1(u1_struct_0(A_340))) | ~m1_pre_topc(B_339, A_340) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.79/1.65  tff(c_179, plain, (![B_51, A_49]: (v3_pre_topc(u1_struct_0(B_51), A_49) | ~v1_tsep_1(B_51, A_49) | ~v2_pre_topc(A_49) | ~m1_pre_topc(B_51, A_49) | ~l1_pre_topc(A_49))), inference(resolution, [status(thm)], [c_32, c_175])).
% 3.79/1.65  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_193, plain, (![B_348, A_349, C_350]: (m1_connsp_2(B_348, A_349, C_350) | ~r2_hidden(C_350, B_348) | ~v3_pre_topc(B_348, A_349) | ~m1_subset_1(C_350, u1_struct_0(A_349)) | ~m1_subset_1(B_348, k1_zfmisc_1(u1_struct_0(A_349))) | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349) | v2_struct_0(A_349))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.79/1.65  tff(c_201, plain, (![B_348]: (m1_connsp_2(B_348, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_348) | ~v3_pre_topc(B_348, '#skF_3') | ~m1_subset_1(B_348, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_193])).
% 3.79/1.65  tff(c_210, plain, (![B_348]: (m1_connsp_2(B_348, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_348) | ~v3_pre_topc(B_348, '#skF_3') | ~m1_subset_1(B_348, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_201])).
% 3.79/1.65  tff(c_228, plain, (![B_352]: (m1_connsp_2(B_352, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_352) | ~v3_pre_topc(B_352, '#skF_3') | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_210])).
% 3.79/1.65  tff(c_236, plain, (![B_51]: (m1_connsp_2(u1_struct_0(B_51), '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_51)) | ~v3_pre_topc(u1_struct_0(B_51), '#skF_3') | ~m1_pre_topc(B_51, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_228])).
% 3.79/1.65  tff(c_243, plain, (![B_51]: (m1_connsp_2(u1_struct_0(B_51), '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_51)) | ~v3_pre_topc(u1_struct_0(B_51), '#skF_3') | ~m1_pre_topc(B_51, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_236])).
% 3.79/1.65  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/1.65  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_76, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_78, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76])).
% 3.79/1.65  tff(c_94, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_78])).
% 3.79/1.65  tff(c_70, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_79, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70])).
% 3.79/1.65  tff(c_120, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_79])).
% 3.79/1.65  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_54, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_293])).
% 3.79/1.65  tff(c_402, plain, (![E_374, C_378, D_377, A_379, G_376, B_375]: (r1_tmap_1(B_375, A_379, C_378, G_376) | ~r1_tmap_1(D_377, A_379, k2_tmap_1(B_375, A_379, C_378, D_377), G_376) | ~m1_connsp_2(E_374, B_375, G_376) | ~r1_tarski(E_374, u1_struct_0(D_377)) | ~m1_subset_1(G_376, u1_struct_0(D_377)) | ~m1_subset_1(G_376, u1_struct_0(B_375)) | ~m1_subset_1(E_374, k1_zfmisc_1(u1_struct_0(B_375))) | ~m1_pre_topc(D_377, B_375) | v2_struct_0(D_377) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_375), u1_struct_0(A_379)))) | ~v1_funct_2(C_378, u1_struct_0(B_375), u1_struct_0(A_379)) | ~v1_funct_1(C_378) | ~l1_pre_topc(B_375) | ~v2_pre_topc(B_375) | v2_struct_0(B_375) | ~l1_pre_topc(A_379) | ~v2_pre_topc(A_379) | v2_struct_0(A_379))), inference(cnfTransformation, [status(thm)], [f_250])).
% 3.79/1.65  tff(c_404, plain, (![E_374]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_374, '#skF_3', '#skF_6') | ~r1_tarski(E_374, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1(E_374, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_94, c_402])).
% 3.79/1.65  tff(c_407, plain, (![E_374]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_374, '#skF_3', '#skF_6') | ~r1_tarski(E_374, u1_struct_0('#skF_5')) | ~m1_subset_1(E_374, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_56, c_54, c_52, c_46, c_44, c_77, c_404])).
% 3.79/1.65  tff(c_409, plain, (![E_380]: (~m1_connsp_2(E_380, '#skF_3', '#skF_6') | ~r1_tarski(E_380, u1_struct_0('#skF_5')) | ~m1_subset_1(E_380, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_50, c_120, c_407])).
% 3.79/1.65  tff(c_423, plain, (![B_51]: (~m1_connsp_2(u1_struct_0(B_51), '#skF_3', '#skF_6') | ~r1_tarski(u1_struct_0(B_51), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_51, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_409])).
% 3.79/1.65  tff(c_433, plain, (![B_381]: (~m1_connsp_2(u1_struct_0(B_381), '#skF_3', '#skF_6') | ~r1_tarski(u1_struct_0(B_381), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_381, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_423])).
% 3.79/1.65  tff(c_437, plain, (~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_433])).
% 3.79/1.65  tff(c_440, plain, (~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_437])).
% 3.79/1.65  tff(c_443, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_243, c_440])).
% 3.79/1.65  tff(c_446, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_443])).
% 3.79/1.65  tff(c_448, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_446])).
% 3.79/1.65  tff(c_451, plain, (~v1_tsep_1('#skF_5', '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_179, c_448])).
% 3.79/1.65  tff(c_455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_46, c_60, c_48, c_451])).
% 3.79/1.65  tff(c_456, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_446])).
% 3.79/1.65  tff(c_466, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_8, c_456])).
% 3.79/1.65  tff(c_469, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_466])).
% 3.79/1.65  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_280, c_469])).
% 3.79/1.65  tff(c_472, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_78])).
% 3.79/1.65  tff(c_653, plain, (![D_436, A_433, F_435, C_434, B_437]: (r1_tmap_1(D_436, A_433, k2_tmap_1(B_437, A_433, C_434, D_436), F_435) | ~r1_tmap_1(B_437, A_433, C_434, F_435) | ~m1_subset_1(F_435, u1_struct_0(D_436)) | ~m1_subset_1(F_435, u1_struct_0(B_437)) | ~m1_pre_topc(D_436, B_437) | v2_struct_0(D_436) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_437), u1_struct_0(A_433)))) | ~v1_funct_2(C_434, u1_struct_0(B_437), u1_struct_0(A_433)) | ~v1_funct_1(C_434) | ~l1_pre_topc(B_437) | ~v2_pre_topc(B_437) | v2_struct_0(B_437) | ~l1_pre_topc(A_433) | ~v2_pre_topc(A_433) | v2_struct_0(A_433))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.79/1.65  tff(c_655, plain, (![D_436, F_435]: (r1_tmap_1(D_436, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_436), F_435) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_435) | ~m1_subset_1(F_435, u1_struct_0(D_436)) | ~m1_subset_1(F_435, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_436, '#skF_3') | v2_struct_0(D_436) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_653])).
% 3.79/1.65  tff(c_658, plain, (![D_436, F_435]: (r1_tmap_1(D_436, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_436), F_435) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_435) | ~m1_subset_1(F_435, u1_struct_0(D_436)) | ~m1_subset_1(F_435, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_436, '#skF_3') | v2_struct_0(D_436) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_56, c_54, c_655])).
% 3.79/1.65  tff(c_798, plain, (![D_461, F_462]: (r1_tmap_1(D_461, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_461), F_462) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_462) | ~m1_subset_1(F_462, u1_struct_0(D_461)) | ~m1_subset_1(F_462, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_461, '#skF_3') | v2_struct_0(D_461))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_658])).
% 3.79/1.65  tff(c_473, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_78])).
% 3.79/1.65  tff(c_803, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_798, c_473])).
% 3.79/1.65  tff(c_810, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_77, c_472, c_803])).
% 3.79/1.65  tff(c_812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_810])).
% 3.79/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.65  
% 3.79/1.65  Inference rules
% 3.79/1.65  ----------------------
% 3.79/1.65  #Ref     : 0
% 3.79/1.65  #Sup     : 125
% 3.79/1.65  #Fact    : 0
% 3.79/1.65  #Define  : 0
% 3.79/1.65  #Split   : 6
% 3.79/1.65  #Chain   : 0
% 3.79/1.65  #Close   : 0
% 3.79/1.65  
% 3.79/1.65  Ordering : KBO
% 3.79/1.65  
% 3.79/1.65  Simplification rules
% 3.79/1.65  ----------------------
% 3.79/1.65  #Subsume      : 36
% 3.79/1.65  #Demod        : 172
% 3.79/1.65  #Tautology    : 24
% 3.79/1.65  #SimpNegUnit  : 53
% 3.79/1.65  #BackRed      : 0
% 3.79/1.65  
% 3.79/1.65  #Partial instantiations: 0
% 3.79/1.65  #Strategies tried      : 1
% 3.79/1.65  
% 3.79/1.65  Timing (in seconds)
% 3.79/1.65  ----------------------
% 3.79/1.65  Preprocessing        : 0.41
% 3.79/1.65  Parsing              : 0.22
% 3.79/1.65  CNF conversion       : 0.05
% 3.79/1.65  Main loop            : 0.39
% 3.79/1.65  Inferencing          : 0.15
% 3.79/1.65  Reduction            : 0.12
% 3.79/1.65  Demodulation         : 0.08
% 3.79/1.65  BG Simplification    : 0.02
% 3.79/1.65  Subsumption          : 0.07
% 3.79/1.65  Abstraction          : 0.02
% 3.79/1.65  MUC search           : 0.00
% 3.79/1.65  Cooper               : 0.00
% 3.79/1.65  Total                : 0.85
% 3.79/1.65  Index Insertion      : 0.00
% 3.79/1.65  Index Deletion       : 0.00
% 3.79/1.65  Index Matching       : 0.00
% 3.79/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
