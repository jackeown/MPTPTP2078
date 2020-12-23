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
% DateTime   : Thu Dec  3 10:27:04 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 345 expanded)
%              Number of leaves         :   43 ( 146 expanded)
%              Depth                    :   17
%              Number of atoms          :  368 (2207 expanded)
%              Number of equality atoms :    6 ( 111 expanded)
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

tff(f_299,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_169,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_125,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_162,axiom,(
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

tff(f_144,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_256,axiom,(
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

tff(f_209,axiom,(
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
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_52,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_46,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_83,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_117,plain,(
    ! [B_311,A_312] :
      ( v2_pre_topc(B_311)
      | ~ m1_pre_topc(B_311,A_312)
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_120,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_117])).

tff(c_123,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_120])).

tff(c_98,plain,(
    ! [B_305,A_306] :
      ( l1_pre_topc(B_305)
      | ~ m1_pre_topc(B_305,A_306)
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_101,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_98])).

tff(c_104,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_101])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135,plain,(
    ! [B_320,A_321] :
      ( m1_subset_1(u1_struct_0(B_320),k1_zfmisc_1(u1_struct_0(A_321)))
      | ~ m1_pre_topc(B_320,A_321)
      | ~ l1_pre_topc(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_143,plain,(
    ! [A_325,A_326,B_327] :
      ( m1_subset_1(A_325,u1_struct_0(A_326))
      | ~ r2_hidden(A_325,u1_struct_0(B_327))
      | ~ m1_pre_topc(B_327,A_326)
      | ~ l1_pre_topc(A_326) ) ),
    inference(resolution,[status(thm)],[c_135,c_14])).

tff(c_217,plain,(
    ! [A_343,A_344,B_345] :
      ( m1_subset_1(A_343,u1_struct_0(A_344))
      | ~ m1_pre_topc(B_345,A_344)
      | ~ l1_pre_topc(A_344)
      | v1_xboole_0(u1_struct_0(B_345))
      | ~ m1_subset_1(A_343,u1_struct_0(B_345)) ) ),
    inference(resolution,[status(thm)],[c_12,c_143])).

tff(c_219,plain,(
    ! [A_343] :
      ( m1_subset_1(A_343,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_343,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_52,c_217])).

tff(c_222,plain,(
    ! [A_343] :
      ( m1_subset_1(A_343,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_343,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_219])).

tff(c_223,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_28,plain,(
    ! [B_36,A_34] :
      ( r2_hidden(B_36,k1_connsp_2(A_34,B_36))
      | ~ m1_subset_1(B_36,u1_struct_0(A_34))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_210,plain,(
    ! [A_341,B_342] :
      ( m1_subset_1(k1_connsp_2(A_341,B_342),k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ m1_subset_1(B_342,u1_struct_0(A_341))
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | v2_struct_0(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_16,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_267,plain,(
    ! [A_359,A_360,B_361] :
      ( ~ v1_xboole_0(u1_struct_0(A_359))
      | ~ r2_hidden(A_360,k1_connsp_2(A_359,B_361))
      | ~ m1_subset_1(B_361,u1_struct_0(A_359))
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(resolution,[status(thm)],[c_210,c_16])).

tff(c_282,plain,(
    ! [A_362,B_363] :
      ( ~ v1_xboole_0(u1_struct_0(A_362))
      | ~ m1_subset_1(B_363,u1_struct_0(A_362))
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(resolution,[status(thm)],[c_28,c_267])).

tff(c_294,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_83,c_282])).

tff(c_303,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_104,c_223,c_294])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_303])).

tff(c_307,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_54,plain,(
    v1_tsep_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_38,plain,(
    ! [B_53,A_51] :
      ( m1_subset_1(u1_struct_0(B_53),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_438,plain,(
    ! [B_385,A_386] :
      ( v3_pre_topc(u1_struct_0(B_385),A_386)
      | ~ v1_tsep_1(B_385,A_386)
      | ~ m1_subset_1(u1_struct_0(B_385),k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ m1_pre_topc(B_385,A_386)
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_442,plain,(
    ! [B_53,A_51] :
      ( v3_pre_topc(u1_struct_0(B_53),A_51)
      | ~ v1_tsep_1(B_53,A_51)
      | ~ v2_pre_topc(A_51)
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_38,c_438])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_511,plain,(
    ! [B_403,A_404,C_405] :
      ( m1_connsp_2(B_403,A_404,C_405)
      | ~ r2_hidden(C_405,B_403)
      | ~ v3_pre_topc(B_403,A_404)
      | ~ m1_subset_1(C_405,u1_struct_0(A_404))
      | ~ m1_subset_1(B_403,k1_zfmisc_1(u1_struct_0(A_404)))
      | ~ l1_pre_topc(A_404)
      | ~ v2_pre_topc(A_404)
      | v2_struct_0(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_529,plain,(
    ! [B_403] :
      ( m1_connsp_2(B_403,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_403)
      | ~ v3_pre_topc(B_403,'#skF_3')
      | ~ m1_subset_1(B_403,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_511])).

tff(c_549,plain,(
    ! [B_403] :
      ( m1_connsp_2(B_403,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_403)
      | ~ v3_pre_topc(B_403,'#skF_3')
      | ~ m1_subset_1(B_403,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_529])).

tff(c_567,plain,(
    ! [B_407] :
      ( m1_connsp_2(B_407,'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',B_407)
      | ~ v3_pre_topc(B_407,'#skF_3')
      | ~ m1_subset_1(B_407,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_549])).

tff(c_575,plain,(
    ! [B_53] :
      ( m1_connsp_2(u1_struct_0(B_53),'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_53))
      | ~ v3_pre_topc(u1_struct_0(B_53),'#skF_3')
      | ~ m1_pre_topc(B_53,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_567])).

tff(c_582,plain,(
    ! [B_53] :
      ( m1_connsp_2(u1_struct_0(B_53),'#skF_3','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_53))
      | ~ v3_pre_topc(u1_struct_0(B_53),'#skF_3')
      | ~ m1_pre_topc(B_53,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_575])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_85,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_76])).

tff(c_134,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_60,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_84,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_82])).

tff(c_152,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_84])).

tff(c_740,plain,(
    ! [E_433,C_437,D_434,A_436,G_435,B_432] :
      ( r1_tmap_1(B_432,A_436,C_437,G_435)
      | ~ r1_tmap_1(D_434,A_436,k2_tmap_1(B_432,A_436,C_437,D_434),G_435)
      | ~ m1_connsp_2(E_433,B_432,G_435)
      | ~ r1_tarski(E_433,u1_struct_0(D_434))
      | ~ m1_subset_1(G_435,u1_struct_0(D_434))
      | ~ m1_subset_1(G_435,u1_struct_0(B_432))
      | ~ m1_subset_1(E_433,k1_zfmisc_1(u1_struct_0(B_432)))
      | ~ m1_pre_topc(D_434,B_432)
      | v2_struct_0(D_434)
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_432),u1_struct_0(A_436))))
      | ~ v1_funct_2(C_437,u1_struct_0(B_432),u1_struct_0(A_436))
      | ~ v1_funct_1(C_437)
      | ~ l1_pre_topc(B_432)
      | ~ v2_pre_topc(B_432)
      | v2_struct_0(B_432)
      | ~ l1_pre_topc(A_436)
      | ~ v2_pre_topc(A_436)
      | v2_struct_0(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_742,plain,(
    ! [E_433] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_433,'#skF_3','#skF_6')
      | ~ r1_tarski(E_433,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_433,k1_zfmisc_1(u1_struct_0('#skF_3')))
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
    inference(resolution,[status(thm)],[c_152,c_740])).

tff(c_745,plain,(
    ! [E_433] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_433,'#skF_3','#skF_6')
      | ~ r1_tarski(E_433,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_433,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_60,c_58,c_52,c_50,c_83,c_742])).

tff(c_747,plain,(
    ! [E_438] :
      ( ~ m1_connsp_2(E_438,'#skF_3','#skF_6')
      | ~ r1_tarski(E_438,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_438,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_56,c_134,c_745])).

tff(c_761,plain,(
    ! [B_53] :
      ( ~ m1_connsp_2(u1_struct_0(B_53),'#skF_3','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_53),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_53,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_747])).

tff(c_771,plain,(
    ! [B_439] :
      ( ~ m1_connsp_2(u1_struct_0(B_439),'#skF_3','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_439),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_439,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_761])).

tff(c_775,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_771])).

tff(c_778,plain,(
    ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_775])).

tff(c_781,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_582,c_778])).

tff(c_784,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_781])).

tff(c_786,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_784])).

tff(c_789,plain,
    ( ~ v1_tsep_1('#skF_5','#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_442,c_786])).

tff(c_793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_52,c_66,c_54,c_789])).

tff(c_794,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_784])).

tff(c_804,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_12,c_794])).

tff(c_807,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_804])).

tff(c_809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_807])).

tff(c_811,plain,(
    r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_1382,plain,(
    ! [B_544,D_547,A_546,F_548,C_545] :
      ( r1_tmap_1(D_547,A_546,k2_tmap_1(B_544,A_546,C_545,D_547),F_548)
      | ~ r1_tmap_1(B_544,A_546,C_545,F_548)
      | ~ m1_subset_1(F_548,u1_struct_0(D_547))
      | ~ m1_subset_1(F_548,u1_struct_0(B_544))
      | ~ m1_pre_topc(D_547,B_544)
      | v2_struct_0(D_547)
      | ~ m1_subset_1(C_545,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_544),u1_struct_0(A_546))))
      | ~ v1_funct_2(C_545,u1_struct_0(B_544),u1_struct_0(A_546))
      | ~ v1_funct_1(C_545)
      | ~ l1_pre_topc(B_544)
      | ~ v2_pre_topc(B_544)
      | v2_struct_0(B_544)
      | ~ l1_pre_topc(A_546)
      | ~ v2_pre_topc(A_546)
      | v2_struct_0(A_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_1384,plain,(
    ! [D_547,F_548] :
      ( r1_tmap_1(D_547,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_547),F_548)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_548)
      | ~ m1_subset_1(F_548,u1_struct_0(D_547))
      | ~ m1_subset_1(F_548,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_547,'#skF_3')
      | v2_struct_0(D_547)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_1382])).

tff(c_1387,plain,(
    ! [D_547,F_548] :
      ( r1_tmap_1(D_547,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_547),F_548)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_548)
      | ~ m1_subset_1(F_548,u1_struct_0(D_547))
      | ~ m1_subset_1(F_548,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_547,'#skF_3')
      | v2_struct_0(D_547)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_60,c_1384])).

tff(c_1646,plain,(
    ! [D_583,F_584] :
      ( r1_tmap_1(D_583,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_583),F_584)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_584)
      | ~ m1_subset_1(F_584,u1_struct_0(D_583))
      | ~ m1_subset_1(F_584,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_583,'#skF_3')
      | v2_struct_0(D_583) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_1387])).

tff(c_810,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_1651,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1646,c_810])).

tff(c_1658,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_83,c_811,c_1651])).

tff(c_1660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1658])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 18:36:00 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.80  
% 4.60/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.81  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 4.60/1.81  
% 4.60/1.81  %Foreground sorts:
% 4.60/1.81  
% 4.60/1.81  
% 4.60/1.81  %Background operators:
% 4.60/1.81  
% 4.60/1.81  
% 4.60/1.81  %Foreground operators:
% 4.60/1.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.60/1.81  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.60/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.60/1.81  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.60/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.60/1.81  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 4.60/1.81  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.60/1.81  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.60/1.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.60/1.81  tff('#skF_7', type, '#skF_7': $i).
% 4.60/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.60/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.60/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.60/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.60/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.60/1.81  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.60/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.81  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.60/1.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.60/1.81  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.60/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.60/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.60/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/1.81  
% 4.88/1.83  tff(f_299, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 4.88/1.83  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.88/1.83  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.88/1.83  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.88/1.83  tff(f_169, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.88/1.83  tff(f_49, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.88/1.83  tff(f_125, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 4.88/1.83  tff(f_99, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 4.88/1.83  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.88/1.83  tff(f_162, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.88/1.83  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 4.88/1.83  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.88/1.83  tff(f_256, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 4.88/1.83  tff(f_209, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 4.88/1.83  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_52, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_46, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_83, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 4.88/1.83  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_117, plain, (![B_311, A_312]: (v2_pre_topc(B_311) | ~m1_pre_topc(B_311, A_312) | ~l1_pre_topc(A_312) | ~v2_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.88/1.83  tff(c_120, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_117])).
% 4.88/1.83  tff(c_123, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_120])).
% 4.88/1.83  tff(c_98, plain, (![B_305, A_306]: (l1_pre_topc(B_305) | ~m1_pre_topc(B_305, A_306) | ~l1_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.88/1.83  tff(c_101, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_98])).
% 4.88/1.83  tff(c_104, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_101])).
% 4.88/1.83  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.88/1.83  tff(c_135, plain, (![B_320, A_321]: (m1_subset_1(u1_struct_0(B_320), k1_zfmisc_1(u1_struct_0(A_321))) | ~m1_pre_topc(B_320, A_321) | ~l1_pre_topc(A_321))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.88/1.83  tff(c_14, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.88/1.83  tff(c_143, plain, (![A_325, A_326, B_327]: (m1_subset_1(A_325, u1_struct_0(A_326)) | ~r2_hidden(A_325, u1_struct_0(B_327)) | ~m1_pre_topc(B_327, A_326) | ~l1_pre_topc(A_326))), inference(resolution, [status(thm)], [c_135, c_14])).
% 4.88/1.83  tff(c_217, plain, (![A_343, A_344, B_345]: (m1_subset_1(A_343, u1_struct_0(A_344)) | ~m1_pre_topc(B_345, A_344) | ~l1_pre_topc(A_344) | v1_xboole_0(u1_struct_0(B_345)) | ~m1_subset_1(A_343, u1_struct_0(B_345)))), inference(resolution, [status(thm)], [c_12, c_143])).
% 4.88/1.83  tff(c_219, plain, (![A_343]: (m1_subset_1(A_343, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_343, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_52, c_217])).
% 4.88/1.83  tff(c_222, plain, (![A_343]: (m1_subset_1(A_343, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_343, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_219])).
% 4.88/1.83  tff(c_223, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_222])).
% 4.88/1.83  tff(c_28, plain, (![B_36, A_34]: (r2_hidden(B_36, k1_connsp_2(A_34, B_36)) | ~m1_subset_1(B_36, u1_struct_0(A_34)) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.88/1.83  tff(c_210, plain, (![A_341, B_342]: (m1_subset_1(k1_connsp_2(A_341, B_342), k1_zfmisc_1(u1_struct_0(A_341))) | ~m1_subset_1(B_342, u1_struct_0(A_341)) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341) | v2_struct_0(A_341))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.88/1.83  tff(c_16, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.88/1.83  tff(c_267, plain, (![A_359, A_360, B_361]: (~v1_xboole_0(u1_struct_0(A_359)) | ~r2_hidden(A_360, k1_connsp_2(A_359, B_361)) | ~m1_subset_1(B_361, u1_struct_0(A_359)) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(resolution, [status(thm)], [c_210, c_16])).
% 4.88/1.83  tff(c_282, plain, (![A_362, B_363]: (~v1_xboole_0(u1_struct_0(A_362)) | ~m1_subset_1(B_363, u1_struct_0(A_362)) | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362) | v2_struct_0(A_362))), inference(resolution, [status(thm)], [c_28, c_267])).
% 4.88/1.83  tff(c_294, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_83, c_282])).
% 4.88/1.83  tff(c_303, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_104, c_223, c_294])).
% 4.88/1.83  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_303])).
% 4.88/1.83  tff(c_307, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_222])).
% 4.88/1.83  tff(c_54, plain, (v1_tsep_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_38, plain, (![B_53, A_51]: (m1_subset_1(u1_struct_0(B_53), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.88/1.83  tff(c_438, plain, (![B_385, A_386]: (v3_pre_topc(u1_struct_0(B_385), A_386) | ~v1_tsep_1(B_385, A_386) | ~m1_subset_1(u1_struct_0(B_385), k1_zfmisc_1(u1_struct_0(A_386))) | ~m1_pre_topc(B_385, A_386) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.88/1.83  tff(c_442, plain, (![B_53, A_51]: (v3_pre_topc(u1_struct_0(B_53), A_51) | ~v1_tsep_1(B_53, A_51) | ~v2_pre_topc(A_51) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_38, c_438])).
% 4.88/1.83  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_511, plain, (![B_403, A_404, C_405]: (m1_connsp_2(B_403, A_404, C_405) | ~r2_hidden(C_405, B_403) | ~v3_pre_topc(B_403, A_404) | ~m1_subset_1(C_405, u1_struct_0(A_404)) | ~m1_subset_1(B_403, k1_zfmisc_1(u1_struct_0(A_404))) | ~l1_pre_topc(A_404) | ~v2_pre_topc(A_404) | v2_struct_0(A_404))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.88/1.83  tff(c_529, plain, (![B_403]: (m1_connsp_2(B_403, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_403) | ~v3_pre_topc(B_403, '#skF_3') | ~m1_subset_1(B_403, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_511])).
% 4.88/1.83  tff(c_549, plain, (![B_403]: (m1_connsp_2(B_403, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_403) | ~v3_pre_topc(B_403, '#skF_3') | ~m1_subset_1(B_403, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_529])).
% 4.88/1.83  tff(c_567, plain, (![B_407]: (m1_connsp_2(B_407, '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', B_407) | ~v3_pre_topc(B_407, '#skF_3') | ~m1_subset_1(B_407, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_549])).
% 4.88/1.83  tff(c_575, plain, (![B_53]: (m1_connsp_2(u1_struct_0(B_53), '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_53)) | ~v3_pre_topc(u1_struct_0(B_53), '#skF_3') | ~m1_pre_topc(B_53, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_567])).
% 4.88/1.83  tff(c_582, plain, (![B_53]: (m1_connsp_2(u1_struct_0(B_53), '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_53)) | ~v3_pre_topc(u1_struct_0(B_53), '#skF_3') | ~m1_pre_topc(B_53, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_575])).
% 4.88/1.83  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.88/1.83  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_76, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_85, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_76])).
% 4.88/1.83  tff(c_134, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_85])).
% 4.88/1.83  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_60, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_82, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_299])).
% 4.88/1.83  tff(c_84, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_82])).
% 4.88/1.83  tff(c_152, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_134, c_84])).
% 4.88/1.83  tff(c_740, plain, (![E_433, C_437, D_434, A_436, G_435, B_432]: (r1_tmap_1(B_432, A_436, C_437, G_435) | ~r1_tmap_1(D_434, A_436, k2_tmap_1(B_432, A_436, C_437, D_434), G_435) | ~m1_connsp_2(E_433, B_432, G_435) | ~r1_tarski(E_433, u1_struct_0(D_434)) | ~m1_subset_1(G_435, u1_struct_0(D_434)) | ~m1_subset_1(G_435, u1_struct_0(B_432)) | ~m1_subset_1(E_433, k1_zfmisc_1(u1_struct_0(B_432))) | ~m1_pre_topc(D_434, B_432) | v2_struct_0(D_434) | ~m1_subset_1(C_437, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_432), u1_struct_0(A_436)))) | ~v1_funct_2(C_437, u1_struct_0(B_432), u1_struct_0(A_436)) | ~v1_funct_1(C_437) | ~l1_pre_topc(B_432) | ~v2_pre_topc(B_432) | v2_struct_0(B_432) | ~l1_pre_topc(A_436) | ~v2_pre_topc(A_436) | v2_struct_0(A_436))), inference(cnfTransformation, [status(thm)], [f_256])).
% 4.88/1.83  tff(c_742, plain, (![E_433]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_433, '#skF_3', '#skF_6') | ~r1_tarski(E_433, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1(E_433, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_152, c_740])).
% 4.88/1.83  tff(c_745, plain, (![E_433]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_433, '#skF_3', '#skF_6') | ~r1_tarski(E_433, u1_struct_0('#skF_5')) | ~m1_subset_1(E_433, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_60, c_58, c_52, c_50, c_83, c_742])).
% 4.88/1.83  tff(c_747, plain, (![E_438]: (~m1_connsp_2(E_438, '#skF_3', '#skF_6') | ~r1_tarski(E_438, u1_struct_0('#skF_5')) | ~m1_subset_1(E_438, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_56, c_134, c_745])).
% 4.88/1.83  tff(c_761, plain, (![B_53]: (~m1_connsp_2(u1_struct_0(B_53), '#skF_3', '#skF_6') | ~r1_tarski(u1_struct_0(B_53), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_53, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_747])).
% 4.88/1.83  tff(c_771, plain, (![B_439]: (~m1_connsp_2(u1_struct_0(B_439), '#skF_3', '#skF_6') | ~r1_tarski(u1_struct_0(B_439), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_439, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_761])).
% 4.88/1.83  tff(c_775, plain, (~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_771])).
% 4.88/1.83  tff(c_778, plain, (~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_775])).
% 4.88/1.83  tff(c_781, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_582, c_778])).
% 4.88/1.83  tff(c_784, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_781])).
% 4.88/1.83  tff(c_786, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_784])).
% 4.88/1.83  tff(c_789, plain, (~v1_tsep_1('#skF_5', '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_442, c_786])).
% 4.88/1.83  tff(c_793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_52, c_66, c_54, c_789])).
% 4.88/1.83  tff(c_794, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_784])).
% 4.88/1.83  tff(c_804, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_794])).
% 4.88/1.83  tff(c_807, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_804])).
% 4.88/1.83  tff(c_809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_307, c_807])).
% 4.88/1.83  tff(c_811, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_85])).
% 4.88/1.83  tff(c_1382, plain, (![B_544, D_547, A_546, F_548, C_545]: (r1_tmap_1(D_547, A_546, k2_tmap_1(B_544, A_546, C_545, D_547), F_548) | ~r1_tmap_1(B_544, A_546, C_545, F_548) | ~m1_subset_1(F_548, u1_struct_0(D_547)) | ~m1_subset_1(F_548, u1_struct_0(B_544)) | ~m1_pre_topc(D_547, B_544) | v2_struct_0(D_547) | ~m1_subset_1(C_545, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_544), u1_struct_0(A_546)))) | ~v1_funct_2(C_545, u1_struct_0(B_544), u1_struct_0(A_546)) | ~v1_funct_1(C_545) | ~l1_pre_topc(B_544) | ~v2_pre_topc(B_544) | v2_struct_0(B_544) | ~l1_pre_topc(A_546) | ~v2_pre_topc(A_546) | v2_struct_0(A_546))), inference(cnfTransformation, [status(thm)], [f_209])).
% 4.88/1.83  tff(c_1384, plain, (![D_547, F_548]: (r1_tmap_1(D_547, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_547), F_548) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_548) | ~m1_subset_1(F_548, u1_struct_0(D_547)) | ~m1_subset_1(F_548, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_547, '#skF_3') | v2_struct_0(D_547) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_1382])).
% 4.88/1.83  tff(c_1387, plain, (![D_547, F_548]: (r1_tmap_1(D_547, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_547), F_548) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_548) | ~m1_subset_1(F_548, u1_struct_0(D_547)) | ~m1_subset_1(F_548, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_547, '#skF_3') | v2_struct_0(D_547) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_60, c_1384])).
% 4.88/1.83  tff(c_1646, plain, (![D_583, F_584]: (r1_tmap_1(D_583, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_583), F_584) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_584) | ~m1_subset_1(F_584, u1_struct_0(D_583)) | ~m1_subset_1(F_584, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_583, '#skF_3') | v2_struct_0(D_583))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_1387])).
% 4.88/1.83  tff(c_810, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_85])).
% 4.88/1.83  tff(c_1651, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1646, c_810])).
% 4.88/1.83  tff(c_1658, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_83, c_811, c_1651])).
% 4.88/1.83  tff(c_1660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1658])).
% 4.88/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.83  
% 4.88/1.83  Inference rules
% 4.88/1.83  ----------------------
% 4.88/1.83  #Ref     : 0
% 4.88/1.83  #Sup     : 290
% 4.88/1.83  #Fact    : 0
% 4.88/1.83  #Define  : 0
% 4.88/1.83  #Split   : 5
% 4.88/1.83  #Chain   : 0
% 4.88/1.83  #Close   : 0
% 4.88/1.83  
% 4.88/1.83  Ordering : KBO
% 4.88/1.83  
% 4.88/1.83  Simplification rules
% 4.88/1.83  ----------------------
% 4.88/1.83  #Subsume      : 59
% 4.88/1.83  #Demod        : 255
% 4.88/1.83  #Tautology    : 38
% 4.88/1.83  #SimpNegUnit  : 104
% 4.88/1.83  #BackRed      : 0
% 4.88/1.83  
% 4.88/1.83  #Partial instantiations: 0
% 4.88/1.83  #Strategies tried      : 1
% 4.88/1.83  
% 4.88/1.83  Timing (in seconds)
% 4.88/1.83  ----------------------
% 4.88/1.83  Preprocessing        : 0.42
% 4.88/1.84  Parsing              : 0.22
% 4.88/1.84  CNF conversion       : 0.05
% 4.88/1.84  Main loop            : 0.64
% 4.88/1.84  Inferencing          : 0.23
% 4.88/1.84  Reduction            : 0.18
% 4.88/1.84  Demodulation         : 0.12
% 4.88/1.84  BG Simplification    : 0.03
% 4.88/1.84  Subsumption          : 0.15
% 4.88/1.84  Abstraction          : 0.02
% 4.88/1.84  MUC search           : 0.00
% 4.88/1.84  Cooper               : 0.00
% 4.88/1.84  Total                : 1.11
% 4.88/1.84  Index Insertion      : 0.00
% 4.88/1.84  Index Deletion       : 0.00
% 4.88/1.84  Index Matching       : 0.00
% 4.88/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
