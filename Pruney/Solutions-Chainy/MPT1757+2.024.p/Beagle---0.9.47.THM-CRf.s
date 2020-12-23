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
% DateTime   : Thu Dec  3 10:27:07 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 342 expanded)
%              Number of leaves         :   43 ( 144 expanded)
%              Depth                    :   16
%              Number of atoms          :  334 (2107 expanded)
%              Number of equality atoms :    7 ( 109 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_268,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_131,axiom,(
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

tff(f_113,axiom,(
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

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_225,axiom,(
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

tff(f_178,axiom,(
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
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_40,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_78,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_97,plain,(
    ! [B_294,A_295] :
      ( l1_pre_topc(B_294)
      | ~ m1_pre_topc(B_294,A_295)
      | ~ l1_pre_topc(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_100,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_97])).

tff(c_103,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_100])).

tff(c_14,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_140,plain,(
    ! [B_312,A_313] :
      ( m1_subset_1(u1_struct_0(B_312),k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ m1_pre_topc(B_312,A_313)
      | ~ l1_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( m1_subset_1(A_7,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_161,plain,(
    ! [A_319,A_320,B_321] :
      ( m1_subset_1(A_319,u1_struct_0(A_320))
      | ~ r2_hidden(A_319,u1_struct_0(B_321))
      | ~ m1_pre_topc(B_321,A_320)
      | ~ l1_pre_topc(A_320) ) ),
    inference(resolution,[status(thm)],[c_140,c_12])).

tff(c_187,plain,(
    ! [A_327,A_328,B_329] :
      ( m1_subset_1(A_327,u1_struct_0(A_328))
      | ~ m1_pre_topc(B_329,A_328)
      | ~ l1_pre_topc(A_328)
      | v1_xboole_0(u1_struct_0(B_329))
      | ~ m1_subset_1(A_327,u1_struct_0(B_329)) ) ),
    inference(resolution,[status(thm)],[c_6,c_161])).

tff(c_189,plain,(
    ! [A_327] :
      ( m1_subset_1(A_327,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_327,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_46,c_187])).

tff(c_192,plain,(
    ! [A_327] :
      ( m1_subset_1(A_327,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_327,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_189])).

tff(c_193,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_18,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_196,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_193,c_18])).

tff(c_199,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_196])).

tff(c_203,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_199])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_203])).

tff(c_209,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_48,plain,(
    v1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_32,plain,(
    ! [B_42,A_40] :
      ( m1_subset_1(u1_struct_0(B_42),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_pre_topc(B_42,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_249,plain,(
    ! [B_343,A_344] :
      ( v3_pre_topc(u1_struct_0(B_343),A_344)
      | ~ v1_tsep_1(B_343,A_344)
      | ~ m1_subset_1(u1_struct_0(B_343),k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ m1_pre_topc(B_343,A_344)
      | ~ l1_pre_topc(A_344)
      | ~ v2_pre_topc(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_260,plain,(
    ! [B_42,A_40] :
      ( v3_pre_topc(u1_struct_0(B_42),A_40)
      | ~ v1_tsep_1(B_42,A_40)
      | ~ v2_pre_topc(A_40)
      | ~ m1_pre_topc(B_42,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_32,c_249])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_284,plain,(
    ! [B_350,A_351,C_352] :
      ( m1_connsp_2(B_350,A_351,C_352)
      | ~ r2_hidden(C_352,B_350)
      | ~ v3_pre_topc(B_350,A_351)
      | ~ m1_subset_1(C_352,u1_struct_0(A_351))
      | ~ m1_subset_1(B_350,k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351)
      | v2_struct_0(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_294,plain,(
    ! [B_350] :
      ( m1_connsp_2(B_350,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_350)
      | ~ v3_pre_topc(B_350,'#skF_2')
      | ~ m1_subset_1(B_350,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_78,c_284])).

tff(c_307,plain,(
    ! [B_350] :
      ( m1_connsp_2(B_350,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_350)
      | ~ v3_pre_topc(B_350,'#skF_2')
      | ~ m1_subset_1(B_350,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_294])).

tff(c_314,plain,(
    ! [B_355] :
      ( m1_connsp_2(B_355,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_355)
      | ~ v3_pre_topc(B_355,'#skF_2')
      | ~ m1_subset_1(B_355,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_307])).

tff(c_318,plain,(
    ! [B_42] :
      ( m1_connsp_2(u1_struct_0(B_42),'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_42))
      | ~ v3_pre_topc(u1_struct_0(B_42),'#skF_2')
      | ~ m1_pre_topc(B_42,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_314])).

tff(c_329,plain,(
    ! [B_42] :
      ( m1_connsp_2(u1_struct_0(B_42),'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',u1_struct_0(B_42))
      | ~ v3_pre_topc(u1_struct_0(B_42),'#skF_2')
      | ~ m1_pre_topc(B_42,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_318])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_80,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_105,plain,(
    ! [A_298,B_299] :
      ( r1_tarski(A_298,B_299)
      | ~ m1_subset_1(A_298,k1_zfmisc_1(B_299)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_80,c_105])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_77,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76])).

tff(c_160,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_79,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70])).

tff(c_167,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_79])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_54,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_396,plain,(
    ! [C_365,A_370,G_368,B_366,D_367,E_369] :
      ( r1_tmap_1(B_366,A_370,C_365,G_368)
      | ~ r1_tmap_1(D_367,A_370,k2_tmap_1(B_366,A_370,C_365,D_367),G_368)
      | ~ m1_connsp_2(E_369,B_366,G_368)
      | ~ r1_tarski(E_369,u1_struct_0(D_367))
      | ~ m1_subset_1(G_368,u1_struct_0(D_367))
      | ~ m1_subset_1(G_368,u1_struct_0(B_366))
      | ~ m1_subset_1(E_369,k1_zfmisc_1(u1_struct_0(B_366)))
      | ~ m1_pre_topc(D_367,B_366)
      | v2_struct_0(D_367)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_366),u1_struct_0(A_370))))
      | ~ v1_funct_2(C_365,u1_struct_0(B_366),u1_struct_0(A_370))
      | ~ v1_funct_1(C_365)
      | ~ l1_pre_topc(B_366)
      | ~ v2_pre_topc(B_366)
      | v2_struct_0(B_366)
      | ~ l1_pre_topc(A_370)
      | ~ v2_pre_topc(A_370)
      | v2_struct_0(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_398,plain,(
    ! [E_369] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_369,'#skF_2','#skF_6')
      | ~ r1_tarski(E_369,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_369,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_160,c_396])).

tff(c_401,plain,(
    ! [E_369] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_369,'#skF_2','#skF_6')
      | ~ r1_tarski(E_369,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_369,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_56,c_54,c_52,c_46,c_78,c_42,c_398])).

tff(c_403,plain,(
    ! [E_371] :
      ( ~ m1_connsp_2(E_371,'#skF_2','#skF_6')
      | ~ r1_tarski(E_371,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_371,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_50,c_167,c_401])).

tff(c_410,plain,(
    ! [B_42] :
      ( ~ m1_connsp_2(u1_struct_0(B_42),'#skF_2','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_42),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_42,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_403])).

tff(c_467,plain,(
    ! [B_375] :
      ( ~ m1_connsp_2(u1_struct_0(B_375),'#skF_2','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_375),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_375,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_410])).

tff(c_475,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_2','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_117,c_467])).

tff(c_481,plain,(
    ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_475])).

tff(c_484,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_329,c_481])).

tff(c_487,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_484])).

tff(c_488,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_487])).

tff(c_491,plain,
    ( ~ v1_tsep_1('#skF_4','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_260,c_488])).

tff(c_495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46,c_60,c_48,c_491])).

tff(c_496,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_487])).

tff(c_506,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_496])).

tff(c_509,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_506])).

tff(c_511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_509])).

tff(c_512,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_690,plain,(
    ! [D_413,C_409,F_410,A_411,B_412] :
      ( r1_tmap_1(D_413,A_411,k2_tmap_1(B_412,A_411,C_409,D_413),F_410)
      | ~ r1_tmap_1(B_412,A_411,C_409,F_410)
      | ~ m1_subset_1(F_410,u1_struct_0(D_413))
      | ~ m1_subset_1(F_410,u1_struct_0(B_412))
      | ~ m1_pre_topc(D_413,B_412)
      | v2_struct_0(D_413)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_412),u1_struct_0(A_411))))
      | ~ v1_funct_2(C_409,u1_struct_0(B_412),u1_struct_0(A_411))
      | ~ v1_funct_1(C_409)
      | ~ l1_pre_topc(B_412)
      | ~ v2_pre_topc(B_412)
      | v2_struct_0(B_412)
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_695,plain,(
    ! [D_413,F_410] :
      ( r1_tmap_1(D_413,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_413),F_410)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_410)
      | ~ m1_subset_1(F_410,u1_struct_0(D_413))
      | ~ m1_subset_1(F_410,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_413,'#skF_2')
      | v2_struct_0(D_413)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_690])).

tff(c_702,plain,(
    ! [D_413,F_410] :
      ( r1_tmap_1(D_413,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_413),F_410)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_410)
      | ~ m1_subset_1(F_410,u1_struct_0(D_413))
      | ~ m1_subset_1(F_410,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_413,'#skF_2')
      | v2_struct_0(D_413)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_56,c_54,c_695])).

tff(c_888,plain,(
    ! [D_443,F_444] :
      ( r1_tmap_1(D_443,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_443),F_444)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_444)
      | ~ m1_subset_1(F_444,u1_struct_0(D_443))
      | ~ m1_subset_1(F_444,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_443,'#skF_2')
      | v2_struct_0(D_443) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_702])).

tff(c_513,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_893,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_888,c_513])).

tff(c_900,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_78,c_42,c_512,c_893])).

tff(c_902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:21:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.71/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.60  
% 3.71/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.60  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.71/1.60  
% 3.71/1.60  %Foreground sorts:
% 3.71/1.60  
% 3.71/1.60  
% 3.71/1.60  %Background operators:
% 3.71/1.60  
% 3.71/1.60  
% 3.71/1.60  %Foreground operators:
% 3.71/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.71/1.60  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.71/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.71/1.60  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.71/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.71/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.71/1.60  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.71/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.71/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.71/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.71/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.71/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.71/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.71/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.71/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.71/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.71/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.71/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.71/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.71/1.60  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.71/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.71/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.71/1.60  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.71/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.71/1.60  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.71/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.71/1.60  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.71/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.71/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.71/1.60  
% 4.03/1.63  tff(f_268, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 4.03/1.63  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.03/1.63  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.03/1.63  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.03/1.63  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.03/1.63  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.03/1.63  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.03/1.63  tff(f_131, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.03/1.63  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 4.03/1.63  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.03/1.63  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.03/1.63  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.03/1.63  tff(f_225, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 4.03/1.63  tff(f_178, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 4.03/1.63  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_40, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_78, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44])).
% 4.03/1.63  tff(c_42, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_97, plain, (![B_294, A_295]: (l1_pre_topc(B_294) | ~m1_pre_topc(B_294, A_295) | ~l1_pre_topc(A_295))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.03/1.63  tff(c_100, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_97])).
% 4.03/1.63  tff(c_103, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_100])).
% 4.03/1.63  tff(c_14, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.03/1.63  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.03/1.63  tff(c_140, plain, (![B_312, A_313]: (m1_subset_1(u1_struct_0(B_312), k1_zfmisc_1(u1_struct_0(A_313))) | ~m1_pre_topc(B_312, A_313) | ~l1_pre_topc(A_313))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.03/1.63  tff(c_12, plain, (![A_7, C_9, B_8]: (m1_subset_1(A_7, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.03/1.63  tff(c_161, plain, (![A_319, A_320, B_321]: (m1_subset_1(A_319, u1_struct_0(A_320)) | ~r2_hidden(A_319, u1_struct_0(B_321)) | ~m1_pre_topc(B_321, A_320) | ~l1_pre_topc(A_320))), inference(resolution, [status(thm)], [c_140, c_12])).
% 4.03/1.63  tff(c_187, plain, (![A_327, A_328, B_329]: (m1_subset_1(A_327, u1_struct_0(A_328)) | ~m1_pre_topc(B_329, A_328) | ~l1_pre_topc(A_328) | v1_xboole_0(u1_struct_0(B_329)) | ~m1_subset_1(A_327, u1_struct_0(B_329)))), inference(resolution, [status(thm)], [c_6, c_161])).
% 4.03/1.63  tff(c_189, plain, (![A_327]: (m1_subset_1(A_327, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_327, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_46, c_187])).
% 4.03/1.63  tff(c_192, plain, (![A_327]: (m1_subset_1(A_327, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_327, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_189])).
% 4.03/1.63  tff(c_193, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_192])).
% 4.03/1.63  tff(c_18, plain, (![A_14]: (~v1_xboole_0(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.03/1.63  tff(c_196, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_193, c_18])).
% 4.03/1.63  tff(c_199, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_196])).
% 4.03/1.63  tff(c_203, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_199])).
% 4.03/1.63  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_203])).
% 4.03/1.63  tff(c_209, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_192])).
% 4.03/1.63  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_48, plain, (v1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_32, plain, (![B_42, A_40]: (m1_subset_1(u1_struct_0(B_42), k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_pre_topc(B_42, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.03/1.63  tff(c_249, plain, (![B_343, A_344]: (v3_pre_topc(u1_struct_0(B_343), A_344) | ~v1_tsep_1(B_343, A_344) | ~m1_subset_1(u1_struct_0(B_343), k1_zfmisc_1(u1_struct_0(A_344))) | ~m1_pre_topc(B_343, A_344) | ~l1_pre_topc(A_344) | ~v2_pre_topc(A_344))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.03/1.63  tff(c_260, plain, (![B_42, A_40]: (v3_pre_topc(u1_struct_0(B_42), A_40) | ~v1_tsep_1(B_42, A_40) | ~v2_pre_topc(A_40) | ~m1_pre_topc(B_42, A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_32, c_249])).
% 4.03/1.63  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_284, plain, (![B_350, A_351, C_352]: (m1_connsp_2(B_350, A_351, C_352) | ~r2_hidden(C_352, B_350) | ~v3_pre_topc(B_350, A_351) | ~m1_subset_1(C_352, u1_struct_0(A_351)) | ~m1_subset_1(B_350, k1_zfmisc_1(u1_struct_0(A_351))) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351) | v2_struct_0(A_351))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.03/1.63  tff(c_294, plain, (![B_350]: (m1_connsp_2(B_350, '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', B_350) | ~v3_pre_topc(B_350, '#skF_2') | ~m1_subset_1(B_350, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_78, c_284])).
% 4.03/1.63  tff(c_307, plain, (![B_350]: (m1_connsp_2(B_350, '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', B_350) | ~v3_pre_topc(B_350, '#skF_2') | ~m1_subset_1(B_350, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_294])).
% 4.03/1.63  tff(c_314, plain, (![B_355]: (m1_connsp_2(B_355, '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', B_355) | ~v3_pre_topc(B_355, '#skF_2') | ~m1_subset_1(B_355, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_307])).
% 4.03/1.63  tff(c_318, plain, (![B_42]: (m1_connsp_2(u1_struct_0(B_42), '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_42)) | ~v3_pre_topc(u1_struct_0(B_42), '#skF_2') | ~m1_pre_topc(B_42, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_314])).
% 4.03/1.63  tff(c_329, plain, (![B_42]: (m1_connsp_2(u1_struct_0(B_42), '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0(B_42)) | ~v3_pre_topc(u1_struct_0(B_42), '#skF_2') | ~m1_pre_topc(B_42, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_318])).
% 4.03/1.63  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.03/1.63  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.03/1.63  tff(c_80, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.03/1.63  tff(c_105, plain, (![A_298, B_299]: (r1_tarski(A_298, B_299) | ~m1_subset_1(A_298, k1_zfmisc_1(B_299)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.03/1.63  tff(c_117, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_80, c_105])).
% 4.03/1.63  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_76, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_77, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76])).
% 4.03/1.63  tff(c_160, plain, (r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_77])).
% 4.03/1.63  tff(c_70, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_79, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70])).
% 4.03/1.63  tff(c_167, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_79])).
% 4.03/1.63  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_54, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_268])).
% 4.03/1.63  tff(c_396, plain, (![C_365, A_370, G_368, B_366, D_367, E_369]: (r1_tmap_1(B_366, A_370, C_365, G_368) | ~r1_tmap_1(D_367, A_370, k2_tmap_1(B_366, A_370, C_365, D_367), G_368) | ~m1_connsp_2(E_369, B_366, G_368) | ~r1_tarski(E_369, u1_struct_0(D_367)) | ~m1_subset_1(G_368, u1_struct_0(D_367)) | ~m1_subset_1(G_368, u1_struct_0(B_366)) | ~m1_subset_1(E_369, k1_zfmisc_1(u1_struct_0(B_366))) | ~m1_pre_topc(D_367, B_366) | v2_struct_0(D_367) | ~m1_subset_1(C_365, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_366), u1_struct_0(A_370)))) | ~v1_funct_2(C_365, u1_struct_0(B_366), u1_struct_0(A_370)) | ~v1_funct_1(C_365) | ~l1_pre_topc(B_366) | ~v2_pre_topc(B_366) | v2_struct_0(B_366) | ~l1_pre_topc(A_370) | ~v2_pre_topc(A_370) | v2_struct_0(A_370))), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.03/1.63  tff(c_398, plain, (![E_369]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_369, '#skF_2', '#skF_6') | ~r1_tarski(E_369, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1(E_369, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_160, c_396])).
% 4.03/1.63  tff(c_401, plain, (![E_369]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_369, '#skF_2', '#skF_6') | ~r1_tarski(E_369, u1_struct_0('#skF_4')) | ~m1_subset_1(E_369, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_56, c_54, c_52, c_46, c_78, c_42, c_398])).
% 4.03/1.63  tff(c_403, plain, (![E_371]: (~m1_connsp_2(E_371, '#skF_2', '#skF_6') | ~r1_tarski(E_371, u1_struct_0('#skF_4')) | ~m1_subset_1(E_371, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_50, c_167, c_401])).
% 4.03/1.63  tff(c_410, plain, (![B_42]: (~m1_connsp_2(u1_struct_0(B_42), '#skF_2', '#skF_6') | ~r1_tarski(u1_struct_0(B_42), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_42, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_403])).
% 4.03/1.63  tff(c_467, plain, (![B_375]: (~m1_connsp_2(u1_struct_0(B_375), '#skF_2', '#skF_6') | ~r1_tarski(u1_struct_0(B_375), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_375, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_410])).
% 4.03/1.63  tff(c_475, plain, (~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_2', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_117, c_467])).
% 4.03/1.63  tff(c_481, plain, (~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_475])).
% 4.03/1.63  tff(c_484, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_329, c_481])).
% 4.03/1.63  tff(c_487, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_484])).
% 4.03/1.63  tff(c_488, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_487])).
% 4.03/1.63  tff(c_491, plain, (~v1_tsep_1('#skF_4', '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_260, c_488])).
% 4.03/1.63  tff(c_495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_46, c_60, c_48, c_491])).
% 4.03/1.63  tff(c_496, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_487])).
% 4.03/1.63  tff(c_506, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_496])).
% 4.03/1.63  tff(c_509, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_506])).
% 4.03/1.63  tff(c_511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_509])).
% 4.03/1.63  tff(c_512, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_77])).
% 4.03/1.63  tff(c_690, plain, (![D_413, C_409, F_410, A_411, B_412]: (r1_tmap_1(D_413, A_411, k2_tmap_1(B_412, A_411, C_409, D_413), F_410) | ~r1_tmap_1(B_412, A_411, C_409, F_410) | ~m1_subset_1(F_410, u1_struct_0(D_413)) | ~m1_subset_1(F_410, u1_struct_0(B_412)) | ~m1_pre_topc(D_413, B_412) | v2_struct_0(D_413) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_412), u1_struct_0(A_411)))) | ~v1_funct_2(C_409, u1_struct_0(B_412), u1_struct_0(A_411)) | ~v1_funct_1(C_409) | ~l1_pre_topc(B_412) | ~v2_pre_topc(B_412) | v2_struct_0(B_412) | ~l1_pre_topc(A_411) | ~v2_pre_topc(A_411) | v2_struct_0(A_411))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.03/1.63  tff(c_695, plain, (![D_413, F_410]: (r1_tmap_1(D_413, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_413), F_410) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_410) | ~m1_subset_1(F_410, u1_struct_0(D_413)) | ~m1_subset_1(F_410, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_413, '#skF_2') | v2_struct_0(D_413) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_690])).
% 4.03/1.63  tff(c_702, plain, (![D_413, F_410]: (r1_tmap_1(D_413, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_413), F_410) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_410) | ~m1_subset_1(F_410, u1_struct_0(D_413)) | ~m1_subset_1(F_410, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_413, '#skF_2') | v2_struct_0(D_413) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_56, c_54, c_695])).
% 4.03/1.63  tff(c_888, plain, (![D_443, F_444]: (r1_tmap_1(D_443, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_443), F_444) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_444) | ~m1_subset_1(F_444, u1_struct_0(D_443)) | ~m1_subset_1(F_444, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_443, '#skF_2') | v2_struct_0(D_443))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_702])).
% 4.03/1.63  tff(c_513, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_77])).
% 4.03/1.63  tff(c_893, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_888, c_513])).
% 4.03/1.63  tff(c_900, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_78, c_42, c_512, c_893])).
% 4.03/1.63  tff(c_902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_900])).
% 4.03/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.63  
% 4.03/1.63  Inference rules
% 4.03/1.63  ----------------------
% 4.03/1.63  #Ref     : 0
% 4.03/1.63  #Sup     : 149
% 4.03/1.63  #Fact    : 0
% 4.03/1.63  #Define  : 0
% 4.03/1.63  #Split   : 13
% 4.03/1.63  #Chain   : 0
% 4.03/1.63  #Close   : 0
% 4.03/1.63  
% 4.03/1.63  Ordering : KBO
% 4.03/1.63  
% 4.03/1.63  Simplification rules
% 4.03/1.63  ----------------------
% 4.03/1.63  #Subsume      : 43
% 4.03/1.63  #Demod        : 119
% 4.03/1.63  #Tautology    : 24
% 4.03/1.63  #SimpNegUnit  : 37
% 4.03/1.63  #BackRed      : 0
% 4.03/1.63  
% 4.03/1.63  #Partial instantiations: 0
% 4.03/1.63  #Strategies tried      : 1
% 4.03/1.63  
% 4.03/1.63  Timing (in seconds)
% 4.03/1.63  ----------------------
% 4.03/1.63  Preprocessing        : 0.41
% 4.03/1.63  Parsing              : 0.21
% 4.03/1.63  CNF conversion       : 0.05
% 4.03/1.63  Main loop            : 0.44
% 4.03/1.63  Inferencing          : 0.16
% 4.03/1.63  Reduction            : 0.14
% 4.03/1.63  Demodulation         : 0.10
% 4.03/1.63  BG Simplification    : 0.03
% 4.03/1.63  Subsumption          : 0.09
% 4.03/1.63  Abstraction          : 0.02
% 4.03/1.63  MUC search           : 0.00
% 4.03/1.63  Cooper               : 0.00
% 4.03/1.63  Total                : 0.90
% 4.03/1.63  Index Insertion      : 0.00
% 4.03/1.63  Index Deletion       : 0.00
% 4.03/1.63  Index Matching       : 0.00
% 4.03/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
