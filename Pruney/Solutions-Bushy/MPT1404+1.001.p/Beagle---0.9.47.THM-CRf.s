%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1404+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:54 EST 2020

% Result     : Theorem 37.68s
% Output     : CNFRefutation 37.79s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 827 expanded)
%              Number of leaves         :   40 ( 297 expanded)
%              Depth                    :   18
%              Number of atoms          :  643 (3557 expanded)
%              Number of equality atoms :   10 (  45 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_182,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,k2_pre_topc(A,B))
                <=> ! [D] :
                      ( m1_connsp_2(D,A,C)
                     => ~ r1_xboole_0(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_connsp_2)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_122,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k2_pre_topc(A,B)
              <=> ! [D] :
                    ( r2_hidden(D,u1_struct_0(A))
                   => ( r2_hidden(D,C)
                    <=> ! [E] :
                          ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v3_pre_topc(E,A)
                              & r2_hidden(D,E)
                              & r1_xboole_0(B,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_pre_topc)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_154,axiom,(
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

tff(f_116,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_160,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_42,plain,(
    ! [A_96] :
      ( l1_struct_0(A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_21704,plain,(
    ! [A_2808,C_2809,B_2810] :
      ( m1_subset_1(A_2808,C_2809)
      | ~ m1_subset_1(B_2810,k1_zfmisc_1(C_2809))
      | ~ r2_hidden(A_2808,B_2810) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_21707,plain,(
    ! [A_2808] :
      ( m1_subset_1(A_2808,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_2808,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_21704])).

tff(c_52,plain,(
    ! [A_106,B_107] :
      ( r2_hidden(A_106,B_107)
      | v1_xboole_0(B_107)
      | ~ m1_subset_1(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_22347,plain,(
    ! [A_2911,B_2912,C_2913] :
      ( m1_subset_1('#skF_3'(A_2911,B_2912,C_2913),k1_zfmisc_1(u1_struct_0(A_2911)))
      | ~ r2_hidden('#skF_2'(A_2911,B_2912,C_2913),C_2913)
      | k2_pre_topc(A_2911,B_2912) = C_2913
      | ~ m1_subset_1(C_2913,k1_zfmisc_1(u1_struct_0(A_2911)))
      | ~ m1_subset_1(B_2912,k1_zfmisc_1(u1_struct_0(A_2911)))
      | ~ l1_pre_topc(A_2911) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_25265,plain,(
    ! [A_3194,B_3195,B_3196] :
      ( m1_subset_1('#skF_3'(A_3194,B_3195,B_3196),k1_zfmisc_1(u1_struct_0(A_3194)))
      | k2_pre_topc(A_3194,B_3195) = B_3196
      | ~ m1_subset_1(B_3196,k1_zfmisc_1(u1_struct_0(A_3194)))
      | ~ m1_subset_1(B_3195,k1_zfmisc_1(u1_struct_0(A_3194)))
      | ~ l1_pre_topc(A_3194)
      | v1_xboole_0(B_3196)
      | ~ m1_subset_1('#skF_2'(A_3194,B_3195,B_3196),B_3196) ) ),
    inference(resolution,[status(thm)],[c_52,c_22347])).

tff(c_25273,plain,(
    ! [A_3194,B_3195] :
      ( m1_subset_1('#skF_3'(A_3194,B_3195,u1_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0(A_3194)))
      | k2_pre_topc(A_3194,B_3195) = u1_struct_0('#skF_4')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_3194)))
      | ~ m1_subset_1(B_3195,k1_zfmisc_1(u1_struct_0(A_3194)))
      | ~ l1_pre_topc(A_3194)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_2'(A_3194,B_3195,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_21707,c_25265])).

tff(c_28436,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_25273])).

tff(c_46,plain,(
    ! [A_101] :
      ( ~ v1_xboole_0(u1_struct_0(A_101))
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_28439,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28436,c_46])).

tff(c_28442,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_28439])).

tff(c_28445,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_28442])).

tff(c_28449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_28445])).

tff(c_28451,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_25273])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_72,plain,
    ( r1_xboole_0('#skF_7','#skF_5')
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_87,plain,(
    ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_94,plain,(
    ! [A_152,C_153,B_154] :
      ( m1_subset_1(A_152,C_153)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(C_153))
      | ~ r2_hidden(A_152,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_97,plain,(
    ! [A_152] :
      ( m1_subset_1(A_152,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_152,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_94])).

tff(c_432,plain,(
    ! [A_240,B_241,C_242] :
      ( m1_subset_1('#skF_3'(A_240,B_241,C_242),k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ r2_hidden('#skF_2'(A_240,B_241,C_242),C_242)
      | k2_pre_topc(A_240,B_241) = C_242
      | ~ m1_subset_1(C_242,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1311,plain,(
    ! [A_370,B_371,B_372] :
      ( m1_subset_1('#skF_3'(A_370,B_371,B_372),k1_zfmisc_1(u1_struct_0(A_370)))
      | k2_pre_topc(A_370,B_371) = B_372
      | ~ m1_subset_1(B_372,k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ m1_subset_1(B_371,k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ l1_pre_topc(A_370)
      | v1_xboole_0(B_372)
      | ~ m1_subset_1('#skF_2'(A_370,B_371,B_372),B_372) ) ),
    inference(resolution,[status(thm)],[c_52,c_432])).

tff(c_1315,plain,(
    ! [A_370,B_371] :
      ( m1_subset_1('#skF_3'(A_370,B_371,u1_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0(A_370)))
      | k2_pre_topc(A_370,B_371) = u1_struct_0('#skF_4')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ m1_subset_1(B_371,k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ l1_pre_topc(A_370)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_2'(A_370,B_371,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_97,c_1311])).

tff(c_2426,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1315])).

tff(c_2429,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2426,c_46])).

tff(c_2432,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2429])).

tff(c_2435,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_2432])).

tff(c_2439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2435])).

tff(c_2441,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1315])).

tff(c_40,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1(k2_pre_topc(A_94,B_95),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_745,plain,(
    ! [D_271,A_272,B_273] :
      ( r2_hidden(D_271,'#skF_1'(A_272,B_273,k2_pre_topc(A_272,B_273),D_271))
      | r2_hidden(D_271,k2_pre_topc(A_272,B_273))
      | ~ r2_hidden(D_271,u1_struct_0(A_272))
      | ~ m1_subset_1(k2_pre_topc(A_272,B_273),k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ l1_pre_topc(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_748,plain,(
    ! [D_271,A_94,B_95] :
      ( r2_hidden(D_271,'#skF_1'(A_94,B_95,k2_pre_topc(A_94,B_95),D_271))
      | r2_hidden(D_271,k2_pre_topc(A_94,B_95))
      | ~ r2_hidden(D_271,u1_struct_0(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_40,c_745])).

tff(c_1019,plain,(
    ! [A_316,B_317,D_318] :
      ( v3_pre_topc('#skF_1'(A_316,B_317,k2_pre_topc(A_316,B_317),D_318),A_316)
      | r2_hidden(D_318,k2_pre_topc(A_316,B_317))
      | ~ r2_hidden(D_318,u1_struct_0(A_316))
      | ~ m1_subset_1(k2_pre_topc(A_316,B_317),k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ m1_subset_1(B_317,k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ l1_pre_topc(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1032,plain,(
    ! [A_94,B_95,D_318] :
      ( v3_pre_topc('#skF_1'(A_94,B_95,k2_pre_topc(A_94,B_95),D_318),A_94)
      | r2_hidden(D_318,k2_pre_topc(A_94,B_95))
      | ~ r2_hidden(D_318,u1_struct_0(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_40,c_1019])).

tff(c_1166,plain,(
    ! [A_337,B_338,D_339] :
      ( m1_subset_1('#skF_1'(A_337,B_338,k2_pre_topc(A_337,B_338),D_339),k1_zfmisc_1(u1_struct_0(A_337)))
      | r2_hidden(D_339,k2_pre_topc(A_337,B_338))
      | ~ r2_hidden(D_339,u1_struct_0(A_337))
      | ~ m1_subset_1(k2_pre_topc(A_337,B_338),k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ m1_subset_1(B_338,k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ l1_pre_topc(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_207,plain,(
    ! [B_201,A_202,C_203] :
      ( m1_connsp_2(B_201,A_202,C_203)
      | ~ r2_hidden(C_203,B_201)
      | ~ v3_pre_topc(B_201,A_202)
      | ~ m1_subset_1(C_203,u1_struct_0(A_202))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_211,plain,(
    ! [B_201] :
      ( m1_connsp_2(B_201,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_201)
      | ~ v3_pre_topc(B_201,'#skF_4')
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_207])).

tff(c_218,plain,(
    ! [B_201] :
      ( m1_connsp_2(B_201,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_201)
      | ~ v3_pre_topc(B_201,'#skF_4')
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_211])).

tff(c_219,plain,(
    ! [B_201] :
      ( m1_connsp_2(B_201,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_201)
      | ~ v3_pre_topc(B_201,'#skF_4')
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_218])).

tff(c_1193,plain,(
    ! [B_338,D_339] :
      ( m1_connsp_2('#skF_1'('#skF_4',B_338,k2_pre_topc('#skF_4',B_338),D_339),'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_338,k2_pre_topc('#skF_4',B_338),D_339))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_338,k2_pre_topc('#skF_4',B_338),D_339),'#skF_4')
      | r2_hidden(D_339,k2_pre_topc('#skF_4',B_338))
      | ~ r2_hidden(D_339,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_338),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_338,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1166,c_219])).

tff(c_4274,plain,(
    ! [B_836,D_837] :
      ( m1_connsp_2('#skF_1'('#skF_4',B_836,k2_pre_topc('#skF_4',B_836),D_837),'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_836,k2_pre_topc('#skF_4',B_836),D_837))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_836,k2_pre_topc('#skF_4',B_836),D_837),'#skF_4')
      | r2_hidden(D_837,k2_pre_topc('#skF_4',B_836))
      | ~ r2_hidden(D_837,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_836),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_836,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1193])).

tff(c_4281,plain,(
    ! [B_95,D_837] :
      ( m1_connsp_2('#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),D_837),'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),D_837))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),D_837),'#skF_4')
      | r2_hidden(D_837,k2_pre_topc('#skF_4',B_95))
      | ~ r2_hidden(D_837,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_4274])).

tff(c_4327,plain,(
    ! [B_849,D_850] :
      ( m1_connsp_2('#skF_1'('#skF_4',B_849,k2_pre_topc('#skF_4',B_849),D_850),'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_849,k2_pre_topc('#skF_4',B_849),D_850))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_849,k2_pre_topc('#skF_4',B_849),D_850),'#skF_4')
      | r2_hidden(D_850,k2_pre_topc('#skF_4',B_849))
      | ~ r2_hidden(D_850,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_849,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4281])).

tff(c_78,plain,(
    ! [D_142] :
      ( r1_xboole_0('#skF_7','#skF_5')
      | ~ r1_xboole_0(D_142,'#skF_5')
      | ~ m1_connsp_2(D_142,'#skF_4','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_99,plain,(
    ! [D_142] :
      ( ~ r1_xboole_0(D_142,'#skF_5')
      | ~ m1_connsp_2(D_142,'#skF_4','#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_4338,plain,(
    ! [B_851,D_852] :
      ( ~ r1_xboole_0('#skF_1'('#skF_4',B_851,k2_pre_topc('#skF_4',B_851),D_852),'#skF_5')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_851,k2_pre_topc('#skF_4',B_851),D_852))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_851,k2_pre_topc('#skF_4',B_851),D_852),'#skF_4')
      | r2_hidden(D_852,k2_pre_topc('#skF_4',B_851))
      | ~ r2_hidden(D_852,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_851,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4327,c_99])).

tff(c_4342,plain,(
    ! [B_95,D_318] :
      ( ~ r1_xboole_0('#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),D_318),'#skF_5')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),D_318))
      | r2_hidden(D_318,k2_pre_topc('#skF_4',B_95))
      | ~ r2_hidden(D_318,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1032,c_4338])).

tff(c_4346,plain,(
    ! [B_853,D_854] :
      ( ~ r1_xboole_0('#skF_1'('#skF_4',B_853,k2_pre_topc('#skF_4',B_853),D_854),'#skF_5')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_853,k2_pre_topc('#skF_4',B_853),D_854))
      | r2_hidden(D_854,k2_pre_topc('#skF_4',B_853))
      | ~ r2_hidden(D_854,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_853,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4342])).

tff(c_4350,plain,(
    ! [B_95] :
      ( ~ r1_xboole_0('#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),'#skF_6'),'#skF_5')
      | r2_hidden('#skF_6',k2_pre_topc('#skF_4',B_95))
      | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_748,c_4346])).

tff(c_4356,plain,(
    ! [B_95] :
      ( ~ r1_xboole_0('#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),'#skF_6'),'#skF_5')
      | r2_hidden('#skF_6',k2_pre_topc('#skF_4',B_95))
      | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4350])).

tff(c_4358,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4356])).

tff(c_4361,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_4358])).

tff(c_4364,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4361])).

tff(c_4366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2441,c_4364])).

tff(c_4368,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4356])).

tff(c_900,plain,(
    ! [B_287,A_288,D_289] :
      ( r1_xboole_0(B_287,'#skF_1'(A_288,B_287,k2_pre_topc(A_288,B_287),D_289))
      | r2_hidden(D_289,k2_pre_topc(A_288,B_287))
      | ~ r2_hidden(D_289,u1_struct_0(A_288))
      | ~ m1_subset_1(k2_pre_topc(A_288,B_287),k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_914,plain,(
    ! [B_290,A_291,D_292] :
      ( r1_xboole_0(B_290,'#skF_1'(A_291,B_290,k2_pre_topc(A_291,B_290),D_292))
      | r2_hidden(D_292,k2_pre_topc(A_291,B_290))
      | ~ r2_hidden(D_292,u1_struct_0(A_291))
      | ~ m1_subset_1(B_290,k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ l1_pre_topc(A_291) ) ),
    inference(resolution,[status(thm)],[c_40,c_900])).

tff(c_50,plain,(
    ! [B_105,A_104] :
      ( r1_xboole_0(B_105,A_104)
      | ~ r1_xboole_0(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_920,plain,(
    ! [A_291,B_290,D_292] :
      ( r1_xboole_0('#skF_1'(A_291,B_290,k2_pre_topc(A_291,B_290),D_292),B_290)
      | r2_hidden(D_292,k2_pre_topc(A_291,B_290))
      | ~ r2_hidden(D_292,u1_struct_0(A_291))
      | ~ m1_subset_1(B_290,k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ l1_pre_topc(A_291) ) ),
    inference(resolution,[status(thm)],[c_914,c_50])).

tff(c_4380,plain,(
    ! [B_859] :
      ( ~ r1_xboole_0('#skF_1'('#skF_4',B_859,k2_pre_topc('#skF_4',B_859),'#skF_6'),'#skF_5')
      | r2_hidden('#skF_6',k2_pre_topc('#skF_4',B_859))
      | ~ m1_subset_1(B_859,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_4356])).

tff(c_4396,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_920,c_4380])).

tff(c_4408,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_4368,c_4396])).

tff(c_4410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_4408])).

tff(c_4411,plain,(
    r1_xboole_0('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_4976,plain,(
    ! [A_1018,B_1019,C_1020] :
      ( m1_subset_1('#skF_3'(A_1018,B_1019,C_1020),k1_zfmisc_1(u1_struct_0(A_1018)))
      | ~ r2_hidden('#skF_2'(A_1018,B_1019,C_1020),C_1020)
      | k2_pre_topc(A_1018,B_1019) = C_1020
      | ~ m1_subset_1(C_1020,k1_zfmisc_1(u1_struct_0(A_1018)))
      | ~ m1_subset_1(B_1019,k1_zfmisc_1(u1_struct_0(A_1018)))
      | ~ l1_pre_topc(A_1018) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6900,plain,(
    ! [A_1254,B_1255,B_1256] :
      ( m1_subset_1('#skF_3'(A_1254,B_1255,B_1256),k1_zfmisc_1(u1_struct_0(A_1254)))
      | k2_pre_topc(A_1254,B_1255) = B_1256
      | ~ m1_subset_1(B_1256,k1_zfmisc_1(u1_struct_0(A_1254)))
      | ~ m1_subset_1(B_1255,k1_zfmisc_1(u1_struct_0(A_1254)))
      | ~ l1_pre_topc(A_1254)
      | v1_xboole_0(B_1256)
      | ~ m1_subset_1('#skF_2'(A_1254,B_1255,B_1256),B_1256) ) ),
    inference(resolution,[status(thm)],[c_52,c_4976])).

tff(c_6904,plain,(
    ! [A_1254,B_1255] :
      ( m1_subset_1('#skF_3'(A_1254,B_1255,u1_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0(A_1254)))
      | k2_pre_topc(A_1254,B_1255) = u1_struct_0('#skF_4')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_1254)))
      | ~ m1_subset_1(B_1255,k1_zfmisc_1(u1_struct_0(A_1254)))
      | ~ l1_pre_topc(A_1254)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_2'(A_1254,B_1255,u1_struct_0('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_97,c_6900])).

tff(c_8527,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6904])).

tff(c_8530,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_8527,c_46])).

tff(c_8533,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_8530])).

tff(c_8536,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_8533])).

tff(c_8540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8536])).

tff(c_8542,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6904])).

tff(c_5357,plain,(
    ! [D_1079,A_1080,B_1081] :
      ( r2_hidden(D_1079,'#skF_1'(A_1080,B_1081,k2_pre_topc(A_1080,B_1081),D_1079))
      | r2_hidden(D_1079,k2_pre_topc(A_1080,B_1081))
      | ~ r2_hidden(D_1079,u1_struct_0(A_1080))
      | ~ m1_subset_1(k2_pre_topc(A_1080,B_1081),k1_zfmisc_1(u1_struct_0(A_1080)))
      | ~ m1_subset_1(B_1081,k1_zfmisc_1(u1_struct_0(A_1080)))
      | ~ l1_pre_topc(A_1080) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5360,plain,(
    ! [D_1079,A_94,B_95] :
      ( r2_hidden(D_1079,'#skF_1'(A_94,B_95,k2_pre_topc(A_94,B_95),D_1079))
      | r2_hidden(D_1079,k2_pre_topc(A_94,B_95))
      | ~ r2_hidden(D_1079,u1_struct_0(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_40,c_5357])).

tff(c_5532,plain,(
    ! [A_1093,B_1094,D_1095] :
      ( v3_pre_topc('#skF_1'(A_1093,B_1094,k2_pre_topc(A_1093,B_1094),D_1095),A_1093)
      | r2_hidden(D_1095,k2_pre_topc(A_1093,B_1094))
      | ~ r2_hidden(D_1095,u1_struct_0(A_1093))
      | ~ m1_subset_1(k2_pre_topc(A_1093,B_1094),k1_zfmisc_1(u1_struct_0(A_1093)))
      | ~ m1_subset_1(B_1094,k1_zfmisc_1(u1_struct_0(A_1093)))
      | ~ l1_pre_topc(A_1093) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5540,plain,(
    ! [A_94,B_95,D_1095] :
      ( v3_pre_topc('#skF_1'(A_94,B_95,k2_pre_topc(A_94,B_95),D_1095),A_94)
      | r2_hidden(D_1095,k2_pre_topc(A_94,B_95))
      | ~ r2_hidden(D_1095,u1_struct_0(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_40,c_5532])).

tff(c_5647,plain,(
    ! [A_1107,B_1108,D_1109] :
      ( m1_subset_1('#skF_1'(A_1107,B_1108,k2_pre_topc(A_1107,B_1108),D_1109),k1_zfmisc_1(u1_struct_0(A_1107)))
      | r2_hidden(D_1109,k2_pre_topc(A_1107,B_1108))
      | ~ r2_hidden(D_1109,u1_struct_0(A_1107))
      | ~ m1_subset_1(k2_pre_topc(A_1107,B_1108),k1_zfmisc_1(u1_struct_0(A_1107)))
      | ~ m1_subset_1(B_1108,k1_zfmisc_1(u1_struct_0(A_1107)))
      | ~ l1_pre_topc(A_1107) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4759,plain,(
    ! [B_974,A_975,C_976] :
      ( m1_connsp_2(B_974,A_975,C_976)
      | ~ r2_hidden(C_976,B_974)
      | ~ v3_pre_topc(B_974,A_975)
      | ~ m1_subset_1(C_976,u1_struct_0(A_975))
      | ~ m1_subset_1(B_974,k1_zfmisc_1(u1_struct_0(A_975)))
      | ~ l1_pre_topc(A_975)
      | ~ v2_pre_topc(A_975)
      | v2_struct_0(A_975) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_4763,plain,(
    ! [B_974] :
      ( m1_connsp_2(B_974,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_974)
      | ~ v3_pre_topc(B_974,'#skF_4')
      | ~ m1_subset_1(B_974,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_4759])).

tff(c_4770,plain,(
    ! [B_974] :
      ( m1_connsp_2(B_974,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_974)
      | ~ v3_pre_topc(B_974,'#skF_4')
      | ~ m1_subset_1(B_974,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_4763])).

tff(c_4771,plain,(
    ! [B_974] :
      ( m1_connsp_2(B_974,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_974)
      | ~ v3_pre_topc(B_974,'#skF_4')
      | ~ m1_subset_1(B_974,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4770])).

tff(c_5672,plain,(
    ! [B_1108,D_1109] :
      ( m1_connsp_2('#skF_1'('#skF_4',B_1108,k2_pre_topc('#skF_4',B_1108),D_1109),'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_1108,k2_pre_topc('#skF_4',B_1108),D_1109))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_1108,k2_pre_topc('#skF_4',B_1108),D_1109),'#skF_4')
      | r2_hidden(D_1109,k2_pre_topc('#skF_4',B_1108))
      | ~ r2_hidden(D_1109,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_1108),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_1108,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5647,c_4771])).

tff(c_11543,plain,(
    ! [B_1678,D_1679] :
      ( m1_connsp_2('#skF_1'('#skF_4',B_1678,k2_pre_topc('#skF_4',B_1678),D_1679),'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_1678,k2_pre_topc('#skF_4',B_1678),D_1679))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_1678,k2_pre_topc('#skF_4',B_1678),D_1679),'#skF_4')
      | r2_hidden(D_1679,k2_pre_topc('#skF_4',B_1678))
      | ~ r2_hidden(D_1679,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_1678),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_1678,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5672])).

tff(c_11550,plain,(
    ! [B_95,D_1679] :
      ( m1_connsp_2('#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),D_1679),'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),D_1679))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),D_1679),'#skF_4')
      | r2_hidden(D_1679,k2_pre_topc('#skF_4',B_95))
      | ~ r2_hidden(D_1679,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_11543])).

tff(c_21376,plain,(
    ! [B_2777,D_2778] :
      ( m1_connsp_2('#skF_1'('#skF_4',B_2777,k2_pre_topc('#skF_4',B_2777),D_2778),'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_2777,k2_pre_topc('#skF_4',B_2777),D_2778))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_2777,k2_pre_topc('#skF_4',B_2777),D_2778),'#skF_4')
      | r2_hidden(D_2778,k2_pre_topc('#skF_4',B_2777))
      | ~ r2_hidden(D_2778,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_2777,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_11550])).

tff(c_80,plain,(
    ! [D_142] :
      ( m1_connsp_2('#skF_7','#skF_4','#skF_6')
      | ~ r1_xboole_0(D_142,'#skF_5')
      | ~ m1_connsp_2(D_142,'#skF_4','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_4418,plain,(
    ! [D_142] :
      ( ~ r1_xboole_0(D_142,'#skF_5')
      | ~ m1_connsp_2(D_142,'#skF_4','#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_21505,plain,(
    ! [B_2781,D_2782] :
      ( ~ r1_xboole_0('#skF_1'('#skF_4',B_2781,k2_pre_topc('#skF_4',B_2781),D_2782),'#skF_5')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_2781,k2_pre_topc('#skF_4',B_2781),D_2782))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_2781,k2_pre_topc('#skF_4',B_2781),D_2782),'#skF_4')
      | r2_hidden(D_2782,k2_pre_topc('#skF_4',B_2781))
      | ~ r2_hidden(D_2782,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_2781,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_21376,c_4418])).

tff(c_21509,plain,(
    ! [B_95,D_1095] :
      ( ~ r1_xboole_0('#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),D_1095),'#skF_5')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),D_1095))
      | r2_hidden(D_1095,k2_pre_topc('#skF_4',B_95))
      | ~ r2_hidden(D_1095,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5540,c_21505])).

tff(c_21513,plain,(
    ! [B_2783,D_2784] :
      ( ~ r1_xboole_0('#skF_1'('#skF_4',B_2783,k2_pre_topc('#skF_4',B_2783),D_2784),'#skF_5')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_2783,k2_pre_topc('#skF_4',B_2783),D_2784))
      | r2_hidden(D_2784,k2_pre_topc('#skF_4',B_2783))
      | ~ r2_hidden(D_2784,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_2783,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_21509])).

tff(c_21517,plain,(
    ! [B_95] :
      ( ~ r1_xboole_0('#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),'#skF_6'),'#skF_5')
      | r2_hidden('#skF_6',k2_pre_topc('#skF_4',B_95))
      | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5360,c_21513])).

tff(c_21523,plain,(
    ! [B_95] :
      ( ~ r1_xboole_0('#skF_1'('#skF_4',B_95,k2_pre_topc('#skF_4',B_95),'#skF_6'),'#skF_5')
      | r2_hidden('#skF_6',k2_pre_topc('#skF_4',B_95))
      | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_21517])).

tff(c_21525,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_21523])).

tff(c_21528,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_21525])).

tff(c_21531,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_21528])).

tff(c_21533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8542,c_21531])).

tff(c_21535,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_21523])).

tff(c_5228,plain,(
    ! [B_1063,A_1064,D_1065] :
      ( r1_xboole_0(B_1063,'#skF_1'(A_1064,B_1063,k2_pre_topc(A_1064,B_1063),D_1065))
      | r2_hidden(D_1065,k2_pre_topc(A_1064,B_1063))
      | ~ r2_hidden(D_1065,u1_struct_0(A_1064))
      | ~ m1_subset_1(k2_pre_topc(A_1064,B_1063),k1_zfmisc_1(u1_struct_0(A_1064)))
      | ~ m1_subset_1(B_1063,k1_zfmisc_1(u1_struct_0(A_1064)))
      | ~ l1_pre_topc(A_1064) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5232,plain,(
    ! [B_1066,A_1067,D_1068] :
      ( r1_xboole_0(B_1066,'#skF_1'(A_1067,B_1066,k2_pre_topc(A_1067,B_1066),D_1068))
      | r2_hidden(D_1068,k2_pre_topc(A_1067,B_1066))
      | ~ r2_hidden(D_1068,u1_struct_0(A_1067))
      | ~ m1_subset_1(B_1066,k1_zfmisc_1(u1_struct_0(A_1067)))
      | ~ l1_pre_topc(A_1067) ) ),
    inference(resolution,[status(thm)],[c_40,c_5228])).

tff(c_5238,plain,(
    ! [A_1067,B_1066,D_1068] :
      ( r1_xboole_0('#skF_1'(A_1067,B_1066,k2_pre_topc(A_1067,B_1066),D_1068),B_1066)
      | r2_hidden(D_1068,k2_pre_topc(A_1067,B_1066))
      | ~ r2_hidden(D_1068,u1_struct_0(A_1067))
      | ~ m1_subset_1(B_1066,k1_zfmisc_1(u1_struct_0(A_1067)))
      | ~ l1_pre_topc(A_1067) ) ),
    inference(resolution,[status(thm)],[c_5232,c_50])).

tff(c_21583,plain,(
    ! [B_2791] :
      ( ~ r1_xboole_0('#skF_1'('#skF_4',B_2791,k2_pre_topc('#skF_4',B_2791),'#skF_6'),'#skF_5')
      | r2_hidden('#skF_6',k2_pre_topc('#skF_4',B_2791))
      | ~ m1_subset_1(B_2791,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_21523])).

tff(c_21599,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_5238,c_21583])).

tff(c_21620,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_21535,c_21599])).

tff(c_21622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_21620])).

tff(c_21623,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_82,plain,(
    ! [D_142] :
      ( r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
      | ~ r1_xboole_0(D_142,'#skF_5')
      | ~ m1_connsp_2(D_142,'#skF_4','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_21632,plain,(
    ! [D_2792] :
      ( ~ r1_xboole_0(D_2792,'#skF_5')
      | ~ m1_connsp_2(D_2792,'#skF_4','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_82])).

tff(c_21635,plain,(
    ~ r1_xboole_0('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_21623,c_21632])).

tff(c_21639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4411,c_21635])).

tff(c_21641,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_74,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_6')
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_21650,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21641,c_74])).

tff(c_21778,plain,(
    ! [C_2835,A_2836,B_2837] :
      ( m1_subset_1(C_2835,k1_zfmisc_1(u1_struct_0(A_2836)))
      | ~ m1_connsp_2(C_2835,A_2836,B_2837)
      | ~ m1_subset_1(B_2837,u1_struct_0(A_2836))
      | ~ l1_pre_topc(A_2836)
      | ~ v2_pre_topc(A_2836)
      | v2_struct_0(A_2836) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_21780,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_21650,c_21778])).

tff(c_21783,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_21780])).

tff(c_21784,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_21783])).

tff(c_48,plain,(
    ! [A_102,B_103] :
      ( v3_pre_topc(k1_tops_1(A_102,B_103),A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_21786,plain,
    ( v3_pre_topc(k1_tops_1('#skF_4','#skF_7'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_21784,c_48])).

tff(c_21793,plain,(
    v3_pre_topc(k1_tops_1('#skF_4','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_21786])).

tff(c_21879,plain,(
    ! [B_2859,A_2860,C_2861] :
      ( r2_hidden(B_2859,k1_tops_1(A_2860,C_2861))
      | ~ m1_connsp_2(C_2861,A_2860,B_2859)
      | ~ m1_subset_1(C_2861,k1_zfmisc_1(u1_struct_0(A_2860)))
      | ~ m1_subset_1(B_2859,u1_struct_0(A_2860))
      | ~ l1_pre_topc(A_2860)
      | ~ v2_pre_topc(A_2860)
      | v2_struct_0(A_2860) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_21881,plain,(
    ! [B_2859] :
      ( r2_hidden(B_2859,k1_tops_1('#skF_4','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_4',B_2859)
      | ~ m1_subset_1(B_2859,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_21784,c_21879])).

tff(c_21890,plain,(
    ! [B_2859] :
      ( r2_hidden(B_2859,k1_tops_1('#skF_4','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_4',B_2859)
      | ~ m1_subset_1(B_2859,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_21881])).

tff(c_21891,plain,(
    ! [B_2859] :
      ( r2_hidden(B_2859,k1_tops_1('#skF_4','#skF_7'))
      | ~ m1_connsp_2('#skF_7','#skF_4',B_2859)
      | ~ m1_subset_1(B_2859,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_21890])).

tff(c_38,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1(k1_tops_1(A_92,B_93),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22004,plain,(
    ! [B_2889,A_2890,C_2891] :
      ( m1_connsp_2(B_2889,A_2890,C_2891)
      | ~ r2_hidden(C_2891,B_2889)
      | ~ v3_pre_topc(B_2889,A_2890)
      | ~ m1_subset_1(C_2891,u1_struct_0(A_2890))
      | ~ m1_subset_1(B_2889,k1_zfmisc_1(u1_struct_0(A_2890)))
      | ~ l1_pre_topc(A_2890)
      | ~ v2_pre_topc(A_2890)
      | v2_struct_0(A_2890) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_22010,plain,(
    ! [B_2889] :
      ( m1_connsp_2(B_2889,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_2889)
      | ~ v3_pre_topc(B_2889,'#skF_4')
      | ~ m1_subset_1(B_2889,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_22004])).

tff(c_22021,plain,(
    ! [B_2889] :
      ( m1_connsp_2(B_2889,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_2889)
      | ~ v3_pre_topc(B_2889,'#skF_4')
      | ~ m1_subset_1(B_2889,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_22010])).

tff(c_22023,plain,(
    ! [B_2892] :
      ( m1_connsp_2(B_2892,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_2892)
      | ~ v3_pre_topc(B_2892,'#skF_4')
      | ~ m1_subset_1(B_2892,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_22021])).

tff(c_22034,plain,(
    ! [B_93] :
      ( m1_connsp_2(k1_tops_1('#skF_4',B_93),'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',k1_tops_1('#skF_4',B_93))
      | ~ v3_pre_topc(k1_tops_1('#skF_4',B_93),'#skF_4')
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_22023])).

tff(c_22140,plain,(
    ! [B_2903] :
      ( m1_connsp_2(k1_tops_1('#skF_4',B_2903),'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',k1_tops_1('#skF_4',B_2903))
      | ~ v3_pre_topc(k1_tops_1('#skF_4',B_2903),'#skF_4')
      | ~ m1_subset_1(B_2903,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_22034])).

tff(c_22143,plain,
    ( m1_connsp_2(k1_tops_1('#skF_4','#skF_7'),'#skF_4','#skF_6')
    | ~ r2_hidden('#skF_6',k1_tops_1('#skF_4','#skF_7'))
    | ~ v3_pre_topc(k1_tops_1('#skF_4','#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_21784,c_22140])).

tff(c_22157,plain,
    ( m1_connsp_2(k1_tops_1('#skF_4','#skF_7'),'#skF_4','#skF_6')
    | ~ r2_hidden('#skF_6',k1_tops_1('#skF_4','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21793,c_22143])).

tff(c_22167,plain,(
    ~ r2_hidden('#skF_6',k1_tops_1('#skF_4','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_22157])).

tff(c_22170,plain,
    ( ~ m1_connsp_2('#skF_7','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_21891,c_22167])).

tff(c_22177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_21650,c_22170])).

tff(c_22178,plain,(
    m1_connsp_2(k1_tops_1('#skF_4','#skF_7'),'#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_22157])).

tff(c_44,plain,(
    ! [C_100,A_97,B_98] :
      ( m1_subset_1(C_100,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_connsp_2(C_100,A_97,B_98)
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22192,plain,
    ( m1_subset_1(k1_tops_1('#skF_4','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_22178,c_44])).

tff(c_22195,plain,
    ( m1_subset_1(k1_tops_1('#skF_4','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_22192])).

tff(c_22196,plain,(
    m1_subset_1(k1_tops_1('#skF_4','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_22195])).

tff(c_54,plain,(
    ! [A_108,B_110] :
      ( r1_tarski(k1_tops_1(A_108,B_110),B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_21788,plain,
    ( r1_tarski(k1_tops_1('#skF_4','#skF_7'),'#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_21784,c_54])).

tff(c_21796,plain,(
    r1_tarski(k1_tops_1('#skF_4','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_21788])).

tff(c_22179,plain,(
    r2_hidden('#skF_6',k1_tops_1('#skF_4','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_22157])).

tff(c_21640,plain,(
    r1_xboole_0('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_21651,plain,(
    ! [A_2793,C_2794,B_2795] :
      ( r1_xboole_0(A_2793,C_2794)
      | ~ r1_xboole_0(B_2795,C_2794)
      | ~ r1_tarski(A_2793,B_2795) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_21659,plain,(
    ! [A_2796] :
      ( r1_xboole_0(A_2796,'#skF_5')
      | ~ r1_tarski(A_2796,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_21640,c_21651])).

tff(c_21665,plain,(
    ! [A_2796] :
      ( r1_xboole_0('#skF_5',A_2796)
      | ~ r1_tarski(A_2796,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_21659,c_50])).

tff(c_22866,plain,(
    ! [B_2952,E_2953,D_2954,A_2955] :
      ( ~ r1_xboole_0(B_2952,E_2953)
      | ~ r2_hidden(D_2954,E_2953)
      | ~ v3_pre_topc(E_2953,A_2955)
      | ~ m1_subset_1(E_2953,k1_zfmisc_1(u1_struct_0(A_2955)))
      | ~ r2_hidden(D_2954,k2_pre_topc(A_2955,B_2952))
      | ~ r2_hidden(D_2954,u1_struct_0(A_2955))
      | ~ m1_subset_1(k2_pre_topc(A_2955,B_2952),k1_zfmisc_1(u1_struct_0(A_2955)))
      | ~ m1_subset_1(B_2952,k1_zfmisc_1(u1_struct_0(A_2955)))
      | ~ l1_pre_topc(A_2955) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40693,plain,(
    ! [D_4484,A_4485,A_4486] :
      ( ~ r2_hidden(D_4484,A_4485)
      | ~ v3_pre_topc(A_4485,A_4486)
      | ~ m1_subset_1(A_4485,k1_zfmisc_1(u1_struct_0(A_4486)))
      | ~ r2_hidden(D_4484,k2_pre_topc(A_4486,'#skF_5'))
      | ~ r2_hidden(D_4484,u1_struct_0(A_4486))
      | ~ m1_subset_1(k2_pre_topc(A_4486,'#skF_5'),k1_zfmisc_1(u1_struct_0(A_4486)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_4486)))
      | ~ l1_pre_topc(A_4486)
      | ~ r1_tarski(A_4485,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_21665,c_22866])).

tff(c_40741,plain,(
    ! [A_4486] :
      ( ~ v3_pre_topc(k1_tops_1('#skF_4','#skF_7'),A_4486)
      | ~ m1_subset_1(k1_tops_1('#skF_4','#skF_7'),k1_zfmisc_1(u1_struct_0(A_4486)))
      | ~ r2_hidden('#skF_6',k2_pre_topc(A_4486,'#skF_5'))
      | ~ r2_hidden('#skF_6',u1_struct_0(A_4486))
      | ~ m1_subset_1(k2_pre_topc(A_4486,'#skF_5'),k1_zfmisc_1(u1_struct_0(A_4486)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_4486)))
      | ~ l1_pre_topc(A_4486)
      | ~ r1_tarski(k1_tops_1('#skF_4','#skF_7'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_22179,c_40693])).

tff(c_46577,plain,(
    ! [A_4901] :
      ( ~ v3_pre_topc(k1_tops_1('#skF_4','#skF_7'),A_4901)
      | ~ m1_subset_1(k1_tops_1('#skF_4','#skF_7'),k1_zfmisc_1(u1_struct_0(A_4901)))
      | ~ r2_hidden('#skF_6',k2_pre_topc(A_4901,'#skF_5'))
      | ~ r2_hidden('#skF_6',u1_struct_0(A_4901))
      | ~ m1_subset_1(k2_pre_topc(A_4901,'#skF_5'),k1_zfmisc_1(u1_struct_0(A_4901)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_4901)))
      | ~ l1_pre_topc(A_4901) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21796,c_40741])).

tff(c_46742,plain,(
    ! [A_4905] :
      ( ~ v3_pre_topc(k1_tops_1('#skF_4','#skF_7'),A_4905)
      | ~ m1_subset_1(k1_tops_1('#skF_4','#skF_7'),k1_zfmisc_1(u1_struct_0(A_4905)))
      | ~ r2_hidden('#skF_6',k2_pre_topc(A_4905,'#skF_5'))
      | ~ r2_hidden('#skF_6',u1_struct_0(A_4905))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_4905)))
      | ~ l1_pre_topc(A_4905) ) ),
    inference(resolution,[status(thm)],[c_40,c_46577])).

tff(c_46745,plain,
    ( ~ v3_pre_topc(k1_tops_1('#skF_4','#skF_7'),'#skF_4')
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22196,c_46742])).

tff(c_46752,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_21641,c_21793,c_46745])).

tff(c_46758,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_46752])).

tff(c_46761,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_46758])).

tff(c_46763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28451,c_46761])).

%------------------------------------------------------------------------------
