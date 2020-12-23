%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:52 EST 2020

% Result     : Theorem 13.82s
% Output     : CNFRefutation 14.05s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 231 expanded)
%              Number of leaves         :   40 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  135 ( 410 expanded)
%              Number of equality atoms :   47 (  99 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_87,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_79,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_308,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(A_90,B_91)
      | k4_xboole_0(A_90,B_91) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_316,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_308,c_62])).

tff(c_68,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3578,plain,(
    ! [A_199,B_200] :
      ( k4_subset_1(u1_struct_0(A_199),B_200,k2_tops_1(A_199,B_200)) = k2_pre_topc(A_199,B_200)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3605,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_3578])).

tff(c_3619,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3605])).

tff(c_2377,plain,(
    ! [A_161,B_162] :
      ( k4_xboole_0(A_161,B_162) = k3_subset_1(A_161,B_162)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(A_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2404,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_2377])).

tff(c_46,plain,(
    ! [A_40,B_41] : k6_subset_1(A_40,B_41) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_42,plain,(
    ! [A_35,B_36] : m1_subset_1(k6_subset_1(A_35,B_36),k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_69,plain,(
    ! [A_35,B_36] : m1_subset_1(k4_xboole_0(A_35,B_36),k1_zfmisc_1(A_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42])).

tff(c_2462,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2404,c_69])).

tff(c_3413,plain,(
    ! [A_195,B_196] :
      ( k2_tops_1(A_195,k3_subset_1(u1_struct_0(A_195),B_196)) = k2_tops_1(A_195,B_196)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3440,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_3413])).

tff(c_3455,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3440])).

tff(c_54,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k2_tops_1(A_46,B_47),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3737,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3455,c_54])).

tff(c_3741,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2462,c_3737])).

tff(c_50,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4041,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3741,c_50])).

tff(c_52,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(A_44,k1_zfmisc_1(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3152,plain,(
    ! [A_187,B_188,C_189] :
      ( k4_subset_1(A_187,B_188,C_189) = k2_xboole_0(B_188,C_189)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(A_187))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(A_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_19734,plain,(
    ! [B_410,B_411,A_412] :
      ( k4_subset_1(B_410,B_411,A_412) = k2_xboole_0(B_411,A_412)
      | ~ m1_subset_1(B_411,k1_zfmisc_1(B_410))
      | ~ r1_tarski(A_412,B_410) ) ),
    inference(resolution,[status(thm)],[c_52,c_3152])).

tff(c_20264,plain,(
    ! [A_417] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_417) = k2_xboole_0('#skF_2',A_417)
      | ~ r1_tarski(A_417,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_66,c_19734])).

tff(c_20345,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4041,c_20264])).

tff(c_20407,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3619,c_20345])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_471,plain,(
    ! [A_103,B_104] :
      ( k2_xboole_0(A_103,B_104) = B_104
      | ~ r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_502,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_471])).

tff(c_64,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3744,plain,(
    ! [A_203,C_204,B_205] :
      ( r1_tarski(k2_pre_topc(A_203,C_204),B_205)
      | ~ r1_tarski(C_204,B_205)
      | ~ v4_pre_topc(B_205,A_203)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3771,plain,(
    ! [B_205] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_205)
      | ~ r1_tarski('#skF_2',B_205)
      | ~ v4_pre_topc(B_205,'#skF_1')
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_3744])).

tff(c_12402,plain,(
    ! [B_356] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_356)
      | ~ r1_tarski('#skF_2',B_356)
      | ~ v4_pre_topc(B_356,'#skF_1')
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3771])).

tff(c_12443,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_12402])).

tff(c_12460,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_8,c_12443])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12491,plain,(
    k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12460,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5722,plain,(
    ! [A_233,B_234] : k2_xboole_0(A_233,k2_xboole_0(A_233,B_234)) = k2_xboole_0(A_233,B_234) ),
    inference(resolution,[status(thm)],[c_34,c_471])).

tff(c_5852,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5722])).

tff(c_12509,plain,(
    k2_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12491,c_5852])).

tff(c_12614,plain,(
    k2_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_12509])).

tff(c_24,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_503,plain,(
    ! [A_18] : k2_xboole_0(k1_xboole_0,A_18) = A_18 ),
    inference(resolution,[status(thm)],[c_24,c_471])).

tff(c_332,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,B_95) = k1_xboole_0
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_353,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k2_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_332])).

tff(c_1285,plain,(
    ! [A_132,B_133] : k2_xboole_0(A_132,k4_xboole_0(B_133,A_132)) = k2_xboole_0(A_132,B_133) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1328,plain,(
    ! [A_27,B_28] : k2_xboole_0(k2_xboole_0(A_27,B_28),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_27,B_28),A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_1285])).

tff(c_1355,plain,(
    ! [A_27,B_28] : k2_xboole_0(k2_xboole_0(A_27,B_28),A_27) = k2_xboole_0(A_27,B_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_2,c_1328])).

tff(c_41015,plain,(
    k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20407,c_1355])).

tff(c_41138,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20407,c_12614,c_2,c_41015])).

tff(c_41150,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41138,c_20407])).

tff(c_131,plain,(
    ! [B_76,A_77] : k2_xboole_0(B_76,A_77) = k2_xboole_0(A_77,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_146,plain,(
    ! [A_77,B_76] : r1_tarski(A_77,k2_xboole_0(B_76,A_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_34])).

tff(c_352,plain,(
    ! [A_77,B_76] : k4_xboole_0(A_77,k2_xboole_0(B_76,A_77)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_146,c_332])).

tff(c_41550,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_41150,c_352])).

tff(c_41609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_41550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.82/6.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.82/6.66  
% 13.82/6.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.82/6.66  %$ v4_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 13.82/6.66  
% 13.82/6.66  %Foreground sorts:
% 13.82/6.66  
% 13.82/6.66  
% 13.82/6.66  %Background operators:
% 13.82/6.66  
% 13.82/6.66  
% 13.82/6.66  %Foreground operators:
% 13.82/6.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.82/6.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.82/6.66  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 13.82/6.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.82/6.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.82/6.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.82/6.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.82/6.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.82/6.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 13.82/6.66  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 13.82/6.66  tff('#skF_2', type, '#skF_2': $i).
% 13.82/6.66  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 13.82/6.66  tff('#skF_1', type, '#skF_1': $i).
% 13.82/6.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.82/6.66  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 13.82/6.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.82/6.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.82/6.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.82/6.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.82/6.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.82/6.66  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 13.82/6.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.82/6.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.82/6.66  
% 14.05/6.67  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 14.05/6.67  tff(f_137, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 14.05/6.67  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 14.05/6.67  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 14.05/6.67  tff(f_87, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 14.05/6.67  tff(f_79, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 14.05/6.67  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 14.05/6.67  tff(f_99, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 14.05/6.67  tff(f_93, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.05/6.67  tff(f_85, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 14.05/6.67  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.05/6.67  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 14.05/6.67  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 14.05/6.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 14.05/6.67  tff(f_67, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 14.05/6.67  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 14.05/6.67  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.05/6.67  tff(c_308, plain, (![A_90, B_91]: (r1_tarski(A_90, B_91) | k4_xboole_0(A_90, B_91)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.05/6.67  tff(c_62, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 14.05/6.67  tff(c_316, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_308, c_62])).
% 14.05/6.67  tff(c_68, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 14.05/6.67  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 14.05/6.67  tff(c_3578, plain, (![A_199, B_200]: (k4_subset_1(u1_struct_0(A_199), B_200, k2_tops_1(A_199, B_200))=k2_pre_topc(A_199, B_200) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199))), inference(cnfTransformation, [status(thm)], [f_127])).
% 14.05/6.67  tff(c_3605, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_3578])).
% 14.05/6.67  tff(c_3619, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3605])).
% 14.05/6.67  tff(c_2377, plain, (![A_161, B_162]: (k4_xboole_0(A_161, B_162)=k3_subset_1(A_161, B_162) | ~m1_subset_1(B_162, k1_zfmisc_1(A_161)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 14.05/6.67  tff(c_2404, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_66, c_2377])).
% 14.05/6.67  tff(c_46, plain, (![A_40, B_41]: (k6_subset_1(A_40, B_41)=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.05/6.67  tff(c_42, plain, (![A_35, B_36]: (m1_subset_1(k6_subset_1(A_35, B_36), k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.05/6.67  tff(c_69, plain, (![A_35, B_36]: (m1_subset_1(k4_xboole_0(A_35, B_36), k1_zfmisc_1(A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42])).
% 14.05/6.67  tff(c_2462, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2404, c_69])).
% 14.05/6.67  tff(c_3413, plain, (![A_195, B_196]: (k2_tops_1(A_195, k3_subset_1(u1_struct_0(A_195), B_196))=k2_tops_1(A_195, B_196) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.05/6.67  tff(c_3440, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_3413])).
% 14.05/6.67  tff(c_3455, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3440])).
% 14.05/6.67  tff(c_54, plain, (![A_46, B_47]: (m1_subset_1(k2_tops_1(A_46, B_47), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.05/6.67  tff(c_3737, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3455, c_54])).
% 14.05/6.67  tff(c_3741, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2462, c_3737])).
% 14.05/6.67  tff(c_50, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.05/6.67  tff(c_4041, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_3741, c_50])).
% 14.05/6.67  tff(c_52, plain, (![A_44, B_45]: (m1_subset_1(A_44, k1_zfmisc_1(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_93])).
% 14.05/6.67  tff(c_3152, plain, (![A_187, B_188, C_189]: (k4_subset_1(A_187, B_188, C_189)=k2_xboole_0(B_188, C_189) | ~m1_subset_1(C_189, k1_zfmisc_1(A_187)) | ~m1_subset_1(B_188, k1_zfmisc_1(A_187)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.05/6.67  tff(c_19734, plain, (![B_410, B_411, A_412]: (k4_subset_1(B_410, B_411, A_412)=k2_xboole_0(B_411, A_412) | ~m1_subset_1(B_411, k1_zfmisc_1(B_410)) | ~r1_tarski(A_412, B_410))), inference(resolution, [status(thm)], [c_52, c_3152])).
% 14.05/6.67  tff(c_20264, plain, (![A_417]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_417)=k2_xboole_0('#skF_2', A_417) | ~r1_tarski(A_417, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_66, c_19734])).
% 14.05/6.67  tff(c_20345, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4041, c_20264])).
% 14.05/6.67  tff(c_20407, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3619, c_20345])).
% 14.05/6.67  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.05/6.67  tff(c_471, plain, (![A_103, B_104]: (k2_xboole_0(A_103, B_104)=B_104 | ~r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.05/6.67  tff(c_502, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_471])).
% 14.05/6.67  tff(c_64, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 14.05/6.67  tff(c_3744, plain, (![A_203, C_204, B_205]: (r1_tarski(k2_pre_topc(A_203, C_204), B_205) | ~r1_tarski(C_204, B_205) | ~v4_pre_topc(B_205, A_203) | ~m1_subset_1(C_204, k1_zfmisc_1(u1_struct_0(A_203))) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_pre_topc(A_203))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.05/6.67  tff(c_3771, plain, (![B_205]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_205) | ~r1_tarski('#skF_2', B_205) | ~v4_pre_topc(B_205, '#skF_1') | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_3744])).
% 14.05/6.67  tff(c_12402, plain, (![B_356]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_356) | ~r1_tarski('#skF_2', B_356) | ~v4_pre_topc(B_356, '#skF_1') | ~m1_subset_1(B_356, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3771])).
% 14.05/6.67  tff(c_12443, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_12402])).
% 14.05/6.67  tff(c_12460, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_8, c_12443])).
% 14.05/6.67  tff(c_16, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.05/6.67  tff(c_12491, plain, (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_12460, c_16])).
% 14.05/6.67  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.05/6.67  tff(c_34, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.05/6.67  tff(c_5722, plain, (![A_233, B_234]: (k2_xboole_0(A_233, k2_xboole_0(A_233, B_234))=k2_xboole_0(A_233, B_234))), inference(resolution, [status(thm)], [c_34, c_471])).
% 14.05/6.67  tff(c_5852, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5722])).
% 14.05/6.67  tff(c_12509, plain, (k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12491, c_5852])).
% 14.05/6.67  tff(c_12614, plain, (k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_502, c_12509])).
% 14.05/6.67  tff(c_24, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.05/6.67  tff(c_503, plain, (![A_18]: (k2_xboole_0(k1_xboole_0, A_18)=A_18)), inference(resolution, [status(thm)], [c_24, c_471])).
% 14.05/6.67  tff(c_332, plain, (![A_94, B_95]: (k4_xboole_0(A_94, B_95)=k1_xboole_0 | ~r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.05/6.67  tff(c_353, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k2_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_332])).
% 14.05/6.67  tff(c_1285, plain, (![A_132, B_133]: (k2_xboole_0(A_132, k4_xboole_0(B_133, A_132))=k2_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.05/6.67  tff(c_1328, plain, (![A_27, B_28]: (k2_xboole_0(k2_xboole_0(A_27, B_28), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_27, B_28), A_27))), inference(superposition, [status(thm), theory('equality')], [c_353, c_1285])).
% 14.05/6.67  tff(c_1355, plain, (![A_27, B_28]: (k2_xboole_0(k2_xboole_0(A_27, B_28), A_27)=k2_xboole_0(A_27, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_2, c_1328])).
% 14.05/6.67  tff(c_41015, plain, (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_20407, c_1355])).
% 14.05/6.67  tff(c_41138, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20407, c_12614, c_2, c_41015])).
% 14.05/6.67  tff(c_41150, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_41138, c_20407])).
% 14.05/6.67  tff(c_131, plain, (![B_76, A_77]: (k2_xboole_0(B_76, A_77)=k2_xboole_0(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.05/6.67  tff(c_146, plain, (![A_77, B_76]: (r1_tarski(A_77, k2_xboole_0(B_76, A_77)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_34])).
% 14.05/6.67  tff(c_352, plain, (![A_77, B_76]: (k4_xboole_0(A_77, k2_xboole_0(B_76, A_77))=k1_xboole_0)), inference(resolution, [status(thm)], [c_146, c_332])).
% 14.05/6.67  tff(c_41550, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_41150, c_352])).
% 14.05/6.67  tff(c_41609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_41550])).
% 14.05/6.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.05/6.67  
% 14.05/6.67  Inference rules
% 14.05/6.67  ----------------------
% 14.05/6.67  #Ref     : 1
% 14.05/6.67  #Sup     : 10548
% 14.05/6.67  #Fact    : 0
% 14.05/6.67  #Define  : 0
% 14.05/6.67  #Split   : 2
% 14.05/6.67  #Chain   : 0
% 14.05/6.67  #Close   : 0
% 14.05/6.67  
% 14.05/6.67  Ordering : KBO
% 14.05/6.67  
% 14.05/6.67  Simplification rules
% 14.05/6.67  ----------------------
% 14.05/6.67  #Subsume      : 1285
% 14.05/6.67  #Demod        : 8532
% 14.05/6.67  #Tautology    : 6057
% 14.05/6.67  #SimpNegUnit  : 93
% 14.05/6.67  #BackRed      : 19
% 14.05/6.67  
% 14.05/6.67  #Partial instantiations: 0
% 14.05/6.67  #Strategies tried      : 1
% 14.05/6.67  
% 14.05/6.67  Timing (in seconds)
% 14.05/6.67  ----------------------
% 14.05/6.68  Preprocessing        : 0.36
% 14.05/6.68  Parsing              : 0.19
% 14.05/6.68  CNF conversion       : 0.02
% 14.05/6.68  Main loop            : 5.55
% 14.05/6.68  Inferencing          : 0.90
% 14.05/6.68  Reduction            : 3.20
% 14.05/6.68  Demodulation         : 2.78
% 14.05/6.68  BG Simplification    : 0.11
% 14.05/6.68  Subsumption          : 1.07
% 14.05/6.68  Abstraction          : 0.19
% 14.05/6.68  MUC search           : 0.00
% 14.05/6.68  Cooper               : 0.00
% 14.05/6.68  Total                : 5.94
% 14.05/6.68  Index Insertion      : 0.00
% 14.05/6.68  Index Deletion       : 0.00
% 14.05/6.68  Index Matching       : 0.00
% 14.05/6.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
