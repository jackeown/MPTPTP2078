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
% DateTime   : Thu Dec  3 10:21:13 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 168 expanded)
%              Number of leaves         :   40 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  150 ( 329 expanded)
%              Number of equality atoms :   52 (  95 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_7134,plain,(
    ! [A_221,B_222,C_223] :
      ( k7_subset_1(A_221,B_222,C_223) = k4_xboole_0(B_222,C_223)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(A_221)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7137,plain,(
    ! [C_223] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_223) = k4_xboole_0('#skF_2',C_223) ),
    inference(resolution,[status(thm)],[c_38,c_7134])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_148,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2199,plain,(
    ! [A_123,B_124] :
      ( k4_subset_1(u1_struct_0(A_123),B_124,k2_tops_1(A_123,B_124)) = k2_pre_topc(A_123,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2203,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_2199])).

tff(c_2207,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2203])).

tff(c_603,plain,(
    ! [A_84,B_85,C_86] :
      ( k7_subset_1(A_84,B_85,C_86) = k4_xboole_0(B_85,C_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_607,plain,(
    ! [C_87] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_87) = k4_xboole_0('#skF_2',C_87) ),
    inference(resolution,[status(thm)],[c_38,c_603])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_287,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_50])).

tff(c_613,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_287])).

tff(c_10,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_429,plain,(
    ! [A_74,B_75] : k2_xboole_0(k5_xboole_0(A_74,B_75),k3_xboole_0(A_74,B_75)) = k2_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_453,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k3_xboole_0(A_3,k3_xboole_0(A_3,B_4))) = k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_429])).

tff(c_471,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k3_xboole_0(A_3,k3_xboole_0(A_3,B_4))) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_453])).

tff(c_16,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_125,plain,(
    ! [B_53,A_54] : k3_tarski(k2_tarski(B_53,A_54)) = k2_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_95])).

tff(c_18,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    ! [B_53,A_54] : k2_xboole_0(B_53,A_54) = k2_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_18])).

tff(c_473,plain,(
    ! [A_76,B_77] : k2_xboole_0(k4_xboole_0(A_76,B_77),k3_xboole_0(A_76,k3_xboole_0(A_76,B_77))) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_453])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_482,plain,(
    ! [A_76,B_77] : k2_xboole_0(k4_xboole_0(A_76,B_77),k3_xboole_0(A_76,k3_xboole_0(A_76,B_77))) = k2_xboole_0(k4_xboole_0(A_76,B_77),A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_12])).

tff(c_494,plain,(
    ! [A_76,B_77] : k2_xboole_0(A_76,k4_xboole_0(A_76,B_77)) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_131,c_482])).

tff(c_628,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_494])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k2_tops_1(A_26,B_27),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1340,plain,(
    ! [A_110,B_111,C_112] :
      ( k4_subset_1(A_110,B_111,C_112) = k2_xboole_0(B_111,C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(A_110))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6039,plain,(
    ! [A_188,B_189,B_190] :
      ( k4_subset_1(u1_struct_0(A_188),B_189,k2_tops_1(A_188,B_190)) = k2_xboole_0(B_189,k2_tops_1(A_188,B_190))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(resolution,[status(thm)],[c_28,c_1340])).

tff(c_6043,plain,(
    ! [B_190] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_190)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_190))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_6039])).

tff(c_6752,plain,(
    ! [B_195] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_195)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_195))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6043])).

tff(c_6759,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_6752])).

tff(c_6764,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2207,c_628,c_6759])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1323,plain,(
    ! [A_108,B_109] :
      ( v4_pre_topc(k2_pre_topc(A_108,B_109),A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1327,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1323])).

tff(c_1331,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1327])).

tff(c_6767,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6764,c_1331])).

tff(c_6771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_6767])).

tff(c_6772,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_7138,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7137,c_6772])).

tff(c_7179,plain,(
    ! [B_227,A_228] :
      ( r1_tarski(B_227,k2_pre_topc(A_228,B_227))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_7181,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_7179])).

tff(c_7184,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7181])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7187,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_7184,c_2])).

tff(c_7188,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_7187])).

tff(c_6773,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8517,plain,(
    ! [A_269,C_270,B_271] :
      ( r1_tarski(k2_pre_topc(A_269,C_270),B_271)
      | ~ r1_tarski(C_270,B_271)
      | ~ v4_pre_topc(B_271,A_269)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ l1_pre_topc(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8521,plain,(
    ! [B_271] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_271)
      | ~ r1_tarski('#skF_2',B_271)
      | ~ v4_pre_topc(B_271,'#skF_1')
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_8517])).

tff(c_8685,plain,(
    ! [B_278] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_278)
      | ~ r1_tarski('#skF_2',B_278)
      | ~ v4_pre_topc(B_278,'#skF_1')
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8521])).

tff(c_8692,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_8685])).

tff(c_8698,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6773,c_6,c_8692])).

tff(c_8700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7188,c_8698])).

tff(c_8701,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7187])).

tff(c_9512,plain,(
    ! [A_310,B_311] :
      ( k7_subset_1(u1_struct_0(A_310),k2_pre_topc(A_310,B_311),k1_tops_1(A_310,B_311)) = k2_tops_1(A_310,B_311)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ l1_pre_topc(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9521,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8701,c_9512])).

tff(c_9525,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_7137,c_9521])).

tff(c_9527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7138,c_9525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:41:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.68/2.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/2.73  
% 7.68/2.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.68/2.73  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 7.68/2.73  
% 7.68/2.73  %Foreground sorts:
% 7.68/2.73  
% 7.68/2.73  
% 7.68/2.73  %Background operators:
% 7.68/2.73  
% 7.68/2.73  
% 7.68/2.73  %Foreground operators:
% 7.68/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.68/2.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.68/2.73  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.68/2.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.68/2.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.68/2.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.68/2.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.68/2.73  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.68/2.73  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.68/2.73  tff('#skF_2', type, '#skF_2': $i).
% 7.68/2.73  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.68/2.73  tff('#skF_1', type, '#skF_1': $i).
% 7.68/2.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.68/2.73  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.68/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.68/2.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.68/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.68/2.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.68/2.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.68/2.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.68/2.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.68/2.73  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.68/2.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.68/2.73  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.68/2.73  
% 7.77/2.75  tff(f_116, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 7.77/2.75  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.77/2.75  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 7.77/2.75  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 7.77/2.75  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.77/2.75  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 7.77/2.75  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.77/2.75  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.77/2.75  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 7.77/2.75  tff(f_68, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 7.77/2.75  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.77/2.75  tff(f_76, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 7.77/2.75  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 7.77/2.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.77/2.75  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_1)).
% 7.77/2.75  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 7.77/2.75  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.77/2.75  tff(c_7134, plain, (![A_221, B_222, C_223]: (k7_subset_1(A_221, B_222, C_223)=k4_xboole_0(B_222, C_223) | ~m1_subset_1(B_222, k1_zfmisc_1(A_221)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.77/2.75  tff(c_7137, plain, (![C_223]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_223)=k4_xboole_0('#skF_2', C_223))), inference(resolution, [status(thm)], [c_38, c_7134])).
% 7.77/2.75  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.77/2.75  tff(c_148, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 7.77/2.75  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.77/2.75  tff(c_2199, plain, (![A_123, B_124]: (k4_subset_1(u1_struct_0(A_123), B_124, k2_tops_1(A_123, B_124))=k2_pre_topc(A_123, B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.77/2.75  tff(c_2203, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_2199])).
% 7.77/2.75  tff(c_2207, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2203])).
% 7.77/2.75  tff(c_603, plain, (![A_84, B_85, C_86]: (k7_subset_1(A_84, B_85, C_86)=k4_xboole_0(B_85, C_86) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.77/2.75  tff(c_607, plain, (![C_87]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_87)=k4_xboole_0('#skF_2', C_87))), inference(resolution, [status(thm)], [c_38, c_603])).
% 7.77/2.75  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.77/2.75  tff(c_287, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_148, c_50])).
% 7.77/2.75  tff(c_613, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_607, c_287])).
% 7.77/2.75  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.77/2.75  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.77/2.75  tff(c_429, plain, (![A_74, B_75]: (k2_xboole_0(k5_xboole_0(A_74, B_75), k3_xboole_0(A_74, B_75))=k2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.77/2.75  tff(c_453, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k3_xboole_0(A_3, k3_xboole_0(A_3, B_4)))=k2_xboole_0(A_3, k3_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_429])).
% 7.77/2.75  tff(c_471, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k3_xboole_0(A_3, k3_xboole_0(A_3, B_4)))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_453])).
% 7.77/2.75  tff(c_16, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.77/2.75  tff(c_95, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.77/2.75  tff(c_125, plain, (![B_53, A_54]: (k3_tarski(k2_tarski(B_53, A_54))=k2_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_16, c_95])).
% 7.77/2.75  tff(c_18, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.77/2.75  tff(c_131, plain, (![B_53, A_54]: (k2_xboole_0(B_53, A_54)=k2_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_125, c_18])).
% 7.77/2.75  tff(c_473, plain, (![A_76, B_77]: (k2_xboole_0(k4_xboole_0(A_76, B_77), k3_xboole_0(A_76, k3_xboole_0(A_76, B_77)))=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_453])).
% 7.77/2.75  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.77/2.75  tff(c_482, plain, (![A_76, B_77]: (k2_xboole_0(k4_xboole_0(A_76, B_77), k3_xboole_0(A_76, k3_xboole_0(A_76, B_77)))=k2_xboole_0(k4_xboole_0(A_76, B_77), A_76))), inference(superposition, [status(thm), theory('equality')], [c_473, c_12])).
% 7.77/2.75  tff(c_494, plain, (![A_76, B_77]: (k2_xboole_0(A_76, k4_xboole_0(A_76, B_77))=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_471, c_131, c_482])).
% 7.77/2.75  tff(c_628, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_613, c_494])).
% 7.77/2.75  tff(c_28, plain, (![A_26, B_27]: (m1_subset_1(k2_tops_1(A_26, B_27), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.77/2.75  tff(c_1340, plain, (![A_110, B_111, C_112]: (k4_subset_1(A_110, B_111, C_112)=k2_xboole_0(B_111, C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(A_110)) | ~m1_subset_1(B_111, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.77/2.75  tff(c_6039, plain, (![A_188, B_189, B_190]: (k4_subset_1(u1_struct_0(A_188), B_189, k2_tops_1(A_188, B_190))=k2_xboole_0(B_189, k2_tops_1(A_188, B_190)) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(resolution, [status(thm)], [c_28, c_1340])).
% 7.77/2.75  tff(c_6043, plain, (![B_190]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_190))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_190)) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_6039])).
% 7.77/2.75  tff(c_6752, plain, (![B_195]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_195))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_195)) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6043])).
% 7.77/2.75  tff(c_6759, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_6752])).
% 7.77/2.75  tff(c_6764, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2207, c_628, c_6759])).
% 7.77/2.75  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.77/2.75  tff(c_1323, plain, (![A_108, B_109]: (v4_pre_topc(k2_pre_topc(A_108, B_109), A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.77/2.75  tff(c_1327, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1323])).
% 7.77/2.75  tff(c_1331, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1327])).
% 7.77/2.75  tff(c_6767, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6764, c_1331])).
% 7.77/2.75  tff(c_6771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_6767])).
% 7.77/2.75  tff(c_6772, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 7.77/2.75  tff(c_7138, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7137, c_6772])).
% 7.77/2.75  tff(c_7179, plain, (![B_227, A_228]: (r1_tarski(B_227, k2_pre_topc(A_228, B_227)) | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.77/2.75  tff(c_7181, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_7179])).
% 7.77/2.75  tff(c_7184, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7181])).
% 7.77/2.75  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.77/2.75  tff(c_7187, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_7184, c_2])).
% 7.77/2.75  tff(c_7188, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_7187])).
% 7.77/2.75  tff(c_6773, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 7.77/2.75  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.77/2.75  tff(c_8517, plain, (![A_269, C_270, B_271]: (r1_tarski(k2_pre_topc(A_269, C_270), B_271) | ~r1_tarski(C_270, B_271) | ~v4_pre_topc(B_271, A_269) | ~m1_subset_1(C_270, k1_zfmisc_1(u1_struct_0(A_269))) | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0(A_269))) | ~l1_pre_topc(A_269))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.77/2.75  tff(c_8521, plain, (![B_271]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_271) | ~r1_tarski('#skF_2', B_271) | ~v4_pre_topc(B_271, '#skF_1') | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_8517])).
% 7.77/2.75  tff(c_8685, plain, (![B_278]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_278) | ~r1_tarski('#skF_2', B_278) | ~v4_pre_topc(B_278, '#skF_1') | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8521])).
% 7.77/2.75  tff(c_8692, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_8685])).
% 7.77/2.75  tff(c_8698, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6773, c_6, c_8692])).
% 7.77/2.75  tff(c_8700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7188, c_8698])).
% 7.77/2.75  tff(c_8701, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_7187])).
% 7.77/2.75  tff(c_9512, plain, (![A_310, B_311]: (k7_subset_1(u1_struct_0(A_310), k2_pre_topc(A_310, B_311), k1_tops_1(A_310, B_311))=k2_tops_1(A_310, B_311) | ~m1_subset_1(B_311, k1_zfmisc_1(u1_struct_0(A_310))) | ~l1_pre_topc(A_310))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.77/2.75  tff(c_9521, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8701, c_9512])).
% 7.77/2.75  tff(c_9525, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_7137, c_9521])).
% 7.77/2.75  tff(c_9527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7138, c_9525])).
% 7.77/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.77/2.75  
% 7.77/2.75  Inference rules
% 7.77/2.75  ----------------------
% 7.77/2.75  #Ref     : 0
% 7.77/2.75  #Sup     : 2337
% 7.77/2.75  #Fact    : 0
% 7.77/2.75  #Define  : 0
% 7.77/2.75  #Split   : 3
% 7.77/2.75  #Chain   : 0
% 7.77/2.75  #Close   : 0
% 7.77/2.75  
% 7.77/2.75  Ordering : KBO
% 7.77/2.75  
% 7.77/2.75  Simplification rules
% 7.77/2.75  ----------------------
% 7.77/2.75  #Subsume      : 52
% 7.77/2.75  #Demod        : 4968
% 7.77/2.75  #Tautology    : 1789
% 7.77/2.75  #SimpNegUnit  : 5
% 7.77/2.75  #BackRed      : 6
% 7.77/2.75  
% 7.77/2.75  #Partial instantiations: 0
% 7.77/2.75  #Strategies tried      : 1
% 7.77/2.75  
% 7.77/2.75  Timing (in seconds)
% 7.77/2.75  ----------------------
% 7.77/2.75  Preprocessing        : 0.34
% 7.77/2.76  Parsing              : 0.18
% 7.77/2.76  CNF conversion       : 0.02
% 7.77/2.76  Main loop            : 1.64
% 7.77/2.76  Inferencing          : 0.42
% 7.77/2.76  Reduction            : 0.95
% 7.77/2.76  Demodulation         : 0.85
% 7.77/2.76  BG Simplification    : 0.04
% 7.77/2.76  Subsumption          : 0.16
% 7.77/2.76  Abstraction          : 0.09
% 7.77/2.76  MUC search           : 0.00
% 7.77/2.76  Cooper               : 0.00
% 7.77/2.76  Total                : 2.01
% 7.77/2.76  Index Insertion      : 0.00
% 7.77/2.76  Index Deletion       : 0.00
% 7.77/2.76  Index Matching       : 0.00
% 7.77/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
