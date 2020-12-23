%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:01 EST 2020

% Result     : Theorem 42.62s
% Output     : CNFRefutation 42.86s
% Verified   : 
% Statistics : Number of formulae       :  204 (1235 expanded)
%              Number of leaves         :   56 ( 441 expanded)
%              Depth                    :   23
%              Number of atoms          :  295 (1876 expanded)
%              Number of equality atoms :  119 ( 868 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_177,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_158,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_86,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_67,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_99,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_165,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_74,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_272,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_3790,plain,(
    ! [A_245,B_246] :
      ( k4_subset_1(u1_struct_0(A_245),B_246,k2_tops_1(A_245,B_246)) = k2_pre_topc(A_245,B_246)
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3813,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_3790])).

tff(c_3829,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3813])).

tff(c_1656,plain,(
    ! [A_183,B_184] :
      ( k4_xboole_0(A_183,B_184) = k3_subset_1(A_183,B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(A_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1686,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1656])).

tff(c_40,plain,(
    ! [A_38,B_39] : k6_subset_1(A_38,B_39) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    ! [A_26,B_27] : m1_subset_1(k6_subset_1(A_26,B_27),k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_81,plain,(
    ! [A_26,B_27] : m1_subset_1(k4_xboole_0(A_26,B_27),k1_zfmisc_1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30])).

tff(c_1812,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1686,c_81])).

tff(c_2950,plain,(
    ! [A_226,B_227] :
      ( k2_tops_1(A_226,k3_subset_1(u1_struct_0(A_226),B_227)) = k2_tops_1(A_226,B_227)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2973,plain,
    ( k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2950])).

tff(c_2991,plain,(
    k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2973])).

tff(c_54,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k2_tops_1(A_53,B_54),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3883,plain,
    ( m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2991,c_54])).

tff(c_3887,plain,(
    m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1812,c_3883])).

tff(c_48,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3930,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3887,c_48])).

tff(c_50,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(A_49,k1_zfmisc_1(B_50))
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2727,plain,(
    ! [A_216,B_217,C_218] :
      ( k4_subset_1(A_216,B_217,C_218) = k2_xboole_0(B_217,C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(A_216))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(A_216)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_25483,plain,(
    ! [B_496,B_497,A_498] :
      ( k4_subset_1(B_496,B_497,A_498) = k2_xboole_0(B_497,A_498)
      | ~ m1_subset_1(B_497,k1_zfmisc_1(B_496))
      | ~ r1_tarski(A_498,B_496) ) ),
    inference(resolution,[status(thm)],[c_50,c_2727])).

tff(c_25867,plain,(
    ! [A_503] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_503) = k2_xboole_0('#skF_3',A_503)
      | ~ r1_tarski(A_503,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_68,c_25483])).

tff(c_25941,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3930,c_25867])).

tff(c_26069,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3829,c_25941])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [B_21,A_20] : k2_tarski(B_21,A_20) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_238,plain,(
    ! [A_92,B_93] : k1_setfam_1(k2_tarski(A_92,B_93)) = k3_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_302,plain,(
    ! [B_105,A_106] : k1_setfam_1(k2_tarski(B_105,A_106)) = k3_xboole_0(A_106,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_238])).

tff(c_46,plain,(
    ! [A_47,B_48] : k1_setfam_1(k2_tarski(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_308,plain,(
    ! [B_105,A_106] : k3_xboole_0(B_105,A_106) = k3_xboole_0(A_106,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_46])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1289,plain,(
    ! [A_171,B_172,C_173] :
      ( r1_tarski(k4_xboole_0(A_171,B_172),C_173)
      | ~ r1_tarski(A_171,k2_xboole_0(B_172,C_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_143,plain,(
    ! [B_88,A_89] : k2_xboole_0(B_88,A_89) = k2_xboole_0(A_89,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_196,plain,(
    ! [A_90] : k2_xboole_0(k1_xboole_0,A_90) = A_90 ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_12])).

tff(c_208,plain,(
    ! [A_90] : r1_tarski(k1_xboole_0,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_22])).

tff(c_400,plain,(
    ! [B_113,A_114] :
      ( B_113 = A_114
      | ~ r1_tarski(B_113,A_114)
      | ~ r1_tarski(A_114,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_419,plain,(
    ! [A_90] :
      ( k1_xboole_0 = A_90
      | ~ r1_tarski(A_90,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_208,c_400])).

tff(c_1304,plain,(
    ! [A_171,B_172] :
      ( k4_xboole_0(A_171,B_172) = k1_xboole_0
      | ~ r1_tarski(A_171,k2_xboole_0(B_172,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1289,c_419])).

tff(c_1330,plain,(
    ! [A_174,B_175] :
      ( k4_xboole_0(A_174,B_175) = k1_xboole_0
      | ~ r1_tarski(A_174,B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1304])).

tff(c_1406,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_1330])).

tff(c_378,plain,(
    ! [A_111,B_112] : k2_xboole_0(k3_xboole_0(A_111,B_112),k4_xboole_0(A_111,B_112)) = A_111 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4914,plain,(
    ! [A_273,B_274] : k2_xboole_0(k3_xboole_0(A_273,B_274),k4_xboole_0(B_274,A_273)) = B_274 ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_378])).

tff(c_4984,plain,(
    ! [A_18,B_19] : k2_xboole_0(k3_xboole_0(k2_xboole_0(A_18,B_19),A_18),k1_xboole_0) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_1406,c_4914])).

tff(c_5039,plain,(
    ! [A_18,B_19] : k3_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_308,c_4984])).

tff(c_26343,plain,(
    k3_xboole_0('#skF_3',k2_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_26069,c_5039])).

tff(c_1965,plain,(
    ! [A_193,B_194,C_195] :
      ( k7_subset_1(A_193,B_194,C_195) = k4_xboole_0(B_194,C_195)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(A_193)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1987,plain,(
    ! [C_195] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_195) = k4_xboole_0('#skF_3',C_195) ),
    inference(resolution,[status(thm)],[c_68,c_1965])).

tff(c_3602,plain,(
    ! [A_242,B_243] :
      ( k7_subset_1(u1_struct_0(A_242),B_243,k2_tops_1(A_242,B_243)) = k1_tops_1(A_242,B_243)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_3625,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_3602])).

tff(c_3643,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1987,c_3625])).

tff(c_2183,plain,(
    ! [A_202,B_203] :
      ( m1_subset_1(k2_pre_topc(A_202,B_203),k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,(
    ! [A_40,B_41,C_42] :
      ( k7_subset_1(A_40,B_41,C_42) = k4_xboole_0(B_41,C_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36716,plain,(
    ! [A_603,B_604,C_605] :
      ( k7_subset_1(u1_struct_0(A_603),k2_pre_topc(A_603,B_604),C_605) = k4_xboole_0(k2_pre_topc(A_603,B_604),C_605)
      | ~ m1_subset_1(B_604,k1_zfmisc_1(u1_struct_0(A_603)))
      | ~ l1_pre_topc(A_603) ) ),
    inference(resolution,[status(thm)],[c_2183,c_42])).

tff(c_36747,plain,(
    ! [C_605] :
      ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_605) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_605)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_36716])).

tff(c_36889,plain,(
    ! [C_607] : k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_607) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_607) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_36747])).

tff(c_80,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_109,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_36903,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36889,c_109])).

tff(c_387,plain,(
    ! [A_111,B_112] : r1_tarski(k3_xboole_0(A_111,B_112),A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_22])).

tff(c_9184,plain,(
    ! [B_356,A_357,C_358] :
      ( k7_subset_1(B_356,A_357,C_358) = k4_xboole_0(A_357,C_358)
      | ~ r1_tarski(A_357,B_356) ) ),
    inference(resolution,[status(thm)],[c_50,c_1965])).

tff(c_9387,plain,(
    ! [A_111,B_112,C_358] : k7_subset_1(A_111,k3_xboole_0(A_111,B_112),C_358) = k4_xboole_0(k3_xboole_0(A_111,B_112),C_358) ),
    inference(resolution,[status(thm)],[c_387,c_9184])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1594,plain,(
    ! [A_181,B_182] : k4_xboole_0(k3_xboole_0(A_181,B_182),A_181) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_387,c_1330])).

tff(c_20,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_xboole_0(A_16,B_17),k4_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1615,plain,(
    ! [A_181,B_182] : k2_xboole_0(k3_xboole_0(k3_xboole_0(A_181,B_182),A_181),k1_xboole_0) = k3_xboole_0(A_181,B_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_1594,c_20])).

tff(c_15922,plain,(
    ! [A_424,B_425] : k3_xboole_0(A_424,k3_xboole_0(A_424,B_425)) = k3_xboole_0(A_424,B_425) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_308,c_1615])).

tff(c_16094,plain,(
    ! [A_424,B_425] : k5_xboole_0(A_424,k3_xboole_0(A_424,B_425)) = k4_xboole_0(A_424,k3_xboole_0(A_424,B_425)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15922,c_10])).

tff(c_16189,plain,(
    ! [A_424,B_425] : k4_xboole_0(A_424,k3_xboole_0(A_424,B_425)) = k4_xboole_0(A_424,B_425) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16094])).

tff(c_6526,plain,(
    ! [B_326,A_327] :
      ( k4_xboole_0(B_326,A_327) = k3_subset_1(B_326,A_327)
      | ~ r1_tarski(A_327,B_326) ) ),
    inference(resolution,[status(thm)],[c_50,c_1656])).

tff(c_6772,plain,(
    ! [A_111,B_112] : k4_xboole_0(A_111,k3_xboole_0(A_111,B_112)) = k3_subset_1(A_111,k3_xboole_0(A_111,B_112)) ),
    inference(resolution,[status(thm)],[c_387,c_6526])).

tff(c_65022,plain,(
    ! [A_897,B_898] : k3_subset_1(A_897,k3_xboole_0(A_897,B_898)) = k4_xboole_0(A_897,B_898) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16189,c_6772])).

tff(c_1101,plain,(
    ! [A_160,B_161] :
      ( k3_subset_1(A_160,k3_subset_1(A_160,B_161)) = B_161
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1117,plain,(
    ! [B_50,A_49] :
      ( k3_subset_1(B_50,k3_subset_1(B_50,A_49)) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_50,c_1101])).

tff(c_65082,plain,(
    ! [A_897,B_898] :
      ( k3_subset_1(A_897,k4_xboole_0(A_897,B_898)) = k3_xboole_0(A_897,B_898)
      | ~ r1_tarski(k3_xboole_0(A_897,B_898),A_897) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65022,c_1117])).

tff(c_65240,plain,(
    ! [A_897,B_898] : k3_subset_1(A_897,k4_xboole_0(A_897,B_898)) = k3_xboole_0(A_897,B_898) ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_65082])).

tff(c_6911,plain,(
    ! [A_330,B_331] : k4_xboole_0(A_330,k4_xboole_0(A_330,B_331)) = k3_subset_1(A_330,k4_xboole_0(A_330,B_331)) ),
    inference(resolution,[status(thm)],[c_81,c_1656])).

tff(c_6995,plain,(
    ! [A_330,B_331] : m1_subset_1(k3_subset_1(A_330,k4_xboole_0(A_330,B_331)),k1_zfmisc_1(A_330)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6911,c_81])).

tff(c_4027,plain,(
    ! [A_249,B_250,C_251] :
      ( k9_subset_1(A_249,B_250,k3_subset_1(A_249,C_251)) = k7_subset_1(A_249,B_250,C_251)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(A_249))
      | ~ m1_subset_1(B_250,k1_zfmisc_1(A_249)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_33769,plain,(
    ! [A_582,B_583,B_584] :
      ( k9_subset_1(A_582,B_583,k3_subset_1(A_582,k4_xboole_0(A_582,B_584))) = k7_subset_1(A_582,B_583,k4_xboole_0(A_582,B_584))
      | ~ m1_subset_1(B_583,k1_zfmisc_1(A_582)) ) ),
    inference(resolution,[status(thm)],[c_81,c_4027])).

tff(c_533,plain,(
    ! [A_120,B_121,C_122] :
      ( k9_subset_1(A_120,B_121,B_121) = B_121
      | ~ m1_subset_1(C_122,k1_zfmisc_1(A_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_546,plain,(
    ! [A_26,B_121] : k9_subset_1(A_26,B_121,B_121) = B_121 ),
    inference(resolution,[status(thm)],[c_81,c_533])).

tff(c_33780,plain,(
    ! [A_582,B_584] :
      ( k7_subset_1(A_582,k3_subset_1(A_582,k4_xboole_0(A_582,B_584)),k4_xboole_0(A_582,B_584)) = k3_subset_1(A_582,k4_xboole_0(A_582,B_584))
      | ~ m1_subset_1(k3_subset_1(A_582,k4_xboole_0(A_582,B_584)),k1_zfmisc_1(A_582)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33769,c_546])).

tff(c_34039,plain,(
    ! [A_582,B_584] : k7_subset_1(A_582,k3_subset_1(A_582,k4_xboole_0(A_582,B_584)),k4_xboole_0(A_582,B_584)) = k3_subset_1(A_582,k4_xboole_0(A_582,B_584)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6995,c_33780])).

tff(c_149691,plain,(
    ! [A_1419,B_1420] : k4_xboole_0(k3_xboole_0(A_1419,B_1420),k4_xboole_0(A_1419,B_1420)) = k3_xboole_0(A_1419,B_1420) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9387,c_65240,c_65240,c_34039])).

tff(c_150138,plain,(
    k4_xboole_0(k3_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3'),k2_tops_1('#skF_2','#skF_3')) = k3_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36903,c_149691])).

tff(c_150602,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26343,c_3643,c_26343,c_308,c_308,c_150138])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_275,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(A_98,B_99)
      | ~ m1_subset_1(A_98,k1_zfmisc_1(B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_291,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_275])).

tff(c_1402,plain,(
    k4_xboole_0('#skF_3',u1_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_291,c_1330])).

tff(c_1465,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3',u1_struct_0('#skF_2')),k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1402,c_20])).

tff(c_2311,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1465,c_12])).

tff(c_4987,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3',u1_struct_0('#skF_2')),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = u1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1686,c_4914])).

tff(c_5040,plain,(
    k2_xboole_0('#skF_3',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2311,c_4987])).

tff(c_3683,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')),k1_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3643,c_20])).

tff(c_158,plain,(
    ! [A_89,B_88] : r1_tarski(A_89,k2_xboole_0(B_88,A_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_22])).

tff(c_1403,plain,(
    ! [A_89,B_88] : k4_xboole_0(A_89,k2_xboole_0(B_88,A_89)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_158,c_1330])).

tff(c_4990,plain,(
    ! [B_88,A_89] : k2_xboole_0(k3_xboole_0(k2_xboole_0(B_88,A_89),A_89),k1_xboole_0) = A_89 ),
    inference(superposition,[status(thm),theory(equality)],[c_1403,c_4914])).

tff(c_5041,plain,(
    ! [A_89,B_88] : k3_xboole_0(A_89,k2_xboole_0(B_88,A_89)) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_308,c_4990])).

tff(c_643,plain,(
    ! [A_129,C_130,B_131] :
      ( r1_tarski(A_129,C_130)
      | ~ r1_tarski(B_131,C_130)
      | ~ r1_tarski(A_129,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_865,plain,(
    ! [A_146,A_147,B_148] :
      ( r1_tarski(A_146,A_147)
      | ~ r1_tarski(A_146,k3_xboole_0(A_147,B_148)) ) ),
    inference(resolution,[status(thm)],[c_387,c_643])).

tff(c_910,plain,(
    ! [A_149,B_150,B_151] : r1_tarski(k3_xboole_0(k3_xboole_0(A_149,B_150),B_151),A_149) ),
    inference(resolution,[status(thm)],[c_387,c_865])).

tff(c_946,plain,(
    ! [A_106,B_105,B_151] : r1_tarski(k3_xboole_0(k3_xboole_0(A_106,B_105),B_151),B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_910])).

tff(c_12352,plain,(
    ! [A_387,B_388,B_389] : k4_xboole_0(k3_xboole_0(k3_xboole_0(A_387,B_388),B_389),B_388) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_946,c_1330])).

tff(c_14411,plain,(
    ! [A_411,A_412,B_413] : k4_xboole_0(k3_xboole_0(A_411,k3_xboole_0(A_412,B_413)),B_413) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_12352])).

tff(c_21421,plain,(
    ! [A_464,A_465,B_466] : k4_xboole_0(k3_xboole_0(A_464,A_465),k2_xboole_0(A_465,B_466)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5039,c_14411])).

tff(c_31045,plain,(
    ! [A_553,B_554,B_555] : k4_xboole_0(A_553,k2_xboole_0(k2_xboole_0(B_554,A_553),B_555)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5041,c_21421])).

tff(c_396,plain,(
    ! [A_106,B_105] : k2_xboole_0(k3_xboole_0(A_106,B_105),k4_xboole_0(B_105,A_106)) = B_105 ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_378])).

tff(c_31170,plain,(
    ! [B_554,A_553,B_555] : k2_xboole_0(k3_xboole_0(k2_xboole_0(k2_xboole_0(B_554,A_553),B_555),A_553),k1_xboole_0) = A_553 ),
    inference(superposition,[status(thm),theory(equality)],[c_31045,c_396])).

tff(c_31336,plain,(
    ! [A_553,B_554,B_555] : k3_xboole_0(A_553,k2_xboole_0(k2_xboole_0(B_554,A_553),B_555)) = A_553 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_308,c_31170])).

tff(c_65733,plain,(
    ! [A_901,B_902] : m1_subset_1(k3_xboole_0(A_901,B_902),k1_zfmisc_1(A_901)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65240,c_6995])).

tff(c_66207,plain,(
    ! [A_905,B_906] : m1_subset_1(k3_xboole_0(A_905,B_906),k1_zfmisc_1(B_906)) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_65733])).

tff(c_72573,plain,(
    ! [A_936,B_937,B_938] : m1_subset_1(A_936,k1_zfmisc_1(k2_xboole_0(k2_xboole_0(B_937,A_936),B_938))) ),
    inference(superposition,[status(thm),theory(equality)],[c_31336,c_66207])).

tff(c_73739,plain,(
    ! [B_952] : m1_subset_1(k1_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_xboole_0('#skF_3',B_952))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3683,c_72573])).

tff(c_73769,plain,(
    m1_subset_1(k1_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5040,c_73739])).

tff(c_56,plain,(
    ! [A_55,B_56] :
      ( v3_pre_topc(k1_tops_1(A_55,B_56),A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_73844,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_3')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_73769,c_56])).

tff(c_73904,plain,(
    v3_pre_topc(k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_73844])).

tff(c_150731,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150602,c_150602,c_73904])).

tff(c_150801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_150731])).

tff(c_150802,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_150873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150802,c_109])).

tff(c_150874,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_151022,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150874,c_74])).

tff(c_152392,plain,(
    ! [A_1529,B_1530,C_1531] :
      ( k7_subset_1(A_1529,B_1530,C_1531) = k4_xboole_0(B_1530,C_1531)
      | ~ m1_subset_1(B_1530,k1_zfmisc_1(A_1529)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_152417,plain,(
    ! [C_1531] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_1531) = k4_xboole_0('#skF_3',C_1531) ),
    inference(resolution,[status(thm)],[c_68,c_152392])).

tff(c_153908,plain,(
    ! [A_1580,B_1581] :
      ( k7_subset_1(u1_struct_0(A_1580),B_1581,k2_tops_1(A_1580,B_1581)) = k1_tops_1(A_1580,B_1581)
      | ~ m1_subset_1(B_1581,k1_zfmisc_1(u1_struct_0(A_1580)))
      | ~ l1_pre_topc(A_1580) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_153931,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_153908])).

tff(c_153949,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_152417,c_153931])).

tff(c_151042,plain,(
    ! [A_1448,B_1449] :
      ( r1_tarski(A_1448,B_1449)
      | ~ m1_subset_1(A_1448,k1_zfmisc_1(B_1449)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_151057,plain,(
    ! [A_26,B_27] : r1_tarski(k4_xboole_0(A_26,B_27),A_26) ),
    inference(resolution,[status(thm)],[c_81,c_151042])).

tff(c_153977,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_153949,c_151057])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_155336,plain,(
    ! [B_1617,A_1618,C_1619] :
      ( r1_tarski(B_1617,k1_tops_1(A_1618,C_1619))
      | ~ r1_tarski(B_1617,C_1619)
      | ~ v3_pre_topc(B_1617,A_1618)
      | ~ m1_subset_1(C_1619,k1_zfmisc_1(u1_struct_0(A_1618)))
      | ~ m1_subset_1(B_1617,k1_zfmisc_1(u1_struct_0(A_1618)))
      | ~ l1_pre_topc(A_1618) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_155361,plain,(
    ! [B_1617] :
      ( r1_tarski(B_1617,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_1617,'#skF_3')
      | ~ v3_pre_topc(B_1617,'#skF_2')
      | ~ m1_subset_1(B_1617,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_155336])).

tff(c_159220,plain,(
    ! [B_1701] :
      ( r1_tarski(B_1701,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_1701,'#skF_3')
      | ~ v3_pre_topc(B_1701,'#skF_2')
      | ~ m1_subset_1(B_1701,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_155361])).

tff(c_159257,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_159220])).

tff(c_159279,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150874,c_8,c_159257])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_159297,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_159279,c_4])).

tff(c_159310,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153977,c_159297])).

tff(c_58,plain,(
    ! [A_57,B_59] :
      ( k7_subset_1(u1_struct_0(A_57),k2_pre_topc(A_57,B_59),k1_tops_1(A_57,B_59)) = k2_tops_1(A_57,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_159345,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_159310,c_58])).

tff(c_159349,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_159345])).

tff(c_159351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151022,c_159349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:09:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 42.62/33.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.65/33.40  
% 42.65/33.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.65/33.40  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 42.65/33.40  
% 42.65/33.40  %Foreground sorts:
% 42.65/33.40  
% 42.65/33.40  
% 42.65/33.40  %Background operators:
% 42.65/33.40  
% 42.65/33.40  
% 42.65/33.40  %Foreground operators:
% 42.65/33.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 42.65/33.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 42.65/33.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 42.65/33.40  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 42.65/33.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 42.65/33.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 42.65/33.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 42.65/33.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 42.65/33.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 42.65/33.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 42.65/33.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 42.65/33.40  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 42.65/33.40  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 42.65/33.40  tff('#skF_2', type, '#skF_2': $i).
% 42.65/33.40  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 42.65/33.40  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 42.65/33.40  tff('#skF_3', type, '#skF_3': $i).
% 42.65/33.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 42.65/33.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 42.65/33.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 42.65/33.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 42.65/33.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 42.65/33.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 42.65/33.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 42.65/33.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 42.65/33.40  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 42.65/33.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 42.65/33.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 42.65/33.40  
% 42.86/33.43  tff(f_177, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 42.86/33.43  tff(f_158, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 42.86/33.43  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 42.86/33.43  tff(f_86, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 42.86/33.43  tff(f_67, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 42.86/33.43  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 42.86/33.43  tff(f_115, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 42.86/33.43  tff(f_103, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 42.86/33.43  tff(f_84, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 42.86/33.43  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 42.86/33.43  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 42.86/33.43  tff(f_99, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 42.86/33.43  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 42.86/33.43  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 42.86/33.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 42.86/33.43  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 42.86/33.43  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 42.86/33.43  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 42.86/33.43  tff(f_165, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 42.86/33.43  tff(f_109, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 42.86/33.43  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 42.86/33.43  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 42.86/33.43  tff(f_97, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 42.86/33.43  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 42.86/33.43  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 42.86/33.43  tff(f_123, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 42.86/33.43  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 42.86/33.43  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 42.86/33.43  tff(c_74, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 42.86/33.43  tff(c_272, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_74])).
% 42.86/33.43  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 42.86/33.43  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 42.86/33.43  tff(c_3790, plain, (![A_245, B_246]: (k4_subset_1(u1_struct_0(A_245), B_246, k2_tops_1(A_245, B_246))=k2_pre_topc(A_245, B_246) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_158])).
% 42.86/33.43  tff(c_3813, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_3790])).
% 42.86/33.43  tff(c_3829, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3813])).
% 42.86/33.43  tff(c_1656, plain, (![A_183, B_184]: (k4_xboole_0(A_183, B_184)=k3_subset_1(A_183, B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(A_183)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 42.86/33.43  tff(c_1686, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_68, c_1656])).
% 42.86/33.43  tff(c_40, plain, (![A_38, B_39]: (k6_subset_1(A_38, B_39)=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_86])).
% 42.86/33.43  tff(c_30, plain, (![A_26, B_27]: (m1_subset_1(k6_subset_1(A_26, B_27), k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 42.86/33.43  tff(c_81, plain, (![A_26, B_27]: (m1_subset_1(k4_xboole_0(A_26, B_27), k1_zfmisc_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30])).
% 42.86/33.43  tff(c_1812, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1686, c_81])).
% 42.86/33.43  tff(c_2950, plain, (![A_226, B_227]: (k2_tops_1(A_226, k3_subset_1(u1_struct_0(A_226), B_227))=k2_tops_1(A_226, B_227) | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(A_226))), inference(cnfTransformation, [status(thm)], [f_151])).
% 42.86/33.43  tff(c_2973, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_2950])).
% 42.86/33.43  tff(c_2991, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2973])).
% 42.86/33.43  tff(c_54, plain, (![A_53, B_54]: (m1_subset_1(k2_tops_1(A_53, B_54), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_115])).
% 42.86/33.43  tff(c_3883, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2991, c_54])).
% 42.86/33.43  tff(c_3887, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1812, c_3883])).
% 42.86/33.43  tff(c_48, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 42.86/33.43  tff(c_3930, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_3887, c_48])).
% 42.86/33.43  tff(c_50, plain, (![A_49, B_50]: (m1_subset_1(A_49, k1_zfmisc_1(B_50)) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_103])).
% 42.86/33.43  tff(c_2727, plain, (![A_216, B_217, C_218]: (k4_subset_1(A_216, B_217, C_218)=k2_xboole_0(B_217, C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(A_216)) | ~m1_subset_1(B_217, k1_zfmisc_1(A_216)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 42.86/33.43  tff(c_25483, plain, (![B_496, B_497, A_498]: (k4_subset_1(B_496, B_497, A_498)=k2_xboole_0(B_497, A_498) | ~m1_subset_1(B_497, k1_zfmisc_1(B_496)) | ~r1_tarski(A_498, B_496))), inference(resolution, [status(thm)], [c_50, c_2727])).
% 42.86/33.43  tff(c_25867, plain, (![A_503]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_503)=k2_xboole_0('#skF_3', A_503) | ~r1_tarski(A_503, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_68, c_25483])).
% 42.86/33.43  tff(c_25941, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_3930, c_25867])).
% 42.86/33.43  tff(c_26069, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3829, c_25941])).
% 42.86/33.43  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 42.86/33.43  tff(c_24, plain, (![B_21, A_20]: (k2_tarski(B_21, A_20)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 42.86/33.43  tff(c_238, plain, (![A_92, B_93]: (k1_setfam_1(k2_tarski(A_92, B_93))=k3_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_99])).
% 42.86/33.43  tff(c_302, plain, (![B_105, A_106]: (k1_setfam_1(k2_tarski(B_105, A_106))=k3_xboole_0(A_106, B_105))), inference(superposition, [status(thm), theory('equality')], [c_24, c_238])).
% 42.86/33.43  tff(c_46, plain, (![A_47, B_48]: (k1_setfam_1(k2_tarski(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_99])).
% 42.86/33.43  tff(c_308, plain, (![B_105, A_106]: (k3_xboole_0(B_105, A_106)=k3_xboole_0(A_106, B_105))), inference(superposition, [status(thm), theory('equality')], [c_302, c_46])).
% 42.86/33.43  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 42.86/33.43  tff(c_1289, plain, (![A_171, B_172, C_173]: (r1_tarski(k4_xboole_0(A_171, B_172), C_173) | ~r1_tarski(A_171, k2_xboole_0(B_172, C_173)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 42.86/33.43  tff(c_143, plain, (![B_88, A_89]: (k2_xboole_0(B_88, A_89)=k2_xboole_0(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_27])).
% 42.86/33.43  tff(c_196, plain, (![A_90]: (k2_xboole_0(k1_xboole_0, A_90)=A_90)), inference(superposition, [status(thm), theory('equality')], [c_143, c_12])).
% 42.86/33.43  tff(c_208, plain, (![A_90]: (r1_tarski(k1_xboole_0, A_90))), inference(superposition, [status(thm), theory('equality')], [c_196, c_22])).
% 42.86/33.43  tff(c_400, plain, (![B_113, A_114]: (B_113=A_114 | ~r1_tarski(B_113, A_114) | ~r1_tarski(A_114, B_113))), inference(cnfTransformation, [status(thm)], [f_33])).
% 42.86/33.43  tff(c_419, plain, (![A_90]: (k1_xboole_0=A_90 | ~r1_tarski(A_90, k1_xboole_0))), inference(resolution, [status(thm)], [c_208, c_400])).
% 42.86/33.43  tff(c_1304, plain, (![A_171, B_172]: (k4_xboole_0(A_171, B_172)=k1_xboole_0 | ~r1_tarski(A_171, k2_xboole_0(B_172, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1289, c_419])).
% 42.86/33.43  tff(c_1330, plain, (![A_174, B_175]: (k4_xboole_0(A_174, B_175)=k1_xboole_0 | ~r1_tarski(A_174, B_175))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1304])).
% 42.86/33.43  tff(c_1406, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_1330])).
% 42.86/33.43  tff(c_378, plain, (![A_111, B_112]: (k2_xboole_0(k3_xboole_0(A_111, B_112), k4_xboole_0(A_111, B_112))=A_111)), inference(cnfTransformation, [status(thm)], [f_53])).
% 42.86/33.43  tff(c_4914, plain, (![A_273, B_274]: (k2_xboole_0(k3_xboole_0(A_273, B_274), k4_xboole_0(B_274, A_273))=B_274)), inference(superposition, [status(thm), theory('equality')], [c_308, c_378])).
% 42.86/33.43  tff(c_4984, plain, (![A_18, B_19]: (k2_xboole_0(k3_xboole_0(k2_xboole_0(A_18, B_19), A_18), k1_xboole_0)=A_18)), inference(superposition, [status(thm), theory('equality')], [c_1406, c_4914])).
% 42.86/33.43  tff(c_5039, plain, (![A_18, B_19]: (k3_xboole_0(A_18, k2_xboole_0(A_18, B_19))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_308, c_4984])).
% 42.86/33.43  tff(c_26343, plain, (k3_xboole_0('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_26069, c_5039])).
% 42.86/33.43  tff(c_1965, plain, (![A_193, B_194, C_195]: (k7_subset_1(A_193, B_194, C_195)=k4_xboole_0(B_194, C_195) | ~m1_subset_1(B_194, k1_zfmisc_1(A_193)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 42.86/33.43  tff(c_1987, plain, (![C_195]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_195)=k4_xboole_0('#skF_3', C_195))), inference(resolution, [status(thm)], [c_68, c_1965])).
% 42.86/33.43  tff(c_3602, plain, (![A_242, B_243]: (k7_subset_1(u1_struct_0(A_242), B_243, k2_tops_1(A_242, B_243))=k1_tops_1(A_242, B_243) | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(A_242))), inference(cnfTransformation, [status(thm)], [f_165])).
% 42.86/33.43  tff(c_3625, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_3602])).
% 42.86/33.43  tff(c_3643, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1987, c_3625])).
% 42.86/33.43  tff(c_2183, plain, (![A_202, B_203]: (m1_subset_1(k2_pre_topc(A_202, B_203), k1_zfmisc_1(u1_struct_0(A_202))) | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202))), inference(cnfTransformation, [status(thm)], [f_109])).
% 42.86/33.43  tff(c_42, plain, (![A_40, B_41, C_42]: (k7_subset_1(A_40, B_41, C_42)=k4_xboole_0(B_41, C_42) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 42.86/33.43  tff(c_36716, plain, (![A_603, B_604, C_605]: (k7_subset_1(u1_struct_0(A_603), k2_pre_topc(A_603, B_604), C_605)=k4_xboole_0(k2_pre_topc(A_603, B_604), C_605) | ~m1_subset_1(B_604, k1_zfmisc_1(u1_struct_0(A_603))) | ~l1_pre_topc(A_603))), inference(resolution, [status(thm)], [c_2183, c_42])).
% 42.86/33.43  tff(c_36747, plain, (![C_605]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_605)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_605) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_36716])).
% 42.86/33.43  tff(c_36889, plain, (![C_607]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_607)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_607))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_36747])).
% 42.86/33.43  tff(c_80, plain, (v3_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 42.86/33.43  tff(c_109, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_80])).
% 42.86/33.43  tff(c_36903, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36889, c_109])).
% 42.86/33.43  tff(c_387, plain, (![A_111, B_112]: (r1_tarski(k3_xboole_0(A_111, B_112), A_111))), inference(superposition, [status(thm), theory('equality')], [c_378, c_22])).
% 42.86/33.43  tff(c_9184, plain, (![B_356, A_357, C_358]: (k7_subset_1(B_356, A_357, C_358)=k4_xboole_0(A_357, C_358) | ~r1_tarski(A_357, B_356))), inference(resolution, [status(thm)], [c_50, c_1965])).
% 42.86/33.43  tff(c_9387, plain, (![A_111, B_112, C_358]: (k7_subset_1(A_111, k3_xboole_0(A_111, B_112), C_358)=k4_xboole_0(k3_xboole_0(A_111, B_112), C_358))), inference(resolution, [status(thm)], [c_387, c_9184])).
% 42.86/33.43  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 42.86/33.43  tff(c_1594, plain, (![A_181, B_182]: (k4_xboole_0(k3_xboole_0(A_181, B_182), A_181)=k1_xboole_0)), inference(resolution, [status(thm)], [c_387, c_1330])).
% 42.86/33.43  tff(c_20, plain, (![A_16, B_17]: (k2_xboole_0(k3_xboole_0(A_16, B_17), k4_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_53])).
% 42.86/33.43  tff(c_1615, plain, (![A_181, B_182]: (k2_xboole_0(k3_xboole_0(k3_xboole_0(A_181, B_182), A_181), k1_xboole_0)=k3_xboole_0(A_181, B_182))), inference(superposition, [status(thm), theory('equality')], [c_1594, c_20])).
% 42.86/33.43  tff(c_15922, plain, (![A_424, B_425]: (k3_xboole_0(A_424, k3_xboole_0(A_424, B_425))=k3_xboole_0(A_424, B_425))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_308, c_1615])).
% 42.86/33.43  tff(c_16094, plain, (![A_424, B_425]: (k5_xboole_0(A_424, k3_xboole_0(A_424, B_425))=k4_xboole_0(A_424, k3_xboole_0(A_424, B_425)))), inference(superposition, [status(thm), theory('equality')], [c_15922, c_10])).
% 42.86/33.43  tff(c_16189, plain, (![A_424, B_425]: (k4_xboole_0(A_424, k3_xboole_0(A_424, B_425))=k4_xboole_0(A_424, B_425))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16094])).
% 42.86/33.43  tff(c_6526, plain, (![B_326, A_327]: (k4_xboole_0(B_326, A_327)=k3_subset_1(B_326, A_327) | ~r1_tarski(A_327, B_326))), inference(resolution, [status(thm)], [c_50, c_1656])).
% 42.86/33.43  tff(c_6772, plain, (![A_111, B_112]: (k4_xboole_0(A_111, k3_xboole_0(A_111, B_112))=k3_subset_1(A_111, k3_xboole_0(A_111, B_112)))), inference(resolution, [status(thm)], [c_387, c_6526])).
% 42.86/33.43  tff(c_65022, plain, (![A_897, B_898]: (k3_subset_1(A_897, k3_xboole_0(A_897, B_898))=k4_xboole_0(A_897, B_898))), inference(demodulation, [status(thm), theory('equality')], [c_16189, c_6772])).
% 42.86/33.43  tff(c_1101, plain, (![A_160, B_161]: (k3_subset_1(A_160, k3_subset_1(A_160, B_161))=B_161 | ~m1_subset_1(B_161, k1_zfmisc_1(A_160)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 42.86/33.43  tff(c_1117, plain, (![B_50, A_49]: (k3_subset_1(B_50, k3_subset_1(B_50, A_49))=A_49 | ~r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_50, c_1101])).
% 42.86/33.43  tff(c_65082, plain, (![A_897, B_898]: (k3_subset_1(A_897, k4_xboole_0(A_897, B_898))=k3_xboole_0(A_897, B_898) | ~r1_tarski(k3_xboole_0(A_897, B_898), A_897))), inference(superposition, [status(thm), theory('equality')], [c_65022, c_1117])).
% 42.86/33.43  tff(c_65240, plain, (![A_897, B_898]: (k3_subset_1(A_897, k4_xboole_0(A_897, B_898))=k3_xboole_0(A_897, B_898))), inference(demodulation, [status(thm), theory('equality')], [c_387, c_65082])).
% 42.86/33.43  tff(c_6911, plain, (![A_330, B_331]: (k4_xboole_0(A_330, k4_xboole_0(A_330, B_331))=k3_subset_1(A_330, k4_xboole_0(A_330, B_331)))), inference(resolution, [status(thm)], [c_81, c_1656])).
% 42.86/33.43  tff(c_6995, plain, (![A_330, B_331]: (m1_subset_1(k3_subset_1(A_330, k4_xboole_0(A_330, B_331)), k1_zfmisc_1(A_330)))), inference(superposition, [status(thm), theory('equality')], [c_6911, c_81])).
% 42.86/33.43  tff(c_4027, plain, (![A_249, B_250, C_251]: (k9_subset_1(A_249, B_250, k3_subset_1(A_249, C_251))=k7_subset_1(A_249, B_250, C_251) | ~m1_subset_1(C_251, k1_zfmisc_1(A_249)) | ~m1_subset_1(B_250, k1_zfmisc_1(A_249)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 42.86/33.43  tff(c_33769, plain, (![A_582, B_583, B_584]: (k9_subset_1(A_582, B_583, k3_subset_1(A_582, k4_xboole_0(A_582, B_584)))=k7_subset_1(A_582, B_583, k4_xboole_0(A_582, B_584)) | ~m1_subset_1(B_583, k1_zfmisc_1(A_582)))), inference(resolution, [status(thm)], [c_81, c_4027])).
% 42.86/33.43  tff(c_533, plain, (![A_120, B_121, C_122]: (k9_subset_1(A_120, B_121, B_121)=B_121 | ~m1_subset_1(C_122, k1_zfmisc_1(A_120)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 42.86/33.43  tff(c_546, plain, (![A_26, B_121]: (k9_subset_1(A_26, B_121, B_121)=B_121)), inference(resolution, [status(thm)], [c_81, c_533])).
% 42.86/33.43  tff(c_33780, plain, (![A_582, B_584]: (k7_subset_1(A_582, k3_subset_1(A_582, k4_xboole_0(A_582, B_584)), k4_xboole_0(A_582, B_584))=k3_subset_1(A_582, k4_xboole_0(A_582, B_584)) | ~m1_subset_1(k3_subset_1(A_582, k4_xboole_0(A_582, B_584)), k1_zfmisc_1(A_582)))), inference(superposition, [status(thm), theory('equality')], [c_33769, c_546])).
% 42.86/33.43  tff(c_34039, plain, (![A_582, B_584]: (k7_subset_1(A_582, k3_subset_1(A_582, k4_xboole_0(A_582, B_584)), k4_xboole_0(A_582, B_584))=k3_subset_1(A_582, k4_xboole_0(A_582, B_584)))), inference(demodulation, [status(thm), theory('equality')], [c_6995, c_33780])).
% 42.86/33.43  tff(c_149691, plain, (![A_1419, B_1420]: (k4_xboole_0(k3_xboole_0(A_1419, B_1420), k4_xboole_0(A_1419, B_1420))=k3_xboole_0(A_1419, B_1420))), inference(demodulation, [status(thm), theory('equality')], [c_9387, c_65240, c_65240, c_34039])).
% 42.86/33.43  tff(c_150138, plain, (k4_xboole_0(k3_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))=k3_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36903, c_149691])).
% 42.86/33.43  tff(c_150602, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26343, c_3643, c_26343, c_308, c_308, c_150138])).
% 42.86/33.43  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 42.86/33.43  tff(c_275, plain, (![A_98, B_99]: (r1_tarski(A_98, B_99) | ~m1_subset_1(A_98, k1_zfmisc_1(B_99)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 42.86/33.43  tff(c_291, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_275])).
% 42.86/33.43  tff(c_1402, plain, (k4_xboole_0('#skF_3', u1_struct_0('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_291, c_1330])).
% 42.86/33.43  tff(c_1465, plain, (k2_xboole_0(k3_xboole_0('#skF_3', u1_struct_0('#skF_2')), k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1402, c_20])).
% 42.86/33.43  tff(c_2311, plain, (k3_xboole_0('#skF_3', u1_struct_0('#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1465, c_12])).
% 42.86/33.43  tff(c_4987, plain, (k2_xboole_0(k3_xboole_0('#skF_3', u1_struct_0('#skF_2')), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=u1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1686, c_4914])).
% 42.86/33.43  tff(c_5040, plain, (k2_xboole_0('#skF_3', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2311, c_4987])).
% 42.86/33.43  tff(c_3683, plain, (k2_xboole_0(k3_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3')), k1_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3643, c_20])).
% 42.86/33.43  tff(c_158, plain, (![A_89, B_88]: (r1_tarski(A_89, k2_xboole_0(B_88, A_89)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_22])).
% 42.86/33.43  tff(c_1403, plain, (![A_89, B_88]: (k4_xboole_0(A_89, k2_xboole_0(B_88, A_89))=k1_xboole_0)), inference(resolution, [status(thm)], [c_158, c_1330])).
% 42.86/33.43  tff(c_4990, plain, (![B_88, A_89]: (k2_xboole_0(k3_xboole_0(k2_xboole_0(B_88, A_89), A_89), k1_xboole_0)=A_89)), inference(superposition, [status(thm), theory('equality')], [c_1403, c_4914])).
% 42.86/33.43  tff(c_5041, plain, (![A_89, B_88]: (k3_xboole_0(A_89, k2_xboole_0(B_88, A_89))=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_308, c_4990])).
% 42.86/33.43  tff(c_643, plain, (![A_129, C_130, B_131]: (r1_tarski(A_129, C_130) | ~r1_tarski(B_131, C_130) | ~r1_tarski(A_129, B_131))), inference(cnfTransformation, [status(thm)], [f_43])).
% 42.86/33.43  tff(c_865, plain, (![A_146, A_147, B_148]: (r1_tarski(A_146, A_147) | ~r1_tarski(A_146, k3_xboole_0(A_147, B_148)))), inference(resolution, [status(thm)], [c_387, c_643])).
% 42.86/33.43  tff(c_910, plain, (![A_149, B_150, B_151]: (r1_tarski(k3_xboole_0(k3_xboole_0(A_149, B_150), B_151), A_149))), inference(resolution, [status(thm)], [c_387, c_865])).
% 42.86/33.43  tff(c_946, plain, (![A_106, B_105, B_151]: (r1_tarski(k3_xboole_0(k3_xboole_0(A_106, B_105), B_151), B_105))), inference(superposition, [status(thm), theory('equality')], [c_308, c_910])).
% 42.86/33.43  tff(c_12352, plain, (![A_387, B_388, B_389]: (k4_xboole_0(k3_xboole_0(k3_xboole_0(A_387, B_388), B_389), B_388)=k1_xboole_0)), inference(resolution, [status(thm)], [c_946, c_1330])).
% 42.86/33.43  tff(c_14411, plain, (![A_411, A_412, B_413]: (k4_xboole_0(k3_xboole_0(A_411, k3_xboole_0(A_412, B_413)), B_413)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_308, c_12352])).
% 42.86/33.43  tff(c_21421, plain, (![A_464, A_465, B_466]: (k4_xboole_0(k3_xboole_0(A_464, A_465), k2_xboole_0(A_465, B_466))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5039, c_14411])).
% 42.86/33.43  tff(c_31045, plain, (![A_553, B_554, B_555]: (k4_xboole_0(A_553, k2_xboole_0(k2_xboole_0(B_554, A_553), B_555))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5041, c_21421])).
% 42.86/33.43  tff(c_396, plain, (![A_106, B_105]: (k2_xboole_0(k3_xboole_0(A_106, B_105), k4_xboole_0(B_105, A_106))=B_105)), inference(superposition, [status(thm), theory('equality')], [c_308, c_378])).
% 42.86/33.43  tff(c_31170, plain, (![B_554, A_553, B_555]: (k2_xboole_0(k3_xboole_0(k2_xboole_0(k2_xboole_0(B_554, A_553), B_555), A_553), k1_xboole_0)=A_553)), inference(superposition, [status(thm), theory('equality')], [c_31045, c_396])).
% 42.86/33.43  tff(c_31336, plain, (![A_553, B_554, B_555]: (k3_xboole_0(A_553, k2_xboole_0(k2_xboole_0(B_554, A_553), B_555))=A_553)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_308, c_31170])).
% 42.86/33.43  tff(c_65733, plain, (![A_901, B_902]: (m1_subset_1(k3_xboole_0(A_901, B_902), k1_zfmisc_1(A_901)))), inference(demodulation, [status(thm), theory('equality')], [c_65240, c_6995])).
% 42.86/33.43  tff(c_66207, plain, (![A_905, B_906]: (m1_subset_1(k3_xboole_0(A_905, B_906), k1_zfmisc_1(B_906)))), inference(superposition, [status(thm), theory('equality')], [c_308, c_65733])).
% 42.86/33.43  tff(c_72573, plain, (![A_936, B_937, B_938]: (m1_subset_1(A_936, k1_zfmisc_1(k2_xboole_0(k2_xboole_0(B_937, A_936), B_938))))), inference(superposition, [status(thm), theory('equality')], [c_31336, c_66207])).
% 42.86/33.43  tff(c_73739, plain, (![B_952]: (m1_subset_1(k1_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_xboole_0('#skF_3', B_952))))), inference(superposition, [status(thm), theory('equality')], [c_3683, c_72573])).
% 42.86/33.43  tff(c_73769, plain, (m1_subset_1(k1_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5040, c_73739])).
% 42.86/33.43  tff(c_56, plain, (![A_55, B_56]: (v3_pre_topc(k1_tops_1(A_55, B_56), A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_123])).
% 42.86/33.43  tff(c_73844, plain, (v3_pre_topc(k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_3')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_73769, c_56])).
% 42.86/33.43  tff(c_73904, plain, (v3_pre_topc(k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_73844])).
% 42.86/33.43  tff(c_150731, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_150602, c_150602, c_73904])).
% 42.86/33.43  tff(c_150801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_150731])).
% 42.86/33.43  tff(c_150802, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_74])).
% 42.86/33.43  tff(c_150873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150802, c_109])).
% 42.86/33.43  tff(c_150874, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_80])).
% 42.86/33.43  tff(c_151022, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_150874, c_74])).
% 42.86/33.43  tff(c_152392, plain, (![A_1529, B_1530, C_1531]: (k7_subset_1(A_1529, B_1530, C_1531)=k4_xboole_0(B_1530, C_1531) | ~m1_subset_1(B_1530, k1_zfmisc_1(A_1529)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 42.86/33.43  tff(c_152417, plain, (![C_1531]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_1531)=k4_xboole_0('#skF_3', C_1531))), inference(resolution, [status(thm)], [c_68, c_152392])).
% 42.86/33.43  tff(c_153908, plain, (![A_1580, B_1581]: (k7_subset_1(u1_struct_0(A_1580), B_1581, k2_tops_1(A_1580, B_1581))=k1_tops_1(A_1580, B_1581) | ~m1_subset_1(B_1581, k1_zfmisc_1(u1_struct_0(A_1580))) | ~l1_pre_topc(A_1580))), inference(cnfTransformation, [status(thm)], [f_165])).
% 42.86/33.43  tff(c_153931, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_153908])).
% 42.86/33.43  tff(c_153949, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_152417, c_153931])).
% 42.86/33.43  tff(c_151042, plain, (![A_1448, B_1449]: (r1_tarski(A_1448, B_1449) | ~m1_subset_1(A_1448, k1_zfmisc_1(B_1449)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 42.86/33.43  tff(c_151057, plain, (![A_26, B_27]: (r1_tarski(k4_xboole_0(A_26, B_27), A_26))), inference(resolution, [status(thm)], [c_81, c_151042])).
% 42.86/33.43  tff(c_153977, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_153949, c_151057])).
% 42.86/33.43  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 42.86/33.43  tff(c_155336, plain, (![B_1617, A_1618, C_1619]: (r1_tarski(B_1617, k1_tops_1(A_1618, C_1619)) | ~r1_tarski(B_1617, C_1619) | ~v3_pre_topc(B_1617, A_1618) | ~m1_subset_1(C_1619, k1_zfmisc_1(u1_struct_0(A_1618))) | ~m1_subset_1(B_1617, k1_zfmisc_1(u1_struct_0(A_1618))) | ~l1_pre_topc(A_1618))), inference(cnfTransformation, [status(thm)], [f_144])).
% 42.86/33.43  tff(c_155361, plain, (![B_1617]: (r1_tarski(B_1617, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_1617, '#skF_3') | ~v3_pre_topc(B_1617, '#skF_2') | ~m1_subset_1(B_1617, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_155336])).
% 42.86/33.43  tff(c_159220, plain, (![B_1701]: (r1_tarski(B_1701, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_1701, '#skF_3') | ~v3_pre_topc(B_1701, '#skF_2') | ~m1_subset_1(B_1701, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_155361])).
% 42.86/33.43  tff(c_159257, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_159220])).
% 42.86/33.43  tff(c_159279, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_150874, c_8, c_159257])).
% 42.86/33.43  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 42.86/33.43  tff(c_159297, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_159279, c_4])).
% 42.86/33.43  tff(c_159310, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_153977, c_159297])).
% 42.86/33.43  tff(c_58, plain, (![A_57, B_59]: (k7_subset_1(u1_struct_0(A_57), k2_pre_topc(A_57, B_59), k1_tops_1(A_57, B_59))=k2_tops_1(A_57, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_130])).
% 42.86/33.43  tff(c_159345, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_159310, c_58])).
% 42.86/33.43  tff(c_159349, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_159345])).
% 42.86/33.43  tff(c_159351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151022, c_159349])).
% 42.86/33.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.86/33.43  
% 42.86/33.43  Inference rules
% 42.86/33.43  ----------------------
% 42.86/33.43  #Ref     : 0
% 42.86/33.43  #Sup     : 38813
% 42.86/33.43  #Fact    : 0
% 42.86/33.43  #Define  : 0
% 42.86/33.43  #Split   : 13
% 42.86/33.43  #Chain   : 0
% 42.86/33.43  #Close   : 0
% 42.86/33.43  
% 42.86/33.43  Ordering : KBO
% 42.86/33.43  
% 42.86/33.43  Simplification rules
% 42.86/33.43  ----------------------
% 42.86/33.43  #Subsume      : 3886
% 42.86/33.43  #Demod        : 39537
% 42.86/33.43  #Tautology    : 21787
% 42.86/33.43  #SimpNegUnit  : 3
% 42.86/33.43  #BackRed      : 107
% 42.86/33.43  
% 42.86/33.43  #Partial instantiations: 0
% 42.86/33.43  #Strategies tried      : 1
% 42.86/33.43  
% 42.86/33.43  Timing (in seconds)
% 42.86/33.43  ----------------------
% 42.86/33.43  Preprocessing        : 0.38
% 42.86/33.43  Parsing              : 0.20
% 42.86/33.43  CNF conversion       : 0.03
% 42.86/33.43  Main loop            : 32.26
% 42.86/33.43  Inferencing          : 2.99
% 42.86/33.43  Reduction            : 20.35
% 42.86/33.43  Demodulation         : 18.32
% 42.86/33.43  BG Simplification    : 0.32
% 42.86/33.43  Subsumption          : 7.37
% 42.86/33.43  Abstraction          : 0.61
% 42.86/33.43  MUC search           : 0.00
% 42.86/33.43  Cooper               : 0.00
% 42.86/33.43  Total                : 32.69
% 42.86/33.43  Index Insertion      : 0.00
% 42.86/33.43  Index Deletion       : 0.00
% 42.86/33.43  Index Matching       : 0.00
% 42.86/33.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
