%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:16 EST 2020

% Result     : Theorem 11.34s
% Output     : CNFRefutation 11.34s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 472 expanded)
%              Number of leaves         :   53 ( 180 expanded)
%              Depth                    :   20
%              Number of atoms          :  207 ( 825 expanded)
%              Number of equality atoms :   89 ( 318 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_151,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_91,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_81,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_69,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_25395,plain,(
    ! [A_563,B_564,C_565] :
      ( k7_subset_1(A_563,B_564,C_565) = k4_xboole_0(B_564,C_565)
      | ~ m1_subset_1(B_564,k1_zfmisc_1(A_563)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_25414,plain,(
    ! [C_565] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_565) = k4_xboole_0('#skF_2',C_565) ),
    inference(resolution,[status(thm)],[c_60,c_25395])).

tff(c_66,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_137,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_1394,plain,(
    ! [A_154,B_155,C_156] :
      ( k7_subset_1(A_154,B_155,C_156) = k4_xboole_0(B_155,C_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1471,plain,(
    ! [C_160] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_160) = k4_xboole_0('#skF_2',C_160) ),
    inference(resolution,[status(thm)],[c_60,c_1394])).

tff(c_72,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_240,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_72])).

tff(c_1477,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1471,c_240])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_139,plain,(
    ! [A_77,B_78] : k1_setfam_1(k2_tarski(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_184,plain,(
    ! [A_85,B_86] : k1_setfam_1(k2_tarski(A_85,B_86)) = k3_xboole_0(B_86,A_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_139])).

tff(c_42,plain,(
    ! [A_44,B_45] : k1_setfam_1(k2_tarski(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_190,plain,(
    ! [B_86,A_85] : k3_xboole_0(B_86,A_85) = k3_xboole_0(A_85,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_42])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_925,plain,(
    ! [A_131,B_132,C_133] :
      ( r1_tarski(k4_xboole_0(A_131,B_132),C_133)
      | ~ r1_tarski(A_131,k2_xboole_0(B_132,C_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_155,plain,(
    ! [A_81,B_82] : k3_tarski(k2_tarski(A_81,B_82)) = k2_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_245,plain,(
    ! [A_89,B_90] : k3_tarski(k2_tarski(A_89,B_90)) = k2_xboole_0(B_90,A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_155])).

tff(c_22,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_268,plain,(
    ! [B_91,A_92] : k2_xboole_0(B_91,A_92) = k2_xboole_0(A_92,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_22])).

tff(c_284,plain,(
    ! [A_92] : k2_xboole_0(k1_xboole_0,A_92) = A_92 ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_4])).

tff(c_16,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_251,plain,(
    ! [B_90,A_89] : k2_xboole_0(B_90,A_89) = k2_xboole_0(A_89,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_22])).

tff(c_446,plain,(
    ! [A_99,B_100] : k2_xboole_0(k3_xboole_0(A_99,B_100),k4_xboole_0(A_99,B_100)) = A_99 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_452,plain,(
    ! [A_99,B_100] : k2_xboole_0(k3_xboole_0(A_99,B_100),k4_xboole_0(A_99,B_100)) = k2_xboole_0(k3_xboole_0(A_99,B_100),A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_18])).

tff(c_465,plain,(
    ! [A_101,B_102] : k2_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = A_101 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_251,c_452])).

tff(c_475,plain,(
    ! [B_102] : k3_xboole_0(k1_xboole_0,B_102) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_284])).

tff(c_499,plain,(
    ! [B_106] : k3_xboole_0(k1_xboole_0,B_106) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_284])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_641,plain,(
    ! [B_113] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_2])).

tff(c_647,plain,(
    ! [B_113] : k2_xboole_0(k3_xboole_0(k1_xboole_0,B_113),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_16])).

tff(c_661,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_475,c_647])).

tff(c_510,plain,(
    ! [B_106] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_2])).

tff(c_668,plain,(
    ! [B_114] : k4_xboole_0(k1_xboole_0,B_114) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_510])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_676,plain,(
    ! [B_114] :
      ( k1_xboole_0 = B_114
      | ~ r1_tarski(B_114,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_10])).

tff(c_934,plain,(
    ! [A_131,B_132] :
      ( k4_xboole_0(A_131,B_132) = k1_xboole_0
      | ~ r1_tarski(A_131,k2_xboole_0(B_132,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_925,c_676])).

tff(c_1650,plain,(
    ! [A_169,B_170] :
      ( k4_xboole_0(A_169,B_170) = k1_xboole_0
      | ~ r1_tarski(A_169,B_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_934])).

tff(c_1754,plain,(
    ! [A_173,B_174] : k4_xboole_0(k4_xboole_0(A_173,B_174),A_173) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_1650])).

tff(c_1775,plain,(
    ! [A_173,B_174] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_173,B_174),A_173),k1_xboole_0) = k4_xboole_0(A_173,B_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_1754,c_16])).

tff(c_22773,plain,(
    ! [A_484,B_485] : k3_xboole_0(A_484,k4_xboole_0(A_484,B_485)) = k4_xboole_0(A_484,B_485) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_190,c_1775])).

tff(c_463,plain,(
    ! [A_99,B_100] : k2_xboole_0(A_99,k3_xboole_0(A_99,B_100)) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_251,c_452])).

tff(c_23264,plain,(
    ! [A_486,B_487] : k2_xboole_0(A_486,k4_xboole_0(A_486,B_487)) = A_486 ),
    inference(superposition,[status(thm),theory(equality)],[c_22773,c_463])).

tff(c_23588,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1477,c_23264])).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_3167,plain,(
    ! [A_210,B_211] :
      ( k4_subset_1(u1_struct_0(A_210),B_211,k2_tops_1(A_210,B_211)) = k2_pre_topc(A_210,B_211)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ l1_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3188,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_3167])).

tff(c_3200,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3188])).

tff(c_370,plain,(
    ! [A_96,B_97] : k2_xboole_0(A_96,k2_xboole_0(A_96,B_97)) = k2_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_402,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_370])).

tff(c_410,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_402])).

tff(c_717,plain,(
    ! [A_116,B_117,C_118] :
      ( r1_tarski(A_116,k2_xboole_0(B_117,C_118))
      | ~ r1_tarski(k4_xboole_0(A_116,B_117),C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_730,plain,(
    ! [A_119,B_120] : r1_tarski(A_119,k2_xboole_0(B_120,A_119)) ),
    inference(resolution,[status(thm)],[c_8,c_717])).

tff(c_748,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_730])).

tff(c_2759,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1477,c_8])).

tff(c_170,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(A_83,B_84)
      | ~ m1_subset_1(A_83,k1_zfmisc_1(B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_183,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_170])).

tff(c_492,plain,(
    ! [A_103,C_104,B_105] :
      ( r1_tarski(A_103,C_104)
      | ~ r1_tarski(B_105,C_104)
      | ~ r1_tarski(A_103,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_574,plain,(
    ! [A_108] :
      ( r1_tarski(A_108,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_108,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_183,c_492])).

tff(c_6,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(A_4,C_6)
      | ~ r1_tarski(B_5,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_577,plain,(
    ! [A_4,A_108] :
      ( r1_tarski(A_4,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_4,A_108)
      | ~ r1_tarski(A_108,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_574,c_6])).

tff(c_2767,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_2759,c_577])).

tff(c_2773,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_2767])).

tff(c_46,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(A_46,k1_zfmisc_1(B_47))
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2245,plain,(
    ! [A_186,B_187,C_188] :
      ( k4_subset_1(A_186,B_187,C_188) = k2_xboole_0(B_187,C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(A_186))
      | ~ m1_subset_1(B_187,k1_zfmisc_1(A_186)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_11362,plain,(
    ! [B_371,B_372,A_373] :
      ( k4_subset_1(B_371,B_372,A_373) = k2_xboole_0(B_372,A_373)
      | ~ m1_subset_1(B_372,k1_zfmisc_1(B_371))
      | ~ r1_tarski(A_373,B_371) ) ),
    inference(resolution,[status(thm)],[c_46,c_2245])).

tff(c_11495,plain,(
    ! [A_376] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_376) = k2_xboole_0('#skF_2',A_376)
      | ~ r1_tarski(A_376,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_60,c_11362])).

tff(c_11590,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2773,c_11495])).

tff(c_11657,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3200,c_11590])).

tff(c_24006,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23588,c_11657])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2139,plain,(
    ! [A_183,B_184] :
      ( v4_pre_topc(k2_pre_topc(A_183,B_184),A_183)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2158,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_2139])).

tff(c_2167,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2158])).

tff(c_24157,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24006,c_2167])).

tff(c_24173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_24157])).

tff(c_24174,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_25492,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25414,c_24174])).

tff(c_24175,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_26222,plain,(
    ! [A_596,B_597] :
      ( r1_tarski(k2_tops_1(A_596,B_597),B_597)
      | ~ v4_pre_topc(B_597,A_596)
      | ~ m1_subset_1(B_597,k1_zfmisc_1(u1_struct_0(A_596)))
      | ~ l1_pre_topc(A_596) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_26243,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_26222])).

tff(c_26255,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_24175,c_26243])).

tff(c_27362,plain,(
    ! [A_630,B_631] :
      ( k7_subset_1(u1_struct_0(A_630),B_631,k2_tops_1(A_630,B_631)) = k1_tops_1(A_630,B_631)
      | ~ m1_subset_1(B_631,k1_zfmisc_1(u1_struct_0(A_630)))
      | ~ l1_pre_topc(A_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_27385,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_27362])).

tff(c_27402,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_25414,c_27385])).

tff(c_24726,plain,(
    ! [A_528,B_529] :
      ( k4_xboole_0(A_528,B_529) = k3_subset_1(A_528,B_529)
      | ~ m1_subset_1(B_529,k1_zfmisc_1(A_528)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28739,plain,(
    ! [B_673,A_674] :
      ( k4_xboole_0(B_673,A_674) = k3_subset_1(B_673,A_674)
      | ~ r1_tarski(A_674,B_673) ) ),
    inference(resolution,[status(thm)],[c_46,c_24726])).

tff(c_28832,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26255,c_28739])).

tff(c_28906,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27402,c_28832])).

tff(c_24984,plain,(
    ! [A_542,B_543] :
      ( k3_subset_1(A_542,k3_subset_1(A_542,B_543)) = B_543
      | ~ m1_subset_1(B_543,k1_zfmisc_1(A_542)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_25000,plain,(
    ! [B_47,A_46] :
      ( k3_subset_1(B_47,k3_subset_1(B_47,A_46)) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_46,c_24984])).

tff(c_31541,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28906,c_25000])).

tff(c_31553,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26255,c_31541])).

tff(c_36,plain,(
    ! [A_37,B_38] : k6_subset_1(A_37,B_38) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    ! [A_30,B_31] : m1_subset_1(k6_subset_1(A_30,B_31),k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_73,plain,(
    ! [A_30,B_31] : m1_subset_1(k4_xboole_0(A_30,B_31),k1_zfmisc_1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30])).

tff(c_29846,plain,(
    ! [A_700,B_701] : k4_xboole_0(A_700,k4_xboole_0(A_700,B_701)) = k3_subset_1(A_700,k4_xboole_0(A_700,B_701)) ),
    inference(resolution,[status(thm)],[c_73,c_24726])).

tff(c_31793,plain,(
    ! [A_727,B_728] : m1_subset_1(k3_subset_1(A_727,k4_xboole_0(A_727,B_728)),k1_zfmisc_1(A_727)) ),
    inference(superposition,[status(thm),theory(equality)],[c_29846,c_73])).

tff(c_31859,plain,(
    m1_subset_1(k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_27402,c_31793])).

tff(c_32130,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31553,c_31859])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k3_subset_1(A_28,B_29),k1_zfmisc_1(A_28))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_37730,plain,(
    ! [A_794,B_795] :
      ( k4_xboole_0(A_794,k3_subset_1(A_794,B_795)) = k3_subset_1(A_794,k3_subset_1(A_794,B_795))
      | ~ m1_subset_1(B_795,k1_zfmisc_1(A_794)) ) ),
    inference(resolution,[status(thm)],[c_28,c_24726])).

tff(c_37732,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_32130,c_37730])).

tff(c_37756,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31553,c_28906,c_28906,c_37732])).

tff(c_37758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25492,c_37756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.34/5.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.34/5.36  
% 11.34/5.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.34/5.36  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.34/5.36  
% 11.34/5.36  %Foreground sorts:
% 11.34/5.36  
% 11.34/5.36  
% 11.34/5.36  %Background operators:
% 11.34/5.36  
% 11.34/5.36  
% 11.34/5.36  %Foreground operators:
% 11.34/5.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.34/5.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.34/5.36  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 11.34/5.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.34/5.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.34/5.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.34/5.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.34/5.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.34/5.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.34/5.36  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.34/5.36  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.34/5.36  tff('#skF_2', type, '#skF_2': $i).
% 11.34/5.36  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.34/5.36  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 11.34/5.36  tff('#skF_1', type, '#skF_1': $i).
% 11.34/5.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.34/5.36  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.34/5.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.34/5.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.34/5.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.34/5.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.34/5.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.34/5.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.34/5.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.34/5.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.34/5.36  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.34/5.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.34/5.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.34/5.36  
% 11.34/5.38  tff(f_151, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 11.34/5.38  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.34/5.38  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 11.34/5.38  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.34/5.38  tff(f_91, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 11.34/5.38  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.34/5.38  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 11.34/5.38  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.34/5.38  tff(f_51, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 11.34/5.38  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 11.34/5.38  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.34/5.38  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 11.34/5.38  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 11.34/5.38  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 11.34/5.38  tff(f_95, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.34/5.38  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.34/5.38  tff(f_79, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.34/5.38  tff(f_109, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 11.34/5.38  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 11.34/5.38  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 11.34/5.38  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 11.34/5.38  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.34/5.38  tff(f_81, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.34/5.38  tff(f_69, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 11.34/5.38  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.34/5.38  tff(c_60, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.34/5.38  tff(c_25395, plain, (![A_563, B_564, C_565]: (k7_subset_1(A_563, B_564, C_565)=k4_xboole_0(B_564, C_565) | ~m1_subset_1(B_564, k1_zfmisc_1(A_563)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.34/5.38  tff(c_25414, plain, (![C_565]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_565)=k4_xboole_0('#skF_2', C_565))), inference(resolution, [status(thm)], [c_60, c_25395])).
% 11.34/5.38  tff(c_66, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.34/5.38  tff(c_137, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_66])).
% 11.34/5.38  tff(c_1394, plain, (![A_154, B_155, C_156]: (k7_subset_1(A_154, B_155, C_156)=k4_xboole_0(B_155, C_156) | ~m1_subset_1(B_155, k1_zfmisc_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.34/5.38  tff(c_1471, plain, (![C_160]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_160)=k4_xboole_0('#skF_2', C_160))), inference(resolution, [status(thm)], [c_60, c_1394])).
% 11.34/5.38  tff(c_72, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.34/5.38  tff(c_240, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_137, c_72])).
% 11.34/5.38  tff(c_1477, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1471, c_240])).
% 11.34/5.38  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.34/5.38  tff(c_20, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.34/5.38  tff(c_139, plain, (![A_77, B_78]: (k1_setfam_1(k2_tarski(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.34/5.38  tff(c_184, plain, (![A_85, B_86]: (k1_setfam_1(k2_tarski(A_85, B_86))=k3_xboole_0(B_86, A_85))), inference(superposition, [status(thm), theory('equality')], [c_20, c_139])).
% 11.34/5.38  tff(c_42, plain, (![A_44, B_45]: (k1_setfam_1(k2_tarski(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.34/5.38  tff(c_190, plain, (![B_86, A_85]: (k3_xboole_0(B_86, A_85)=k3_xboole_0(A_85, B_86))), inference(superposition, [status(thm), theory('equality')], [c_184, c_42])).
% 11.34/5.38  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.34/5.38  tff(c_925, plain, (![A_131, B_132, C_133]: (r1_tarski(k4_xboole_0(A_131, B_132), C_133) | ~r1_tarski(A_131, k2_xboole_0(B_132, C_133)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.34/5.38  tff(c_155, plain, (![A_81, B_82]: (k3_tarski(k2_tarski(A_81, B_82))=k2_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.34/5.38  tff(c_245, plain, (![A_89, B_90]: (k3_tarski(k2_tarski(A_89, B_90))=k2_xboole_0(B_90, A_89))), inference(superposition, [status(thm), theory('equality')], [c_20, c_155])).
% 11.34/5.38  tff(c_22, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.34/5.38  tff(c_268, plain, (![B_91, A_92]: (k2_xboole_0(B_91, A_92)=k2_xboole_0(A_92, B_91))), inference(superposition, [status(thm), theory('equality')], [c_245, c_22])).
% 11.34/5.38  tff(c_284, plain, (![A_92]: (k2_xboole_0(k1_xboole_0, A_92)=A_92)), inference(superposition, [status(thm), theory('equality')], [c_268, c_4])).
% 11.34/5.38  tff(c_16, plain, (![A_17, B_18]: (k2_xboole_0(k3_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.34/5.38  tff(c_251, plain, (![B_90, A_89]: (k2_xboole_0(B_90, A_89)=k2_xboole_0(A_89, B_90))), inference(superposition, [status(thm), theory('equality')], [c_245, c_22])).
% 11.34/5.38  tff(c_446, plain, (![A_99, B_100]: (k2_xboole_0(k3_xboole_0(A_99, B_100), k4_xboole_0(A_99, B_100))=A_99)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.34/5.38  tff(c_18, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k2_xboole_0(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.34/5.38  tff(c_452, plain, (![A_99, B_100]: (k2_xboole_0(k3_xboole_0(A_99, B_100), k4_xboole_0(A_99, B_100))=k2_xboole_0(k3_xboole_0(A_99, B_100), A_99))), inference(superposition, [status(thm), theory('equality')], [c_446, c_18])).
% 11.34/5.38  tff(c_465, plain, (![A_101, B_102]: (k2_xboole_0(A_101, k3_xboole_0(A_101, B_102))=A_101)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_251, c_452])).
% 11.34/5.38  tff(c_475, plain, (![B_102]: (k3_xboole_0(k1_xboole_0, B_102)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_465, c_284])).
% 11.34/5.38  tff(c_499, plain, (![B_106]: (k3_xboole_0(k1_xboole_0, B_106)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_465, c_284])).
% 11.34/5.38  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.34/5.38  tff(c_641, plain, (![B_113]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_113))), inference(superposition, [status(thm), theory('equality')], [c_499, c_2])).
% 11.34/5.38  tff(c_647, plain, (![B_113]: (k2_xboole_0(k3_xboole_0(k1_xboole_0, B_113), k5_xboole_0(k1_xboole_0, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_641, c_16])).
% 11.34/5.38  tff(c_661, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_284, c_475, c_647])).
% 11.34/5.38  tff(c_510, plain, (![B_106]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_106))), inference(superposition, [status(thm), theory('equality')], [c_499, c_2])).
% 11.34/5.38  tff(c_668, plain, (![B_114]: (k4_xboole_0(k1_xboole_0, B_114)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_661, c_510])).
% 11.34/5.38  tff(c_10, plain, (![A_9, B_10]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k4_xboole_0(B_10, A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.34/5.38  tff(c_676, plain, (![B_114]: (k1_xboole_0=B_114 | ~r1_tarski(B_114, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_668, c_10])).
% 11.34/5.38  tff(c_934, plain, (![A_131, B_132]: (k4_xboole_0(A_131, B_132)=k1_xboole_0 | ~r1_tarski(A_131, k2_xboole_0(B_132, k1_xboole_0)))), inference(resolution, [status(thm)], [c_925, c_676])).
% 11.34/5.38  tff(c_1650, plain, (![A_169, B_170]: (k4_xboole_0(A_169, B_170)=k1_xboole_0 | ~r1_tarski(A_169, B_170))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_934])).
% 11.34/5.38  tff(c_1754, plain, (![A_173, B_174]: (k4_xboole_0(k4_xboole_0(A_173, B_174), A_173)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1650])).
% 11.34/5.38  tff(c_1775, plain, (![A_173, B_174]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_173, B_174), A_173), k1_xboole_0)=k4_xboole_0(A_173, B_174))), inference(superposition, [status(thm), theory('equality')], [c_1754, c_16])).
% 11.34/5.38  tff(c_22773, plain, (![A_484, B_485]: (k3_xboole_0(A_484, k4_xboole_0(A_484, B_485))=k4_xboole_0(A_484, B_485))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_190, c_1775])).
% 11.34/5.38  tff(c_463, plain, (![A_99, B_100]: (k2_xboole_0(A_99, k3_xboole_0(A_99, B_100))=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_251, c_452])).
% 11.34/5.38  tff(c_23264, plain, (![A_486, B_487]: (k2_xboole_0(A_486, k4_xboole_0(A_486, B_487))=A_486)), inference(superposition, [status(thm), theory('equality')], [c_22773, c_463])).
% 11.34/5.38  tff(c_23588, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1477, c_23264])).
% 11.34/5.38  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.34/5.38  tff(c_3167, plain, (![A_210, B_211]: (k4_subset_1(u1_struct_0(A_210), B_211, k2_tops_1(A_210, B_211))=k2_pre_topc(A_210, B_211) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_210))) | ~l1_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.34/5.38  tff(c_3188, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_3167])).
% 11.34/5.38  tff(c_3200, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3188])).
% 11.34/5.38  tff(c_370, plain, (![A_96, B_97]: (k2_xboole_0(A_96, k2_xboole_0(A_96, B_97))=k2_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.34/5.38  tff(c_402, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_370])).
% 11.34/5.38  tff(c_410, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_402])).
% 11.34/5.38  tff(c_717, plain, (![A_116, B_117, C_118]: (r1_tarski(A_116, k2_xboole_0(B_117, C_118)) | ~r1_tarski(k4_xboole_0(A_116, B_117), C_118))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.34/5.38  tff(c_730, plain, (![A_119, B_120]: (r1_tarski(A_119, k2_xboole_0(B_120, A_119)))), inference(resolution, [status(thm)], [c_8, c_717])).
% 11.34/5.38  tff(c_748, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_410, c_730])).
% 11.34/5.38  tff(c_2759, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1477, c_8])).
% 11.34/5.38  tff(c_170, plain, (![A_83, B_84]: (r1_tarski(A_83, B_84) | ~m1_subset_1(A_83, k1_zfmisc_1(B_84)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.34/5.38  tff(c_183, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_170])).
% 11.34/5.38  tff(c_492, plain, (![A_103, C_104, B_105]: (r1_tarski(A_103, C_104) | ~r1_tarski(B_105, C_104) | ~r1_tarski(A_103, B_105))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.34/5.38  tff(c_574, plain, (![A_108]: (r1_tarski(A_108, u1_struct_0('#skF_1')) | ~r1_tarski(A_108, '#skF_2'))), inference(resolution, [status(thm)], [c_183, c_492])).
% 11.34/5.38  tff(c_6, plain, (![A_4, C_6, B_5]: (r1_tarski(A_4, C_6) | ~r1_tarski(B_5, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.34/5.38  tff(c_577, plain, (![A_4, A_108]: (r1_tarski(A_4, u1_struct_0('#skF_1')) | ~r1_tarski(A_4, A_108) | ~r1_tarski(A_108, '#skF_2'))), inference(resolution, [status(thm)], [c_574, c_6])).
% 11.34/5.38  tff(c_2767, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_2759, c_577])).
% 11.34/5.38  tff(c_2773, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_748, c_2767])).
% 11.34/5.38  tff(c_46, plain, (![A_46, B_47]: (m1_subset_1(A_46, k1_zfmisc_1(B_47)) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.34/5.38  tff(c_2245, plain, (![A_186, B_187, C_188]: (k4_subset_1(A_186, B_187, C_188)=k2_xboole_0(B_187, C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(A_186)) | ~m1_subset_1(B_187, k1_zfmisc_1(A_186)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.34/5.38  tff(c_11362, plain, (![B_371, B_372, A_373]: (k4_subset_1(B_371, B_372, A_373)=k2_xboole_0(B_372, A_373) | ~m1_subset_1(B_372, k1_zfmisc_1(B_371)) | ~r1_tarski(A_373, B_371))), inference(resolution, [status(thm)], [c_46, c_2245])).
% 11.34/5.38  tff(c_11495, plain, (![A_376]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_376)=k2_xboole_0('#skF_2', A_376) | ~r1_tarski(A_376, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_60, c_11362])).
% 11.34/5.38  tff(c_11590, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2773, c_11495])).
% 11.34/5.38  tff(c_11657, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3200, c_11590])).
% 11.34/5.38  tff(c_24006, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_23588, c_11657])).
% 11.34/5.38  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.34/5.38  tff(c_2139, plain, (![A_183, B_184]: (v4_pre_topc(k2_pre_topc(A_183, B_184), A_183) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.34/5.38  tff(c_2158, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_2139])).
% 11.34/5.38  tff(c_2167, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2158])).
% 11.34/5.38  tff(c_24157, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24006, c_2167])).
% 11.34/5.38  tff(c_24173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_24157])).
% 11.34/5.38  tff(c_24174, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_66])).
% 11.34/5.38  tff(c_25492, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25414, c_24174])).
% 11.34/5.38  tff(c_24175, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 11.34/5.38  tff(c_26222, plain, (![A_596, B_597]: (r1_tarski(k2_tops_1(A_596, B_597), B_597) | ~v4_pre_topc(B_597, A_596) | ~m1_subset_1(B_597, k1_zfmisc_1(u1_struct_0(A_596))) | ~l1_pre_topc(A_596))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.34/5.38  tff(c_26243, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_26222])).
% 11.34/5.38  tff(c_26255, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_24175, c_26243])).
% 11.34/5.38  tff(c_27362, plain, (![A_630, B_631]: (k7_subset_1(u1_struct_0(A_630), B_631, k2_tops_1(A_630, B_631))=k1_tops_1(A_630, B_631) | ~m1_subset_1(B_631, k1_zfmisc_1(u1_struct_0(A_630))) | ~l1_pre_topc(A_630))), inference(cnfTransformation, [status(thm)], [f_139])).
% 11.34/5.38  tff(c_27385, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_27362])).
% 11.34/5.38  tff(c_27402, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_25414, c_27385])).
% 11.34/5.38  tff(c_24726, plain, (![A_528, B_529]: (k4_xboole_0(A_528, B_529)=k3_subset_1(A_528, B_529) | ~m1_subset_1(B_529, k1_zfmisc_1(A_528)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.34/5.38  tff(c_28739, plain, (![B_673, A_674]: (k4_xboole_0(B_673, A_674)=k3_subset_1(B_673, A_674) | ~r1_tarski(A_674, B_673))), inference(resolution, [status(thm)], [c_46, c_24726])).
% 11.34/5.38  tff(c_28832, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26255, c_28739])).
% 11.34/5.38  tff(c_28906, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_27402, c_28832])).
% 11.34/5.38  tff(c_24984, plain, (![A_542, B_543]: (k3_subset_1(A_542, k3_subset_1(A_542, B_543))=B_543 | ~m1_subset_1(B_543, k1_zfmisc_1(A_542)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.34/5.38  tff(c_25000, plain, (![B_47, A_46]: (k3_subset_1(B_47, k3_subset_1(B_47, A_46))=A_46 | ~r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_46, c_24984])).
% 11.34/5.38  tff(c_31541, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28906, c_25000])).
% 11.34/5.38  tff(c_31553, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26255, c_31541])).
% 11.34/5.38  tff(c_36, plain, (![A_37, B_38]: (k6_subset_1(A_37, B_38)=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.34/5.38  tff(c_30, plain, (![A_30, B_31]: (m1_subset_1(k6_subset_1(A_30, B_31), k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.34/5.38  tff(c_73, plain, (![A_30, B_31]: (m1_subset_1(k4_xboole_0(A_30, B_31), k1_zfmisc_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30])).
% 11.34/5.38  tff(c_29846, plain, (![A_700, B_701]: (k4_xboole_0(A_700, k4_xboole_0(A_700, B_701))=k3_subset_1(A_700, k4_xboole_0(A_700, B_701)))), inference(resolution, [status(thm)], [c_73, c_24726])).
% 11.34/5.38  tff(c_31793, plain, (![A_727, B_728]: (m1_subset_1(k3_subset_1(A_727, k4_xboole_0(A_727, B_728)), k1_zfmisc_1(A_727)))), inference(superposition, [status(thm), theory('equality')], [c_29846, c_73])).
% 11.34/5.38  tff(c_31859, plain, (m1_subset_1(k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_27402, c_31793])).
% 11.34/5.38  tff(c_32130, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_31553, c_31859])).
% 11.34/5.38  tff(c_28, plain, (![A_28, B_29]: (m1_subset_1(k3_subset_1(A_28, B_29), k1_zfmisc_1(A_28)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.34/5.38  tff(c_37730, plain, (![A_794, B_795]: (k4_xboole_0(A_794, k3_subset_1(A_794, B_795))=k3_subset_1(A_794, k3_subset_1(A_794, B_795)) | ~m1_subset_1(B_795, k1_zfmisc_1(A_794)))), inference(resolution, [status(thm)], [c_28, c_24726])).
% 11.34/5.38  tff(c_37732, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_32130, c_37730])).
% 11.34/5.38  tff(c_37756, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_31553, c_28906, c_28906, c_37732])).
% 11.34/5.38  tff(c_37758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25492, c_37756])).
% 11.34/5.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.34/5.38  
% 11.34/5.38  Inference rules
% 11.34/5.38  ----------------------
% 11.34/5.38  #Ref     : 0
% 11.34/5.38  #Sup     : 9244
% 11.34/5.38  #Fact    : 0
% 11.34/5.38  #Define  : 0
% 11.34/5.38  #Split   : 4
% 11.34/5.38  #Chain   : 0
% 11.34/5.38  #Close   : 0
% 11.34/5.38  
% 11.34/5.38  Ordering : KBO
% 11.34/5.38  
% 11.34/5.38  Simplification rules
% 11.34/5.38  ----------------------
% 11.54/5.38  #Subsume      : 436
% 11.54/5.38  #Demod        : 9254
% 11.54/5.38  #Tautology    : 6555
% 11.54/5.38  #SimpNegUnit  : 3
% 11.54/5.38  #BackRed      : 42
% 11.54/5.38  
% 11.54/5.38  #Partial instantiations: 0
% 11.54/5.38  #Strategies tried      : 1
% 11.54/5.38  
% 11.54/5.38  Timing (in seconds)
% 11.54/5.38  ----------------------
% 11.54/5.39  Preprocessing        : 0.34
% 11.54/5.39  Parsing              : 0.18
% 11.54/5.39  CNF conversion       : 0.02
% 11.54/5.39  Main loop            : 4.26
% 11.54/5.39  Inferencing          : 0.84
% 11.54/5.39  Reduction            : 2.32
% 11.54/5.39  Demodulation         : 1.98
% 11.54/5.39  BG Simplification    : 0.09
% 11.54/5.39  Subsumption          : 0.79
% 11.54/5.39  Abstraction          : 0.14
% 11.54/5.39  MUC search           : 0.00
% 11.54/5.39  Cooper               : 0.00
% 11.54/5.39  Total                : 4.65
% 11.54/5.39  Index Insertion      : 0.00
% 11.54/5.39  Index Deletion       : 0.00
% 11.54/5.39  Index Matching       : 0.00
% 11.54/5.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
