%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:14 EST 2020

% Result     : Theorem 15.61s
% Output     : CNFRefutation 15.61s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 387 expanded)
%              Number of leaves         :   51 ( 149 expanded)
%              Depth                    :   17
%              Number of atoms          :  243 ( 632 expanded)
%              Number of equality atoms :  120 ( 286 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_158,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_146,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_68,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_44,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_23087,plain,(
    ! [A_616,B_617,C_618] :
      ( k7_subset_1(A_616,B_617,C_618) = k4_xboole_0(B_617,C_618)
      | ~ m1_subset_1(B_617,k1_zfmisc_1(A_616)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_23096,plain,(
    ! [C_618] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_618) = k4_xboole_0('#skF_3',C_618) ),
    inference(resolution,[status(thm)],[c_64,c_23087])).

tff(c_25792,plain,(
    ! [A_676,B_677] :
      ( k7_subset_1(u1_struct_0(A_676),B_677,k2_tops_1(A_676,B_677)) = k1_tops_1(A_676,B_677)
      | ~ m1_subset_1(B_677,k1_zfmisc_1(u1_struct_0(A_676)))
      | ~ l1_pre_topc(A_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_25802,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_25792])).

tff(c_25808,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_23096,c_25802])).

tff(c_26,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_25846,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k3_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25808,c_26])).

tff(c_76,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_115,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_70,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_230,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_4001,plain,(
    ! [B_243,A_244] :
      ( v4_pre_topc(B_243,A_244)
      | k2_pre_topc(A_244,B_243) != B_243
      | ~ v2_pre_topc(A_244)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ l1_pre_topc(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4015,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_4001])).

tff(c_4021,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_4015])).

tff(c_4022,plain,(
    k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_4021])).

tff(c_167,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(A_80,B_81)
      | ~ m1_subset_1(A_80,k1_zfmisc_1(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_171,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_167])).

tff(c_2721,plain,(
    ! [A_198,B_199,C_200] :
      ( k7_subset_1(A_198,B_199,C_200) = k4_xboole_0(B_199,C_200)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_198)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2822,plain,(
    ! [C_202] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_202) = k4_xboole_0('#skF_3',C_202) ),
    inference(resolution,[status(thm)],[c_64,c_2721])).

tff(c_2834,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_2822])).

tff(c_2730,plain,(
    ! [C_200] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_200) = k4_xboole_0('#skF_3',C_200) ),
    inference(resolution,[status(thm)],[c_64,c_2721])).

tff(c_4307,plain,(
    ! [A_255,B_256] :
      ( k7_subset_1(u1_struct_0(A_255),B_256,k2_tops_1(A_255,B_256)) = k1_tops_1(A_255,B_256)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_4317,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_4307])).

tff(c_4323,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2730,c_4317])).

tff(c_4419,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k3_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4323,c_26])).

tff(c_4429,plain,(
    k3_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2834,c_4419])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6725,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4429,c_12])).

tff(c_4511,plain,(
    ! [A_257,B_258] :
      ( k4_subset_1(u1_struct_0(A_257),B_258,k2_tops_1(A_257,B_258)) = k2_pre_topc(A_257,B_258)
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ l1_pre_topc(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4521,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_4511])).

tff(c_4527,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4521])).

tff(c_30,plain,(
    ! [B_30,A_29] : k2_tarski(B_30,A_29) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_172,plain,(
    ! [A_82,B_83] : k3_tarski(k2_tarski(A_82,B_83)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_437,plain,(
    ! [A_100,B_101] : k3_tarski(k2_tarski(A_100,B_101)) = k2_xboole_0(B_101,A_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_172])).

tff(c_32,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_443,plain,(
    ! [B_101,A_100] : k2_xboole_0(B_101,A_100) = k2_xboole_0(A_100,B_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_32])).

tff(c_28,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_752,plain,(
    ! [A_117,C_118,B_119] :
      ( r1_tarski(A_117,C_118)
      | ~ r1_tarski(B_119,C_118)
      | ~ r1_tarski(A_117,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_906,plain,(
    ! [A_131,A_132,B_133] :
      ( r1_tarski(A_131,k2_xboole_0(A_132,B_133))
      | ~ r1_tarski(A_131,A_132) ) ),
    inference(resolution,[status(thm)],[c_28,c_752])).

tff(c_920,plain,(
    ! [A_131,A_100,B_101] :
      ( r1_tarski(A_131,k2_xboole_0(A_100,B_101))
      | ~ r1_tarski(A_131,B_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_906])).

tff(c_971,plain,(
    ! [A_137,B_138,C_139] :
      ( r1_tarski(k4_xboole_0(A_137,B_138),C_139)
      | ~ r1_tarski(A_137,k2_xboole_0(B_138,C_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8434,plain,(
    ! [A_329,B_330,C_331] :
      ( r1_tarski(k3_xboole_0(A_329,B_330),C_331)
      | ~ r1_tarski(A_329,k2_xboole_0(k4_xboole_0(A_329,B_330),C_331)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_971])).

tff(c_8656,plain,(
    ! [A_332,B_333,B_334] :
      ( r1_tarski(k3_xboole_0(A_332,B_333),B_334)
      | ~ r1_tarski(A_332,B_334) ) ),
    inference(resolution,[status(thm)],[c_920,c_8434])).

tff(c_8713,plain,(
    ! [B_334] :
      ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),B_334)
      | ~ r1_tarski('#skF_3',B_334) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4429,c_8656])).

tff(c_48,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3730,plain,(
    ! [A_230,B_231,C_232] :
      ( k4_subset_1(A_230,B_231,C_232) = k2_xboole_0(B_231,C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(A_230))
      | ~ m1_subset_1(B_231,k1_zfmisc_1(A_230)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20049,plain,(
    ! [B_460,B_461,A_462] :
      ( k4_subset_1(B_460,B_461,A_462) = k2_xboole_0(B_461,A_462)
      | ~ m1_subset_1(B_461,k1_zfmisc_1(B_460))
      | ~ r1_tarski(A_462,B_460) ) ),
    inference(resolution,[status(thm)],[c_48,c_3730])).

tff(c_20421,plain,(
    ! [A_467] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_467) = k2_xboole_0('#skF_3',A_467)
      | ~ r1_tarski(A_467,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_64,c_20049])).

tff(c_20445,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8713,c_20421])).

tff(c_20584,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_6725,c_4527,c_20445])).

tff(c_20586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4022,c_20584])).

tff(c_20587,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_20944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_20587])).

tff(c_20945,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_21039,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20945,c_70])).

tff(c_23169,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23096,c_21039])).

tff(c_63502,plain,(
    k3_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25846,c_23169])).

tff(c_23421,plain,(
    ! [A_625,B_626] :
      ( k2_pre_topc(A_625,B_626) = B_626
      | ~ v4_pre_topc(B_626,A_625)
      | ~ m1_subset_1(B_626,k1_zfmisc_1(u1_struct_0(A_625)))
      | ~ l1_pre_topc(A_625) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_23432,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_23421])).

tff(c_23437,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_20945,c_23432])).

tff(c_25558,plain,(
    ! [A_666,B_667] :
      ( k4_subset_1(u1_struct_0(A_666),B_667,k2_tops_1(A_666,B_667)) = k2_pre_topc(A_666,B_667)
      | ~ m1_subset_1(B_667,k1_zfmisc_1(u1_struct_0(A_666)))
      | ~ l1_pre_topc(A_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_25568,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_25558])).

tff(c_25574,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_23437,c_25568])).

tff(c_54,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(k2_tops_1(A_52,B_53),k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_24640,plain,(
    ! [A_651,B_652,C_653] :
      ( k4_subset_1(A_651,B_652,C_653) = k2_xboole_0(B_652,C_653)
      | ~ m1_subset_1(C_653,k1_zfmisc_1(A_651))
      | ~ m1_subset_1(B_652,k1_zfmisc_1(A_651)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_59816,plain,(
    ! [A_1035,B_1036,B_1037] :
      ( k4_subset_1(u1_struct_0(A_1035),B_1036,k2_tops_1(A_1035,B_1037)) = k2_xboole_0(B_1036,k2_tops_1(A_1035,B_1037))
      | ~ m1_subset_1(B_1036,k1_zfmisc_1(u1_struct_0(A_1035)))
      | ~ m1_subset_1(B_1037,k1_zfmisc_1(u1_struct_0(A_1035)))
      | ~ l1_pre_topc(A_1035) ) ),
    inference(resolution,[status(thm)],[c_54,c_24640])).

tff(c_59832,plain,(
    ! [B_1037] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_1037)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_1037))
      | ~ m1_subset_1(B_1037,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_59816])).

tff(c_64759,plain,(
    ! [B_1075] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_1075)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_1075))
      | ~ m1_subset_1(B_1075,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_59832])).

tff(c_64782,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_64759])).

tff(c_64791,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25574,c_64782])).

tff(c_20,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_21403,plain,(
    ! [A_517,B_518] : k4_xboole_0(A_517,k4_xboole_0(A_517,B_518)) = k3_xboole_0(A_517,B_518) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_21435,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_21403])).

tff(c_21455,plain,(
    ! [A_520] : k4_xboole_0(A_520,A_520) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_21435])).

tff(c_21460,plain,(
    ! [A_520] : k4_xboole_0(A_520,k1_xboole_0) = k3_xboole_0(A_520,A_520) ),
    inference(superposition,[status(thm),theory(equality)],[c_21455,c_26])).

tff(c_21484,plain,(
    ! [A_520] : k3_xboole_0(A_520,A_520) = A_520 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_21460])).

tff(c_21003,plain,(
    ! [A_492,B_493] : k3_tarski(k2_tarski(A_492,B_493)) = k2_xboole_0(A_492,B_493) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_21267,plain,(
    ! [A_512,B_513] : k3_tarski(k2_tarski(A_512,B_513)) = k2_xboole_0(B_513,A_512) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_21003])).

tff(c_21290,plain,(
    ! [B_514,A_515] : k2_xboole_0(B_514,A_515) = k2_xboole_0(A_515,B_514) ),
    inference(superposition,[status(thm),theory(equality)],[c_21267,c_32])).

tff(c_21316,plain,(
    ! [B_514,A_515] : r1_tarski(B_514,k2_xboole_0(A_515,B_514)) ),
    inference(superposition,[status(thm),theory(equality)],[c_21290,c_28])).

tff(c_99,plain,(
    ! [A_73,B_74] : k2_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = A_73 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_111,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_22907,plain,(
    ! [A_607,B_608,C_609] :
      ( r1_tarski(k4_xboole_0(A_607,B_608),C_609)
      | ~ r1_tarski(A_607,k2_xboole_0(B_608,C_609)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_21155,plain,(
    ! [A_503,B_504] : k5_xboole_0(A_503,k3_xboole_0(A_503,B_504)) = k4_xboole_0(A_503,B_504) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_21173,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k4_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_21155])).

tff(c_21176,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_21173])).

tff(c_21018,plain,(
    ! [A_494,B_495] : k1_setfam_1(k2_tarski(A_494,B_495)) = k3_xboole_0(A_494,B_495) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_21040,plain,(
    ! [A_498,B_499] : k1_setfam_1(k2_tarski(A_498,B_499)) = k3_xboole_0(B_499,A_498) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_21018])).

tff(c_44,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_21063,plain,(
    ! [B_500,A_501] : k3_xboole_0(B_500,A_501) = k3_xboole_0(A_501,B_500) ),
    inference(superposition,[status(thm),theory(equality)],[c_21040,c_44])).

tff(c_21085,plain,(
    ! [A_501] : k3_xboole_0(k1_xboole_0,A_501) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_21063,c_14])).

tff(c_21164,plain,(
    ! [A_501] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_501) ),
    inference(superposition,[status(thm),theory(equality)],[c_21085,c_21155])).

tff(c_21228,plain,(
    ! [A_508] : k4_xboole_0(k1_xboole_0,A_508) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21176,c_21164])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k4_xboole_0(B_17,A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_21233,plain,(
    ! [A_508] :
      ( k1_xboole_0 = A_508
      | ~ r1_tarski(A_508,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21228,c_18])).

tff(c_22925,plain,(
    ! [A_607,B_608] :
      ( k4_xboole_0(A_607,B_608) = k1_xboole_0
      | ~ r1_tarski(A_607,k2_xboole_0(B_608,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_22907,c_21233])).

tff(c_23181,plain,(
    ! [A_623,B_624] :
      ( k4_xboole_0(A_623,B_624) = k1_xboole_0
      | ~ r1_tarski(A_623,B_624) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_22925])).

tff(c_23745,plain,(
    ! [B_633,A_634] : k4_xboole_0(B_633,k2_xboole_0(A_634,B_633)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21316,c_23181])).

tff(c_23792,plain,(
    ! [B_633,A_634] : k3_xboole_0(B_633,k2_xboole_0(A_634,B_633)) = k4_xboole_0(B_633,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_23745,c_26])).

tff(c_23847,plain,(
    ! [B_633,A_634] : k3_xboole_0(B_633,k2_xboole_0(A_634,B_633)) = B_633 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_23792])).

tff(c_21046,plain,(
    ! [B_499,A_498] : k3_xboole_0(B_499,A_498) = k3_xboole_0(A_498,B_499) ),
    inference(superposition,[status(thm),theory(equality)],[c_21040,c_44])).

tff(c_94,plain,(
    ! [A_70,B_71] : r1_tarski(k4_xboole_0(A_70,B_71),A_70) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_97,plain,(
    ! [A_18] : r1_tarski(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_94])).

tff(c_21441,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_21435])).

tff(c_22781,plain,(
    ! [A_602,B_603] :
      ( k4_xboole_0(A_602,B_603) = k3_subset_1(A_602,B_603)
      | ~ m1_subset_1(B_603,k1_zfmisc_1(A_602)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26697,plain,(
    ! [B_698,A_699] :
      ( k4_xboole_0(B_698,A_699) = k3_subset_1(B_698,A_699)
      | ~ r1_tarski(A_699,B_698) ) ),
    inference(resolution,[status(thm)],[c_48,c_22781])).

tff(c_26847,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_subset_1(A_18,A_18) ),
    inference(resolution,[status(thm)],[c_97,c_26697])).

tff(c_26911,plain,(
    ! [A_700] : k3_subset_1(A_700,A_700) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21441,c_26847])).

tff(c_22542,plain,(
    ! [A_588,B_589] :
      ( k3_subset_1(A_588,k3_subset_1(A_588,B_589)) = B_589
      | ~ m1_subset_1(B_589,k1_zfmisc_1(A_588)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22550,plain,(
    ! [B_48,A_47] :
      ( k3_subset_1(B_48,k3_subset_1(B_48,A_47)) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_48,c_22542])).

tff(c_26916,plain,(
    ! [A_700] :
      ( k3_subset_1(A_700,k1_xboole_0) = A_700
      | ~ r1_tarski(A_700,A_700) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26911,c_22550])).

tff(c_26924,plain,(
    ! [A_700] : k3_subset_1(A_700,k1_xboole_0) = A_700 ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_26916])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21595,plain,(
    ! [A_529,B_530] : r1_tarski(k3_xboole_0(A_529,B_530),A_529) ),
    inference(superposition,[status(thm),theory(equality)],[c_21403,c_16])).

tff(c_21608,plain,(
    ! [B_499,A_498] : r1_tarski(k3_xboole_0(B_499,A_498),A_498) ),
    inference(superposition,[status(thm),theory(equality)],[c_21046,c_21595])).

tff(c_23302,plain,(
    ! [B_499,A_498] : k4_xboole_0(k3_xboole_0(B_499,A_498),A_498) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21608,c_23181])).

tff(c_26850,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_subset_1(A_14,k4_xboole_0(A_14,B_15)) ),
    inference(resolution,[status(thm)],[c_16,c_26697])).

tff(c_27003,plain,(
    ! [A_703,B_704] : k3_subset_1(A_703,k4_xboole_0(A_703,B_704)) = k3_xboole_0(A_703,B_704) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26850])).

tff(c_27057,plain,(
    ! [B_499,A_498] : k3_xboole_0(k3_xboole_0(B_499,A_498),A_498) = k3_subset_1(k3_xboole_0(B_499,A_498),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_23302,c_27003])).

tff(c_38473,plain,(
    ! [B_845,A_846] : k3_xboole_0(k3_xboole_0(B_845,A_846),A_846) = k3_xboole_0(B_845,A_846) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26924,c_27057])).

tff(c_46634,plain,(
    ! [A_922,B_923] : k3_xboole_0(k3_xboole_0(A_922,B_923),A_922) = k3_xboole_0(B_923,A_922) ),
    inference(superposition,[status(thm),theory(equality)],[c_21046,c_38473])).

tff(c_46925,plain,(
    ! [A_634,B_633] : k3_xboole_0(k2_xboole_0(A_634,B_633),B_633) = k3_xboole_0(B_633,B_633) ),
    inference(superposition,[status(thm),theory(equality)],[c_23847,c_46634])).

tff(c_47022,plain,(
    ! [A_634,B_633] : k3_xboole_0(k2_xboole_0(A_634,B_633),B_633) = B_633 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21484,c_46925])).

tff(c_64844,plain,(
    k3_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_64791,c_47022])).

tff(c_64968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63502,c_64844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:15:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.61/8.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.61/8.63  
% 15.61/8.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.61/8.64  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 15.61/8.64  
% 15.61/8.64  %Foreground sorts:
% 15.61/8.64  
% 15.61/8.64  
% 15.61/8.64  %Background operators:
% 15.61/8.64  
% 15.61/8.64  
% 15.61/8.64  %Foreground operators:
% 15.61/8.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.61/8.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.61/8.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.61/8.64  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 15.61/8.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.61/8.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.61/8.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.61/8.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.61/8.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.61/8.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 15.61/8.64  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 15.61/8.64  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 15.61/8.64  tff('#skF_2', type, '#skF_2': $i).
% 15.61/8.64  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 15.61/8.64  tff('#skF_3', type, '#skF_3': $i).
% 15.61/8.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.61/8.64  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 15.61/8.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.61/8.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 15.61/8.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.61/8.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 15.61/8.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.61/8.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.61/8.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.61/8.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.61/8.64  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 15.61/8.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.61/8.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 15.61/8.64  
% 15.61/8.66  tff(f_158, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 15.61/8.66  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 15.61/8.66  tff(f_146, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 15.61/8.66  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.61/8.66  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 15.61/8.66  tff(f_96, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 15.61/8.66  tff(f_42, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 15.61/8.66  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 15.61/8.66  tff(f_66, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 15.61/8.66  tff(f_68, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 15.61/8.66  tff(f_64, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 15.61/8.66  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 15.61/8.66  tff(f_56, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 15.61/8.66  tff(f_86, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 15.61/8.66  tff(f_117, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 15.61/8.66  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 15.61/8.66  tff(f_44, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 15.61/8.66  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.61/8.66  tff(f_92, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 15.61/8.66  tff(f_50, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 15.61/8.66  tff(f_46, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 15.61/8.66  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 15.61/8.66  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 15.61/8.66  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 15.61/8.66  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 15.61/8.66  tff(c_23087, plain, (![A_616, B_617, C_618]: (k7_subset_1(A_616, B_617, C_618)=k4_xboole_0(B_617, C_618) | ~m1_subset_1(B_617, k1_zfmisc_1(A_616)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 15.61/8.66  tff(c_23096, plain, (![C_618]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_618)=k4_xboole_0('#skF_3', C_618))), inference(resolution, [status(thm)], [c_64, c_23087])).
% 15.61/8.66  tff(c_25792, plain, (![A_676, B_677]: (k7_subset_1(u1_struct_0(A_676), B_677, k2_tops_1(A_676, B_677))=k1_tops_1(A_676, B_677) | ~m1_subset_1(B_677, k1_zfmisc_1(u1_struct_0(A_676))) | ~l1_pre_topc(A_676))), inference(cnfTransformation, [status(thm)], [f_146])).
% 15.61/8.66  tff(c_25802, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_25792])).
% 15.61/8.66  tff(c_25808, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_23096, c_25802])).
% 15.61/8.66  tff(c_26, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_62])).
% 15.61/8.66  tff(c_25846, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k3_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_25808, c_26])).
% 15.61/8.66  tff(c_76, plain, (v4_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 15.61/8.66  tff(c_115, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_76])).
% 15.61/8.66  tff(c_70, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 15.61/8.66  tff(c_230, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_70])).
% 15.61/8.66  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 15.61/8.66  tff(c_4001, plain, (![B_243, A_244]: (v4_pre_topc(B_243, A_244) | k2_pre_topc(A_244, B_243)!=B_243 | ~v2_pre_topc(A_244) | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(A_244))) | ~l1_pre_topc(A_244))), inference(cnfTransformation, [status(thm)], [f_111])).
% 15.61/8.66  tff(c_4015, plain, (v4_pre_topc('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3' | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_4001])).
% 15.61/8.66  tff(c_4021, plain, (v4_pre_topc('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_4015])).
% 15.61/8.66  tff(c_4022, plain, (k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_230, c_4021])).
% 15.61/8.66  tff(c_167, plain, (![A_80, B_81]: (r1_tarski(A_80, B_81) | ~m1_subset_1(A_80, k1_zfmisc_1(B_81)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.61/8.66  tff(c_171, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_167])).
% 15.61/8.66  tff(c_2721, plain, (![A_198, B_199, C_200]: (k7_subset_1(A_198, B_199, C_200)=k4_xboole_0(B_199, C_200) | ~m1_subset_1(B_199, k1_zfmisc_1(A_198)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 15.61/8.66  tff(c_2822, plain, (![C_202]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_202)=k4_xboole_0('#skF_3', C_202))), inference(resolution, [status(thm)], [c_64, c_2721])).
% 15.61/8.66  tff(c_2834, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_115, c_2822])).
% 15.61/8.66  tff(c_2730, plain, (![C_200]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_200)=k4_xboole_0('#skF_3', C_200))), inference(resolution, [status(thm)], [c_64, c_2721])).
% 15.61/8.66  tff(c_4307, plain, (![A_255, B_256]: (k7_subset_1(u1_struct_0(A_255), B_256, k2_tops_1(A_255, B_256))=k1_tops_1(A_255, B_256) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255))), inference(cnfTransformation, [status(thm)], [f_146])).
% 15.61/8.66  tff(c_4317, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_4307])).
% 15.61/8.66  tff(c_4323, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2730, c_4317])).
% 15.61/8.66  tff(c_4419, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k3_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4323, c_26])).
% 15.61/8.66  tff(c_4429, plain, (k3_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2834, c_4419])).
% 15.61/8.66  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k3_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.61/8.66  tff(c_6725, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4429, c_12])).
% 15.61/8.66  tff(c_4511, plain, (![A_257, B_258]: (k4_subset_1(u1_struct_0(A_257), B_258, k2_tops_1(A_257, B_258))=k2_pre_topc(A_257, B_258) | ~m1_subset_1(B_258, k1_zfmisc_1(u1_struct_0(A_257))) | ~l1_pre_topc(A_257))), inference(cnfTransformation, [status(thm)], [f_139])).
% 15.61/8.66  tff(c_4521, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_4511])).
% 15.61/8.66  tff(c_4527, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4521])).
% 15.61/8.66  tff(c_30, plain, (![B_30, A_29]: (k2_tarski(B_30, A_29)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_66])).
% 15.61/8.66  tff(c_172, plain, (![A_82, B_83]: (k3_tarski(k2_tarski(A_82, B_83))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.61/8.66  tff(c_437, plain, (![A_100, B_101]: (k3_tarski(k2_tarski(A_100, B_101))=k2_xboole_0(B_101, A_100))), inference(superposition, [status(thm), theory('equality')], [c_30, c_172])).
% 15.61/8.66  tff(c_32, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.61/8.66  tff(c_443, plain, (![B_101, A_100]: (k2_xboole_0(B_101, A_100)=k2_xboole_0(A_100, B_101))), inference(superposition, [status(thm), theory('equality')], [c_437, c_32])).
% 15.61/8.66  tff(c_28, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.61/8.66  tff(c_752, plain, (![A_117, C_118, B_119]: (r1_tarski(A_117, C_118) | ~r1_tarski(B_119, C_118) | ~r1_tarski(A_117, B_119))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.61/8.66  tff(c_906, plain, (![A_131, A_132, B_133]: (r1_tarski(A_131, k2_xboole_0(A_132, B_133)) | ~r1_tarski(A_131, A_132))), inference(resolution, [status(thm)], [c_28, c_752])).
% 15.61/8.66  tff(c_920, plain, (![A_131, A_100, B_101]: (r1_tarski(A_131, k2_xboole_0(A_100, B_101)) | ~r1_tarski(A_131, B_101))), inference(superposition, [status(thm), theory('equality')], [c_443, c_906])).
% 15.61/8.66  tff(c_971, plain, (![A_137, B_138, C_139]: (r1_tarski(k4_xboole_0(A_137, B_138), C_139) | ~r1_tarski(A_137, k2_xboole_0(B_138, C_139)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 15.61/8.66  tff(c_8434, plain, (![A_329, B_330, C_331]: (r1_tarski(k3_xboole_0(A_329, B_330), C_331) | ~r1_tarski(A_329, k2_xboole_0(k4_xboole_0(A_329, B_330), C_331)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_971])).
% 15.61/8.66  tff(c_8656, plain, (![A_332, B_333, B_334]: (r1_tarski(k3_xboole_0(A_332, B_333), B_334) | ~r1_tarski(A_332, B_334))), inference(resolution, [status(thm)], [c_920, c_8434])).
% 15.61/8.66  tff(c_8713, plain, (![B_334]: (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), B_334) | ~r1_tarski('#skF_3', B_334))), inference(superposition, [status(thm), theory('equality')], [c_4429, c_8656])).
% 15.61/8.66  tff(c_48, plain, (![A_47, B_48]: (m1_subset_1(A_47, k1_zfmisc_1(B_48)) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.61/8.66  tff(c_3730, plain, (![A_230, B_231, C_232]: (k4_subset_1(A_230, B_231, C_232)=k2_xboole_0(B_231, C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(A_230)) | ~m1_subset_1(B_231, k1_zfmisc_1(A_230)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.61/8.66  tff(c_20049, plain, (![B_460, B_461, A_462]: (k4_subset_1(B_460, B_461, A_462)=k2_xboole_0(B_461, A_462) | ~m1_subset_1(B_461, k1_zfmisc_1(B_460)) | ~r1_tarski(A_462, B_460))), inference(resolution, [status(thm)], [c_48, c_3730])).
% 15.61/8.66  tff(c_20421, plain, (![A_467]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_467)=k2_xboole_0('#skF_3', A_467) | ~r1_tarski(A_467, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_64, c_20049])).
% 15.61/8.66  tff(c_20445, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_8713, c_20421])).
% 15.61/8.66  tff(c_20584, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_171, c_6725, c_4527, c_20445])).
% 15.61/8.66  tff(c_20586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4022, c_20584])).
% 15.61/8.66  tff(c_20587, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_70])).
% 15.61/8.66  tff(c_20944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_20587])).
% 15.61/8.66  tff(c_20945, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_76])).
% 15.61/8.66  tff(c_21039, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20945, c_70])).
% 15.61/8.66  tff(c_23169, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23096, c_21039])).
% 15.61/8.66  tff(c_63502, plain, (k3_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25846, c_23169])).
% 15.61/8.66  tff(c_23421, plain, (![A_625, B_626]: (k2_pre_topc(A_625, B_626)=B_626 | ~v4_pre_topc(B_626, A_625) | ~m1_subset_1(B_626, k1_zfmisc_1(u1_struct_0(A_625))) | ~l1_pre_topc(A_625))), inference(cnfTransformation, [status(thm)], [f_111])).
% 15.61/8.66  tff(c_23432, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_23421])).
% 15.61/8.66  tff(c_23437, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_20945, c_23432])).
% 15.61/8.66  tff(c_25558, plain, (![A_666, B_667]: (k4_subset_1(u1_struct_0(A_666), B_667, k2_tops_1(A_666, B_667))=k2_pre_topc(A_666, B_667) | ~m1_subset_1(B_667, k1_zfmisc_1(u1_struct_0(A_666))) | ~l1_pre_topc(A_666))), inference(cnfTransformation, [status(thm)], [f_139])).
% 15.61/8.66  tff(c_25568, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_25558])).
% 15.61/8.66  tff(c_25574, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_23437, c_25568])).
% 15.61/8.66  tff(c_54, plain, (![A_52, B_53]: (m1_subset_1(k2_tops_1(A_52, B_53), k1_zfmisc_1(u1_struct_0(A_52))) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_117])).
% 15.61/8.66  tff(c_24640, plain, (![A_651, B_652, C_653]: (k4_subset_1(A_651, B_652, C_653)=k2_xboole_0(B_652, C_653) | ~m1_subset_1(C_653, k1_zfmisc_1(A_651)) | ~m1_subset_1(B_652, k1_zfmisc_1(A_651)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.61/8.66  tff(c_59816, plain, (![A_1035, B_1036, B_1037]: (k4_subset_1(u1_struct_0(A_1035), B_1036, k2_tops_1(A_1035, B_1037))=k2_xboole_0(B_1036, k2_tops_1(A_1035, B_1037)) | ~m1_subset_1(B_1036, k1_zfmisc_1(u1_struct_0(A_1035))) | ~m1_subset_1(B_1037, k1_zfmisc_1(u1_struct_0(A_1035))) | ~l1_pre_topc(A_1035))), inference(resolution, [status(thm)], [c_54, c_24640])).
% 15.61/8.66  tff(c_59832, plain, (![B_1037]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_1037))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_1037)) | ~m1_subset_1(B_1037, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_59816])).
% 15.61/8.66  tff(c_64759, plain, (![B_1075]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_1075))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_1075)) | ~m1_subset_1(B_1075, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_59832])).
% 15.61/8.66  tff(c_64782, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_64759])).
% 15.61/8.66  tff(c_64791, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25574, c_64782])).
% 15.61/8.66  tff(c_20, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.61/8.66  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.61/8.66  tff(c_21403, plain, (![A_517, B_518]: (k4_xboole_0(A_517, k4_xboole_0(A_517, B_518))=k3_xboole_0(A_517, B_518))), inference(cnfTransformation, [status(thm)], [f_62])).
% 15.61/8.66  tff(c_21435, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_21403])).
% 15.61/8.66  tff(c_21455, plain, (![A_520]: (k4_xboole_0(A_520, A_520)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_21435])).
% 15.61/8.66  tff(c_21460, plain, (![A_520]: (k4_xboole_0(A_520, k1_xboole_0)=k3_xboole_0(A_520, A_520))), inference(superposition, [status(thm), theory('equality')], [c_21455, c_26])).
% 15.61/8.66  tff(c_21484, plain, (![A_520]: (k3_xboole_0(A_520, A_520)=A_520)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_21460])).
% 15.61/8.66  tff(c_21003, plain, (![A_492, B_493]: (k3_tarski(k2_tarski(A_492, B_493))=k2_xboole_0(A_492, B_493))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.61/8.66  tff(c_21267, plain, (![A_512, B_513]: (k3_tarski(k2_tarski(A_512, B_513))=k2_xboole_0(B_513, A_512))), inference(superposition, [status(thm), theory('equality')], [c_30, c_21003])).
% 15.61/8.66  tff(c_21290, plain, (![B_514, A_515]: (k2_xboole_0(B_514, A_515)=k2_xboole_0(A_515, B_514))), inference(superposition, [status(thm), theory('equality')], [c_21267, c_32])).
% 15.61/8.66  tff(c_21316, plain, (![B_514, A_515]: (r1_tarski(B_514, k2_xboole_0(A_515, B_514)))), inference(superposition, [status(thm), theory('equality')], [c_21290, c_28])).
% 15.61/8.66  tff(c_99, plain, (![A_73, B_74]: (k2_xboole_0(A_73, k3_xboole_0(A_73, B_74))=A_73)), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.61/8.66  tff(c_111, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(superposition, [status(thm), theory('equality')], [c_14, c_99])).
% 15.61/8.66  tff(c_22907, plain, (![A_607, B_608, C_609]: (r1_tarski(k4_xboole_0(A_607, B_608), C_609) | ~r1_tarski(A_607, k2_xboole_0(B_608, C_609)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 15.61/8.66  tff(c_21155, plain, (![A_503, B_504]: (k5_xboole_0(A_503, k3_xboole_0(A_503, B_504))=k4_xboole_0(A_503, B_504))), inference(cnfTransformation, [status(thm)], [f_34])).
% 15.61/8.66  tff(c_21173, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k4_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_21155])).
% 15.61/8.66  tff(c_21176, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_21173])).
% 15.61/8.66  tff(c_21018, plain, (![A_494, B_495]: (k1_setfam_1(k2_tarski(A_494, B_495))=k3_xboole_0(A_494, B_495))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.61/8.66  tff(c_21040, plain, (![A_498, B_499]: (k1_setfam_1(k2_tarski(A_498, B_499))=k3_xboole_0(B_499, A_498))), inference(superposition, [status(thm), theory('equality')], [c_30, c_21018])).
% 15.61/8.66  tff(c_44, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.61/8.66  tff(c_21063, plain, (![B_500, A_501]: (k3_xboole_0(B_500, A_501)=k3_xboole_0(A_501, B_500))), inference(superposition, [status(thm), theory('equality')], [c_21040, c_44])).
% 15.61/8.66  tff(c_21085, plain, (![A_501]: (k3_xboole_0(k1_xboole_0, A_501)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_21063, c_14])).
% 15.61/8.66  tff(c_21164, plain, (![A_501]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_501))), inference(superposition, [status(thm), theory('equality')], [c_21085, c_21155])).
% 15.61/8.66  tff(c_21228, plain, (![A_508]: (k4_xboole_0(k1_xboole_0, A_508)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_21176, c_21164])).
% 15.61/8.66  tff(c_18, plain, (![A_16, B_17]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k4_xboole_0(B_17, A_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.61/8.66  tff(c_21233, plain, (![A_508]: (k1_xboole_0=A_508 | ~r1_tarski(A_508, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_21228, c_18])).
% 15.61/8.66  tff(c_22925, plain, (![A_607, B_608]: (k4_xboole_0(A_607, B_608)=k1_xboole_0 | ~r1_tarski(A_607, k2_xboole_0(B_608, k1_xboole_0)))), inference(resolution, [status(thm)], [c_22907, c_21233])).
% 15.61/8.66  tff(c_23181, plain, (![A_623, B_624]: (k4_xboole_0(A_623, B_624)=k1_xboole_0 | ~r1_tarski(A_623, B_624))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_22925])).
% 15.61/8.66  tff(c_23745, plain, (![B_633, A_634]: (k4_xboole_0(B_633, k2_xboole_0(A_634, B_633))=k1_xboole_0)), inference(resolution, [status(thm)], [c_21316, c_23181])).
% 15.61/8.66  tff(c_23792, plain, (![B_633, A_634]: (k3_xboole_0(B_633, k2_xboole_0(A_634, B_633))=k4_xboole_0(B_633, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_23745, c_26])).
% 15.61/8.66  tff(c_23847, plain, (![B_633, A_634]: (k3_xboole_0(B_633, k2_xboole_0(A_634, B_633))=B_633)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_23792])).
% 15.61/8.66  tff(c_21046, plain, (![B_499, A_498]: (k3_xboole_0(B_499, A_498)=k3_xboole_0(A_498, B_499))), inference(superposition, [status(thm), theory('equality')], [c_21040, c_44])).
% 15.61/8.66  tff(c_94, plain, (![A_70, B_71]: (r1_tarski(k4_xboole_0(A_70, B_71), A_70))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.61/8.66  tff(c_97, plain, (![A_18]: (r1_tarski(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_94])).
% 15.61/8.66  tff(c_21441, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_21435])).
% 15.61/8.66  tff(c_22781, plain, (![A_602, B_603]: (k4_xboole_0(A_602, B_603)=k3_subset_1(A_602, B_603) | ~m1_subset_1(B_603, k1_zfmisc_1(A_602)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.61/8.66  tff(c_26697, plain, (![B_698, A_699]: (k4_xboole_0(B_698, A_699)=k3_subset_1(B_698, A_699) | ~r1_tarski(A_699, B_698))), inference(resolution, [status(thm)], [c_48, c_22781])).
% 15.61/8.66  tff(c_26847, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_subset_1(A_18, A_18))), inference(resolution, [status(thm)], [c_97, c_26697])).
% 15.61/8.66  tff(c_26911, plain, (![A_700]: (k3_subset_1(A_700, A_700)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_21441, c_26847])).
% 15.61/8.66  tff(c_22542, plain, (![A_588, B_589]: (k3_subset_1(A_588, k3_subset_1(A_588, B_589))=B_589 | ~m1_subset_1(B_589, k1_zfmisc_1(A_588)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.61/8.66  tff(c_22550, plain, (![B_48, A_47]: (k3_subset_1(B_48, k3_subset_1(B_48, A_47))=A_47 | ~r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_48, c_22542])).
% 15.61/8.66  tff(c_26916, plain, (![A_700]: (k3_subset_1(A_700, k1_xboole_0)=A_700 | ~r1_tarski(A_700, A_700))), inference(superposition, [status(thm), theory('equality')], [c_26911, c_22550])).
% 15.61/8.66  tff(c_26924, plain, (![A_700]: (k3_subset_1(A_700, k1_xboole_0)=A_700)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_26916])).
% 15.61/8.66  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.61/8.66  tff(c_21595, plain, (![A_529, B_530]: (r1_tarski(k3_xboole_0(A_529, B_530), A_529))), inference(superposition, [status(thm), theory('equality')], [c_21403, c_16])).
% 15.61/8.66  tff(c_21608, plain, (![B_499, A_498]: (r1_tarski(k3_xboole_0(B_499, A_498), A_498))), inference(superposition, [status(thm), theory('equality')], [c_21046, c_21595])).
% 15.61/8.66  tff(c_23302, plain, (![B_499, A_498]: (k4_xboole_0(k3_xboole_0(B_499, A_498), A_498)=k1_xboole_0)), inference(resolution, [status(thm)], [c_21608, c_23181])).
% 15.61/8.66  tff(c_26850, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_subset_1(A_14, k4_xboole_0(A_14, B_15)))), inference(resolution, [status(thm)], [c_16, c_26697])).
% 15.61/8.66  tff(c_27003, plain, (![A_703, B_704]: (k3_subset_1(A_703, k4_xboole_0(A_703, B_704))=k3_xboole_0(A_703, B_704))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26850])).
% 15.61/8.66  tff(c_27057, plain, (![B_499, A_498]: (k3_xboole_0(k3_xboole_0(B_499, A_498), A_498)=k3_subset_1(k3_xboole_0(B_499, A_498), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_23302, c_27003])).
% 15.61/8.66  tff(c_38473, plain, (![B_845, A_846]: (k3_xboole_0(k3_xboole_0(B_845, A_846), A_846)=k3_xboole_0(B_845, A_846))), inference(demodulation, [status(thm), theory('equality')], [c_26924, c_27057])).
% 15.61/8.66  tff(c_46634, plain, (![A_922, B_923]: (k3_xboole_0(k3_xboole_0(A_922, B_923), A_922)=k3_xboole_0(B_923, A_922))), inference(superposition, [status(thm), theory('equality')], [c_21046, c_38473])).
% 15.61/8.66  tff(c_46925, plain, (![A_634, B_633]: (k3_xboole_0(k2_xboole_0(A_634, B_633), B_633)=k3_xboole_0(B_633, B_633))), inference(superposition, [status(thm), theory('equality')], [c_23847, c_46634])).
% 15.61/8.66  tff(c_47022, plain, (![A_634, B_633]: (k3_xboole_0(k2_xboole_0(A_634, B_633), B_633)=B_633)), inference(demodulation, [status(thm), theory('equality')], [c_21484, c_46925])).
% 15.61/8.66  tff(c_64844, plain, (k3_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_64791, c_47022])).
% 15.61/8.66  tff(c_64968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63502, c_64844])).
% 15.61/8.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.61/8.66  
% 15.61/8.66  Inference rules
% 15.61/8.66  ----------------------
% 15.61/8.66  #Ref     : 0
% 15.61/8.66  #Sup     : 15827
% 15.61/8.66  #Fact    : 0
% 15.61/8.66  #Define  : 0
% 15.61/8.66  #Split   : 11
% 15.61/8.66  #Chain   : 0
% 15.61/8.66  #Close   : 0
% 15.61/8.66  
% 15.61/8.66  Ordering : KBO
% 15.61/8.66  
% 15.61/8.66  Simplification rules
% 15.61/8.66  ----------------------
% 15.61/8.66  #Subsume      : 1049
% 15.61/8.66  #Demod        : 14484
% 15.61/8.66  #Tautology    : 10736
% 15.61/8.66  #SimpNegUnit  : 9
% 15.61/8.66  #BackRed      : 3
% 15.61/8.66  
% 15.61/8.66  #Partial instantiations: 0
% 15.61/8.66  #Strategies tried      : 1
% 15.61/8.66  
% 15.61/8.66  Timing (in seconds)
% 15.61/8.66  ----------------------
% 15.61/8.67  Preprocessing        : 0.36
% 15.61/8.67  Parsing              : 0.19
% 15.61/8.67  CNF conversion       : 0.02
% 15.61/8.67  Main loop            : 7.46
% 15.61/8.67  Inferencing          : 1.24
% 15.61/8.67  Reduction            : 4.25
% 15.61/8.67  Demodulation         : 3.71
% 15.61/8.67  BG Simplification    : 0.12
% 15.61/8.67  Subsumption          : 1.50
% 15.61/8.67  Abstraction          : 0.20
% 15.61/8.67  MUC search           : 0.00
% 15.61/8.67  Cooper               : 0.00
% 15.61/8.67  Total                : 7.87
% 15.61/8.67  Index Insertion      : 0.00
% 15.61/8.67  Index Deletion       : 0.00
% 15.61/8.67  Index Matching       : 0.00
% 15.61/8.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
