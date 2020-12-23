%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:09 EST 2020

% Result     : Theorem 16.10s
% Output     : CNFRefutation 16.23s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 628 expanded)
%              Number of leaves         :   41 ( 227 expanded)
%              Depth                    :   11
%              Number of atoms          :  203 (1415 expanded)
%              Number of equality atoms :   59 ( 359 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_46,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_50,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_134,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_386,plain,(
    ! [B_94,A_95] :
      ( r1_tarski(B_94,k2_pre_topc(A_95,B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_394,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_386])).

tff(c_402,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_394])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_489,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1(k2_pre_topc(A_103,B_104),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] :
      ( k7_subset_1(A_18,B_19,C_20) = k4_xboole_0(B_19,C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4773,plain,(
    ! [A_257,B_258,C_259] :
      ( k7_subset_1(u1_struct_0(A_257),k2_pre_topc(A_257,B_258),C_259) = k4_xboole_0(k2_pre_topc(A_257,B_258),C_259)
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ l1_pre_topc(A_257) ) ),
    inference(resolution,[status(thm)],[c_489,c_22])).

tff(c_4788,plain,(
    ! [C_259] :
      ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_259) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_259)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_4773])).

tff(c_4803,plain,(
    ! [C_260] : k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_260) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_260) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4788])).

tff(c_56,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_80,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_4817,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4803,c_80])).

tff(c_216,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = k3_subset_1(A_81,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_231,plain,(
    ! [B_28,A_27] :
      ( k4_xboole_0(B_28,A_27) = k3_subset_1(B_28,A_27)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_30,c_216])).

tff(c_409,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_402,c_231])).

tff(c_4842,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4817,c_409])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k3_subset_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4945,plain,
    ( m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_14])).

tff(c_5698,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4945])).

tff(c_5701,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_5698])).

tff(c_5705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_5701])).

tff(c_5707,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4945])).

tff(c_143,plain,(
    ! [A_75,B_76] :
      ( k3_subset_1(A_75,k3_subset_1(A_75,B_76)) = B_76
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_154,plain,(
    ! [B_28,A_27] :
      ( k3_subset_1(B_28,k3_subset_1(B_28,A_27)) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_30,c_143])).

tff(c_4939,plain,
    ( k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_154])).

tff(c_4969,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_4939])).

tff(c_291,plain,(
    ! [A_86,B_87,C_88] :
      ( k7_subset_1(A_86,B_87,C_88) = k4_xboole_0(B_87,C_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_303,plain,(
    ! [C_88] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_88) = k4_xboole_0('#skF_3',C_88) ),
    inference(resolution,[status(thm)],[c_44,c_291])).

tff(c_822,plain,(
    ! [A_127,B_128] :
      ( k7_subset_1(u1_struct_0(A_127),B_128,k2_tops_1(A_127,B_128)) = k1_tops_1(A_127,B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_832,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_822])).

tff(c_841,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_303,c_832])).

tff(c_439,plain,(
    ! [B_97,A_98,C_99] :
      ( k7_subset_1(B_97,A_98,C_99) = k4_xboole_0(A_98,C_99)
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(resolution,[status(thm)],[c_30,c_291])).

tff(c_462,plain,(
    ! [C_99] : k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3',C_99) = k4_xboole_0('#skF_3',C_99) ),
    inference(resolution,[status(thm)],[c_402,c_439])).

tff(c_933,plain,(
    ! [A_129,B_130,C_131] :
      ( k9_subset_1(A_129,B_130,k3_subset_1(A_129,C_131)) = k7_subset_1(A_129,B_130,C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(A_129))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5302,plain,(
    ! [A_263,B_264,B_265] :
      ( k9_subset_1(A_263,B_264,k3_subset_1(A_263,k3_subset_1(A_263,B_265))) = k7_subset_1(A_263,B_264,k3_subset_1(A_263,B_265))
      | ~ m1_subset_1(B_264,k1_zfmisc_1(A_263))
      | ~ m1_subset_1(B_265,k1_zfmisc_1(A_263)) ) ),
    inference(resolution,[status(thm)],[c_14,c_933])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1('#skF_1'(A_11),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_113,plain,(
    ! [A_65,B_66,C_67] :
      ( k9_subset_1(A_65,B_66,B_66) = B_66
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_122,plain,(
    ! [A_65,B_66] : k9_subset_1(A_65,B_66,B_66) = B_66 ),
    inference(resolution,[status(thm)],[c_16,c_113])).

tff(c_32433,plain,(
    ! [A_579,B_580] :
      ( k7_subset_1(A_579,k3_subset_1(A_579,k3_subset_1(A_579,B_580)),k3_subset_1(A_579,B_580)) = k3_subset_1(A_579,k3_subset_1(A_579,B_580))
      | ~ m1_subset_1(k3_subset_1(A_579,k3_subset_1(A_579,B_580)),k1_zfmisc_1(A_579))
      | ~ m1_subset_1(B_580,k1_zfmisc_1(A_579)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5302,c_122])).

tff(c_32475,plain,
    ( k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3')),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3')) = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3'))
    | ~ m1_subset_1(k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')),k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_32433])).

tff(c_32538,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5707,c_5707,c_4969,c_841,c_462,c_4969,c_4842,c_4842,c_4969,c_4842,c_32475])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ r1_tarski(B_63,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(A_5,B_6)) ) ),
    inference(resolution,[status(thm)],[c_10,c_96])).

tff(c_859,plain,
    ( k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_107])).

tff(c_867,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_859])).

tff(c_904,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_867])).

tff(c_32577,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32538,c_904])).

tff(c_32600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32577])).

tff(c_32601,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_867])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_719,plain,(
    ! [A_115,B_116] :
      ( v3_pre_topc(k1_tops_1(A_115,B_116),A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_729,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_719])).

tff(c_738,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_729])).

tff(c_32607,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32601,c_738])).

tff(c_32612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_32607])).

tff(c_32613,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_32685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32613,c_80])).

tff(c_32686,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_32742,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32686,c_50])).

tff(c_32897,plain,(
    ! [A_620,B_621,C_622] :
      ( k7_subset_1(A_620,B_621,C_622) = k4_xboole_0(B_621,C_622)
      | ~ m1_subset_1(B_621,k1_zfmisc_1(A_620)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32909,plain,(
    ! [C_622] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_622) = k4_xboole_0('#skF_3',C_622) ),
    inference(resolution,[status(thm)],[c_44,c_32897])).

tff(c_33428,plain,(
    ! [A_661,B_662] :
      ( k7_subset_1(u1_struct_0(A_661),B_662,k2_tops_1(A_661,B_662)) = k1_tops_1(A_661,B_662)
      | ~ m1_subset_1(B_662,k1_zfmisc_1(u1_struct_0(A_661)))
      | ~ l1_pre_topc(A_661) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_33438,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_33428])).

tff(c_33447,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_32909,c_33438])).

tff(c_32703,plain,(
    ! [B_597,A_598] :
      ( B_597 = A_598
      | ~ r1_tarski(B_597,A_598)
      | ~ r1_tarski(A_598,B_597) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32714,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(A_5,B_6)) ) ),
    inference(resolution,[status(thm)],[c_10,c_32703])).

tff(c_33465,plain,
    ( k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33447,c_32714])).

tff(c_33473,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33447,c_33465])).

tff(c_33510,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_33473])).

tff(c_33821,plain,(
    ! [B_680,A_681,C_682] :
      ( r1_tarski(B_680,k1_tops_1(A_681,C_682))
      | ~ r1_tarski(B_680,C_682)
      | ~ v3_pre_topc(B_680,A_681)
      | ~ m1_subset_1(C_682,k1_zfmisc_1(u1_struct_0(A_681)))
      | ~ m1_subset_1(B_680,k1_zfmisc_1(u1_struct_0(A_681)))
      | ~ l1_pre_topc(A_681) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_33833,plain,(
    ! [B_680] :
      ( r1_tarski(B_680,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_680,'#skF_3')
      | ~ v3_pre_topc(B_680,'#skF_2')
      | ~ m1_subset_1(B_680,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_33821])).

tff(c_33905,plain,(
    ! [B_687] :
      ( r1_tarski(B_687,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_687,'#skF_3')
      | ~ v3_pre_topc(B_687,'#skF_2')
      | ~ m1_subset_1(B_687,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_33833])).

tff(c_33923,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_33905])).

tff(c_33936,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32686,c_6,c_33923])).

tff(c_33938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33510,c_33936])).

tff(c_33939,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_33473])).

tff(c_34113,plain,(
    ! [A_696,B_697] :
      ( k7_subset_1(u1_struct_0(A_696),k2_pre_topc(A_696,B_697),k1_tops_1(A_696,B_697)) = k2_tops_1(A_696,B_697)
      | ~ m1_subset_1(B_697,k1_zfmisc_1(u1_struct_0(A_696)))
      | ~ l1_pre_topc(A_696) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34122,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_33939,c_34113])).

tff(c_34126,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34122])).

tff(c_34128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32742,c_34126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:28:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.10/7.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.23/7.55  
% 16.23/7.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.23/7.55  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3
% 16.23/7.55  
% 16.23/7.55  %Foreground sorts:
% 16.23/7.55  
% 16.23/7.55  
% 16.23/7.55  %Background operators:
% 16.23/7.55  
% 16.23/7.55  
% 16.23/7.55  %Foreground operators:
% 16.23/7.55  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 16.23/7.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.23/7.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.23/7.55  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 16.23/7.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 16.23/7.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.23/7.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.23/7.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.23/7.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.23/7.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 16.23/7.55  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 16.23/7.55  tff('#skF_2', type, '#skF_2': $i).
% 16.23/7.55  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 16.23/7.55  tff('#skF_3', type, '#skF_3': $i).
% 16.23/7.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.23/7.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.23/7.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.23/7.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.23/7.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.23/7.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.23/7.55  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 16.23/7.55  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 16.23/7.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.23/7.55  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.23/7.55  
% 16.23/7.57  tff(f_132, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 16.23/7.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.23/7.57  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 16.23/7.57  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 16.23/7.57  tff(f_77, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 16.23/7.57  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 16.23/7.57  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 16.23/7.57  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 16.23/7.57  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 16.23/7.57  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 16.23/7.57  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 16.23/7.57  tff(f_46, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 16.23/7.57  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 16.23/7.57  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 16.23/7.57  tff(f_92, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 16.23/7.57  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 16.23/7.57  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 16.23/7.57  tff(c_50, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 16.23/7.57  tff(c_134, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 16.23/7.57  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.23/7.57  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 16.23/7.57  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 16.23/7.57  tff(c_386, plain, (![B_94, A_95]: (r1_tarski(B_94, k2_pre_topc(A_95, B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.23/7.57  tff(c_394, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_386])).
% 16.23/7.57  tff(c_402, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_394])).
% 16.23/7.57  tff(c_30, plain, (![A_27, B_28]: (m1_subset_1(A_27, k1_zfmisc_1(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.23/7.57  tff(c_489, plain, (![A_103, B_104]: (m1_subset_1(k2_pre_topc(A_103, B_104), k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.23/7.57  tff(c_22, plain, (![A_18, B_19, C_20]: (k7_subset_1(A_18, B_19, C_20)=k4_xboole_0(B_19, C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.23/7.57  tff(c_4773, plain, (![A_257, B_258, C_259]: (k7_subset_1(u1_struct_0(A_257), k2_pre_topc(A_257, B_258), C_259)=k4_xboole_0(k2_pre_topc(A_257, B_258), C_259) | ~m1_subset_1(B_258, k1_zfmisc_1(u1_struct_0(A_257))) | ~l1_pre_topc(A_257))), inference(resolution, [status(thm)], [c_489, c_22])).
% 16.23/7.57  tff(c_4788, plain, (![C_259]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_259)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_259) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_4773])).
% 16.23/7.57  tff(c_4803, plain, (![C_260]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_260)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_260))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4788])).
% 16.23/7.57  tff(c_56, plain, (v3_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 16.23/7.57  tff(c_80, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 16.23/7.57  tff(c_4817, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4803, c_80])).
% 16.23/7.57  tff(c_216, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=k3_subset_1(A_81, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.23/7.57  tff(c_231, plain, (![B_28, A_27]: (k4_xboole_0(B_28, A_27)=k3_subset_1(B_28, A_27) | ~r1_tarski(A_27, B_28))), inference(resolution, [status(thm)], [c_30, c_216])).
% 16.23/7.57  tff(c_409, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_402, c_231])).
% 16.23/7.57  tff(c_4842, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4817, c_409])).
% 16.23/7.57  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(k3_subset_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.23/7.57  tff(c_4945, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4842, c_14])).
% 16.23/7.57  tff(c_5698, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_4945])).
% 16.23/7.57  tff(c_5701, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_5698])).
% 16.23/7.57  tff(c_5705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_402, c_5701])).
% 16.23/7.57  tff(c_5707, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_4945])).
% 16.23/7.57  tff(c_143, plain, (![A_75, B_76]: (k3_subset_1(A_75, k3_subset_1(A_75, B_76))=B_76 | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.23/7.57  tff(c_154, plain, (![B_28, A_27]: (k3_subset_1(B_28, k3_subset_1(B_28, A_27))=A_27 | ~r1_tarski(A_27, B_28))), inference(resolution, [status(thm)], [c_30, c_143])).
% 16.23/7.57  tff(c_4939, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4842, c_154])).
% 16.23/7.57  tff(c_4969, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_402, c_4939])).
% 16.23/7.57  tff(c_291, plain, (![A_86, B_87, C_88]: (k7_subset_1(A_86, B_87, C_88)=k4_xboole_0(B_87, C_88) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.23/7.57  tff(c_303, plain, (![C_88]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_88)=k4_xboole_0('#skF_3', C_88))), inference(resolution, [status(thm)], [c_44, c_291])).
% 16.23/7.57  tff(c_822, plain, (![A_127, B_128]: (k7_subset_1(u1_struct_0(A_127), B_128, k2_tops_1(A_127, B_128))=k1_tops_1(A_127, B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_120])).
% 16.23/7.57  tff(c_832, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_822])).
% 16.23/7.57  tff(c_841, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_303, c_832])).
% 16.23/7.57  tff(c_439, plain, (![B_97, A_98, C_99]: (k7_subset_1(B_97, A_98, C_99)=k4_xboole_0(A_98, C_99) | ~r1_tarski(A_98, B_97))), inference(resolution, [status(thm)], [c_30, c_291])).
% 16.23/7.57  tff(c_462, plain, (![C_99]: (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3', C_99)=k4_xboole_0('#skF_3', C_99))), inference(resolution, [status(thm)], [c_402, c_439])).
% 16.23/7.57  tff(c_933, plain, (![A_129, B_130, C_131]: (k9_subset_1(A_129, B_130, k3_subset_1(A_129, C_131))=k7_subset_1(A_129, B_130, C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(A_129)) | ~m1_subset_1(B_130, k1_zfmisc_1(A_129)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.23/7.57  tff(c_5302, plain, (![A_263, B_264, B_265]: (k9_subset_1(A_263, B_264, k3_subset_1(A_263, k3_subset_1(A_263, B_265)))=k7_subset_1(A_263, B_264, k3_subset_1(A_263, B_265)) | ~m1_subset_1(B_264, k1_zfmisc_1(A_263)) | ~m1_subset_1(B_265, k1_zfmisc_1(A_263)))), inference(resolution, [status(thm)], [c_14, c_933])).
% 16.23/7.57  tff(c_16, plain, (![A_11]: (m1_subset_1('#skF_1'(A_11), A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.23/7.57  tff(c_113, plain, (![A_65, B_66, C_67]: (k9_subset_1(A_65, B_66, B_66)=B_66 | ~m1_subset_1(C_67, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.23/7.57  tff(c_122, plain, (![A_65, B_66]: (k9_subset_1(A_65, B_66, B_66)=B_66)), inference(resolution, [status(thm)], [c_16, c_113])).
% 16.23/7.57  tff(c_32433, plain, (![A_579, B_580]: (k7_subset_1(A_579, k3_subset_1(A_579, k3_subset_1(A_579, B_580)), k3_subset_1(A_579, B_580))=k3_subset_1(A_579, k3_subset_1(A_579, B_580)) | ~m1_subset_1(k3_subset_1(A_579, k3_subset_1(A_579, B_580)), k1_zfmisc_1(A_579)) | ~m1_subset_1(B_580, k1_zfmisc_1(A_579)))), inference(superposition, [status(thm), theory('equality')], [c_5302, c_122])).
% 16.23/7.57  tff(c_32475, plain, (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3'))=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')) | ~m1_subset_1(k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3')), k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4842, c_32433])).
% 16.23/7.57  tff(c_32538, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5707, c_5707, c_4969, c_841, c_462, c_4969, c_4842, c_4842, c_4969, c_4842, c_32475])).
% 16.23/7.57  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.23/7.57  tff(c_96, plain, (![B_63, A_64]: (B_63=A_64 | ~r1_tarski(B_63, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.23/7.57  tff(c_107, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_96])).
% 16.23/7.57  tff(c_859, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_841, c_107])).
% 16.23/7.57  tff(c_867, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_841, c_859])).
% 16.23/7.57  tff(c_904, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_867])).
% 16.23/7.57  tff(c_32577, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32538, c_904])).
% 16.23/7.57  tff(c_32600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_32577])).
% 16.23/7.57  tff(c_32601, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_867])).
% 16.23/7.57  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 16.23/7.57  tff(c_719, plain, (![A_115, B_116]: (v3_pre_topc(k1_tops_1(A_115, B_116), A_115) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.23/7.57  tff(c_729, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_719])).
% 16.23/7.57  tff(c_738, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_729])).
% 16.23/7.57  tff(c_32607, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32601, c_738])).
% 16.23/7.57  tff(c_32612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_32607])).
% 16.23/7.57  tff(c_32613, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 16.23/7.57  tff(c_32685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32613, c_80])).
% 16.23/7.57  tff(c_32686, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 16.23/7.57  tff(c_32742, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32686, c_50])).
% 16.23/7.57  tff(c_32897, plain, (![A_620, B_621, C_622]: (k7_subset_1(A_620, B_621, C_622)=k4_xboole_0(B_621, C_622) | ~m1_subset_1(B_621, k1_zfmisc_1(A_620)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.23/7.57  tff(c_32909, plain, (![C_622]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_622)=k4_xboole_0('#skF_3', C_622))), inference(resolution, [status(thm)], [c_44, c_32897])).
% 16.23/7.57  tff(c_33428, plain, (![A_661, B_662]: (k7_subset_1(u1_struct_0(A_661), B_662, k2_tops_1(A_661, B_662))=k1_tops_1(A_661, B_662) | ~m1_subset_1(B_662, k1_zfmisc_1(u1_struct_0(A_661))) | ~l1_pre_topc(A_661))), inference(cnfTransformation, [status(thm)], [f_120])).
% 16.23/7.57  tff(c_33438, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_33428])).
% 16.23/7.57  tff(c_33447, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_32909, c_33438])).
% 16.23/7.57  tff(c_32703, plain, (![B_597, A_598]: (B_597=A_598 | ~r1_tarski(B_597, A_598) | ~r1_tarski(A_598, B_597))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.23/7.57  tff(c_32714, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_32703])).
% 16.23/7.57  tff(c_33465, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_33447, c_32714])).
% 16.23/7.57  tff(c_33473, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_33447, c_33465])).
% 16.23/7.57  tff(c_33510, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_33473])).
% 16.23/7.57  tff(c_33821, plain, (![B_680, A_681, C_682]: (r1_tarski(B_680, k1_tops_1(A_681, C_682)) | ~r1_tarski(B_680, C_682) | ~v3_pre_topc(B_680, A_681) | ~m1_subset_1(C_682, k1_zfmisc_1(u1_struct_0(A_681))) | ~m1_subset_1(B_680, k1_zfmisc_1(u1_struct_0(A_681))) | ~l1_pre_topc(A_681))), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.23/7.57  tff(c_33833, plain, (![B_680]: (r1_tarski(B_680, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_680, '#skF_3') | ~v3_pre_topc(B_680, '#skF_2') | ~m1_subset_1(B_680, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_33821])).
% 16.23/7.57  tff(c_33905, plain, (![B_687]: (r1_tarski(B_687, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_687, '#skF_3') | ~v3_pre_topc(B_687, '#skF_2') | ~m1_subset_1(B_687, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_33833])).
% 16.23/7.57  tff(c_33923, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_33905])).
% 16.23/7.57  tff(c_33936, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32686, c_6, c_33923])).
% 16.23/7.57  tff(c_33938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33510, c_33936])).
% 16.23/7.57  tff(c_33939, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_33473])).
% 16.23/7.57  tff(c_34113, plain, (![A_696, B_697]: (k7_subset_1(u1_struct_0(A_696), k2_pre_topc(A_696, B_697), k1_tops_1(A_696, B_697))=k2_tops_1(A_696, B_697) | ~m1_subset_1(B_697, k1_zfmisc_1(u1_struct_0(A_696))) | ~l1_pre_topc(A_696))), inference(cnfTransformation, [status(thm)], [f_99])).
% 16.23/7.57  tff(c_34122, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_33939, c_34113])).
% 16.23/7.57  tff(c_34126, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34122])).
% 16.23/7.57  tff(c_34128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32742, c_34126])).
% 16.23/7.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.23/7.57  
% 16.23/7.57  Inference rules
% 16.23/7.57  ----------------------
% 16.23/7.57  #Ref     : 0
% 16.23/7.57  #Sup     : 8249
% 16.23/7.57  #Fact    : 0
% 16.23/7.57  #Define  : 0
% 16.23/7.57  #Split   : 29
% 16.23/7.57  #Chain   : 0
% 16.23/7.57  #Close   : 0
% 16.23/7.57  
% 16.23/7.57  Ordering : KBO
% 16.23/7.57  
% 16.23/7.57  Simplification rules
% 16.23/7.57  ----------------------
% 16.23/7.57  #Subsume      : 934
% 16.23/7.57  #Demod        : 8722
% 16.23/7.57  #Tautology    : 2698
% 16.23/7.57  #SimpNegUnit  : 20
% 16.23/7.57  #BackRed      : 71
% 16.23/7.57  
% 16.23/7.57  #Partial instantiations: 0
% 16.23/7.57  #Strategies tried      : 1
% 16.23/7.57  
% 16.23/7.57  Timing (in seconds)
% 16.23/7.57  ----------------------
% 16.23/7.57  Preprocessing        : 0.36
% 16.23/7.57  Parsing              : 0.19
% 16.23/7.57  CNF conversion       : 0.02
% 16.23/7.57  Main loop            : 6.44
% 16.23/7.57  Inferencing          : 1.30
% 16.23/7.57  Reduction            : 3.18
% 16.23/7.57  Demodulation         : 2.69
% 16.23/7.57  BG Simplification    : 0.15
% 16.23/7.57  Subsumption          : 1.46
% 16.23/7.57  Abstraction          : 0.25
% 16.23/7.57  MUC search           : 0.00
% 16.23/7.57  Cooper               : 0.00
% 16.23/7.57  Total                : 6.83
% 16.23/7.57  Index Insertion      : 0.00
% 16.23/7.57  Index Deletion       : 0.00
% 16.23/7.57  Index Matching       : 0.00
% 16.23/7.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
