%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1260+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:39 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 325 expanded)
%              Number of leaves         :   35 ( 125 expanded)
%              Depth                    :   10
%              Number of atoms          :  179 ( 706 expanded)
%              Number of equality atoms :   64 ( 193 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k6_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_56,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_36,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(c_40,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_74,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_163,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,B_72) = k3_subset_1(A_71,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_179,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_163])).

tff(c_16,plain,(
    ! [A_17,B_18] : k6_subset_1(A_17,B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_5,B_6] : m1_subset_1(k6_subset_1(A_5,B_6),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_47,plain,(
    ! [A_5,B_6] : m1_subset_1(k4_xboole_0(A_5,B_6),k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6])).

tff(c_187,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_47])).

tff(c_28,plain,(
    ! [C_43,A_31,D_45,B_39] :
      ( v3_pre_topc(C_43,A_31)
      | k1_tops_1(A_31,C_43) != C_43
      | ~ m1_subset_1(D_45,k1_zfmisc_1(u1_struct_0(B_39)))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(B_39)
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1043,plain,(
    ! [D_120,B_121] :
      ( ~ m1_subset_1(D_120,k1_zfmisc_1(u1_struct_0(B_121)))
      | ~ l1_pre_topc(B_121) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_1052,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_187,c_1043])).

tff(c_1071,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1052])).

tff(c_1288,plain,(
    ! [C_129,A_130] :
      ( v3_pre_topc(C_129,A_130)
      | k1_tops_1(A_130,C_129) != C_129
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1313,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != '#skF_3'
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_1288])).

tff(c_1328,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1313])).

tff(c_1329,plain,(
    k1_tops_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1328])).

tff(c_191,plain,(
    ! [A_73,B_74,C_75] :
      ( k7_subset_1(A_73,B_74,C_75) = k4_xboole_0(B_74,C_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_203,plain,(
    ! [C_75] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_75) = k4_xboole_0('#skF_3',C_75) ),
    inference(resolution,[status(thm)],[c_34,c_191])).

tff(c_683,plain,(
    ! [A_108,B_109] :
      ( k7_subset_1(u1_struct_0(A_108),B_109,k2_tops_1(A_108,B_109)) = k1_tops_1(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_701,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_683])).

tff(c_716,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_203,c_701])).

tff(c_569,plain,(
    ! [A_99,B_100] :
      ( m1_subset_1(k2_pre_topc(A_99,B_100),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    ! [A_19,B_20,C_21] :
      ( k7_subset_1(A_19,B_20,C_21) = k4_xboole_0(B_20,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2975,plain,(
    ! [A_178,B_179,C_180] :
      ( k7_subset_1(u1_struct_0(A_178),k2_pre_topc(A_178,B_179),C_180) = k4_xboole_0(k2_pre_topc(A_178,B_179),C_180)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_569,c_18])).

tff(c_2993,plain,(
    ! [C_180] :
      ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_180) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_180)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_2975])).

tff(c_3009,plain,(
    ! [C_181] : k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_181) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2993])).

tff(c_14,plain,(
    ! [A_14,B_16] :
      ( k7_subset_1(u1_struct_0(A_14),k2_pre_topc(A_14,B_16),k1_tops_1(A_14,B_16)) = k2_tops_1(A_14,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3024,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3009,c_14])).

tff(c_3050,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_3024])).

tff(c_367,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(B_88,k2_pre_topc(A_89,B_88))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_380,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_367])).

tff(c_392,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_380])).

tff(c_46,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_124,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_46])).

tff(c_3027,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3009,c_124])).

tff(c_24,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_177,plain,(
    ! [B_27,A_26] :
      ( k4_xboole_0(B_27,A_26) = k3_subset_1(B_27,A_26)
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_24,c_163])).

tff(c_397,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_392,c_177])).

tff(c_3056,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3027,c_397])).

tff(c_104,plain,(
    ! [A_67,B_68] :
      ( k3_subset_1(A_67,k3_subset_1(A_67,B_68)) = B_68
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_114,plain,(
    ! [B_27,A_26] :
      ( k3_subset_1(B_27,k3_subset_1(B_27,A_26)) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_24,c_104])).

tff(c_3112,plain,
    ( k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3056,c_114])).

tff(c_3116,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_3112])).

tff(c_271,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k3_subset_1(A_80,k4_xboole_0(A_80,B_81)) ),
    inference(resolution,[status(thm)],[c_47,c_163])).

tff(c_283,plain,(
    ! [A_80,B_81] : m1_subset_1(k3_subset_1(A_80,k4_xboole_0(A_80,B_81)),k1_zfmisc_1(A_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_47])).

tff(c_178,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) ),
    inference(resolution,[status(thm)],[c_47,c_163])).

tff(c_645,plain,(
    ! [A_103,B_104,C_105] : k7_subset_1(A_103,k4_xboole_0(A_103,B_104),C_105) = k4_xboole_0(k4_xboole_0(A_103,B_104),C_105) ),
    inference(resolution,[status(thm)],[c_47,c_191])).

tff(c_660,plain,(
    ! [A_5,B_6,C_105] : k7_subset_1(A_5,k3_subset_1(A_5,k4_xboole_0(A_5,B_6)),C_105) = k4_xboole_0(k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)),C_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_645])).

tff(c_671,plain,(
    ! [A_5,B_6,C_105] : k7_subset_1(A_5,k3_subset_1(A_5,k4_xboole_0(A_5,B_6)),C_105) = k4_xboole_0(k3_subset_1(A_5,k4_xboole_0(A_5,B_6)),C_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_660])).

tff(c_81,plain,(
    ! [A_62,B_63,C_64] :
      ( k9_subset_1(A_62,B_63,B_63) = B_63
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_5,B_63] : k9_subset_1(A_5,B_63,B_63) = B_63 ),
    inference(resolution,[status(thm)],[c_47,c_81])).

tff(c_878,plain,(
    ! [A_110,B_111,C_112] :
      ( k9_subset_1(A_110,B_111,k3_subset_1(A_110,C_112)) = k7_subset_1(A_110,B_111,C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(A_110))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2230,plain,(
    ! [A_163,B_164,B_165] :
      ( k9_subset_1(A_163,B_164,k3_subset_1(A_163,k4_xboole_0(A_163,B_165))) = k7_subset_1(A_163,B_164,k4_xboole_0(A_163,B_165))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(A_163)) ) ),
    inference(resolution,[status(thm)],[c_47,c_878])).

tff(c_2294,plain,(
    ! [A_5,B_165] :
      ( k7_subset_1(A_5,k3_subset_1(A_5,k4_xboole_0(A_5,B_165)),k4_xboole_0(A_5,B_165)) = k3_subset_1(A_5,k4_xboole_0(A_5,B_165))
      | ~ m1_subset_1(k3_subset_1(A_5,k4_xboole_0(A_5,B_165)),k1_zfmisc_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2230])).

tff(c_4050,plain,(
    ! [A_194,B_195] : k4_xboole_0(k3_subset_1(A_194,k4_xboole_0(A_194,B_195)),k4_xboole_0(A_194,B_195)) = k3_subset_1(A_194,k4_xboole_0(A_194,B_195)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_671,c_2294])).

tff(c_4125,plain,(
    k4_xboole_0(k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')),k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3'))) = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3050,c_4050])).

tff(c_4255,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_3050,c_3116,c_3050,c_3116,c_4125])).

tff(c_4257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1329,c_4255])).

tff(c_4258,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_4259,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_4344,plain,(
    ! [A_208,B_209] :
      ( k4_xboole_0(A_208,B_209) = k3_subset_1(A_208,B_209)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(A_208)) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_4360,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_4344])).

tff(c_4368,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4360,c_47])).

tff(c_30,plain,(
    ! [B_39,D_45,C_43,A_31] :
      ( k1_tops_1(B_39,D_45) = D_45
      | ~ v3_pre_topc(D_45,B_39)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(u1_struct_0(B_39)))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(B_39)
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5637,plain,(
    ! [C_270,A_271] :
      ( ~ m1_subset_1(C_270,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271) ) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_5649,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4368,c_5637])).

tff(c_5669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_5649])).

tff(c_5671,plain,(
    ! [B_272,D_273] :
      ( k1_tops_1(B_272,D_273) = D_273
      | ~ v3_pre_topc(D_273,B_272)
      | ~ m1_subset_1(D_273,k1_zfmisc_1(u1_struct_0(B_272)))
      | ~ l1_pre_topc(B_272) ) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_5696,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_5671])).

tff(c_5711,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4259,c_5696])).

tff(c_5725,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5711,c_14])).

tff(c_5729,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_5725])).

tff(c_5731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4258,c_5729])).

%------------------------------------------------------------------------------
