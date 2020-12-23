%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:31 EST 2020

% Result     : Theorem 10.30s
% Output     : CNFRefutation 10.66s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 216 expanded)
%              Number of leaves         :   40 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  159 ( 378 expanded)
%              Number of equality atoms :   79 ( 144 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_8988,plain,(
    ! [A_292,B_293,C_294] :
      ( k7_subset_1(A_292,B_293,C_294) = k4_xboole_0(B_293,C_294)
      | ~ m1_subset_1(B_293,k1_zfmisc_1(A_292)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8994,plain,(
    ! [C_294] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_294) = k4_xboole_0('#skF_2',C_294) ),
    inference(resolution,[status(thm)],[c_42,c_8988])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_112,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_222,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2054,plain,(
    ! [B_139,A_140] :
      ( v4_pre_topc(B_139,A_140)
      | k2_pre_topc(A_140,B_139) != B_139
      | ~ v2_pre_topc(A_140)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2064,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2054])).

tff(c_2069,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_2064])).

tff(c_2070,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_2069])).

tff(c_2180,plain,(
    ! [A_143,B_144] :
      ( k4_subset_1(u1_struct_0(A_143),B_144,k2_tops_1(A_143,B_144)) = k2_pre_topc(A_143,B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2187,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2180])).

tff(c_2192,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2187])).

tff(c_768,plain,(
    ! [A_88,B_89,C_90] :
      ( k7_subset_1(A_88,B_89,C_90) = k4_xboole_0(B_89,C_90)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_775,plain,(
    ! [C_91] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_91) = k4_xboole_0('#skF_2',C_91) ),
    inference(resolution,[status(thm)],[c_42,c_768])).

tff(c_781,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_112])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_223,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k4_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_113,plain,(
    ! [A_50,B_51] :
      ( k2_xboole_0(A_50,B_51) = B_51
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_141,plain,(
    ! [A_53,B_54] : k2_xboole_0(k4_xboole_0(A_53,B_54),A_53) = A_53 ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_148,plain,(
    ! [B_54] : k4_xboole_0(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_8])).

tff(c_263,plain,(
    ! [B_62] : k3_xboole_0(k1_xboole_0,B_62) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_148])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_268,plain,(
    ! [B_62] : k3_xboole_0(B_62,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_2])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_258,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_223])).

tff(c_458,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_258])).

tff(c_73,plain,(
    ! [A_43,B_44] : r1_tarski(k4_xboole_0(A_43,B_44),A_43) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_73])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_596,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,B_81) = k3_subset_1(A_80,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_929,plain,(
    ! [B_98,A_99] :
      ( k4_xboole_0(B_98,A_99) = k3_subset_1(B_98,A_99)
      | ~ r1_tarski(A_99,B_98) ) ),
    inference(resolution,[status(thm)],[c_28,c_596])).

tff(c_950,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_subset_1(A_12,A_12) ),
    inference(resolution,[status(thm)],[c_76,c_929])).

tff(c_964,plain,(
    ! [A_12] : k3_subset_1(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_950])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_953,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_subset_1(A_8,k4_xboole_0(A_8,B_9)) ),
    inference(resolution,[status(thm)],[c_10,c_929])).

tff(c_1008,plain,(
    ! [A_102,B_103] : k3_subset_1(A_102,k4_xboole_0(A_102,B_103)) = k3_xboole_0(A_102,B_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_953])).

tff(c_386,plain,(
    ! [A_70,B_71] :
      ( k3_subset_1(A_70,k3_subset_1(A_70,B_71)) = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_391,plain,(
    ! [B_26,A_25] :
      ( k3_subset_1(B_26,k3_subset_1(B_26,A_25)) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_28,c_386])).

tff(c_1014,plain,(
    ! [A_102,B_103] :
      ( k3_subset_1(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103)
      | ~ r1_tarski(k4_xboole_0(A_102,B_103),A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_391])).

tff(c_1038,plain,(
    ! [A_102,B_103] : k3_subset_1(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1014])).

tff(c_242,plain,(
    ! [A_60,B_61] : r1_tarski(k3_xboole_0(A_60,B_61),A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_10])).

tff(c_960,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k3_subset_1(A_60,k3_xboole_0(A_60,B_61)) ),
    inference(resolution,[status(thm)],[c_242,c_929])).

tff(c_1424,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_960])).

tff(c_245,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,k4_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_223])).

tff(c_1494,plain,(
    ! [A_123,B_124] : k3_xboole_0(A_123,k4_xboole_0(A_123,B_124)) = k4_xboole_0(A_123,B_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1424,c_245])).

tff(c_1156,plain,(
    ! [A_106,B_107] : k3_subset_1(A_106,k3_xboole_0(A_106,B_107)) = k4_xboole_0(A_106,B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1014])).

tff(c_1183,plain,(
    ! [B_2,A_1] : k3_subset_1(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1156])).

tff(c_1503,plain,(
    ! [A_123,B_124] : k3_subset_1(k4_xboole_0(A_123,B_124),k4_xboole_0(A_123,B_124)) = k4_xboole_0(k4_xboole_0(A_123,B_124),A_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_1494,c_1183])).

tff(c_1607,plain,(
    ! [A_128,B_129] : k4_xboole_0(k4_xboole_0(A_128,B_129),A_128) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_964,c_1503])).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1630,plain,(
    ! [A_128,B_129] : k2_xboole_0(A_128,k4_xboole_0(A_128,B_129)) = k2_xboole_0(A_128,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1607,c_12])).

tff(c_1801,plain,(
    ! [A_133,B_134] : k2_xboole_0(A_133,k4_xboole_0(A_133,B_134)) = A_133 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1630])).

tff(c_1836,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_1801])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k2_tops_1(A_30,B_31),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1597,plain,(
    ! [A_125,B_126,C_127] :
      ( k4_subset_1(A_125,B_126,C_127) = k2_xboole_0(B_126,C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(A_125))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7844,plain,(
    ! [A_226,B_227,B_228] :
      ( k4_subset_1(u1_struct_0(A_226),B_227,k2_tops_1(A_226,B_228)) = k2_xboole_0(B_227,k2_tops_1(A_226,B_228))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(A_226) ) ),
    inference(resolution,[status(thm)],[c_34,c_1597])).

tff(c_7851,plain,(
    ! [B_228] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_228)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_228))
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_7844])).

tff(c_7860,plain,(
    ! [B_229] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_229)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_229))
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7851])).

tff(c_7871,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_7860])).

tff(c_7877,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2192,c_1836,c_7871])).

tff(c_7879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2070,c_7877])).

tff(c_7880,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_8428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_7880])).

tff(c_8429,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_8460,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8429,c_48])).

tff(c_9046,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8994,c_8460])).

tff(c_9312,plain,(
    ! [A_312,B_313] :
      ( k2_pre_topc(A_312,B_313) = B_313
      | ~ v4_pre_topc(B_313,A_312)
      | ~ m1_subset_1(B_313,k1_zfmisc_1(u1_struct_0(A_312)))
      | ~ l1_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_9319,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_9312])).

tff(c_9323,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8429,c_9319])).

tff(c_10743,plain,(
    ! [A_361,B_362] :
      ( k7_subset_1(u1_struct_0(A_361),k2_pre_topc(A_361,B_362),k1_tops_1(A_361,B_362)) = k2_tops_1(A_361,B_362)
      | ~ m1_subset_1(B_362,k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ l1_pre_topc(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10752,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9323,c_10743])).

tff(c_10756,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_8994,c_10752])).

tff(c_10758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9046,c_10756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:05:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.30/3.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.30/3.85  
% 10.30/3.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.30/3.85  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.30/3.85  
% 10.30/3.85  %Foreground sorts:
% 10.30/3.85  
% 10.30/3.85  
% 10.30/3.85  %Background operators:
% 10.30/3.85  
% 10.30/3.85  
% 10.30/3.85  %Foreground operators:
% 10.30/3.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.30/3.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.30/3.85  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.30/3.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.30/3.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.30/3.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.30/3.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.30/3.85  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.30/3.85  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.30/3.85  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.30/3.85  tff('#skF_2', type, '#skF_2': $i).
% 10.30/3.85  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.30/3.85  tff('#skF_1', type, '#skF_1': $i).
% 10.30/3.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.30/3.85  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.30/3.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.30/3.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.30/3.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.30/3.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.30/3.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.30/3.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.30/3.85  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.30/3.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.30/3.85  
% 10.66/3.88  tff(f_120, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 10.66/3.88  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.66/3.88  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 10.66/3.88  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 10.66/3.88  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 10.66/3.88  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.66/3.88  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.66/3.88  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.66/3.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.66/3.88  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 10.66/3.88  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.66/3.88  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 10.66/3.88  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.66/3.88  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.66/3.88  tff(f_86, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 10.66/3.88  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.66/3.88  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 10.66/3.88  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.66/3.88  tff(c_8988, plain, (![A_292, B_293, C_294]: (k7_subset_1(A_292, B_293, C_294)=k4_xboole_0(B_293, C_294) | ~m1_subset_1(B_293, k1_zfmisc_1(A_292)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.66/3.88  tff(c_8994, plain, (![C_294]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_294)=k4_xboole_0('#skF_2', C_294))), inference(resolution, [status(thm)], [c_42, c_8988])).
% 10.66/3.88  tff(c_54, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.66/3.88  tff(c_112, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 10.66/3.88  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.66/3.88  tff(c_222, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 10.66/3.88  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.66/3.88  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.66/3.88  tff(c_2054, plain, (![B_139, A_140]: (v4_pre_topc(B_139, A_140) | k2_pre_topc(A_140, B_139)!=B_139 | ~v2_pre_topc(A_140) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.66/3.88  tff(c_2064, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2054])).
% 10.66/3.88  tff(c_2069, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_2064])).
% 10.66/3.88  tff(c_2070, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_222, c_2069])).
% 10.66/3.88  tff(c_2180, plain, (![A_143, B_144]: (k4_subset_1(u1_struct_0(A_143), B_144, k2_tops_1(A_143, B_144))=k2_pre_topc(A_143, B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.66/3.88  tff(c_2187, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2180])).
% 10.66/3.88  tff(c_2192, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2187])).
% 10.66/3.88  tff(c_768, plain, (![A_88, B_89, C_90]: (k7_subset_1(A_88, B_89, C_90)=k4_xboole_0(B_89, C_90) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.66/3.88  tff(c_775, plain, (![C_91]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_91)=k4_xboole_0('#skF_2', C_91))), inference(resolution, [status(thm)], [c_42, c_768])).
% 10.66/3.88  tff(c_781, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_775, c_112])).
% 10.66/3.88  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.66/3.88  tff(c_223, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k4_xboole_0(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.66/3.88  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.66/3.88  tff(c_113, plain, (![A_50, B_51]: (k2_xboole_0(A_50, B_51)=B_51 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.66/3.88  tff(c_141, plain, (![A_53, B_54]: (k2_xboole_0(k4_xboole_0(A_53, B_54), A_53)=A_53)), inference(resolution, [status(thm)], [c_10, c_113])).
% 10.66/3.88  tff(c_148, plain, (![B_54]: (k4_xboole_0(k1_xboole_0, B_54)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_141, c_8])).
% 10.66/3.88  tff(c_263, plain, (![B_62]: (k3_xboole_0(k1_xboole_0, B_62)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_223, c_148])).
% 10.66/3.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.66/3.88  tff(c_268, plain, (![B_62]: (k3_xboole_0(B_62, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_263, c_2])).
% 10.66/3.88  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.66/3.88  tff(c_258, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_223])).
% 10.66/3.88  tff(c_458, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_268, c_258])).
% 10.66/3.88  tff(c_73, plain, (![A_43, B_44]: (r1_tarski(k4_xboole_0(A_43, B_44), A_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.66/3.88  tff(c_76, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_73])).
% 10.66/3.88  tff(c_28, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.66/3.88  tff(c_596, plain, (![A_80, B_81]: (k4_xboole_0(A_80, B_81)=k3_subset_1(A_80, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.66/3.88  tff(c_929, plain, (![B_98, A_99]: (k4_xboole_0(B_98, A_99)=k3_subset_1(B_98, A_99) | ~r1_tarski(A_99, B_98))), inference(resolution, [status(thm)], [c_28, c_596])).
% 10.66/3.88  tff(c_950, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_subset_1(A_12, A_12))), inference(resolution, [status(thm)], [c_76, c_929])).
% 10.66/3.88  tff(c_964, plain, (![A_12]: (k3_subset_1(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_458, c_950])).
% 10.66/3.88  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.66/3.88  tff(c_953, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_subset_1(A_8, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_10, c_929])).
% 10.66/3.88  tff(c_1008, plain, (![A_102, B_103]: (k3_subset_1(A_102, k4_xboole_0(A_102, B_103))=k3_xboole_0(A_102, B_103))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_953])).
% 10.66/3.88  tff(c_386, plain, (![A_70, B_71]: (k3_subset_1(A_70, k3_subset_1(A_70, B_71))=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.66/3.88  tff(c_391, plain, (![B_26, A_25]: (k3_subset_1(B_26, k3_subset_1(B_26, A_25))=A_25 | ~r1_tarski(A_25, B_26))), inference(resolution, [status(thm)], [c_28, c_386])).
% 10.66/3.88  tff(c_1014, plain, (![A_102, B_103]: (k3_subset_1(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103) | ~r1_tarski(k4_xboole_0(A_102, B_103), A_102))), inference(superposition, [status(thm), theory('equality')], [c_1008, c_391])).
% 10.66/3.88  tff(c_1038, plain, (![A_102, B_103]: (k3_subset_1(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1014])).
% 10.66/3.88  tff(c_242, plain, (![A_60, B_61]: (r1_tarski(k3_xboole_0(A_60, B_61), A_60))), inference(superposition, [status(thm), theory('equality')], [c_223, c_10])).
% 10.66/3.88  tff(c_960, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k3_subset_1(A_60, k3_xboole_0(A_60, B_61)))), inference(resolution, [status(thm)], [c_242, c_929])).
% 10.66/3.88  tff(c_1424, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_960])).
% 10.66/3.88  tff(c_245, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k3_xboole_0(A_13, k4_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_223])).
% 10.66/3.88  tff(c_1494, plain, (![A_123, B_124]: (k3_xboole_0(A_123, k4_xboole_0(A_123, B_124))=k4_xboole_0(A_123, B_124))), inference(demodulation, [status(thm), theory('equality')], [c_1424, c_245])).
% 10.66/3.88  tff(c_1156, plain, (![A_106, B_107]: (k3_subset_1(A_106, k3_xboole_0(A_106, B_107))=k4_xboole_0(A_106, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1014])).
% 10.66/3.88  tff(c_1183, plain, (![B_2, A_1]: (k3_subset_1(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1156])).
% 10.66/3.88  tff(c_1503, plain, (![A_123, B_124]: (k3_subset_1(k4_xboole_0(A_123, B_124), k4_xboole_0(A_123, B_124))=k4_xboole_0(k4_xboole_0(A_123, B_124), A_123))), inference(superposition, [status(thm), theory('equality')], [c_1494, c_1183])).
% 10.66/3.88  tff(c_1607, plain, (![A_128, B_129]: (k4_xboole_0(k4_xboole_0(A_128, B_129), A_128)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_964, c_1503])).
% 10.66/3.88  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.66/3.88  tff(c_1630, plain, (![A_128, B_129]: (k2_xboole_0(A_128, k4_xboole_0(A_128, B_129))=k2_xboole_0(A_128, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1607, c_12])).
% 10.66/3.88  tff(c_1801, plain, (![A_133, B_134]: (k2_xboole_0(A_133, k4_xboole_0(A_133, B_134))=A_133)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1630])).
% 10.66/3.88  tff(c_1836, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_781, c_1801])).
% 10.66/3.88  tff(c_34, plain, (![A_30, B_31]: (m1_subset_1(k2_tops_1(A_30, B_31), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.66/3.88  tff(c_1597, plain, (![A_125, B_126, C_127]: (k4_subset_1(A_125, B_126, C_127)=k2_xboole_0(B_126, C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(A_125)) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.66/3.88  tff(c_7844, plain, (![A_226, B_227, B_228]: (k4_subset_1(u1_struct_0(A_226), B_227, k2_tops_1(A_226, B_228))=k2_xboole_0(B_227, k2_tops_1(A_226, B_228)) | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(A_226))) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(A_226))), inference(resolution, [status(thm)], [c_34, c_1597])).
% 10.66/3.88  tff(c_7851, plain, (![B_228]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_228))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_228)) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_7844])).
% 10.66/3.88  tff(c_7860, plain, (![B_229]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_229))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_229)) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7851])).
% 10.66/3.88  tff(c_7871, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_7860])).
% 10.66/3.88  tff(c_7877, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2192, c_1836, c_7871])).
% 10.66/3.88  tff(c_7879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2070, c_7877])).
% 10.66/3.88  tff(c_7880, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 10.66/3.88  tff(c_8428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_7880])).
% 10.66/3.88  tff(c_8429, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 10.66/3.88  tff(c_8460, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8429, c_48])).
% 10.66/3.88  tff(c_9046, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8994, c_8460])).
% 10.66/3.88  tff(c_9312, plain, (![A_312, B_313]: (k2_pre_topc(A_312, B_313)=B_313 | ~v4_pre_topc(B_313, A_312) | ~m1_subset_1(B_313, k1_zfmisc_1(u1_struct_0(A_312))) | ~l1_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.66/3.88  tff(c_9319, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_9312])).
% 10.66/3.88  tff(c_9323, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8429, c_9319])).
% 10.66/3.88  tff(c_10743, plain, (![A_361, B_362]: (k7_subset_1(u1_struct_0(A_361), k2_pre_topc(A_361, B_362), k1_tops_1(A_361, B_362))=k2_tops_1(A_361, B_362) | ~m1_subset_1(B_362, k1_zfmisc_1(u1_struct_0(A_361))) | ~l1_pre_topc(A_361))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.66/3.88  tff(c_10752, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9323, c_10743])).
% 10.66/3.88  tff(c_10756, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_8994, c_10752])).
% 10.66/3.88  tff(c_10758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9046, c_10756])).
% 10.66/3.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.66/3.88  
% 10.66/3.88  Inference rules
% 10.66/3.88  ----------------------
% 10.66/3.88  #Ref     : 0
% 10.66/3.88  #Sup     : 2651
% 10.66/3.88  #Fact    : 0
% 10.66/3.88  #Define  : 0
% 10.66/3.88  #Split   : 3
% 10.66/3.88  #Chain   : 0
% 10.66/3.88  #Close   : 0
% 10.66/3.88  
% 10.66/3.88  Ordering : KBO
% 10.66/3.88  
% 10.66/3.88  Simplification rules
% 10.66/3.88  ----------------------
% 10.66/3.88  #Subsume      : 87
% 10.66/3.88  #Demod        : 3382
% 10.66/3.88  #Tautology    : 2075
% 10.66/3.88  #SimpNegUnit  : 5
% 10.66/3.88  #BackRed      : 6
% 10.66/3.88  
% 10.66/3.88  #Partial instantiations: 0
% 10.66/3.88  #Strategies tried      : 1
% 10.66/3.88  
% 10.66/3.88  Timing (in seconds)
% 10.66/3.88  ----------------------
% 10.66/3.89  Preprocessing        : 0.52
% 10.66/3.89  Parsing              : 0.27
% 10.66/3.89  CNF conversion       : 0.04
% 10.66/3.89  Main loop            : 2.50
% 10.66/3.89  Inferencing          : 0.71
% 10.66/3.89  Reduction            : 1.22
% 10.66/3.89  Demodulation         : 1.02
% 10.66/3.89  BG Simplification    : 0.07
% 10.66/3.89  Subsumption          : 0.34
% 10.66/3.89  Abstraction          : 0.12
% 10.66/3.89  MUC search           : 0.00
% 10.66/3.89  Cooper               : 0.00
% 10.66/3.89  Total                : 3.09
% 10.66/3.89  Index Insertion      : 0.00
% 10.66/3.89  Index Deletion       : 0.00
% 10.66/3.89  Index Matching       : 0.00
% 10.66/3.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
