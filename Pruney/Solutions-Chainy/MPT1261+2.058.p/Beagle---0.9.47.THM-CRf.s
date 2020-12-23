%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:20 EST 2020

% Result     : Theorem 10.44s
% Output     : CNFRefutation 10.44s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 270 expanded)
%              Number of leaves         :   45 ( 108 expanded)
%              Depth                    :   16
%              Number of atoms          :  199 ( 480 expanded)
%              Number of equality atoms :   72 ( 158 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
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

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_14511,plain,(
    ! [A_444,B_445,C_446] :
      ( k7_subset_1(A_444,B_445,C_446) = k4_xboole_0(B_445,C_446)
      | ~ m1_subset_1(B_445,k1_zfmisc_1(A_444)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14520,plain,(
    ! [C_446] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_446) = k4_xboole_0('#skF_2',C_446) ),
    inference(resolution,[status(thm)],[c_52,c_14511])).

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_204,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3752,plain,(
    ! [A_202,B_203] :
      ( k4_subset_1(u1_struct_0(A_202),B_203,k2_tops_1(A_202,B_203)) = k2_pre_topc(A_202,B_203)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3760,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_3752])).

tff(c_3765,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3760])).

tff(c_64,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_124,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1867,plain,(
    ! [A_150,B_151,C_152] :
      ( k7_subset_1(A_150,B_151,C_152) = k4_xboole_0(B_151,C_152)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(A_150)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2073,plain,(
    ! [C_157] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_157) = k4_xboole_0('#skF_2',C_157) ),
    inference(resolution,[status(thm)],[c_52,c_1867])).

tff(c_2085,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_2073])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_125,plain,(
    ! [A_66,B_67] :
      ( k2_xboole_0(A_66,B_67) = B_67
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),A_9) = A_9 ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_22,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_189,plain,(
    ! [A_77,B_78] : k3_tarski(k2_tarski(A_77,B_78)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_388,plain,(
    ! [A_89,B_90] : k3_tarski(k2_tarski(A_89,B_90)) = k2_xboole_0(B_90,A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_189])).

tff(c_24,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_411,plain,(
    ! [B_91,A_92] : k2_xboole_0(B_91,A_92) = k2_xboole_0(A_92,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_24])).

tff(c_449,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = A_9 ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_411])).

tff(c_3591,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2085,c_449])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,(
    ! [A_59,B_60] : r1_tarski(k4_xboole_0(A_59,B_60),A_59) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_81])).

tff(c_3603,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2085,c_10])).

tff(c_119,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_123,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_119])).

tff(c_588,plain,(
    ! [A_98,C_99,B_100] :
      ( r1_tarski(A_98,C_99)
      | ~ r1_tarski(B_100,C_99)
      | ~ r1_tarski(A_98,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_749,plain,(
    ! [A_108] :
      ( r1_tarski(A_108,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_108,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_123,c_588])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_755,plain,(
    ! [A_5,A_108] :
      ( r1_tarski(A_5,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_5,A_108)
      | ~ r1_tarski(A_108,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_749,c_6])).

tff(c_3611,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_3603,c_755])).

tff(c_3620,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3611])).

tff(c_40,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(A_40,k1_zfmisc_1(B_41))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2447,plain,(
    ! [A_166,B_167,C_168] :
      ( k4_subset_1(A_166,B_167,C_168) = k2_xboole_0(B_167,C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(A_166))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12002,plain,(
    ! [B_344,B_345,A_346] :
      ( k4_subset_1(B_344,B_345,A_346) = k2_xboole_0(B_345,A_346)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(B_344))
      | ~ r1_tarski(A_346,B_344) ) ),
    inference(resolution,[status(thm)],[c_40,c_2447])).

tff(c_12614,plain,(
    ! [A_352] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_352) = k2_xboole_0('#skF_2',A_352)
      | ~ r1_tarski(A_352,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_52,c_12002])).

tff(c_12678,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3620,c_12614])).

tff(c_12744,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3765,c_3591,c_12678])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2355,plain,(
    ! [A_163,B_164] :
      ( v4_pre_topc(k2_pre_topc(A_163,B_164),A_163)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2363,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2355])).

tff(c_2368,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2363])).

tff(c_12765,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12744,c_2368])).

tff(c_12767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_12765])).

tff(c_12768,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_13080,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12768,c_124])).

tff(c_13081,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_13158,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13081,c_58])).

tff(c_14718,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14520,c_13158])).

tff(c_15921,plain,(
    ! [A_482,B_483] :
      ( k4_subset_1(u1_struct_0(A_482),B_483,k2_tops_1(A_482,B_483)) = k2_pre_topc(A_482,B_483)
      | ~ m1_subset_1(B_483,k1_zfmisc_1(u1_struct_0(A_482)))
      | ~ l1_pre_topc(A_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_15929,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_15921])).

tff(c_15934,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_15929])).

tff(c_15290,plain,(
    ! [A_465,B_466] :
      ( r1_tarski(k2_tops_1(A_465,B_466),B_466)
      | ~ v4_pre_topc(B_466,A_465)
      | ~ m1_subset_1(B_466,k1_zfmisc_1(u1_struct_0(A_465)))
      | ~ l1_pre_topc(A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_15298,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_15290])).

tff(c_15303,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_13081,c_15298])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_15314,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_15303,c_4])).

tff(c_13116,plain,(
    ! [A_374,B_375] : k3_tarski(k2_tarski(A_374,B_375)) = k2_xboole_0(A_374,B_375) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_13164,plain,(
    ! [A_381,B_382] : k3_tarski(k2_tarski(A_381,B_382)) = k2_xboole_0(B_382,A_381) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_13116])).

tff(c_13170,plain,(
    ! [B_382,A_381] : k2_xboole_0(B_382,A_381) = k2_xboole_0(A_381,B_382) ),
    inference(superposition,[status(thm),theory(equality)],[c_13164,c_24])).

tff(c_15336,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_15314,c_13170])).

tff(c_13484,plain,(
    ! [A_398,C_399,B_400] :
      ( r1_tarski(A_398,C_399)
      | ~ r1_tarski(B_400,C_399)
      | ~ r1_tarski(A_398,B_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13589,plain,(
    ! [A_405] :
      ( r1_tarski(A_405,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_405,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_123,c_13484])).

tff(c_13596,plain,(
    ! [A_405] :
      ( k2_xboole_0(A_405,u1_struct_0('#skF_1')) = u1_struct_0('#skF_1')
      | ~ r1_tarski(A_405,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_13589,c_4])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_13247,plain,(
    ! [A_387,B_388] : k4_xboole_0(A_387,k4_xboole_0(A_387,B_388)) = k3_xboole_0(A_387,B_388) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_13274,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_13247])).

tff(c_13278,plain,(
    ! [A_389] : k4_xboole_0(A_389,A_389) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_13274])).

tff(c_13295,plain,(
    ! [A_389] : r1_tarski(k1_xboole_0,A_389) ),
    inference(superposition,[status(thm),theory(equality)],[c_13278,c_10])).

tff(c_13103,plain,(
    ! [A_372,B_373] :
      ( k2_xboole_0(A_372,B_373) = B_373
      | ~ r1_tarski(A_372,B_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13115,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),A_9) = A_9 ),
    inference(resolution,[status(thm)],[c_10,c_13103])).

tff(c_13341,plain,(
    ! [A_392] : k2_xboole_0(k1_xboole_0,A_392) = A_392 ),
    inference(superposition,[status(thm),theory(equality)],[c_13278,c_13115])).

tff(c_13354,plain,(
    ! [A_392] : k2_xboole_0(A_392,k1_xboole_0) = A_392 ),
    inference(superposition,[status(thm),theory(equality)],[c_13341,c_13170])).

tff(c_14322,plain,(
    ! [A_437,B_438,C_439] :
      ( r1_tarski(k4_xboole_0(A_437,B_438),C_439)
      | ~ r1_tarski(A_437,k2_xboole_0(B_438,C_439)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(B_12,A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13289,plain,(
    ! [A_389] :
      ( k1_xboole_0 = A_389
      | ~ r1_tarski(A_389,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13278,c_12])).

tff(c_14332,plain,(
    ! [A_437,B_438] :
      ( k4_xboole_0(A_437,B_438) = k1_xboole_0
      | ~ r1_tarski(A_437,k2_xboole_0(B_438,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_14322,c_13289])).

tff(c_14361,plain,(
    ! [A_437,B_438] :
      ( k4_xboole_0(A_437,B_438) = k1_xboole_0
      | ~ r1_tarski(A_437,B_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13354,c_14332])).

tff(c_15312,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15303,c_14361])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(A_17,k2_xboole_0(B_18,C_19))
      | ~ r1_tarski(k4_xboole_0(A_17,B_18),C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_15395,plain,(
    ! [C_19] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0('#skF_2',C_19))
      | ~ r1_tarski(k1_xboole_0,C_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15312,c_18])).

tff(c_15727,plain,(
    ! [C_477] : r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0('#skF_2',C_477)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13295,c_15395])).

tff(c_15749,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13596,c_15727])).

tff(c_15779,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_15749])).

tff(c_15423,plain,(
    ! [A_467,B_468,C_469] :
      ( k4_subset_1(A_467,B_468,C_469) = k2_xboole_0(B_468,C_469)
      | ~ m1_subset_1(C_469,k1_zfmisc_1(A_467))
      | ~ m1_subset_1(B_468,k1_zfmisc_1(A_467)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26783,plain,(
    ! [B_666,B_667,A_668] :
      ( k4_subset_1(B_666,B_667,A_668) = k2_xboole_0(B_667,A_668)
      | ~ m1_subset_1(B_667,k1_zfmisc_1(B_666))
      | ~ r1_tarski(A_668,B_666) ) ),
    inference(resolution,[status(thm)],[c_40,c_15423])).

tff(c_26998,plain,(
    ! [A_674] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_674) = k2_xboole_0('#skF_2',A_674)
      | ~ r1_tarski(A_674,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_52,c_26783])).

tff(c_27087,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_15779,c_26998])).

tff(c_27150,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15934,c_15336,c_27087])).

tff(c_44,plain,(
    ! [A_44,B_46] :
      ( k7_subset_1(u1_struct_0(A_44),k2_pre_topc(A_44,B_46),k1_tops_1(A_44,B_46)) = k2_tops_1(A_44,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_27172,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_27150,c_44])).

tff(c_27178,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_14520,c_27172])).

tff(c_27180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14718,c_27178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:19:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.44/4.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.44/4.09  
% 10.44/4.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.44/4.09  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.44/4.09  
% 10.44/4.09  %Foreground sorts:
% 10.44/4.09  
% 10.44/4.09  
% 10.44/4.09  %Background operators:
% 10.44/4.09  
% 10.44/4.09  
% 10.44/4.09  %Foreground operators:
% 10.44/4.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.44/4.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.44/4.09  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.44/4.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.44/4.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.44/4.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.44/4.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.44/4.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.44/4.09  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.44/4.09  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.44/4.09  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.44/4.09  tff('#skF_2', type, '#skF_2': $i).
% 10.44/4.09  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.44/4.09  tff('#skF_1', type, '#skF_1': $i).
% 10.44/4.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.44/4.09  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.44/4.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.44/4.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.44/4.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.44/4.09  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.44/4.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.44/4.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.44/4.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.44/4.09  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.44/4.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.44/4.09  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.44/4.09  
% 10.44/4.11  tff(f_139, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 10.44/4.11  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.44/4.11  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 10.44/4.11  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.44/4.11  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.44/4.11  tff(f_59, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.44/4.11  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.44/4.11  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.44/4.11  tff(f_89, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.44/4.11  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.44/4.11  tff(f_79, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.44/4.11  tff(f_97, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 10.44/4.11  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 10.44/4.11  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 10.44/4.11  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.44/4.11  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 10.44/4.11  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 10.44/4.11  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 10.44/4.11  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 10.44/4.11  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 10.44/4.11  tff(c_14511, plain, (![A_444, B_445, C_446]: (k7_subset_1(A_444, B_445, C_446)=k4_xboole_0(B_445, C_446) | ~m1_subset_1(B_445, k1_zfmisc_1(A_444)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.44/4.11  tff(c_14520, plain, (![C_446]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_446)=k4_xboole_0('#skF_2', C_446))), inference(resolution, [status(thm)], [c_52, c_14511])).
% 10.44/4.11  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 10.44/4.11  tff(c_204, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 10.44/4.11  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 10.44/4.11  tff(c_3752, plain, (![A_202, B_203]: (k4_subset_1(u1_struct_0(A_202), B_203, k2_tops_1(A_202, B_203))=k2_pre_topc(A_202, B_203) | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.44/4.11  tff(c_3760, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_3752])).
% 10.44/4.11  tff(c_3765, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3760])).
% 10.44/4.11  tff(c_64, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 10.44/4.11  tff(c_124, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 10.44/4.11  tff(c_1867, plain, (![A_150, B_151, C_152]: (k7_subset_1(A_150, B_151, C_152)=k4_xboole_0(B_151, C_152) | ~m1_subset_1(B_151, k1_zfmisc_1(A_150)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.44/4.11  tff(c_2073, plain, (![C_157]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_157)=k4_xboole_0('#skF_2', C_157))), inference(resolution, [status(thm)], [c_52, c_1867])).
% 10.44/4.11  tff(c_2085, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_124, c_2073])).
% 10.44/4.11  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.44/4.11  tff(c_125, plain, (![A_66, B_67]: (k2_xboole_0(A_66, B_67)=B_67 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.44/4.11  tff(c_137, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), A_9)=A_9)), inference(resolution, [status(thm)], [c_10, c_125])).
% 10.44/4.11  tff(c_22, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.44/4.11  tff(c_189, plain, (![A_77, B_78]: (k3_tarski(k2_tarski(A_77, B_78))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.44/4.11  tff(c_388, plain, (![A_89, B_90]: (k3_tarski(k2_tarski(A_89, B_90))=k2_xboole_0(B_90, A_89))), inference(superposition, [status(thm), theory('equality')], [c_22, c_189])).
% 10.44/4.11  tff(c_24, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.44/4.11  tff(c_411, plain, (![B_91, A_92]: (k2_xboole_0(B_91, A_92)=k2_xboole_0(A_92, B_91))), inference(superposition, [status(thm), theory('equality')], [c_388, c_24])).
% 10.44/4.11  tff(c_449, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(A_9, B_10))=A_9)), inference(superposition, [status(thm), theory('equality')], [c_137, c_411])).
% 10.44/4.11  tff(c_3591, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2085, c_449])).
% 10.44/4.11  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.44/4.11  tff(c_81, plain, (![A_59, B_60]: (r1_tarski(k4_xboole_0(A_59, B_60), A_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.44/4.11  tff(c_84, plain, (![A_13]: (r1_tarski(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_81])).
% 10.44/4.11  tff(c_3603, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2085, c_10])).
% 10.44/4.11  tff(c_119, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.44/4.11  tff(c_123, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_119])).
% 10.44/4.11  tff(c_588, plain, (![A_98, C_99, B_100]: (r1_tarski(A_98, C_99) | ~r1_tarski(B_100, C_99) | ~r1_tarski(A_98, B_100))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.44/4.11  tff(c_749, plain, (![A_108]: (r1_tarski(A_108, u1_struct_0('#skF_1')) | ~r1_tarski(A_108, '#skF_2'))), inference(resolution, [status(thm)], [c_123, c_588])).
% 10.44/4.11  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.44/4.11  tff(c_755, plain, (![A_5, A_108]: (r1_tarski(A_5, u1_struct_0('#skF_1')) | ~r1_tarski(A_5, A_108) | ~r1_tarski(A_108, '#skF_2'))), inference(resolution, [status(thm)], [c_749, c_6])).
% 10.44/4.11  tff(c_3611, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_3603, c_755])).
% 10.44/4.11  tff(c_3620, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_3611])).
% 10.44/4.11  tff(c_40, plain, (![A_40, B_41]: (m1_subset_1(A_40, k1_zfmisc_1(B_41)) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.44/4.11  tff(c_2447, plain, (![A_166, B_167, C_168]: (k4_subset_1(A_166, B_167, C_168)=k2_xboole_0(B_167, C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(A_166)) | ~m1_subset_1(B_167, k1_zfmisc_1(A_166)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.44/4.11  tff(c_12002, plain, (![B_344, B_345, A_346]: (k4_subset_1(B_344, B_345, A_346)=k2_xboole_0(B_345, A_346) | ~m1_subset_1(B_345, k1_zfmisc_1(B_344)) | ~r1_tarski(A_346, B_344))), inference(resolution, [status(thm)], [c_40, c_2447])).
% 10.44/4.11  tff(c_12614, plain, (![A_352]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_352)=k2_xboole_0('#skF_2', A_352) | ~r1_tarski(A_352, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_52, c_12002])).
% 10.44/4.11  tff(c_12678, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3620, c_12614])).
% 10.44/4.11  tff(c_12744, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3765, c_3591, c_12678])).
% 10.44/4.11  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 10.44/4.11  tff(c_2355, plain, (![A_163, B_164]: (v4_pre_topc(k2_pre_topc(A_163, B_164), A_163) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.44/4.11  tff(c_2363, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2355])).
% 10.44/4.11  tff(c_2368, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2363])).
% 10.44/4.11  tff(c_12765, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12744, c_2368])).
% 10.44/4.11  tff(c_12767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_204, c_12765])).
% 10.44/4.11  tff(c_12768, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 10.44/4.11  tff(c_13080, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12768, c_124])).
% 10.44/4.11  tff(c_13081, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 10.44/4.11  tff(c_13158, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13081, c_58])).
% 10.44/4.11  tff(c_14718, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14520, c_13158])).
% 10.44/4.11  tff(c_15921, plain, (![A_482, B_483]: (k4_subset_1(u1_struct_0(A_482), B_483, k2_tops_1(A_482, B_483))=k2_pre_topc(A_482, B_483) | ~m1_subset_1(B_483, k1_zfmisc_1(u1_struct_0(A_482))) | ~l1_pre_topc(A_482))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.44/4.11  tff(c_15929, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_15921])).
% 10.44/4.11  tff(c_15934, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_15929])).
% 10.44/4.11  tff(c_15290, plain, (![A_465, B_466]: (r1_tarski(k2_tops_1(A_465, B_466), B_466) | ~v4_pre_topc(B_466, A_465) | ~m1_subset_1(B_466, k1_zfmisc_1(u1_struct_0(A_465))) | ~l1_pre_topc(A_465))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.44/4.11  tff(c_15298, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_15290])).
% 10.44/4.11  tff(c_15303, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_13081, c_15298])).
% 10.44/4.11  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.44/4.11  tff(c_15314, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_15303, c_4])).
% 10.44/4.11  tff(c_13116, plain, (![A_374, B_375]: (k3_tarski(k2_tarski(A_374, B_375))=k2_xboole_0(A_374, B_375))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.44/4.11  tff(c_13164, plain, (![A_381, B_382]: (k3_tarski(k2_tarski(A_381, B_382))=k2_xboole_0(B_382, A_381))), inference(superposition, [status(thm), theory('equality')], [c_22, c_13116])).
% 10.44/4.11  tff(c_13170, plain, (![B_382, A_381]: (k2_xboole_0(B_382, A_381)=k2_xboole_0(A_381, B_382))), inference(superposition, [status(thm), theory('equality')], [c_13164, c_24])).
% 10.44/4.11  tff(c_15336, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_15314, c_13170])).
% 10.44/4.11  tff(c_13484, plain, (![A_398, C_399, B_400]: (r1_tarski(A_398, C_399) | ~r1_tarski(B_400, C_399) | ~r1_tarski(A_398, B_400))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.44/4.11  tff(c_13589, plain, (![A_405]: (r1_tarski(A_405, u1_struct_0('#skF_1')) | ~r1_tarski(A_405, '#skF_2'))), inference(resolution, [status(thm)], [c_123, c_13484])).
% 10.44/4.11  tff(c_13596, plain, (![A_405]: (k2_xboole_0(A_405, u1_struct_0('#skF_1'))=u1_struct_0('#skF_1') | ~r1_tarski(A_405, '#skF_2'))), inference(resolution, [status(thm)], [c_13589, c_4])).
% 10.44/4.11  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.44/4.11  tff(c_13247, plain, (![A_387, B_388]: (k4_xboole_0(A_387, k4_xboole_0(A_387, B_388))=k3_xboole_0(A_387, B_388))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.44/4.11  tff(c_13274, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_13247])).
% 10.44/4.11  tff(c_13278, plain, (![A_389]: (k4_xboole_0(A_389, A_389)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_13274])).
% 10.44/4.11  tff(c_13295, plain, (![A_389]: (r1_tarski(k1_xboole_0, A_389))), inference(superposition, [status(thm), theory('equality')], [c_13278, c_10])).
% 10.44/4.11  tff(c_13103, plain, (![A_372, B_373]: (k2_xboole_0(A_372, B_373)=B_373 | ~r1_tarski(A_372, B_373))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.44/4.11  tff(c_13115, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), A_9)=A_9)), inference(resolution, [status(thm)], [c_10, c_13103])).
% 10.44/4.11  tff(c_13341, plain, (![A_392]: (k2_xboole_0(k1_xboole_0, A_392)=A_392)), inference(superposition, [status(thm), theory('equality')], [c_13278, c_13115])).
% 10.44/4.11  tff(c_13354, plain, (![A_392]: (k2_xboole_0(A_392, k1_xboole_0)=A_392)), inference(superposition, [status(thm), theory('equality')], [c_13341, c_13170])).
% 10.44/4.11  tff(c_14322, plain, (![A_437, B_438, C_439]: (r1_tarski(k4_xboole_0(A_437, B_438), C_439) | ~r1_tarski(A_437, k2_xboole_0(B_438, C_439)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.44/4.11  tff(c_12, plain, (![A_11, B_12]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k4_xboole_0(B_12, A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.44/4.11  tff(c_13289, plain, (![A_389]: (k1_xboole_0=A_389 | ~r1_tarski(A_389, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13278, c_12])).
% 10.44/4.11  tff(c_14332, plain, (![A_437, B_438]: (k4_xboole_0(A_437, B_438)=k1_xboole_0 | ~r1_tarski(A_437, k2_xboole_0(B_438, k1_xboole_0)))), inference(resolution, [status(thm)], [c_14322, c_13289])).
% 10.44/4.11  tff(c_14361, plain, (![A_437, B_438]: (k4_xboole_0(A_437, B_438)=k1_xboole_0 | ~r1_tarski(A_437, B_438))), inference(demodulation, [status(thm), theory('equality')], [c_13354, c_14332])).
% 10.44/4.11  tff(c_15312, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_15303, c_14361])).
% 10.44/4.11  tff(c_18, plain, (![A_17, B_18, C_19]: (r1_tarski(A_17, k2_xboole_0(B_18, C_19)) | ~r1_tarski(k4_xboole_0(A_17, B_18), C_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.44/4.11  tff(c_15395, plain, (![C_19]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0('#skF_2', C_19)) | ~r1_tarski(k1_xboole_0, C_19))), inference(superposition, [status(thm), theory('equality')], [c_15312, c_18])).
% 10.44/4.11  tff(c_15727, plain, (![C_477]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0('#skF_2', C_477)))), inference(demodulation, [status(thm), theory('equality')], [c_13295, c_15395])).
% 10.44/4.11  tff(c_15749, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13596, c_15727])).
% 10.44/4.11  tff(c_15779, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_15749])).
% 10.44/4.11  tff(c_15423, plain, (![A_467, B_468, C_469]: (k4_subset_1(A_467, B_468, C_469)=k2_xboole_0(B_468, C_469) | ~m1_subset_1(C_469, k1_zfmisc_1(A_467)) | ~m1_subset_1(B_468, k1_zfmisc_1(A_467)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.44/4.11  tff(c_26783, plain, (![B_666, B_667, A_668]: (k4_subset_1(B_666, B_667, A_668)=k2_xboole_0(B_667, A_668) | ~m1_subset_1(B_667, k1_zfmisc_1(B_666)) | ~r1_tarski(A_668, B_666))), inference(resolution, [status(thm)], [c_40, c_15423])).
% 10.44/4.11  tff(c_26998, plain, (![A_674]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_674)=k2_xboole_0('#skF_2', A_674) | ~r1_tarski(A_674, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_52, c_26783])).
% 10.44/4.11  tff(c_27087, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_15779, c_26998])).
% 10.44/4.11  tff(c_27150, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15934, c_15336, c_27087])).
% 10.44/4.11  tff(c_44, plain, (![A_44, B_46]: (k7_subset_1(u1_struct_0(A_44), k2_pre_topc(A_44, B_46), k1_tops_1(A_44, B_46))=k2_tops_1(A_44, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.44/4.11  tff(c_27172, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_27150, c_44])).
% 10.44/4.11  tff(c_27178, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_14520, c_27172])).
% 10.44/4.11  tff(c_27180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14718, c_27178])).
% 10.44/4.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.44/4.11  
% 10.44/4.11  Inference rules
% 10.44/4.11  ----------------------
% 10.44/4.11  #Ref     : 0
% 10.44/4.11  #Sup     : 6554
% 10.44/4.11  #Fact    : 0
% 10.44/4.11  #Define  : 0
% 10.44/4.11  #Split   : 4
% 10.44/4.11  #Chain   : 0
% 10.44/4.11  #Close   : 0
% 10.44/4.11  
% 10.44/4.11  Ordering : KBO
% 10.44/4.11  
% 10.44/4.11  Simplification rules
% 10.44/4.11  ----------------------
% 10.44/4.11  #Subsume      : 251
% 10.44/4.11  #Demod        : 5248
% 10.44/4.11  #Tautology    : 4220
% 10.44/4.11  #SimpNegUnit  : 3
% 10.44/4.11  #BackRed      : 5
% 10.44/4.11  
% 10.44/4.11  #Partial instantiations: 0
% 10.44/4.11  #Strategies tried      : 1
% 10.44/4.11  
% 10.44/4.11  Timing (in seconds)
% 10.44/4.11  ----------------------
% 10.44/4.11  Preprocessing        : 0.35
% 10.44/4.11  Parsing              : 0.20
% 10.44/4.11  CNF conversion       : 0.02
% 10.44/4.11  Main loop            : 2.97
% 10.44/4.11  Inferencing          : 0.66
% 10.44/4.11  Reduction            : 1.49
% 10.44/4.11  Demodulation         : 1.27
% 10.44/4.11  BG Simplification    : 0.08
% 10.44/4.11  Subsumption          : 0.56
% 10.44/4.11  Abstraction          : 0.11
% 10.44/4.11  MUC search           : 0.00
% 10.44/4.11  Cooper               : 0.00
% 10.44/4.11  Total                : 3.36
% 10.44/4.11  Index Insertion      : 0.00
% 10.44/4.11  Index Deletion       : 0.00
% 10.44/4.11  Index Matching       : 0.00
% 10.44/4.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
