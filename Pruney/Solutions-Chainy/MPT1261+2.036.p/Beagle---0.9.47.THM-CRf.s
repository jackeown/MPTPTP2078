%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:16 EST 2020

% Result     : Theorem 23.15s
% Output     : CNFRefutation 23.15s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 476 expanded)
%              Number of leaves         :   51 ( 179 expanded)
%              Depth                    :   16
%              Number of atoms          :  233 ( 812 expanded)
%              Number of equality atoms :  113 ( 309 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_91,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

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

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_32412,plain,(
    ! [A_719,B_720,C_721] :
      ( k7_subset_1(A_719,B_720,C_721) = k4_xboole_0(B_720,C_721)
      | ~ m1_subset_1(B_720,k1_zfmisc_1(A_719)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32421,plain,(
    ! [C_721] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_721) = k4_xboole_0('#skF_2',C_721) ),
    inference(resolution,[status(thm)],[c_60,c_32412])).

tff(c_72,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_105,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_66,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_246,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_462,plain,(
    ! [A_102,B_103] : k4_xboole_0(A_102,k4_xboole_0(A_102,B_103)) = k3_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_497,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_462])).

tff(c_505,plain,(
    ! [A_104] : k4_xboole_0(A_104,A_104) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_497])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_522,plain,(
    ! [A_104] : r1_tarski(k1_xboole_0,A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_8])).

tff(c_46,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,k1_zfmisc_1(B_46))
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1764,plain,(
    ! [A_174,B_175] :
      ( k4_xboole_0(A_174,B_175) = k3_subset_1(A_174,B_175)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(A_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4862,plain,(
    ! [B_292,A_293] :
      ( k4_xboole_0(B_292,A_293) = k3_subset_1(B_292,A_293)
      | ~ r1_tarski(A_293,B_292) ) ),
    inference(resolution,[status(thm)],[c_46,c_1764])).

tff(c_5081,plain,(
    ! [A_104] : k4_xboole_0(A_104,k1_xboole_0) = k3_subset_1(A_104,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_522,c_4862])).

tff(c_5173,plain,(
    ! [A_104] : k3_subset_1(A_104,k1_xboole_0) = A_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5081])).

tff(c_2166,plain,(
    ! [A_194,B_195,C_196] :
      ( k7_subset_1(A_194,B_195,C_196) = k4_xboole_0(B_195,C_196)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2179,plain,(
    ! [C_197] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_197) = k4_xboole_0('#skF_2',C_197) ),
    inference(resolution,[status(thm)],[c_60,c_2166])).

tff(c_2185,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2179,c_105])).

tff(c_2694,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2185,c_8])).

tff(c_160,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(A_80,B_81)
      | ~ m1_subset_1(A_80,k1_zfmisc_1(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_168,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_160])).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_631,plain,(
    ! [A_110,C_111,B_112] :
      ( r1_tarski(A_110,C_111)
      | ~ r1_tarski(B_112,C_111)
      | ~ r1_tarski(A_110,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_649,plain,(
    ! [A_110] :
      ( r1_tarski(A_110,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_110,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_168,c_631])).

tff(c_3385,plain,(
    ! [A_236,B_237,C_238] :
      ( k4_subset_1(A_236,B_237,C_238) = k2_xboole_0(B_237,C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(A_236))
      | ~ m1_subset_1(B_237,k1_zfmisc_1(A_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16057,plain,(
    ! [B_427,B_428,A_429] :
      ( k4_subset_1(B_427,B_428,A_429) = k2_xboole_0(B_428,A_429)
      | ~ m1_subset_1(B_428,k1_zfmisc_1(B_427))
      | ~ r1_tarski(A_429,B_427) ) ),
    inference(resolution,[status(thm)],[c_46,c_3385])).

tff(c_16633,plain,(
    ! [A_435] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_435) = k2_xboole_0('#skF_2',A_435)
      | ~ r1_tarski(A_435,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_60,c_16057])).

tff(c_25068,plain,(
    ! [A_513] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_513) = k2_xboole_0('#skF_2',A_513)
      | ~ r1_tarski(A_513,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_649,c_16633])).

tff(c_4023,plain,(
    ! [A_260,B_261] :
      ( k4_subset_1(u1_struct_0(A_260),B_261,k2_tops_1(A_260,B_261)) = k2_pre_topc(A_260,B_261)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ l1_pre_topc(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4036,plain,(
    ! [A_260,A_45] :
      ( k4_subset_1(u1_struct_0(A_260),A_45,k2_tops_1(A_260,A_45)) = k2_pre_topc(A_260,A_45)
      | ~ l1_pre_topc(A_260)
      | ~ r1_tarski(A_45,u1_struct_0(A_260)) ) ),
    inference(resolution,[status(thm)],[c_46,c_4023])).

tff(c_25075,plain,
    ( k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1'))
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_25068,c_4036])).

tff(c_25123,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2694,c_168,c_62,c_25075])).

tff(c_22,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25247,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25123,c_22])).

tff(c_650,plain,(
    ! [A_110,A_22,B_23] :
      ( r1_tarski(A_110,k2_xboole_0(A_22,B_23))
      | ~ r1_tarski(A_110,A_22) ) ),
    inference(resolution,[status(thm)],[c_22,c_631])).

tff(c_2049,plain,(
    ! [A_188,B_189,C_190] :
      ( r1_tarski(k4_xboole_0(A_188,B_189),C_190)
      | ~ r1_tarski(A_188,k2_xboole_0(B_189,C_190)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9936,plain,(
    ! [A_365,B_366,B_367] :
      ( k4_xboole_0(A_365,B_366) = k1_xboole_0
      | ~ r1_tarski(A_365,k2_xboole_0(B_366,k4_xboole_0(B_367,k4_xboole_0(A_365,B_366)))) ) ),
    inference(resolution,[status(thm)],[c_2049,c_10])).

tff(c_10084,plain,(
    ! [A_110,A_22] :
      ( k4_xboole_0(A_110,A_22) = k1_xboole_0
      | ~ r1_tarski(A_110,A_22) ) ),
    inference(resolution,[status(thm)],[c_650,c_9936])).

tff(c_25270,plain,(
    k4_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25247,c_10084])).

tff(c_20,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5096,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_subset_1(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_8,c_4862])).

tff(c_5181,plain,(
    ! [A_7,B_8] : k3_subset_1(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5096])).

tff(c_25318,plain,(
    k3_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_25270,c_5181])).

tff(c_25375,plain,(
    k3_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5173,c_25318])).

tff(c_24,plain,(
    ! [B_25,A_24] : k2_tarski(B_25,A_24) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_169,plain,(
    ! [A_82,B_83] : k1_setfam_1(k2_tarski(A_82,B_83)) = k3_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_257,plain,(
    ! [A_90,B_91] : k1_setfam_1(k2_tarski(A_90,B_91)) = k3_xboole_0(B_91,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_169])).

tff(c_42,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_263,plain,(
    ! [B_91,A_90] : k3_xboole_0(B_91,A_90) = k3_xboole_0(A_90,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_42])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_513,plain,(
    ! [A_104] : k2_xboole_0(A_104,k1_xboole_0) = k2_xboole_0(A_104,A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_12])).

tff(c_504,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_497])).

tff(c_510,plain,(
    ! [A_104] : k4_xboole_0(A_104,k1_xboole_0) = k3_xboole_0(A_104,A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_20])).

tff(c_556,plain,(
    ! [A_106] : k3_xboole_0(A_106,A_106) = A_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_510])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_566,plain,(
    ! [A_106] : k5_xboole_0(A_106,A_106) = k4_xboole_0(A_106,A_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_2])).

tff(c_584,plain,(
    ! [A_106] : k5_xboole_0(A_106,A_106) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_566])).

tff(c_2175,plain,(
    ! [C_196] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_196) = k4_xboole_0('#skF_2',C_196) ),
    inference(resolution,[status(thm)],[c_60,c_2166])).

tff(c_4117,plain,(
    ! [A_264,B_265] :
      ( k7_subset_1(u1_struct_0(A_264),B_265,k2_tops_1(A_264,B_265)) = k1_tops_1(A_264,B_265)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_pre_topc(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4127,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_4117])).

tff(c_4133,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2175,c_4127])).

tff(c_4220,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4133,c_20])).

tff(c_4232,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2185,c_4220])).

tff(c_302,plain,(
    ! [B_95,A_96] : k3_xboole_0(B_95,A_96) = k3_xboole_0(A_96,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_42])).

tff(c_7043,plain,(
    ! [B_326,A_327] : k5_xboole_0(B_326,k3_xboole_0(A_327,B_326)) = k4_xboole_0(B_326,A_327) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_2])).

tff(c_7056,plain,(
    k5_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4232,c_7043])).

tff(c_7082,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_7056])).

tff(c_7131,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7082,c_12])).

tff(c_7154,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_7131])).

tff(c_29547,plain,(
    k2_xboole_0('#skF_2','#skF_2') = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25123,c_7154])).

tff(c_145,plain,(
    ! [A_78,B_79] : k3_tarski(k2_tarski(A_78,B_79)) = k2_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_184,plain,(
    ! [A_84,B_85] : k3_tarski(k2_tarski(A_84,B_85)) = k2_xboole_0(B_85,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_145])).

tff(c_26,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_190,plain,(
    ! [B_85,A_84] : k2_xboole_0(B_85,A_84) = k2_xboole_0(A_84,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_26])).

tff(c_684,plain,(
    ! [A_115] : k2_xboole_0(A_115,k1_xboole_0) = k2_xboole_0(A_115,A_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_12])).

tff(c_718,plain,(
    ! [A_84] : k2_xboole_0(k1_xboole_0,A_84) = k2_xboole_0(A_84,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_684])).

tff(c_2398,plain,(
    ! [A_210,C_211] :
      ( r1_tarski(A_210,C_211)
      | ~ r1_tarski(A_210,k2_xboole_0(k1_xboole_0,C_211)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2049])).

tff(c_2824,plain,(
    ! [C_217,B_218] : r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0,C_217),B_218),C_217) ),
    inference(resolution,[status(thm)],[c_8,c_2398])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(A_17,k2_xboole_0(B_18,C_19))
      | ~ r1_tarski(k4_xboole_0(A_17,B_18),C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3056,plain,(
    ! [C_224,B_225] : r1_tarski(k2_xboole_0(k1_xboole_0,C_224),k2_xboole_0(B_225,C_224)) ),
    inference(resolution,[status(thm)],[c_2824,c_18])).

tff(c_3900,plain,(
    ! [A_256,B_257] : r1_tarski(k2_xboole_0(A_256,A_256),k2_xboole_0(B_257,A_256)) ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_3056])).

tff(c_3938,plain,(
    ! [B_85,A_84] : r1_tarski(k2_xboole_0(B_85,B_85),k2_xboole_0(B_85,A_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_3900])).

tff(c_10081,plain,(
    ! [B_85] : k4_xboole_0(k2_xboole_0(B_85,B_85),B_85) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3938,c_9936])).

tff(c_29615,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_29547,c_10081])).

tff(c_29873,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_29615,c_20])).

tff(c_29907,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25375,c_263,c_14,c_29873])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2798,plain,(
    ! [A_215,B_216] :
      ( v4_pre_topc(k2_pre_topc(A_215,B_216),A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2808,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_2798])).

tff(c_2814,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2808])).

tff(c_29929,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29907,c_2814])).

tff(c_29944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_29929])).

tff(c_29945,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_30190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_29945])).

tff(c_30191,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_30295,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30191,c_66])).

tff(c_32425,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32421,c_30295])).

tff(c_33320,plain,(
    ! [A_755,B_756] :
      ( r1_tarski(k2_tops_1(A_755,B_756),B_756)
      | ~ v4_pre_topc(B_756,A_755)
      | ~ m1_subset_1(B_756,k1_zfmisc_1(u1_struct_0(A_755)))
      | ~ l1_pre_topc(A_755) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_33330,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_33320])).

tff(c_33336,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_30191,c_33330])).

tff(c_33967,plain,(
    ! [A_777,B_778] :
      ( k7_subset_1(u1_struct_0(A_777),B_778,k2_tops_1(A_777,B_778)) = k1_tops_1(A_777,B_778)
      | ~ m1_subset_1(B_778,k1_zfmisc_1(u1_struct_0(A_777)))
      | ~ l1_pre_topc(A_777) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_33977,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_33967])).

tff(c_33983,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_32421,c_33977])).

tff(c_31756,plain,(
    ! [A_684,B_685] :
      ( k4_xboole_0(A_684,B_685) = k3_subset_1(A_684,B_685)
      | ~ m1_subset_1(B_685,k1_zfmisc_1(A_684)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34906,plain,(
    ! [B_811,A_812] :
      ( k4_xboole_0(B_811,A_812) = k3_subset_1(B_811,A_812)
      | ~ r1_tarski(A_812,B_811) ) ),
    inference(resolution,[status(thm)],[c_46,c_31756])).

tff(c_35005,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_33336,c_34906])).

tff(c_35162,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33983,c_35005])).

tff(c_31506,plain,(
    ! [A_670,B_671] :
      ( k3_subset_1(A_670,k3_subset_1(A_670,B_671)) = B_671
      | ~ m1_subset_1(B_671,k1_zfmisc_1(A_670)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_31511,plain,(
    ! [B_46,A_45] :
      ( k3_subset_1(B_46,k3_subset_1(B_46,A_45)) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_46,c_31506])).

tff(c_37708,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_35162,c_31511])).

tff(c_37718,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33336,c_37708])).

tff(c_35128,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_subset_1(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_8,c_34906])).

tff(c_36793,plain,(
    ! [A_840,B_841] : k3_subset_1(A_840,k4_xboole_0(A_840,B_841)) = k3_xboole_0(A_840,B_841) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_35128])).

tff(c_36805,plain,(
    ! [A_840,B_841] :
      ( k3_subset_1(A_840,k3_xboole_0(A_840,B_841)) = k4_xboole_0(A_840,B_841)
      | ~ r1_tarski(k4_xboole_0(A_840,B_841),A_840) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36793,c_31511])).

tff(c_36838,plain,(
    ! [A_840,B_841] : k3_subset_1(A_840,k3_xboole_0(A_840,B_841)) = k4_xboole_0(A_840,B_841) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36805])).

tff(c_30473,plain,(
    ! [A_613,B_614] : k4_xboole_0(A_613,k4_xboole_0(A_613,B_614)) = k3_xboole_0(A_613,B_614) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30488,plain,(
    ! [A_613,B_614] : r1_tarski(k3_xboole_0(A_613,B_614),A_613) ),
    inference(superposition,[status(thm),theory(equality)],[c_30473,c_8])).

tff(c_35198,plain,(
    ! [A_613,B_614] : k4_xboole_0(A_613,k3_xboole_0(A_613,B_614)) = k3_subset_1(A_613,k3_xboole_0(A_613,B_614)) ),
    inference(resolution,[status(thm)],[c_30488,c_34906])).

tff(c_66935,plain,(
    ! [A_613,B_614] : k4_xboole_0(A_613,k3_xboole_0(A_613,B_614)) = k4_xboole_0(A_613,B_614) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36838,c_35198])).

tff(c_30476,plain,(
    ! [A_613,B_614] : k4_xboole_0(A_613,k3_xboole_0(A_613,B_614)) = k3_xboole_0(A_613,k4_xboole_0(A_613,B_614)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30473,c_20])).

tff(c_67202,plain,(
    ! [A_1149,B_1150] : k3_xboole_0(A_1149,k4_xboole_0(A_1149,B_1150)) = k4_xboole_0(A_1149,B_1150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66935,c_30476])).

tff(c_67564,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33983,c_67202])).

tff(c_67690,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33983,c_67564])).

tff(c_68316,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_67690,c_36838])).

tff(c_68392,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37718,c_68316])).

tff(c_68394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32425,c_68392])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.15/13.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.15/13.15  
% 23.15/13.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.15/13.16  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 23.15/13.16  
% 23.15/13.16  %Foreground sorts:
% 23.15/13.16  
% 23.15/13.16  
% 23.15/13.16  %Background operators:
% 23.15/13.16  
% 23.15/13.16  
% 23.15/13.16  %Foreground operators:
% 23.15/13.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.15/13.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.15/13.16  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 23.15/13.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.15/13.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 23.15/13.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 23.15/13.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.15/13.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.15/13.16  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 23.15/13.16  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 23.15/13.16  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 23.15/13.16  tff('#skF_2', type, '#skF_2': $i).
% 23.15/13.16  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 23.15/13.16  tff('#skF_1', type, '#skF_1': $i).
% 23.15/13.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.15/13.16  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 23.15/13.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.15/13.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 23.15/13.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.15/13.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 23.15/13.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.15/13.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.15/13.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 23.15/13.16  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 23.15/13.16  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 23.15/13.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.15/13.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 23.15/13.16  
% 23.15/13.18  tff(f_151, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 23.15/13.18  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 23.15/13.18  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 23.15/13.18  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 23.15/13.18  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 23.15/13.18  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 23.15/13.18  tff(f_95, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 23.15/13.18  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 23.15/13.18  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 23.15/13.18  tff(f_81, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 23.15/13.18  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 23.15/13.18  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 23.15/13.18  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 23.15/13.18  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 23.15/13.18  tff(f_59, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 23.15/13.18  tff(f_91, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 23.15/13.18  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 23.15/13.18  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 23.15/13.18  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 23.15/13.18  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 23.15/13.18  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 23.15/13.18  tff(f_109, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 23.15/13.18  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 23.15/13.18  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 23.15/13.18  tff(c_60, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.15/13.18  tff(c_32412, plain, (![A_719, B_720, C_721]: (k7_subset_1(A_719, B_720, C_721)=k4_xboole_0(B_720, C_721) | ~m1_subset_1(B_720, k1_zfmisc_1(A_719)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 23.15/13.18  tff(c_32421, plain, (![C_721]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_721)=k4_xboole_0('#skF_2', C_721))), inference(resolution, [status(thm)], [c_60, c_32412])).
% 23.15/13.18  tff(c_72, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.15/13.18  tff(c_105, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_72])).
% 23.15/13.18  tff(c_66, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.15/13.18  tff(c_246, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_66])).
% 23.15/13.18  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.15/13.18  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.15/13.18  tff(c_462, plain, (![A_102, B_103]: (k4_xboole_0(A_102, k4_xboole_0(A_102, B_103))=k3_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.15/13.18  tff(c_497, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_462])).
% 23.15/13.18  tff(c_505, plain, (![A_104]: (k4_xboole_0(A_104, A_104)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_497])).
% 23.15/13.18  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 23.15/13.18  tff(c_522, plain, (![A_104]: (r1_tarski(k1_xboole_0, A_104))), inference(superposition, [status(thm), theory('equality')], [c_505, c_8])).
% 23.15/13.18  tff(c_46, plain, (![A_45, B_46]: (m1_subset_1(A_45, k1_zfmisc_1(B_46)) | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_95])).
% 23.15/13.18  tff(c_1764, plain, (![A_174, B_175]: (k4_xboole_0(A_174, B_175)=k3_subset_1(A_174, B_175) | ~m1_subset_1(B_175, k1_zfmisc_1(A_174)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.15/13.18  tff(c_4862, plain, (![B_292, A_293]: (k4_xboole_0(B_292, A_293)=k3_subset_1(B_292, A_293) | ~r1_tarski(A_293, B_292))), inference(resolution, [status(thm)], [c_46, c_1764])).
% 23.15/13.18  tff(c_5081, plain, (![A_104]: (k4_xboole_0(A_104, k1_xboole_0)=k3_subset_1(A_104, k1_xboole_0))), inference(resolution, [status(thm)], [c_522, c_4862])).
% 23.15/13.18  tff(c_5173, plain, (![A_104]: (k3_subset_1(A_104, k1_xboole_0)=A_104)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5081])).
% 23.15/13.18  tff(c_2166, plain, (![A_194, B_195, C_196]: (k7_subset_1(A_194, B_195, C_196)=k4_xboole_0(B_195, C_196) | ~m1_subset_1(B_195, k1_zfmisc_1(A_194)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 23.15/13.18  tff(c_2179, plain, (![C_197]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_197)=k4_xboole_0('#skF_2', C_197))), inference(resolution, [status(thm)], [c_60, c_2166])).
% 23.15/13.18  tff(c_2185, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2179, c_105])).
% 23.15/13.18  tff(c_2694, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2185, c_8])).
% 23.15/13.18  tff(c_160, plain, (![A_80, B_81]: (r1_tarski(A_80, B_81) | ~m1_subset_1(A_80, k1_zfmisc_1(B_81)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 23.15/13.18  tff(c_168, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_160])).
% 23.15/13.18  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.15/13.18  tff(c_631, plain, (![A_110, C_111, B_112]: (r1_tarski(A_110, C_111) | ~r1_tarski(B_112, C_111) | ~r1_tarski(A_110, B_112))), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.15/13.18  tff(c_649, plain, (![A_110]: (r1_tarski(A_110, u1_struct_0('#skF_1')) | ~r1_tarski(A_110, '#skF_2'))), inference(resolution, [status(thm)], [c_168, c_631])).
% 23.15/13.18  tff(c_3385, plain, (![A_236, B_237, C_238]: (k4_subset_1(A_236, B_237, C_238)=k2_xboole_0(B_237, C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(A_236)) | ~m1_subset_1(B_237, k1_zfmisc_1(A_236)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 23.15/13.18  tff(c_16057, plain, (![B_427, B_428, A_429]: (k4_subset_1(B_427, B_428, A_429)=k2_xboole_0(B_428, A_429) | ~m1_subset_1(B_428, k1_zfmisc_1(B_427)) | ~r1_tarski(A_429, B_427))), inference(resolution, [status(thm)], [c_46, c_3385])).
% 23.15/13.18  tff(c_16633, plain, (![A_435]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_435)=k2_xboole_0('#skF_2', A_435) | ~r1_tarski(A_435, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_60, c_16057])).
% 23.15/13.18  tff(c_25068, plain, (![A_513]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_513)=k2_xboole_0('#skF_2', A_513) | ~r1_tarski(A_513, '#skF_2'))), inference(resolution, [status(thm)], [c_649, c_16633])).
% 23.15/13.18  tff(c_4023, plain, (![A_260, B_261]: (k4_subset_1(u1_struct_0(A_260), B_261, k2_tops_1(A_260, B_261))=k2_pre_topc(A_260, B_261) | ~m1_subset_1(B_261, k1_zfmisc_1(u1_struct_0(A_260))) | ~l1_pre_topc(A_260))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.15/13.18  tff(c_4036, plain, (![A_260, A_45]: (k4_subset_1(u1_struct_0(A_260), A_45, k2_tops_1(A_260, A_45))=k2_pre_topc(A_260, A_45) | ~l1_pre_topc(A_260) | ~r1_tarski(A_45, u1_struct_0(A_260)))), inference(resolution, [status(thm)], [c_46, c_4023])).
% 23.15/13.18  tff(c_25075, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', u1_struct_0('#skF_1')) | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_25068, c_4036])).
% 23.15/13.18  tff(c_25123, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2694, c_168, c_62, c_25075])).
% 23.15/13.18  tff(c_22, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 23.15/13.18  tff(c_25247, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_25123, c_22])).
% 23.15/13.18  tff(c_650, plain, (![A_110, A_22, B_23]: (r1_tarski(A_110, k2_xboole_0(A_22, B_23)) | ~r1_tarski(A_110, A_22))), inference(resolution, [status(thm)], [c_22, c_631])).
% 23.15/13.18  tff(c_2049, plain, (![A_188, B_189, C_190]: (r1_tarski(k4_xboole_0(A_188, B_189), C_190) | ~r1_tarski(A_188, k2_xboole_0(B_189, C_190)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 23.15/13.18  tff(c_10, plain, (![A_9, B_10]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k4_xboole_0(B_10, A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.15/13.18  tff(c_9936, plain, (![A_365, B_366, B_367]: (k4_xboole_0(A_365, B_366)=k1_xboole_0 | ~r1_tarski(A_365, k2_xboole_0(B_366, k4_xboole_0(B_367, k4_xboole_0(A_365, B_366)))))), inference(resolution, [status(thm)], [c_2049, c_10])).
% 23.15/13.18  tff(c_10084, plain, (![A_110, A_22]: (k4_xboole_0(A_110, A_22)=k1_xboole_0 | ~r1_tarski(A_110, A_22))), inference(resolution, [status(thm)], [c_650, c_9936])).
% 23.15/13.18  tff(c_25270, plain, (k4_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_25247, c_10084])).
% 23.15/13.18  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.15/13.18  tff(c_5096, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_subset_1(A_7, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_8, c_4862])).
% 23.15/13.18  tff(c_5181, plain, (![A_7, B_8]: (k3_subset_1(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5096])).
% 23.15/13.18  tff(c_25318, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_25270, c_5181])).
% 23.15/13.18  tff(c_25375, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5173, c_25318])).
% 23.15/13.18  tff(c_24, plain, (![B_25, A_24]: (k2_tarski(B_25, A_24)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 23.15/13.18  tff(c_169, plain, (![A_82, B_83]: (k1_setfam_1(k2_tarski(A_82, B_83))=k3_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_91])).
% 23.15/13.18  tff(c_257, plain, (![A_90, B_91]: (k1_setfam_1(k2_tarski(A_90, B_91))=k3_xboole_0(B_91, A_90))), inference(superposition, [status(thm), theory('equality')], [c_24, c_169])).
% 23.15/13.18  tff(c_42, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_91])).
% 23.15/13.18  tff(c_263, plain, (![B_91, A_90]: (k3_xboole_0(B_91, A_90)=k3_xboole_0(A_90, B_91))), inference(superposition, [status(thm), theory('equality')], [c_257, c_42])).
% 23.15/13.18  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.15/13.18  tff(c_513, plain, (![A_104]: (k2_xboole_0(A_104, k1_xboole_0)=k2_xboole_0(A_104, A_104))), inference(superposition, [status(thm), theory('equality')], [c_505, c_12])).
% 23.15/13.18  tff(c_504, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_497])).
% 23.15/13.18  tff(c_510, plain, (![A_104]: (k4_xboole_0(A_104, k1_xboole_0)=k3_xboole_0(A_104, A_104))), inference(superposition, [status(thm), theory('equality')], [c_505, c_20])).
% 23.15/13.18  tff(c_556, plain, (![A_106]: (k3_xboole_0(A_106, A_106)=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_510])).
% 23.15/13.18  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.15/13.18  tff(c_566, plain, (![A_106]: (k5_xboole_0(A_106, A_106)=k4_xboole_0(A_106, A_106))), inference(superposition, [status(thm), theory('equality')], [c_556, c_2])).
% 23.15/13.18  tff(c_584, plain, (![A_106]: (k5_xboole_0(A_106, A_106)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_504, c_566])).
% 23.15/13.18  tff(c_2175, plain, (![C_196]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_196)=k4_xboole_0('#skF_2', C_196))), inference(resolution, [status(thm)], [c_60, c_2166])).
% 23.15/13.18  tff(c_4117, plain, (![A_264, B_265]: (k7_subset_1(u1_struct_0(A_264), B_265, k2_tops_1(A_264, B_265))=k1_tops_1(A_264, B_265) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_pre_topc(A_264))), inference(cnfTransformation, [status(thm)], [f_139])).
% 23.15/13.18  tff(c_4127, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_4117])).
% 23.15/13.18  tff(c_4133, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2175, c_4127])).
% 23.15/13.18  tff(c_4220, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4133, c_20])).
% 23.15/13.18  tff(c_4232, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2185, c_4220])).
% 23.15/13.18  tff(c_302, plain, (![B_95, A_96]: (k3_xboole_0(B_95, A_96)=k3_xboole_0(A_96, B_95))), inference(superposition, [status(thm), theory('equality')], [c_257, c_42])).
% 23.15/13.18  tff(c_7043, plain, (![B_326, A_327]: (k5_xboole_0(B_326, k3_xboole_0(A_327, B_326))=k4_xboole_0(B_326, A_327))), inference(superposition, [status(thm), theory('equality')], [c_302, c_2])).
% 23.15/13.18  tff(c_7056, plain, (k5_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4232, c_7043])).
% 23.15/13.18  tff(c_7082, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_584, c_7056])).
% 23.15/13.18  tff(c_7131, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7082, c_12])).
% 23.15/13.18  tff(c_7154, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_513, c_7131])).
% 23.15/13.18  tff(c_29547, plain, (k2_xboole_0('#skF_2', '#skF_2')=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25123, c_7154])).
% 23.15/13.18  tff(c_145, plain, (![A_78, B_79]: (k3_tarski(k2_tarski(A_78, B_79))=k2_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_61])).
% 23.15/13.18  tff(c_184, plain, (![A_84, B_85]: (k3_tarski(k2_tarski(A_84, B_85))=k2_xboole_0(B_85, A_84))), inference(superposition, [status(thm), theory('equality')], [c_24, c_145])).
% 23.15/13.18  tff(c_26, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 23.15/13.18  tff(c_190, plain, (![B_85, A_84]: (k2_xboole_0(B_85, A_84)=k2_xboole_0(A_84, B_85))), inference(superposition, [status(thm), theory('equality')], [c_184, c_26])).
% 23.15/13.18  tff(c_684, plain, (![A_115]: (k2_xboole_0(A_115, k1_xboole_0)=k2_xboole_0(A_115, A_115))), inference(superposition, [status(thm), theory('equality')], [c_505, c_12])).
% 23.15/13.18  tff(c_718, plain, (![A_84]: (k2_xboole_0(k1_xboole_0, A_84)=k2_xboole_0(A_84, A_84))), inference(superposition, [status(thm), theory('equality')], [c_190, c_684])).
% 23.15/13.18  tff(c_2398, plain, (![A_210, C_211]: (r1_tarski(A_210, C_211) | ~r1_tarski(A_210, k2_xboole_0(k1_xboole_0, C_211)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2049])).
% 23.15/13.18  tff(c_2824, plain, (![C_217, B_218]: (r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0, C_217), B_218), C_217))), inference(resolution, [status(thm)], [c_8, c_2398])).
% 23.15/13.18  tff(c_18, plain, (![A_17, B_18, C_19]: (r1_tarski(A_17, k2_xboole_0(B_18, C_19)) | ~r1_tarski(k4_xboole_0(A_17, B_18), C_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.15/13.18  tff(c_3056, plain, (![C_224, B_225]: (r1_tarski(k2_xboole_0(k1_xboole_0, C_224), k2_xboole_0(B_225, C_224)))), inference(resolution, [status(thm)], [c_2824, c_18])).
% 23.15/13.18  tff(c_3900, plain, (![A_256, B_257]: (r1_tarski(k2_xboole_0(A_256, A_256), k2_xboole_0(B_257, A_256)))), inference(superposition, [status(thm), theory('equality')], [c_718, c_3056])).
% 23.15/13.18  tff(c_3938, plain, (![B_85, A_84]: (r1_tarski(k2_xboole_0(B_85, B_85), k2_xboole_0(B_85, A_84)))), inference(superposition, [status(thm), theory('equality')], [c_190, c_3900])).
% 23.15/13.18  tff(c_10081, plain, (![B_85]: (k4_xboole_0(k2_xboole_0(B_85, B_85), B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3938, c_9936])).
% 23.15/13.18  tff(c_29615, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_29547, c_10081])).
% 23.15/13.18  tff(c_29873, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_29615, c_20])).
% 23.15/13.18  tff(c_29907, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_25375, c_263, c_14, c_29873])).
% 23.15/13.18  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 23.15/13.18  tff(c_2798, plain, (![A_215, B_216]: (v4_pre_topc(k2_pre_topc(A_215, B_216), A_215) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.15/13.18  tff(c_2808, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_2798])).
% 23.15/13.18  tff(c_2814, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2808])).
% 23.15/13.18  tff(c_29929, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29907, c_2814])).
% 23.15/13.18  tff(c_29944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246, c_29929])).
% 23.15/13.18  tff(c_29945, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_66])).
% 23.15/13.18  tff(c_30190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_29945])).
% 23.15/13.18  tff(c_30191, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 23.15/13.18  tff(c_30295, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30191, c_66])).
% 23.15/13.18  tff(c_32425, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32421, c_30295])).
% 23.15/13.18  tff(c_33320, plain, (![A_755, B_756]: (r1_tarski(k2_tops_1(A_755, B_756), B_756) | ~v4_pre_topc(B_756, A_755) | ~m1_subset_1(B_756, k1_zfmisc_1(u1_struct_0(A_755))) | ~l1_pre_topc(A_755))), inference(cnfTransformation, [status(thm)], [f_132])).
% 23.15/13.18  tff(c_33330, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_33320])).
% 23.15/13.18  tff(c_33336, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_30191, c_33330])).
% 23.15/13.18  tff(c_33967, plain, (![A_777, B_778]: (k7_subset_1(u1_struct_0(A_777), B_778, k2_tops_1(A_777, B_778))=k1_tops_1(A_777, B_778) | ~m1_subset_1(B_778, k1_zfmisc_1(u1_struct_0(A_777))) | ~l1_pre_topc(A_777))), inference(cnfTransformation, [status(thm)], [f_139])).
% 23.15/13.18  tff(c_33977, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_33967])).
% 23.15/13.18  tff(c_33983, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_32421, c_33977])).
% 23.15/13.18  tff(c_31756, plain, (![A_684, B_685]: (k4_xboole_0(A_684, B_685)=k3_subset_1(A_684, B_685) | ~m1_subset_1(B_685, k1_zfmisc_1(A_684)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.15/13.18  tff(c_34906, plain, (![B_811, A_812]: (k4_xboole_0(B_811, A_812)=k3_subset_1(B_811, A_812) | ~r1_tarski(A_812, B_811))), inference(resolution, [status(thm)], [c_46, c_31756])).
% 23.15/13.18  tff(c_35005, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_33336, c_34906])).
% 23.15/13.18  tff(c_35162, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33983, c_35005])).
% 23.15/13.18  tff(c_31506, plain, (![A_670, B_671]: (k3_subset_1(A_670, k3_subset_1(A_670, B_671))=B_671 | ~m1_subset_1(B_671, k1_zfmisc_1(A_670)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 23.15/13.18  tff(c_31511, plain, (![B_46, A_45]: (k3_subset_1(B_46, k3_subset_1(B_46, A_45))=A_45 | ~r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_46, c_31506])).
% 23.15/13.18  tff(c_37708, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_35162, c_31511])).
% 23.15/13.18  tff(c_37718, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33336, c_37708])).
% 23.15/13.18  tff(c_35128, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_subset_1(A_7, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_8, c_34906])).
% 23.15/13.18  tff(c_36793, plain, (![A_840, B_841]: (k3_subset_1(A_840, k4_xboole_0(A_840, B_841))=k3_xboole_0(A_840, B_841))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_35128])).
% 23.15/13.18  tff(c_36805, plain, (![A_840, B_841]: (k3_subset_1(A_840, k3_xboole_0(A_840, B_841))=k4_xboole_0(A_840, B_841) | ~r1_tarski(k4_xboole_0(A_840, B_841), A_840))), inference(superposition, [status(thm), theory('equality')], [c_36793, c_31511])).
% 23.15/13.18  tff(c_36838, plain, (![A_840, B_841]: (k3_subset_1(A_840, k3_xboole_0(A_840, B_841))=k4_xboole_0(A_840, B_841))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36805])).
% 23.15/13.18  tff(c_30473, plain, (![A_613, B_614]: (k4_xboole_0(A_613, k4_xboole_0(A_613, B_614))=k3_xboole_0(A_613, B_614))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.15/13.18  tff(c_30488, plain, (![A_613, B_614]: (r1_tarski(k3_xboole_0(A_613, B_614), A_613))), inference(superposition, [status(thm), theory('equality')], [c_30473, c_8])).
% 23.15/13.18  tff(c_35198, plain, (![A_613, B_614]: (k4_xboole_0(A_613, k3_xboole_0(A_613, B_614))=k3_subset_1(A_613, k3_xboole_0(A_613, B_614)))), inference(resolution, [status(thm)], [c_30488, c_34906])).
% 23.15/13.18  tff(c_66935, plain, (![A_613, B_614]: (k4_xboole_0(A_613, k3_xboole_0(A_613, B_614))=k4_xboole_0(A_613, B_614))), inference(demodulation, [status(thm), theory('equality')], [c_36838, c_35198])).
% 23.15/13.18  tff(c_30476, plain, (![A_613, B_614]: (k4_xboole_0(A_613, k3_xboole_0(A_613, B_614))=k3_xboole_0(A_613, k4_xboole_0(A_613, B_614)))), inference(superposition, [status(thm), theory('equality')], [c_30473, c_20])).
% 23.15/13.18  tff(c_67202, plain, (![A_1149, B_1150]: (k3_xboole_0(A_1149, k4_xboole_0(A_1149, B_1150))=k4_xboole_0(A_1149, B_1150))), inference(demodulation, [status(thm), theory('equality')], [c_66935, c_30476])).
% 23.15/13.18  tff(c_67564, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_33983, c_67202])).
% 23.15/13.18  tff(c_67690, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33983, c_67564])).
% 23.15/13.18  tff(c_68316, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_67690, c_36838])).
% 23.15/13.18  tff(c_68392, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37718, c_68316])).
% 23.15/13.18  tff(c_68394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32425, c_68392])).
% 23.15/13.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.15/13.18  
% 23.15/13.18  Inference rules
% 23.15/13.18  ----------------------
% 23.15/13.18  #Ref     : 0
% 23.15/13.18  #Sup     : 16382
% 23.15/13.18  #Fact    : 0
% 23.15/13.18  #Define  : 0
% 23.15/13.18  #Split   : 6
% 23.15/13.18  #Chain   : 0
% 23.15/13.18  #Close   : 0
% 23.15/13.18  
% 23.15/13.18  Ordering : KBO
% 23.15/13.18  
% 23.15/13.18  Simplification rules
% 23.15/13.18  ----------------------
% 23.15/13.18  #Subsume      : 994
% 23.15/13.18  #Demod        : 14771
% 23.15/13.18  #Tautology    : 10453
% 23.15/13.18  #SimpNegUnit  : 2
% 23.15/13.18  #BackRed      : 118
% 23.15/13.18  
% 23.15/13.18  #Partial instantiations: 0
% 23.15/13.18  #Strategies tried      : 1
% 23.15/13.18  
% 23.15/13.18  Timing (in seconds)
% 23.15/13.18  ----------------------
% 23.15/13.19  Preprocessing        : 0.57
% 23.15/13.19  Parsing              : 0.30
% 23.15/13.19  CNF conversion       : 0.04
% 23.15/13.19  Main loop            : 11.69
% 23.15/13.19  Inferencing          : 1.82
% 23.15/13.19  Reduction            : 6.55
% 23.15/13.19  Demodulation         : 5.69
% 23.15/13.19  BG Simplification    : 0.21
% 23.15/13.19  Subsumption          : 2.48
% 23.15/13.19  Abstraction          : 0.28
% 23.15/13.19  MUC search           : 0.00
% 23.15/13.19  Cooper               : 0.00
% 23.15/13.19  Total                : 12.32
% 23.15/13.19  Index Insertion      : 0.00
% 23.15/13.19  Index Deletion       : 0.00
% 23.15/13.19  Index Matching       : 0.00
% 23.15/13.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
