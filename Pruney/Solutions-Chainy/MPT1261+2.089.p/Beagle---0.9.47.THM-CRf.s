%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:24 EST 2020

% Result     : Theorem 6.88s
% Output     : CNFRefutation 6.92s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 184 expanded)
%              Number of leaves         :   35 (  76 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 ( 379 expanded)
%              Number of equality atoms :   52 ( 103 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6089,plain,(
    ! [A_227,B_228,C_229] :
      ( k7_subset_1(A_227,B_228,C_229) = k4_xboole_0(B_228,C_229)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(A_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6095,plain,(
    ! [C_229] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_229) = k4_xboole_0('#skF_2',C_229) ),
    inference(resolution,[status(thm)],[c_38,c_6089])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_130,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_215,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_121,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_129,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_121])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1453,plain,(
    ! [A_114,B_115] :
      ( k4_subset_1(u1_struct_0(A_114),B_115,k2_tops_1(A_114,B_115)) = k2_pre_topc(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1458,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1453])).

tff(c_1462,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1458])).

tff(c_482,plain,(
    ! [A_78,B_79,C_80] :
      ( k7_subset_1(A_78,B_79,C_80) = k4_xboole_0(B_79,C_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_492,plain,(
    ! [C_81] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_81) = k4_xboole_0('#skF_2',C_81) ),
    inference(resolution,[status(thm)],[c_38,c_482])).

tff(c_504,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_492])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,(
    ! [A_49,B_50] :
      ( k2_xboole_0(A_49,B_50) = B_50
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_153,plain,(
    ! [A_52,B_53] : k2_xboole_0(k4_xboole_0(A_52,B_53),A_52) = A_52 ),
    inference(resolution,[status(thm)],[c_18,c_131])).

tff(c_169,plain,(
    ! [B_2,B_53] : k2_xboole_0(B_2,k4_xboole_0(B_2,B_53)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_153])).

tff(c_752,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_169])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(k4_xboole_0(A_7,C_9),B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_749,plain,(
    ! [B_8] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),B_8)
      | ~ r1_tarski('#skF_2',B_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_12])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_833,plain,(
    ! [A_96,B_97,C_98] :
      ( k4_subset_1(A_96,B_97,C_98) = k2_xboole_0(B_97,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_96))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5322,plain,(
    ! [B_187,B_188,A_189] :
      ( k4_subset_1(B_187,B_188,A_189) = k2_xboole_0(B_188,A_189)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(B_187))
      | ~ r1_tarski(A_189,B_187) ) ),
    inference(resolution,[status(thm)],[c_28,c_833])).

tff(c_5681,plain,(
    ! [A_192] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_192) = k2_xboole_0('#skF_2',A_192)
      | ~ r1_tarski(A_192,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_38,c_5322])).

tff(c_5685,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_749,c_5681])).

tff(c_5719,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_1462,c_752,c_5685])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_682,plain,(
    ! [A_89,B_90] :
      ( v4_pre_topc(k2_pre_topc(A_89,B_90),A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_687,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_682])).

tff(c_691,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_687])).

tff(c_5731,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5719,c_691])).

tff(c_5733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_5731])).

tff(c_5734,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_5734])).

tff(c_5890,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_5906,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5890,c_44])).

tff(c_6219,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6095,c_5906])).

tff(c_6558,plain,(
    ! [A_254,B_255] :
      ( k4_subset_1(u1_struct_0(A_254),B_255,k2_tops_1(A_254,B_255)) = k2_pre_topc(A_254,B_255)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ l1_pre_topc(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6563,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_6558])).

tff(c_6567,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6563])).

tff(c_6267,plain,(
    ! [A_241,B_242] :
      ( r1_tarski(k2_tops_1(A_241,B_242),B_242)
      | ~ v4_pre_topc(B_242,A_241)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6272,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_6267])).

tff(c_6276,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5890,c_6272])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6286,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6276,c_14])).

tff(c_6291,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_6286,c_2])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6287,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6276,c_16])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6007,plain,(
    ! [A_221,B_222] : k4_xboole_0(A_221,k4_xboole_0(A_221,B_222)) = k3_xboole_0(A_221,B_222) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6357,plain,(
    ! [A_247,B_248,B_249] :
      ( r1_tarski(k3_xboole_0(A_247,B_248),B_249)
      | ~ r1_tarski(A_247,B_249) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6007,c_12])).

tff(c_6568,plain,(
    ! [B_256,A_257,B_258] :
      ( r1_tarski(k3_xboole_0(B_256,A_257),B_258)
      | ~ r1_tarski(A_257,B_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_6357])).

tff(c_6579,plain,(
    ! [B_258] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),B_258)
      | ~ r1_tarski('#skF_2',B_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6287,c_6568])).

tff(c_6313,plain,(
    ! [A_243,B_244,C_245] :
      ( k4_subset_1(A_243,B_244,C_245) = k2_xboole_0(B_244,C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(A_243))
      | ~ m1_subset_1(B_244,k1_zfmisc_1(A_243)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10158,plain,(
    ! [B_339,B_340,A_341] :
      ( k4_subset_1(B_339,B_340,A_341) = k2_xboole_0(B_340,A_341)
      | ~ m1_subset_1(B_340,k1_zfmisc_1(B_339))
      | ~ r1_tarski(A_341,B_339) ) ),
    inference(resolution,[status(thm)],[c_28,c_6313])).

tff(c_10165,plain,(
    ! [A_342] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_342) = k2_xboole_0('#skF_2',A_342)
      | ~ r1_tarski(A_342,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_38,c_10158])).

tff(c_10173,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6579,c_10165])).

tff(c_10208,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_6567,c_6291,c_10173])).

tff(c_32,plain,(
    ! [A_28,B_30] :
      ( k7_subset_1(u1_struct_0(A_28),k2_pre_topc(A_28,B_30),k1_tops_1(A_28,B_30)) = k2_tops_1(A_28,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10228,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10208,c_32])).

tff(c_10234,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_6095,c_10228])).

tff(c_10236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6219,c_10234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.88/2.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.92/2.51  
% 6.92/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.92/2.52  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 6.92/2.52  
% 6.92/2.52  %Foreground sorts:
% 6.92/2.52  
% 6.92/2.52  
% 6.92/2.52  %Background operators:
% 6.92/2.52  
% 6.92/2.52  
% 6.92/2.52  %Foreground operators:
% 6.92/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.92/2.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.92/2.52  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.92/2.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.92/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.92/2.52  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.92/2.52  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.92/2.52  tff('#skF_2', type, '#skF_2': $i).
% 6.92/2.52  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.92/2.52  tff('#skF_1', type, '#skF_1': $i).
% 6.92/2.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.92/2.52  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.92/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.92/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.92/2.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.92/2.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.92/2.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.92/2.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.92/2.52  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.92/2.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.92/2.52  
% 6.92/2.53  tff(f_108, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 6.92/2.53  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.92/2.53  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.92/2.53  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 6.92/2.53  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.92/2.53  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.92/2.53  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.92/2.53  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 6.92/2.53  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.92/2.53  tff(f_73, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 6.92/2.53  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 6.92/2.53  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.92/2.53  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.92/2.53  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.92/2.53  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 6.92/2.53  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.92/2.53  tff(c_6089, plain, (![A_227, B_228, C_229]: (k7_subset_1(A_227, B_228, C_229)=k4_xboole_0(B_228, C_229) | ~m1_subset_1(B_228, k1_zfmisc_1(A_227)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.92/2.53  tff(c_6095, plain, (![C_229]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_229)=k4_xboole_0('#skF_2', C_229))), inference(resolution, [status(thm)], [c_38, c_6089])).
% 6.92/2.53  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.92/2.53  tff(c_130, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 6.92/2.53  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.92/2.53  tff(c_215, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 6.92/2.53  tff(c_121, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.92/2.53  tff(c_129, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_121])).
% 6.92/2.53  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.92/2.53  tff(c_1453, plain, (![A_114, B_115]: (k4_subset_1(u1_struct_0(A_114), B_115, k2_tops_1(A_114, B_115))=k2_pre_topc(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.92/2.53  tff(c_1458, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1453])).
% 6.92/2.53  tff(c_1462, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1458])).
% 6.92/2.53  tff(c_482, plain, (![A_78, B_79, C_80]: (k7_subset_1(A_78, B_79, C_80)=k4_xboole_0(B_79, C_80) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.92/2.53  tff(c_492, plain, (![C_81]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_81)=k4_xboole_0('#skF_2', C_81))), inference(resolution, [status(thm)], [c_38, c_482])).
% 6.92/2.53  tff(c_504, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_130, c_492])).
% 6.92/2.53  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.92/2.53  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.92/2.53  tff(c_131, plain, (![A_49, B_50]: (k2_xboole_0(A_49, B_50)=B_50 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.92/2.53  tff(c_153, plain, (![A_52, B_53]: (k2_xboole_0(k4_xboole_0(A_52, B_53), A_52)=A_52)), inference(resolution, [status(thm)], [c_18, c_131])).
% 6.92/2.53  tff(c_169, plain, (![B_2, B_53]: (k2_xboole_0(B_2, k4_xboole_0(B_2, B_53))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_153])).
% 6.92/2.53  tff(c_752, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_504, c_169])).
% 6.92/2.53  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(k4_xboole_0(A_7, C_9), B_8) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.92/2.53  tff(c_749, plain, (![B_8]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), B_8) | ~r1_tarski('#skF_2', B_8))), inference(superposition, [status(thm), theory('equality')], [c_504, c_12])).
% 6.92/2.53  tff(c_28, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.92/2.53  tff(c_833, plain, (![A_96, B_97, C_98]: (k4_subset_1(A_96, B_97, C_98)=k2_xboole_0(B_97, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(A_96)) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.92/2.53  tff(c_5322, plain, (![B_187, B_188, A_189]: (k4_subset_1(B_187, B_188, A_189)=k2_xboole_0(B_188, A_189) | ~m1_subset_1(B_188, k1_zfmisc_1(B_187)) | ~r1_tarski(A_189, B_187))), inference(resolution, [status(thm)], [c_28, c_833])).
% 6.92/2.53  tff(c_5681, plain, (![A_192]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_192)=k2_xboole_0('#skF_2', A_192) | ~r1_tarski(A_192, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_38, c_5322])).
% 6.92/2.53  tff(c_5685, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_749, c_5681])).
% 6.92/2.53  tff(c_5719, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_1462, c_752, c_5685])).
% 6.92/2.53  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.92/2.53  tff(c_682, plain, (![A_89, B_90]: (v4_pre_topc(k2_pre_topc(A_89, B_90), A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.92/2.53  tff(c_687, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_682])).
% 6.92/2.53  tff(c_691, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_687])).
% 6.92/2.53  tff(c_5731, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5719, c_691])).
% 6.92/2.53  tff(c_5733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215, c_5731])).
% 6.92/2.53  tff(c_5734, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 6.92/2.53  tff(c_5889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_5734])).
% 6.92/2.53  tff(c_5890, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 6.92/2.53  tff(c_5906, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5890, c_44])).
% 6.92/2.53  tff(c_6219, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6095, c_5906])).
% 6.92/2.53  tff(c_6558, plain, (![A_254, B_255]: (k4_subset_1(u1_struct_0(A_254), B_255, k2_tops_1(A_254, B_255))=k2_pre_topc(A_254, B_255) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_254))) | ~l1_pre_topc(A_254))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.92/2.53  tff(c_6563, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_6558])).
% 6.92/2.53  tff(c_6567, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6563])).
% 6.92/2.53  tff(c_6267, plain, (![A_241, B_242]: (r1_tarski(k2_tops_1(A_241, B_242), B_242) | ~v4_pre_topc(B_242, A_241) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.92/2.53  tff(c_6272, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_6267])).
% 6.92/2.53  tff(c_6276, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5890, c_6272])).
% 6.92/2.53  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.92/2.53  tff(c_6286, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_6276, c_14])).
% 6.92/2.53  tff(c_6291, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_6286, c_2])).
% 6.92/2.53  tff(c_16, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.92/2.53  tff(c_6287, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6276, c_16])).
% 6.92/2.53  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.92/2.53  tff(c_6007, plain, (![A_221, B_222]: (k4_xboole_0(A_221, k4_xboole_0(A_221, B_222))=k3_xboole_0(A_221, B_222))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.92/2.53  tff(c_6357, plain, (![A_247, B_248, B_249]: (r1_tarski(k3_xboole_0(A_247, B_248), B_249) | ~r1_tarski(A_247, B_249))), inference(superposition, [status(thm), theory('equality')], [c_6007, c_12])).
% 6.92/2.53  tff(c_6568, plain, (![B_256, A_257, B_258]: (r1_tarski(k3_xboole_0(B_256, A_257), B_258) | ~r1_tarski(A_257, B_258))), inference(superposition, [status(thm), theory('equality')], [c_4, c_6357])).
% 6.92/2.53  tff(c_6579, plain, (![B_258]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), B_258) | ~r1_tarski('#skF_2', B_258))), inference(superposition, [status(thm), theory('equality')], [c_6287, c_6568])).
% 6.92/2.53  tff(c_6313, plain, (![A_243, B_244, C_245]: (k4_subset_1(A_243, B_244, C_245)=k2_xboole_0(B_244, C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(A_243)) | ~m1_subset_1(B_244, k1_zfmisc_1(A_243)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.92/2.53  tff(c_10158, plain, (![B_339, B_340, A_341]: (k4_subset_1(B_339, B_340, A_341)=k2_xboole_0(B_340, A_341) | ~m1_subset_1(B_340, k1_zfmisc_1(B_339)) | ~r1_tarski(A_341, B_339))), inference(resolution, [status(thm)], [c_28, c_6313])).
% 6.92/2.53  tff(c_10165, plain, (![A_342]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_342)=k2_xboole_0('#skF_2', A_342) | ~r1_tarski(A_342, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_38, c_10158])).
% 6.92/2.53  tff(c_10173, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6579, c_10165])).
% 6.92/2.53  tff(c_10208, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_6567, c_6291, c_10173])).
% 6.92/2.53  tff(c_32, plain, (![A_28, B_30]: (k7_subset_1(u1_struct_0(A_28), k2_pre_topc(A_28, B_30), k1_tops_1(A_28, B_30))=k2_tops_1(A_28, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.92/2.53  tff(c_10228, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10208, c_32])).
% 6.92/2.53  tff(c_10234, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_6095, c_10228])).
% 6.92/2.53  tff(c_10236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6219, c_10234])).
% 6.92/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.92/2.53  
% 6.92/2.53  Inference rules
% 6.92/2.53  ----------------------
% 6.92/2.53  #Ref     : 0
% 6.92/2.53  #Sup     : 2548
% 6.92/2.53  #Fact    : 0
% 6.92/2.53  #Define  : 0
% 6.92/2.53  #Split   : 7
% 6.92/2.53  #Chain   : 0
% 6.92/2.53  #Close   : 0
% 6.92/2.53  
% 6.92/2.53  Ordering : KBO
% 6.92/2.53  
% 6.92/2.53  Simplification rules
% 6.92/2.53  ----------------------
% 6.92/2.53  #Subsume      : 489
% 6.92/2.53  #Demod        : 2272
% 6.92/2.53  #Tautology    : 1381
% 6.92/2.53  #SimpNegUnit  : 2
% 6.92/2.53  #BackRed      : 5
% 6.92/2.53  
% 6.92/2.53  #Partial instantiations: 0
% 6.92/2.53  #Strategies tried      : 1
% 6.92/2.53  
% 6.92/2.53  Timing (in seconds)
% 6.92/2.53  ----------------------
% 6.92/2.54  Preprocessing        : 0.34
% 6.92/2.54  Parsing              : 0.19
% 6.92/2.54  CNF conversion       : 0.02
% 6.92/2.54  Main loop            : 1.41
% 6.92/2.54  Inferencing          : 0.41
% 6.92/2.54  Reduction            : 0.64
% 6.92/2.54  Demodulation         : 0.54
% 6.92/2.54  BG Simplification    : 0.05
% 6.92/2.54  Subsumption          : 0.23
% 6.92/2.54  Abstraction          : 0.07
% 6.92/2.54  MUC search           : 0.00
% 6.92/2.54  Cooper               : 0.00
% 6.92/2.54  Total                : 1.79
% 6.92/2.54  Index Insertion      : 0.00
% 6.92/2.54  Index Deletion       : 0.00
% 6.92/2.54  Index Matching       : 0.00
% 6.92/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
