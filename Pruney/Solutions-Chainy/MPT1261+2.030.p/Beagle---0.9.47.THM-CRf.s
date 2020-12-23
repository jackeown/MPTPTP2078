%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:15 EST 2020

% Result     : Theorem 11.02s
% Output     : CNFRefutation 11.02s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 378 expanded)
%              Number of leaves         :   53 ( 147 expanded)
%              Depth                    :   16
%              Number of atoms          :  195 ( 735 expanded)
%              Number of equality atoms :   78 ( 227 expanded)
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

tff(f_157,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_145,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_87,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_75,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_15174,plain,(
    ! [A_519,B_520,C_521] :
      ( k7_subset_1(A_519,B_520,C_521) = k4_xboole_0(B_520,C_521)
      | ~ m1_subset_1(B_520,k1_zfmisc_1(A_519)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_15193,plain,(
    ! [C_521] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_521) = k4_xboole_0('#skF_2',C_521) ),
    inference(resolution,[status(thm)],[c_66,c_15174])).

tff(c_78,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_122,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_72,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_210,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_190,plain,(
    ! [A_89,B_90] :
      ( r1_tarski(A_89,B_90)
      | ~ m1_subset_1(A_89,k1_zfmisc_1(B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_204,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_190])).

tff(c_68,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_3658,plain,(
    ! [A_234,B_235] :
      ( k4_subset_1(u1_struct_0(A_234),B_235,k2_tops_1(A_234,B_235)) = k2_pre_topc(A_234,B_235)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3681,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_3658])).

tff(c_3696,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3681])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_170,plain,(
    ! [A_85,B_86] : k3_tarski(k2_tarski(A_85,B_86)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_226,plain,(
    ! [A_95,B_96] : k3_tarski(k2_tarski(A_95,B_96)) = k2_xboole_0(B_96,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_170])).

tff(c_28,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_249,plain,(
    ! [B_97,A_98] : k2_xboole_0(B_97,A_98) = k2_xboole_0(A_98,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_28])).

tff(c_296,plain,(
    ! [A_99] : k2_xboole_0(k1_xboole_0,A_99) = A_99 ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_4])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_309,plain,(
    ! [B_8] : k3_xboole_0(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_8])).

tff(c_392,plain,(
    ! [A_104,B_105] : k4_xboole_0(A_104,k3_xboole_0(A_104,B_105)) = k4_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_418,plain,(
    ! [B_8] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_392])).

tff(c_423,plain,(
    ! [B_8] : k4_xboole_0(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_418])).

tff(c_564,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k4_xboole_0(B_112,A_111)) = k2_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_573,plain,(
    ! [B_8] : k5_xboole_0(B_8,k1_xboole_0) = k2_xboole_0(B_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_564])).

tff(c_582,plain,(
    ! [B_8] : k5_xboole_0(B_8,k1_xboole_0) = B_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_573])).

tff(c_1610,plain,(
    ! [A_166,B_167,C_168] :
      ( k7_subset_1(A_166,B_167,C_168) = k4_xboole_0(B_167,C_168)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1723,plain,(
    ! [C_173] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_173) = k4_xboole_0('#skF_2',C_173) ),
    inference(resolution,[status(thm)],[c_66,c_1610])).

tff(c_1729,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1723,c_122])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2319,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1729,c_10])).

tff(c_1059,plain,(
    ! [A_140,B_141,C_142] :
      ( r1_tarski(k4_xboole_0(A_140,B_141),C_142)
      | ~ r1_tarski(A_140,k2_xboole_0(B_141,C_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_425,plain,(
    ! [B_106] : k4_xboole_0(k1_xboole_0,B_106) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_418])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(B_12,A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_434,plain,(
    ! [B_106] :
      ( k1_xboole_0 = B_106
      | ~ r1_tarski(B_106,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_12])).

tff(c_1069,plain,(
    ! [A_140,B_141] :
      ( k4_xboole_0(A_140,B_141) = k1_xboole_0
      | ~ r1_tarski(A_140,k2_xboole_0(B_141,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1059,c_434])).

tff(c_1092,plain,(
    ! [A_140,B_141] :
      ( k4_xboole_0(A_140,B_141) = k1_xboole_0
      | ~ r1_tarski(A_140,B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1069])).

tff(c_2329,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2319,c_1092])).

tff(c_24,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2367,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2329,c_24])).

tff(c_2384,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_2367])).

tff(c_1403,plain,(
    ! [A_155,B_156,C_157] :
      ( r1_tarski(A_155,k2_xboole_0(B_156,C_157))
      | ~ r1_tarski(k4_xboole_0(A_155,B_156),C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1451,plain,(
    ! [A_158,B_159] : r1_tarski(A_158,k2_xboole_0(B_159,A_158)) ),
    inference(resolution,[status(thm)],[c_10,c_1403])).

tff(c_6,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(A_4,C_6)
      | ~ r1_tarski(B_5,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1487,plain,(
    ! [A_4,B_159,A_158] :
      ( r1_tarski(A_4,k2_xboole_0(B_159,A_158))
      | ~ r1_tarski(A_4,A_158) ) ),
    inference(resolution,[status(thm)],[c_1451,c_6])).

tff(c_20,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_9024,plain,(
    ! [A_335,B_336,C_337] :
      ( r1_tarski(k4_xboole_0(A_335,B_336),C_337)
      | ~ r1_tarski(A_335,k2_xboole_0(k3_xboole_0(A_335,B_336),C_337)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1059])).

tff(c_9457,plain,(
    ! [A_345,B_346,A_347] :
      ( r1_tarski(k4_xboole_0(A_345,B_346),A_347)
      | ~ r1_tarski(A_345,A_347) ) ),
    inference(resolution,[status(thm)],[c_1487,c_9024])).

tff(c_9554,plain,(
    ! [A_347] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),A_347)
      | ~ r1_tarski('#skF_2',A_347) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1729,c_9457])).

tff(c_52,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(A_51,k1_zfmisc_1(B_52))
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2565,plain,(
    ! [A_197,B_198,C_199] :
      ( k4_subset_1(A_197,B_198,C_199) = k2_xboole_0(B_198,C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(A_197))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(A_197)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12704,plain,(
    ! [B_400,B_401,A_402] :
      ( k4_subset_1(B_400,B_401,A_402) = k2_xboole_0(B_401,A_402)
      | ~ m1_subset_1(B_401,k1_zfmisc_1(B_400))
      | ~ r1_tarski(A_402,B_400) ) ),
    inference(resolution,[status(thm)],[c_52,c_2565])).

tff(c_12827,plain,(
    ! [A_404] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_404) = k2_xboole_0('#skF_2',A_404)
      | ~ r1_tarski(A_404,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_66,c_12704])).

tff(c_12831,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_9554,c_12827])).

tff(c_12951,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_3696,c_2384,c_12831])).

tff(c_70,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2236,plain,(
    ! [A_190,B_191] :
      ( v4_pre_topc(k2_pre_topc(A_190,B_191),A_190)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2255,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_2236])).

tff(c_2266,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_2255])).

tff(c_13002,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12951,c_2266])).

tff(c_13004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_13002])).

tff(c_13005,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_13268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_13005])).

tff(c_13269,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_13354,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13269,c_72])).

tff(c_15294,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15193,c_13354])).

tff(c_16303,plain,(
    ! [A_566,B_567] :
      ( r1_tarski(k2_tops_1(A_566,B_567),B_567)
      | ~ v4_pre_topc(B_567,A_566)
      | ~ m1_subset_1(B_567,k1_zfmisc_1(u1_struct_0(A_566)))
      | ~ l1_pre_topc(A_566) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_16324,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_16303])).

tff(c_16336,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_13269,c_16324])).

tff(c_17335,plain,(
    ! [A_592,B_593] :
      ( k7_subset_1(u1_struct_0(A_592),B_593,k2_tops_1(A_592,B_593)) = k1_tops_1(A_592,B_593)
      | ~ m1_subset_1(B_593,k1_zfmisc_1(u1_struct_0(A_592)))
      | ~ l1_pre_topc(A_592) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_17358,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_17335])).

tff(c_17375,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_15193,c_17358])).

tff(c_13917,plain,(
    ! [A_464,B_465] :
      ( k4_xboole_0(A_464,B_465) = k3_subset_1(A_464,B_465)
      | ~ m1_subset_1(B_465,k1_zfmisc_1(A_464)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18324,plain,(
    ! [B_616,A_617] :
      ( k4_xboole_0(B_616,A_617) = k3_subset_1(B_616,A_617)
      | ~ r1_tarski(A_617,B_616) ) ),
    inference(resolution,[status(thm)],[c_52,c_13917])).

tff(c_18390,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16336,c_18324])).

tff(c_18488,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17375,c_18390])).

tff(c_14178,plain,(
    ! [A_480,B_481] :
      ( k3_subset_1(A_480,k3_subset_1(A_480,B_481)) = B_481
      | ~ m1_subset_1(B_481,k1_zfmisc_1(A_480)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14187,plain,(
    ! [B_52,A_51] :
      ( k3_subset_1(B_52,k3_subset_1(B_52,A_51)) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_52,c_14178])).

tff(c_20277,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18488,c_14187])).

tff(c_20287,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16336,c_20277])).

tff(c_42,plain,(
    ! [A_42,B_43] : k6_subset_1(A_42,B_43) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    ! [A_35,B_36] : m1_subset_1(k6_subset_1(A_35,B_36),k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_79,plain,(
    ! [A_35,B_36] : m1_subset_1(k4_xboole_0(A_35,B_36),k1_zfmisc_1(A_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36])).

tff(c_19528,plain,(
    ! [A_641,B_642] : k4_xboole_0(A_641,k4_xboole_0(A_641,B_642)) = k3_subset_1(A_641,k4_xboole_0(A_641,B_642)) ),
    inference(resolution,[status(thm)],[c_79,c_13917])).

tff(c_21105,plain,(
    ! [A_660,B_661] : m1_subset_1(k3_subset_1(A_660,k4_xboole_0(A_660,B_661)),k1_zfmisc_1(A_660)) ),
    inference(superposition,[status(thm),theory(equality)],[c_19528,c_79])).

tff(c_21156,plain,(
    m1_subset_1(k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17375,c_21105])).

tff(c_21787,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20287,c_21156])).

tff(c_14399,plain,(
    ! [A_491,B_492] :
      ( m1_subset_1(k3_subset_1(A_491,B_492),k1_zfmisc_1(A_491))
      | ~ m1_subset_1(B_492,k1_zfmisc_1(A_491)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_32,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k3_subset_1(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30498,plain,(
    ! [A_788,B_789] :
      ( k4_xboole_0(A_788,k3_subset_1(A_788,B_789)) = k3_subset_1(A_788,k3_subset_1(A_788,B_789))
      | ~ m1_subset_1(B_789,k1_zfmisc_1(A_788)) ) ),
    inference(resolution,[status(thm)],[c_14399,c_32])).

tff(c_30512,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_21787,c_30498])).

tff(c_30542,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20287,c_18488,c_18488,c_30512])).

tff(c_30544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15294,c_30542])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:12 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.02/4.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.02/4.62  
% 11.02/4.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.02/4.62  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.02/4.62  
% 11.02/4.62  %Foreground sorts:
% 11.02/4.62  
% 11.02/4.62  
% 11.02/4.62  %Background operators:
% 11.02/4.62  
% 11.02/4.62  
% 11.02/4.62  %Foreground operators:
% 11.02/4.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.02/4.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.02/4.62  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 11.02/4.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.02/4.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.02/4.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.02/4.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.02/4.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.02/4.62  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.02/4.62  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.02/4.62  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.02/4.62  tff('#skF_2', type, '#skF_2': $i).
% 11.02/4.62  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.02/4.62  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 11.02/4.62  tff('#skF_1', type, '#skF_1': $i).
% 11.02/4.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.02/4.62  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.02/4.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.02/4.62  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.02/4.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.02/4.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.02/4.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.02/4.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.02/4.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.02/4.62  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.02/4.62  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.02/4.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.02/4.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.02/4.62  
% 11.02/4.64  tff(f_157, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 11.02/4.64  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.02/4.64  tff(f_101, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.02/4.64  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 11.02/4.64  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 11.02/4.64  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 11.02/4.64  tff(f_61, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.02/4.64  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.02/4.64  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 11.02/4.64  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 11.02/4.64  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.02/4.64  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.02/4.64  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 11.02/4.64  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 11.02/4.64  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 11.02/4.64  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.02/4.64  tff(f_85, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.02/4.64  tff(f_115, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 11.02/4.64  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 11.02/4.64  tff(f_145, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 11.02/4.64  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 11.02/4.64  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.02/4.64  tff(f_87, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.02/4.64  tff(f_75, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 11.02/4.64  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.02/4.64  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.02/4.64  tff(c_15174, plain, (![A_519, B_520, C_521]: (k7_subset_1(A_519, B_520, C_521)=k4_xboole_0(B_520, C_521) | ~m1_subset_1(B_520, k1_zfmisc_1(A_519)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.02/4.64  tff(c_15193, plain, (![C_521]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_521)=k4_xboole_0('#skF_2', C_521))), inference(resolution, [status(thm)], [c_66, c_15174])).
% 11.02/4.64  tff(c_78, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.02/4.64  tff(c_122, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_78])).
% 11.02/4.64  tff(c_72, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.02/4.64  tff(c_210, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_72])).
% 11.02/4.64  tff(c_190, plain, (![A_89, B_90]: (r1_tarski(A_89, B_90) | ~m1_subset_1(A_89, k1_zfmisc_1(B_90)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.02/4.64  tff(c_204, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_190])).
% 11.02/4.64  tff(c_68, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.02/4.64  tff(c_3658, plain, (![A_234, B_235]: (k4_subset_1(u1_struct_0(A_234), B_235, k2_tops_1(A_234, B_235))=k2_pre_topc(A_234, B_235) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234))), inference(cnfTransformation, [status(thm)], [f_129])).
% 11.02/4.64  tff(c_3681, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_3658])).
% 11.02/4.64  tff(c_3696, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3681])).
% 11.02/4.64  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.02/4.64  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.02/4.64  tff(c_26, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.02/4.64  tff(c_170, plain, (![A_85, B_86]: (k3_tarski(k2_tarski(A_85, B_86))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.02/4.64  tff(c_226, plain, (![A_95, B_96]: (k3_tarski(k2_tarski(A_95, B_96))=k2_xboole_0(B_96, A_95))), inference(superposition, [status(thm), theory('equality')], [c_26, c_170])).
% 11.02/4.64  tff(c_28, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.02/4.64  tff(c_249, plain, (![B_97, A_98]: (k2_xboole_0(B_97, A_98)=k2_xboole_0(A_98, B_97))), inference(superposition, [status(thm), theory('equality')], [c_226, c_28])).
% 11.02/4.64  tff(c_296, plain, (![A_99]: (k2_xboole_0(k1_xboole_0, A_99)=A_99)), inference(superposition, [status(thm), theory('equality')], [c_249, c_4])).
% 11.02/4.64  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.02/4.64  tff(c_309, plain, (![B_8]: (k3_xboole_0(k1_xboole_0, B_8)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_296, c_8])).
% 11.02/4.64  tff(c_392, plain, (![A_104, B_105]: (k4_xboole_0(A_104, k3_xboole_0(A_104, B_105))=k4_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.02/4.64  tff(c_418, plain, (![B_8]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_8))), inference(superposition, [status(thm), theory('equality')], [c_309, c_392])).
% 11.02/4.64  tff(c_423, plain, (![B_8]: (k4_xboole_0(k1_xboole_0, B_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_418])).
% 11.02/4.64  tff(c_564, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k4_xboole_0(B_112, A_111))=k2_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.02/4.64  tff(c_573, plain, (![B_8]: (k5_xboole_0(B_8, k1_xboole_0)=k2_xboole_0(B_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_423, c_564])).
% 11.02/4.64  tff(c_582, plain, (![B_8]: (k5_xboole_0(B_8, k1_xboole_0)=B_8)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_573])).
% 11.02/4.64  tff(c_1610, plain, (![A_166, B_167, C_168]: (k7_subset_1(A_166, B_167, C_168)=k4_xboole_0(B_167, C_168) | ~m1_subset_1(B_167, k1_zfmisc_1(A_166)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.02/4.64  tff(c_1723, plain, (![C_173]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_173)=k4_xboole_0('#skF_2', C_173))), inference(resolution, [status(thm)], [c_66, c_1610])).
% 11.02/4.64  tff(c_1729, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1723, c_122])).
% 11.02/4.64  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.02/4.64  tff(c_2319, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1729, c_10])).
% 11.02/4.64  tff(c_1059, plain, (![A_140, B_141, C_142]: (r1_tarski(k4_xboole_0(A_140, B_141), C_142) | ~r1_tarski(A_140, k2_xboole_0(B_141, C_142)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.02/4.64  tff(c_425, plain, (![B_106]: (k4_xboole_0(k1_xboole_0, B_106)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_418])).
% 11.02/4.64  tff(c_12, plain, (![A_11, B_12]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k4_xboole_0(B_12, A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.02/4.64  tff(c_434, plain, (![B_106]: (k1_xboole_0=B_106 | ~r1_tarski(B_106, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_425, c_12])).
% 11.02/4.64  tff(c_1069, plain, (![A_140, B_141]: (k4_xboole_0(A_140, B_141)=k1_xboole_0 | ~r1_tarski(A_140, k2_xboole_0(B_141, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1059, c_434])).
% 11.02/4.64  tff(c_1092, plain, (![A_140, B_141]: (k4_xboole_0(A_140, B_141)=k1_xboole_0 | ~r1_tarski(A_140, B_141))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1069])).
% 11.02/4.64  tff(c_2329, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2319, c_1092])).
% 11.02/4.64  tff(c_24, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.02/4.64  tff(c_2367, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2329, c_24])).
% 11.02/4.64  tff(c_2384, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_582, c_2367])).
% 11.02/4.64  tff(c_1403, plain, (![A_155, B_156, C_157]: (r1_tarski(A_155, k2_xboole_0(B_156, C_157)) | ~r1_tarski(k4_xboole_0(A_155, B_156), C_157))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.02/4.64  tff(c_1451, plain, (![A_158, B_159]: (r1_tarski(A_158, k2_xboole_0(B_159, A_158)))), inference(resolution, [status(thm)], [c_10, c_1403])).
% 11.02/4.64  tff(c_6, plain, (![A_4, C_6, B_5]: (r1_tarski(A_4, C_6) | ~r1_tarski(B_5, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.02/4.64  tff(c_1487, plain, (![A_4, B_159, A_158]: (r1_tarski(A_4, k2_xboole_0(B_159, A_158)) | ~r1_tarski(A_4, A_158))), inference(resolution, [status(thm)], [c_1451, c_6])).
% 11.02/4.64  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.02/4.64  tff(c_9024, plain, (![A_335, B_336, C_337]: (r1_tarski(k4_xboole_0(A_335, B_336), C_337) | ~r1_tarski(A_335, k2_xboole_0(k3_xboole_0(A_335, B_336), C_337)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1059])).
% 11.02/4.64  tff(c_9457, plain, (![A_345, B_346, A_347]: (r1_tarski(k4_xboole_0(A_345, B_346), A_347) | ~r1_tarski(A_345, A_347))), inference(resolution, [status(thm)], [c_1487, c_9024])).
% 11.02/4.64  tff(c_9554, plain, (![A_347]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), A_347) | ~r1_tarski('#skF_2', A_347))), inference(superposition, [status(thm), theory('equality')], [c_1729, c_9457])).
% 11.02/4.64  tff(c_52, plain, (![A_51, B_52]: (m1_subset_1(A_51, k1_zfmisc_1(B_52)) | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.02/4.64  tff(c_2565, plain, (![A_197, B_198, C_199]: (k4_subset_1(A_197, B_198, C_199)=k2_xboole_0(B_198, C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(A_197)) | ~m1_subset_1(B_198, k1_zfmisc_1(A_197)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.02/4.64  tff(c_12704, plain, (![B_400, B_401, A_402]: (k4_subset_1(B_400, B_401, A_402)=k2_xboole_0(B_401, A_402) | ~m1_subset_1(B_401, k1_zfmisc_1(B_400)) | ~r1_tarski(A_402, B_400))), inference(resolution, [status(thm)], [c_52, c_2565])).
% 11.02/4.64  tff(c_12827, plain, (![A_404]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_404)=k2_xboole_0('#skF_2', A_404) | ~r1_tarski(A_404, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_66, c_12704])).
% 11.02/4.64  tff(c_12831, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_9554, c_12827])).
% 11.02/4.64  tff(c_12951, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_3696, c_2384, c_12831])).
% 11.02/4.64  tff(c_70, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.02/4.64  tff(c_2236, plain, (![A_190, B_191]: (v4_pre_topc(k2_pre_topc(A_190, B_191), A_190) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.02/4.64  tff(c_2255, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_2236])).
% 11.02/4.64  tff(c_2266, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_2255])).
% 11.02/4.64  tff(c_13002, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12951, c_2266])).
% 11.02/4.64  tff(c_13004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210, c_13002])).
% 11.02/4.64  tff(c_13005, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_72])).
% 11.02/4.64  tff(c_13268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_13005])).
% 11.02/4.64  tff(c_13269, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_78])).
% 11.02/4.64  tff(c_13354, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13269, c_72])).
% 11.02/4.64  tff(c_15294, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15193, c_13354])).
% 11.02/4.64  tff(c_16303, plain, (![A_566, B_567]: (r1_tarski(k2_tops_1(A_566, B_567), B_567) | ~v4_pre_topc(B_567, A_566) | ~m1_subset_1(B_567, k1_zfmisc_1(u1_struct_0(A_566))) | ~l1_pre_topc(A_566))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.02/4.64  tff(c_16324, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_16303])).
% 11.02/4.64  tff(c_16336, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_13269, c_16324])).
% 11.02/4.64  tff(c_17335, plain, (![A_592, B_593]: (k7_subset_1(u1_struct_0(A_592), B_593, k2_tops_1(A_592, B_593))=k1_tops_1(A_592, B_593) | ~m1_subset_1(B_593, k1_zfmisc_1(u1_struct_0(A_592))) | ~l1_pre_topc(A_592))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.02/4.64  tff(c_17358, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_17335])).
% 11.02/4.64  tff(c_17375, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_15193, c_17358])).
% 11.02/4.64  tff(c_13917, plain, (![A_464, B_465]: (k4_xboole_0(A_464, B_465)=k3_subset_1(A_464, B_465) | ~m1_subset_1(B_465, k1_zfmisc_1(A_464)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.02/4.64  tff(c_18324, plain, (![B_616, A_617]: (k4_xboole_0(B_616, A_617)=k3_subset_1(B_616, A_617) | ~r1_tarski(A_617, B_616))), inference(resolution, [status(thm)], [c_52, c_13917])).
% 11.02/4.64  tff(c_18390, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16336, c_18324])).
% 11.02/4.64  tff(c_18488, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17375, c_18390])).
% 11.02/4.64  tff(c_14178, plain, (![A_480, B_481]: (k3_subset_1(A_480, k3_subset_1(A_480, B_481))=B_481 | ~m1_subset_1(B_481, k1_zfmisc_1(A_480)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.02/4.64  tff(c_14187, plain, (![B_52, A_51]: (k3_subset_1(B_52, k3_subset_1(B_52, A_51))=A_51 | ~r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_52, c_14178])).
% 11.02/4.64  tff(c_20277, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18488, c_14187])).
% 11.02/4.64  tff(c_20287, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16336, c_20277])).
% 11.02/4.64  tff(c_42, plain, (![A_42, B_43]: (k6_subset_1(A_42, B_43)=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.02/4.64  tff(c_36, plain, (![A_35, B_36]: (m1_subset_1(k6_subset_1(A_35, B_36), k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.02/4.64  tff(c_79, plain, (![A_35, B_36]: (m1_subset_1(k4_xboole_0(A_35, B_36), k1_zfmisc_1(A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36])).
% 11.02/4.64  tff(c_19528, plain, (![A_641, B_642]: (k4_xboole_0(A_641, k4_xboole_0(A_641, B_642))=k3_subset_1(A_641, k4_xboole_0(A_641, B_642)))), inference(resolution, [status(thm)], [c_79, c_13917])).
% 11.02/4.64  tff(c_21105, plain, (![A_660, B_661]: (m1_subset_1(k3_subset_1(A_660, k4_xboole_0(A_660, B_661)), k1_zfmisc_1(A_660)))), inference(superposition, [status(thm), theory('equality')], [c_19528, c_79])).
% 11.02/4.64  tff(c_21156, plain, (m1_subset_1(k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_17375, c_21105])).
% 11.02/4.64  tff(c_21787, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20287, c_21156])).
% 11.02/4.64  tff(c_14399, plain, (![A_491, B_492]: (m1_subset_1(k3_subset_1(A_491, B_492), k1_zfmisc_1(A_491)) | ~m1_subset_1(B_492, k1_zfmisc_1(A_491)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.02/4.64  tff(c_32, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k3_subset_1(A_31, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.02/4.64  tff(c_30498, plain, (![A_788, B_789]: (k4_xboole_0(A_788, k3_subset_1(A_788, B_789))=k3_subset_1(A_788, k3_subset_1(A_788, B_789)) | ~m1_subset_1(B_789, k1_zfmisc_1(A_788)))), inference(resolution, [status(thm)], [c_14399, c_32])).
% 11.02/4.64  tff(c_30512, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_21787, c_30498])).
% 11.02/4.64  tff(c_30542, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20287, c_18488, c_18488, c_30512])).
% 11.02/4.64  tff(c_30544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15294, c_30542])).
% 11.02/4.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.02/4.64  
% 11.02/4.64  Inference rules
% 11.02/4.64  ----------------------
% 11.02/4.64  #Ref     : 0
% 11.02/4.64  #Sup     : 7374
% 11.02/4.64  #Fact    : 0
% 11.02/4.64  #Define  : 0
% 11.02/4.64  #Split   : 8
% 11.02/4.64  #Chain   : 0
% 11.02/4.64  #Close   : 0
% 11.02/4.64  
% 11.02/4.64  Ordering : KBO
% 11.02/4.64  
% 11.02/4.64  Simplification rules
% 11.02/4.64  ----------------------
% 11.02/4.64  #Subsume      : 398
% 11.02/4.64  #Demod        : 6358
% 11.02/4.64  #Tautology    : 4569
% 11.02/4.64  #SimpNegUnit  : 2
% 11.02/4.64  #BackRed      : 42
% 11.02/4.64  
% 11.02/4.64  #Partial instantiations: 0
% 11.02/4.64  #Strategies tried      : 1
% 11.02/4.64  
% 11.02/4.64  Timing (in seconds)
% 11.02/4.64  ----------------------
% 11.02/4.65  Preprocessing        : 0.39
% 11.02/4.65  Parsing              : 0.21
% 11.02/4.65  CNF conversion       : 0.03
% 11.02/4.65  Main loop            : 3.43
% 11.02/4.65  Inferencing          : 0.73
% 11.02/4.65  Reduction            : 1.77
% 11.02/4.65  Demodulation         : 1.50
% 11.02/4.65  BG Simplification    : 0.08
% 11.02/4.65  Subsumption          : 0.63
% 11.02/4.65  Abstraction          : 0.12
% 11.02/4.65  MUC search           : 0.00
% 11.02/4.65  Cooper               : 0.00
% 11.02/4.65  Total                : 3.87
% 11.02/4.65  Index Insertion      : 0.00
% 11.02/4.65  Index Deletion       : 0.00
% 11.02/4.65  Index Matching       : 0.00
% 11.02/4.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
