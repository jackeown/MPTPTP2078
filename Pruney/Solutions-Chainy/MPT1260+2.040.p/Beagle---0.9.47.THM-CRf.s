%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:05 EST 2020

% Result     : Theorem 27.42s
% Output     : CNFRefutation 27.59s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 392 expanded)
%              Number of leaves         :   51 ( 152 expanded)
%              Depth                    :   12
%              Number of atoms          :  241 ( 716 expanded)
%              Number of equality atoms :   95 ( 256 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(f_176,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_96,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_164,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_150,axiom,(
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

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_82,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_122,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_76,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_311,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_109,plain,(
    ! [A_83,B_84] : k4_xboole_0(A_83,k2_xboole_0(A_83,B_84)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_114,plain,(
    ! [A_83] : r1_tarski(k1_xboole_0,A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_22])).

tff(c_16,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_119,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_109])).

tff(c_46,plain,(
    ! [A_45] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1779,plain,(
    ! [A_158,B_159] :
      ( k4_xboole_0(A_158,B_159) = k3_subset_1(A_158,B_159)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1788,plain,(
    ! [A_45] : k4_xboole_0(A_45,k1_xboole_0) = k3_subset_1(A_45,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_46,c_1779])).

tff(c_1792,plain,(
    ! [A_45] : k3_subset_1(A_45,k1_xboole_0) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1788])).

tff(c_1994,plain,(
    ! [A_165,B_166] :
      ( m1_subset_1(k3_subset_1(A_165,B_166),k1_zfmisc_1(A_165))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(A_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2003,plain,(
    ! [A_45] :
      ( m1_subset_1(A_45,k1_zfmisc_1(A_45))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1792,c_1994])).

tff(c_2008,plain,(
    ! [A_167] : m1_subset_1(A_167,k1_zfmisc_1(A_167)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2003])).

tff(c_34,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k3_subset_1(A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2011,plain,(
    ! [A_167] : k4_xboole_0(A_167,A_167) = k3_subset_1(A_167,A_167) ),
    inference(resolution,[status(thm)],[c_2008,c_34])).

tff(c_2016,plain,(
    ! [A_167] : k3_subset_1(A_167,A_167) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_2011])).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_70,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_4322,plain,(
    ! [A_236,B_237] :
      ( m1_subset_1(k2_pre_topc(A_236,B_237),k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    ! [A_38,B_39,C_40] :
      ( k7_subset_1(A_38,B_39,C_40) = k4_xboole_0(B_39,C_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_41813,plain,(
    ! [A_621,B_622,C_623] :
      ( k7_subset_1(u1_struct_0(A_621),k2_pre_topc(A_621,B_622),C_623) = k4_xboole_0(k2_pre_topc(A_621,B_622),C_623)
      | ~ m1_subset_1(B_622,k1_zfmisc_1(u1_struct_0(A_621)))
      | ~ l1_pre_topc(A_621) ) ),
    inference(resolution,[status(thm)],[c_4322,c_42])).

tff(c_41828,plain,(
    ! [C_623] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_623) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_623)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_41813])).

tff(c_42572,plain,(
    ! [C_626] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_626) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_626) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_41828])).

tff(c_42586,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42572,c_122])).

tff(c_30,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k2_xboole_0(A_25,B_26)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_820,plain,(
    ! [A_121,B_122] : k4_xboole_0(A_121,k4_xboole_0(A_121,B_122)) = k3_xboole_0(A_121,B_122) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_870,plain,(
    ! [A_25,B_26] : k3_xboole_0(A_25,k2_xboole_0(A_25,B_26)) = k4_xboole_0(A_25,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_820])).

tff(c_883,plain,(
    ! [A_25,B_26] : k3_xboole_0(A_25,k2_xboole_0(A_25,B_26)) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_870])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_986,plain,(
    ! [A_128,B_129] : k4_xboole_0(k2_xboole_0(A_128,B_129),B_129) = k4_xboole_0(A_128,B_129) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1029,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_986])).

tff(c_32,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_365,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(A_97,B_98) = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_376,plain,(
    ! [A_17,B_18] : k3_xboole_0(k4_xboole_0(A_17,B_18),A_17) = k4_xboole_0(A_17,B_18) ),
    inference(resolution,[status(thm)],[c_22,c_365])).

tff(c_780,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2548,plain,(
    ! [A_185,B_186] : k5_xboole_0(A_185,k3_xboole_0(B_186,A_185)) = k4_xboole_0(A_185,B_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_780])).

tff(c_2561,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_2548])).

tff(c_15489,plain,(
    ! [A_407,B_408] : k5_xboole_0(A_407,k4_xboole_0(A_407,B_408)) = k3_xboole_0(A_407,B_408) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2561])).

tff(c_15510,plain,(
    ! [B_2,A_1] : k5_xboole_0(k2_xboole_0(B_2,A_1),k4_xboole_0(A_1,B_2)) = k3_xboole_0(k2_xboole_0(B_2,A_1),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_15489])).

tff(c_15563,plain,(
    ! [B_2,A_1] : k5_xboole_0(k2_xboole_0(B_2,A_1),k4_xboole_0(A_1,B_2)) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_4,c_15510])).

tff(c_1199,plain,(
    ! [A_136,C_137,B_138] :
      ( r1_tarski(A_136,C_137)
      | ~ r1_tarski(B_138,C_137)
      | ~ r1_tarski(A_136,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2605,plain,(
    ! [A_187,A_188,B_189] :
      ( r1_tarski(A_187,A_188)
      | ~ r1_tarski(A_187,k4_xboole_0(A_188,B_189)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1199])).

tff(c_2669,plain,(
    ! [A_188,B_189,B_18] : r1_tarski(k4_xboole_0(k4_xboole_0(A_188,B_189),B_18),A_188) ),
    inference(resolution,[status(thm)],[c_22,c_2605])).

tff(c_26,plain,(
    ! [A_20,B_21] : k4_xboole_0(k2_xboole_0(A_20,B_21),B_21) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2998,plain,(
    ! [A_199,B_200,C_201] :
      ( r1_tarski(A_199,k2_xboole_0(B_200,C_201))
      | ~ r1_tarski(k4_xboole_0(A_199,B_200),C_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22367,plain,(
    ! [A_476,B_477,C_478] :
      ( r1_tarski(k2_xboole_0(A_476,B_477),k2_xboole_0(B_477,C_478))
      | ~ r1_tarski(k4_xboole_0(A_476,B_477),C_478) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2998])).

tff(c_22517,plain,(
    ! [A_1,B_2,C_478] :
      ( r1_tarski(k2_xboole_0(A_1,B_2),k2_xboole_0(A_1,C_478))
      | ~ r1_tarski(k4_xboole_0(B_2,A_1),C_478) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22367])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3253,plain,(
    ! [A_204,B_205] : r1_tarski(A_204,k2_xboole_0(B_205,k4_xboole_0(A_204,B_205))) ),
    inference(resolution,[status(thm)],[c_10,c_2998])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106099,plain,(
    ! [B_958,A_959] :
      ( k2_xboole_0(B_958,k4_xboole_0(A_959,B_958)) = A_959
      | ~ r1_tarski(k2_xboole_0(B_958,k4_xboole_0(A_959,B_958)),A_959) ) ),
    inference(resolution,[status(thm)],[c_3253,c_6])).

tff(c_106109,plain,(
    ! [A_1,C_478] :
      ( k2_xboole_0(A_1,k4_xboole_0(k2_xboole_0(A_1,C_478),A_1)) = k2_xboole_0(A_1,C_478)
      | ~ r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(A_1,C_478),A_1),A_1),C_478) ) ),
    inference(resolution,[status(thm)],[c_22517,c_106099])).

tff(c_106543,plain,(
    ! [A_960,C_961] : k2_xboole_0(A_960,k4_xboole_0(C_961,A_960)) = k2_xboole_0(A_960,C_961) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2669,c_1029,c_1029,c_106109])).

tff(c_1052,plain,(
    ! [A_130,B_131] : k3_xboole_0(A_130,k2_xboole_0(A_130,B_131)) = A_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_870])).

tff(c_1096,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1052])).

tff(c_2567,plain,(
    ! [A_1,B_2] : k5_xboole_0(k2_xboole_0(A_1,B_2),B_2) = k4_xboole_0(k2_xboole_0(A_1,B_2),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_1096,c_2548])).

tff(c_2597,plain,(
    ! [A_1,B_2] : k5_xboole_0(k2_xboole_0(A_1,B_2),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2567])).

tff(c_106909,plain,(
    ! [A_960,C_961] : k5_xboole_0(k2_xboole_0(A_960,C_961),k4_xboole_0(C_961,A_960)) = k4_xboole_0(A_960,k4_xboole_0(C_961,A_960)) ),
    inference(superposition,[status(thm),theory(equality)],[c_106543,c_2597])).

tff(c_107486,plain,(
    ! [A_962,C_963] : k4_xboole_0(A_962,k4_xboole_0(C_963,A_962)) = A_962 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15563,c_106909])).

tff(c_107908,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_42586,c_107486])).

tff(c_3740,plain,(
    ! [A_217,B_218,C_219] :
      ( k7_subset_1(A_217,B_218,C_219) = k4_xboole_0(B_218,C_219)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(A_217)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3754,plain,(
    ! [C_219] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_219) = k4_xboole_0('#skF_2',C_219) ),
    inference(resolution,[status(thm)],[c_70,c_3740])).

tff(c_5431,plain,(
    ! [A_267,B_268] :
      ( k7_subset_1(u1_struct_0(A_267),B_268,k2_tops_1(A_267,B_268)) = k1_tops_1(A_267,B_268)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_5444,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_5431])).

tff(c_5455,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3754,c_5444])).

tff(c_108219,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107908,c_5455])).

tff(c_52,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(A_48,k1_zfmisc_1(B_49))
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_15067,plain,(
    ! [B_403,A_404] :
      ( k4_xboole_0(B_403,A_404) = k3_subset_1(B_403,A_404)
      | ~ r1_tarski(A_404,B_403) ) ),
    inference(resolution,[status(thm)],[c_52,c_1779])).

tff(c_15235,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_subset_1(A_17,k4_xboole_0(A_17,B_18)) ),
    inference(resolution,[status(thm)],[c_22,c_15067])).

tff(c_15304,plain,(
    ! [A_405,B_406] : k3_subset_1(A_405,k4_xboole_0(A_405,B_406)) = k3_xboole_0(A_405,B_406) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_15235])).

tff(c_15337,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5455,c_15304])).

tff(c_744,plain,(
    ! [B_115,A_116] :
      ( B_115 = A_116
      | ~ r1_tarski(B_115,A_116)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_13835,plain,(
    ! [A_386,B_387] :
      ( k4_xboole_0(A_386,B_387) = A_386
      | ~ r1_tarski(A_386,k4_xboole_0(A_386,B_387)) ) ),
    inference(resolution,[status(thm)],[c_22,c_744])).

tff(c_13847,plain,
    ( k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5455,c_13835])).

tff(c_13897,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5455,c_13847])).

tff(c_56167,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_13897])).

tff(c_486,plain,(
    ! [A_104,B_105] :
      ( k2_xboole_0(A_104,B_105) = B_105
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_541,plain,(
    ! [A_107,B_108] : k2_xboole_0(k4_xboole_0(A_107,B_108),A_107) = A_107 ),
    inference(resolution,[status(thm)],[c_22,c_486])).

tff(c_577,plain,(
    ! [A_1,B_108] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_108)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_541])).

tff(c_5506,plain,(
    k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_5455,c_577])).

tff(c_5500,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5455,c_32])).

tff(c_73933,plain,(
    ! [A_805,A_806] :
      ( r1_tarski(k2_xboole_0(A_805,A_806),A_806)
      | ~ r1_tarski(k4_xboole_0(A_805,A_806),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_22367])).

tff(c_73935,plain,
    ( r1_tarski(k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5500,c_73933])).

tff(c_74092,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5506,c_73935])).

tff(c_74093,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_56167,c_74092])).

tff(c_98591,plain,(
    ~ r1_tarski(k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15337,c_74093])).

tff(c_108479,plain,(
    ~ r1_tarski(k3_subset_1('#skF_2','#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108219,c_98591])).

tff(c_108530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_2016,c_108479])).

tff(c_108531,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_13897])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_4824,plain,(
    ! [A_249,B_250] :
      ( v3_pre_topc(k1_tops_1(A_249,B_250),A_249)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4837,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_4824])).

tff(c_4847,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4837])).

tff(c_108563,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108531,c_4847])).

tff(c_108592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_108563])).

tff(c_108593,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_108900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_108593])).

tff(c_108901,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_109055,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108901,c_76])).

tff(c_112098,plain,(
    ! [A_1103,B_1104,C_1105] :
      ( k7_subset_1(A_1103,B_1104,C_1105) = k4_xboole_0(B_1104,C_1105)
      | ~ m1_subset_1(B_1104,k1_zfmisc_1(A_1103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_112112,plain,(
    ! [C_1105] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_1105) = k4_xboole_0('#skF_2',C_1105) ),
    inference(resolution,[status(thm)],[c_70,c_112098])).

tff(c_113819,plain,(
    ! [A_1156,B_1157] :
      ( k7_subset_1(u1_struct_0(A_1156),B_1157,k2_tops_1(A_1156,B_1157)) = k1_tops_1(A_1156,B_1157)
      | ~ m1_subset_1(B_1157,k1_zfmisc_1(u1_struct_0(A_1156)))
      | ~ l1_pre_topc(A_1156) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_113832,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_113819])).

tff(c_113843,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_112112,c_113832])).

tff(c_113891,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_113843,c_22])).

tff(c_114436,plain,(
    ! [B_1170,A_1171,C_1172] :
      ( r1_tarski(B_1170,k1_tops_1(A_1171,C_1172))
      | ~ r1_tarski(B_1170,C_1172)
      | ~ v3_pre_topc(B_1170,A_1171)
      | ~ m1_subset_1(C_1172,k1_zfmisc_1(u1_struct_0(A_1171)))
      | ~ m1_subset_1(B_1170,k1_zfmisc_1(u1_struct_0(A_1171)))
      | ~ l1_pre_topc(A_1171) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_114449,plain,(
    ! [B_1170] :
      ( r1_tarski(B_1170,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_1170,'#skF_2')
      | ~ v3_pre_topc(B_1170,'#skF_1')
      | ~ m1_subset_1(B_1170,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_70,c_114436])).

tff(c_115961,plain,(
    ! [B_1202] :
      ( r1_tarski(B_1202,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_1202,'#skF_2')
      | ~ v3_pre_topc(B_1202,'#skF_1')
      | ~ m1_subset_1(B_1202,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_114449])).

tff(c_115980,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_115961])).

tff(c_115993,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108901,c_10,c_115980])).

tff(c_116000,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_115993,c_6])).

tff(c_116010,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113891,c_116000])).

tff(c_62,plain,(
    ! [A_60,B_62] :
      ( k7_subset_1(u1_struct_0(A_60),k2_pre_topc(A_60,B_62),k1_tops_1(A_60,B_62)) = k2_tops_1(A_60,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_116043,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_116010,c_62])).

tff(c_116047,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_116043])).

tff(c_116049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109055,c_116047])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.42/18.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.42/18.36  
% 27.42/18.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.42/18.36  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 27.42/18.36  
% 27.42/18.36  %Foreground sorts:
% 27.42/18.36  
% 27.42/18.36  
% 27.42/18.36  %Background operators:
% 27.42/18.36  
% 27.42/18.36  
% 27.42/18.36  %Foreground operators:
% 27.42/18.36  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 27.42/18.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.42/18.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.42/18.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 27.42/18.36  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 27.42/18.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.42/18.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 27.42/18.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 27.42/18.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.42/18.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 27.42/18.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 27.42/18.36  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 27.42/18.36  tff('#skF_2', type, '#skF_2': $i).
% 27.42/18.36  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 27.42/18.36  tff('#skF_1', type, '#skF_1': $i).
% 27.42/18.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.42/18.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.42/18.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.42/18.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 27.42/18.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.42/18.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 27.42/18.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 27.42/18.36  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 27.42/18.36  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 27.42/18.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.42/18.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 27.42/18.36  
% 27.59/18.39  tff(f_176, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 27.59/18.39  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 27.59/18.39  tff(f_55, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 27.59/18.39  tff(f_43, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 27.59/18.39  tff(f_96, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 27.59/18.39  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 27.59/18.39  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 27.59/18.39  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 27.59/18.39  tff(f_114, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 27.59/18.39  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 27.59/18.39  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 27.59/18.39  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 27.59/18.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 27.59/18.39  tff(f_59, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 27.59/18.39  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 27.59/18.39  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 27.59/18.39  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 27.59/18.39  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 27.59/18.39  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.59/18.39  tff(f_164, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 27.59/18.39  tff(f_102, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 27.59/18.39  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 27.59/18.39  tff(f_129, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 27.59/18.39  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 27.59/18.39  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 27.59/18.39  tff(c_82, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 27.59/18.39  tff(c_122, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_82])).
% 27.59/18.39  tff(c_76, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 27.59/18.39  tff(c_311, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_76])).
% 27.59/18.39  tff(c_109, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k2_xboole_0(A_83, B_84))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 27.59/18.39  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 27.59/18.39  tff(c_114, plain, (![A_83]: (r1_tarski(k1_xboole_0, A_83))), inference(superposition, [status(thm), theory('equality')], [c_109, c_22])).
% 27.59/18.39  tff(c_16, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 27.59/18.39  tff(c_119, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_109])).
% 27.59/18.39  tff(c_46, plain, (![A_45]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 27.59/18.39  tff(c_24, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_57])).
% 27.59/18.39  tff(c_1779, plain, (![A_158, B_159]: (k4_xboole_0(A_158, B_159)=k3_subset_1(A_158, B_159) | ~m1_subset_1(B_159, k1_zfmisc_1(A_158)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 27.59/18.39  tff(c_1788, plain, (![A_45]: (k4_xboole_0(A_45, k1_xboole_0)=k3_subset_1(A_45, k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_1779])).
% 27.59/18.39  tff(c_1792, plain, (![A_45]: (k3_subset_1(A_45, k1_xboole_0)=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1788])).
% 27.59/18.39  tff(c_1994, plain, (![A_165, B_166]: (m1_subset_1(k3_subset_1(A_165, B_166), k1_zfmisc_1(A_165)) | ~m1_subset_1(B_166, k1_zfmisc_1(A_165)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 27.59/18.39  tff(c_2003, plain, (![A_45]: (m1_subset_1(A_45, k1_zfmisc_1(A_45)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_1792, c_1994])).
% 27.59/18.39  tff(c_2008, plain, (![A_167]: (m1_subset_1(A_167, k1_zfmisc_1(A_167)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2003])).
% 27.59/18.39  tff(c_34, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k3_subset_1(A_29, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 27.59/18.39  tff(c_2011, plain, (![A_167]: (k4_xboole_0(A_167, A_167)=k3_subset_1(A_167, A_167))), inference(resolution, [status(thm)], [c_2008, c_34])).
% 27.59/18.39  tff(c_2016, plain, (![A_167]: (k3_subset_1(A_167, A_167)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_2011])).
% 27.59/18.39  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 27.59/18.39  tff(c_70, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 27.59/18.39  tff(c_4322, plain, (![A_236, B_237]: (m1_subset_1(k2_pre_topc(A_236, B_237), k1_zfmisc_1(u1_struct_0(A_236))) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236))), inference(cnfTransformation, [status(thm)], [f_114])).
% 27.59/18.39  tff(c_42, plain, (![A_38, B_39, C_40]: (k7_subset_1(A_38, B_39, C_40)=k4_xboole_0(B_39, C_40) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 27.59/18.39  tff(c_41813, plain, (![A_621, B_622, C_623]: (k7_subset_1(u1_struct_0(A_621), k2_pre_topc(A_621, B_622), C_623)=k4_xboole_0(k2_pre_topc(A_621, B_622), C_623) | ~m1_subset_1(B_622, k1_zfmisc_1(u1_struct_0(A_621))) | ~l1_pre_topc(A_621))), inference(resolution, [status(thm)], [c_4322, c_42])).
% 27.59/18.39  tff(c_41828, plain, (![C_623]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_623)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_623) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_41813])).
% 27.59/18.39  tff(c_42572, plain, (![C_626]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_626)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_626))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_41828])).
% 27.59/18.39  tff(c_42586, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42572, c_122])).
% 27.59/18.39  tff(c_30, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k2_xboole_0(A_25, B_26))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 27.59/18.39  tff(c_820, plain, (![A_121, B_122]: (k4_xboole_0(A_121, k4_xboole_0(A_121, B_122))=k3_xboole_0(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_67])).
% 27.59/18.39  tff(c_870, plain, (![A_25, B_26]: (k3_xboole_0(A_25, k2_xboole_0(A_25, B_26))=k4_xboole_0(A_25, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_820])).
% 27.59/18.39  tff(c_883, plain, (![A_25, B_26]: (k3_xboole_0(A_25, k2_xboole_0(A_25, B_26))=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_870])).
% 27.59/18.39  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 27.59/18.39  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.59/18.39  tff(c_986, plain, (![A_128, B_129]: (k4_xboole_0(k2_xboole_0(A_128, B_129), B_129)=k4_xboole_0(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_59])).
% 27.59/18.39  tff(c_1029, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_986])).
% 27.59/18.39  tff(c_32, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 27.59/18.39  tff(c_365, plain, (![A_97, B_98]: (k3_xboole_0(A_97, B_98)=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.59/18.39  tff(c_376, plain, (![A_17, B_18]: (k3_xboole_0(k4_xboole_0(A_17, B_18), A_17)=k4_xboole_0(A_17, B_18))), inference(resolution, [status(thm)], [c_22, c_365])).
% 27.59/18.39  tff(c_780, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.59/18.39  tff(c_2548, plain, (![A_185, B_186]: (k5_xboole_0(A_185, k3_xboole_0(B_186, A_185))=k4_xboole_0(A_185, B_186))), inference(superposition, [status(thm), theory('equality')], [c_4, c_780])).
% 27.59/18.39  tff(c_2561, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k4_xboole_0(A_17, k4_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_376, c_2548])).
% 27.59/18.39  tff(c_15489, plain, (![A_407, B_408]: (k5_xboole_0(A_407, k4_xboole_0(A_407, B_408))=k3_xboole_0(A_407, B_408))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2561])).
% 27.59/18.39  tff(c_15510, plain, (![B_2, A_1]: (k5_xboole_0(k2_xboole_0(B_2, A_1), k4_xboole_0(A_1, B_2))=k3_xboole_0(k2_xboole_0(B_2, A_1), B_2))), inference(superposition, [status(thm), theory('equality')], [c_1029, c_15489])).
% 27.59/18.39  tff(c_15563, plain, (![B_2, A_1]: (k5_xboole_0(k2_xboole_0(B_2, A_1), k4_xboole_0(A_1, B_2))=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_883, c_4, c_15510])).
% 27.59/18.39  tff(c_1199, plain, (![A_136, C_137, B_138]: (r1_tarski(A_136, C_137) | ~r1_tarski(B_138, C_137) | ~r1_tarski(A_136, B_138))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.59/18.39  tff(c_2605, plain, (![A_187, A_188, B_189]: (r1_tarski(A_187, A_188) | ~r1_tarski(A_187, k4_xboole_0(A_188, B_189)))), inference(resolution, [status(thm)], [c_22, c_1199])).
% 27.59/18.39  tff(c_2669, plain, (![A_188, B_189, B_18]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_188, B_189), B_18), A_188))), inference(resolution, [status(thm)], [c_22, c_2605])).
% 27.59/18.39  tff(c_26, plain, (![A_20, B_21]: (k4_xboole_0(k2_xboole_0(A_20, B_21), B_21)=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 27.59/18.39  tff(c_2998, plain, (![A_199, B_200, C_201]: (r1_tarski(A_199, k2_xboole_0(B_200, C_201)) | ~r1_tarski(k4_xboole_0(A_199, B_200), C_201))), inference(cnfTransformation, [status(thm)], [f_63])).
% 27.59/18.39  tff(c_22367, plain, (![A_476, B_477, C_478]: (r1_tarski(k2_xboole_0(A_476, B_477), k2_xboole_0(B_477, C_478)) | ~r1_tarski(k4_xboole_0(A_476, B_477), C_478))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2998])).
% 27.59/18.39  tff(c_22517, plain, (![A_1, B_2, C_478]: (r1_tarski(k2_xboole_0(A_1, B_2), k2_xboole_0(A_1, C_478)) | ~r1_tarski(k4_xboole_0(B_2, A_1), C_478))), inference(superposition, [status(thm), theory('equality')], [c_2, c_22367])).
% 27.59/18.39  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 27.59/18.39  tff(c_3253, plain, (![A_204, B_205]: (r1_tarski(A_204, k2_xboole_0(B_205, k4_xboole_0(A_204, B_205))))), inference(resolution, [status(thm)], [c_10, c_2998])).
% 27.59/18.39  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 27.59/18.39  tff(c_106099, plain, (![B_958, A_959]: (k2_xboole_0(B_958, k4_xboole_0(A_959, B_958))=A_959 | ~r1_tarski(k2_xboole_0(B_958, k4_xboole_0(A_959, B_958)), A_959))), inference(resolution, [status(thm)], [c_3253, c_6])).
% 27.59/18.39  tff(c_106109, plain, (![A_1, C_478]: (k2_xboole_0(A_1, k4_xboole_0(k2_xboole_0(A_1, C_478), A_1))=k2_xboole_0(A_1, C_478) | ~r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(A_1, C_478), A_1), A_1), C_478))), inference(resolution, [status(thm)], [c_22517, c_106099])).
% 27.59/18.39  tff(c_106543, plain, (![A_960, C_961]: (k2_xboole_0(A_960, k4_xboole_0(C_961, A_960))=k2_xboole_0(A_960, C_961))), inference(demodulation, [status(thm), theory('equality')], [c_2669, c_1029, c_1029, c_106109])).
% 27.59/18.39  tff(c_1052, plain, (![A_130, B_131]: (k3_xboole_0(A_130, k2_xboole_0(A_130, B_131))=A_130)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_870])).
% 27.59/18.39  tff(c_1096, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k2_xboole_0(A_1, B_2))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1052])).
% 27.59/18.39  tff(c_2567, plain, (![A_1, B_2]: (k5_xboole_0(k2_xboole_0(A_1, B_2), B_2)=k4_xboole_0(k2_xboole_0(A_1, B_2), B_2))), inference(superposition, [status(thm), theory('equality')], [c_1096, c_2548])).
% 27.59/18.39  tff(c_2597, plain, (![A_1, B_2]: (k5_xboole_0(k2_xboole_0(A_1, B_2), B_2)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2567])).
% 27.59/18.39  tff(c_106909, plain, (![A_960, C_961]: (k5_xboole_0(k2_xboole_0(A_960, C_961), k4_xboole_0(C_961, A_960))=k4_xboole_0(A_960, k4_xboole_0(C_961, A_960)))), inference(superposition, [status(thm), theory('equality')], [c_106543, c_2597])).
% 27.59/18.39  tff(c_107486, plain, (![A_962, C_963]: (k4_xboole_0(A_962, k4_xboole_0(C_963, A_962))=A_962)), inference(demodulation, [status(thm), theory('equality')], [c_15563, c_106909])).
% 27.59/18.39  tff(c_107908, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_42586, c_107486])).
% 27.59/18.39  tff(c_3740, plain, (![A_217, B_218, C_219]: (k7_subset_1(A_217, B_218, C_219)=k4_xboole_0(B_218, C_219) | ~m1_subset_1(B_218, k1_zfmisc_1(A_217)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 27.59/18.39  tff(c_3754, plain, (![C_219]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_219)=k4_xboole_0('#skF_2', C_219))), inference(resolution, [status(thm)], [c_70, c_3740])).
% 27.59/18.39  tff(c_5431, plain, (![A_267, B_268]: (k7_subset_1(u1_struct_0(A_267), B_268, k2_tops_1(A_267, B_268))=k1_tops_1(A_267, B_268) | ~m1_subset_1(B_268, k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267))), inference(cnfTransformation, [status(thm)], [f_164])).
% 27.59/18.39  tff(c_5444, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_5431])).
% 27.59/18.39  tff(c_5455, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3754, c_5444])).
% 27.59/18.39  tff(c_108219, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_107908, c_5455])).
% 27.59/18.39  tff(c_52, plain, (![A_48, B_49]: (m1_subset_1(A_48, k1_zfmisc_1(B_49)) | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_102])).
% 27.59/18.39  tff(c_15067, plain, (![B_403, A_404]: (k4_xboole_0(B_403, A_404)=k3_subset_1(B_403, A_404) | ~r1_tarski(A_404, B_403))), inference(resolution, [status(thm)], [c_52, c_1779])).
% 27.59/18.39  tff(c_15235, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_subset_1(A_17, k4_xboole_0(A_17, B_18)))), inference(resolution, [status(thm)], [c_22, c_15067])).
% 27.59/18.39  tff(c_15304, plain, (![A_405, B_406]: (k3_subset_1(A_405, k4_xboole_0(A_405, B_406))=k3_xboole_0(A_405, B_406))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_15235])).
% 27.59/18.39  tff(c_15337, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5455, c_15304])).
% 27.59/18.39  tff(c_744, plain, (![B_115, A_116]: (B_115=A_116 | ~r1_tarski(B_115, A_116) | ~r1_tarski(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_35])).
% 27.59/18.39  tff(c_13835, plain, (![A_386, B_387]: (k4_xboole_0(A_386, B_387)=A_386 | ~r1_tarski(A_386, k4_xboole_0(A_386, B_387)))), inference(resolution, [status(thm)], [c_22, c_744])).
% 27.59/18.39  tff(c_13847, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5455, c_13835])).
% 27.59/18.39  tff(c_13897, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5455, c_13847])).
% 27.59/18.39  tff(c_56167, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_13897])).
% 27.59/18.39  tff(c_486, plain, (![A_104, B_105]: (k2_xboole_0(A_104, B_105)=B_105 | ~r1_tarski(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_41])).
% 27.59/18.39  tff(c_541, plain, (![A_107, B_108]: (k2_xboole_0(k4_xboole_0(A_107, B_108), A_107)=A_107)), inference(resolution, [status(thm)], [c_22, c_486])).
% 27.59/18.39  tff(c_577, plain, (![A_1, B_108]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_108))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_541])).
% 27.59/18.39  tff(c_5506, plain, (k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_5455, c_577])).
% 27.59/18.39  tff(c_5500, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5455, c_32])).
% 27.59/18.39  tff(c_73933, plain, (![A_805, A_806]: (r1_tarski(k2_xboole_0(A_805, A_806), A_806) | ~r1_tarski(k4_xboole_0(A_805, A_806), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_22367])).
% 27.59/18.39  tff(c_73935, plain, (r1_tarski(k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5500, c_73933])).
% 27.59/18.39  tff(c_74092, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5506, c_73935])).
% 27.59/18.39  tff(c_74093, plain, (~r1_tarski(k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_56167, c_74092])).
% 27.59/18.39  tff(c_98591, plain, (~r1_tarski(k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_15337, c_74093])).
% 27.59/18.39  tff(c_108479, plain, (~r1_tarski(k3_subset_1('#skF_2', '#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108219, c_98591])).
% 27.59/18.39  tff(c_108530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_2016, c_108479])).
% 27.59/18.39  tff(c_108531, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_13897])).
% 27.59/18.39  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 27.59/18.39  tff(c_4824, plain, (![A_249, B_250]: (v3_pre_topc(k1_tops_1(A_249, B_250), A_249) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_129])).
% 27.59/18.39  tff(c_4837, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_4824])).
% 27.59/18.39  tff(c_4847, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4837])).
% 27.59/18.39  tff(c_108563, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_108531, c_4847])).
% 27.59/18.39  tff(c_108592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_311, c_108563])).
% 27.59/18.39  tff(c_108593, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_76])).
% 27.59/18.39  tff(c_108900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_108593])).
% 27.59/18.39  tff(c_108901, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_82])).
% 27.59/18.39  tff(c_109055, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_108901, c_76])).
% 27.59/18.39  tff(c_112098, plain, (![A_1103, B_1104, C_1105]: (k7_subset_1(A_1103, B_1104, C_1105)=k4_xboole_0(B_1104, C_1105) | ~m1_subset_1(B_1104, k1_zfmisc_1(A_1103)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 27.59/18.39  tff(c_112112, plain, (![C_1105]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_1105)=k4_xboole_0('#skF_2', C_1105))), inference(resolution, [status(thm)], [c_70, c_112098])).
% 27.59/18.39  tff(c_113819, plain, (![A_1156, B_1157]: (k7_subset_1(u1_struct_0(A_1156), B_1157, k2_tops_1(A_1156, B_1157))=k1_tops_1(A_1156, B_1157) | ~m1_subset_1(B_1157, k1_zfmisc_1(u1_struct_0(A_1156))) | ~l1_pre_topc(A_1156))), inference(cnfTransformation, [status(thm)], [f_164])).
% 27.59/18.39  tff(c_113832, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_113819])).
% 27.59/18.39  tff(c_113843, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_112112, c_113832])).
% 27.59/18.39  tff(c_113891, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_113843, c_22])).
% 27.59/18.39  tff(c_114436, plain, (![B_1170, A_1171, C_1172]: (r1_tarski(B_1170, k1_tops_1(A_1171, C_1172)) | ~r1_tarski(B_1170, C_1172) | ~v3_pre_topc(B_1170, A_1171) | ~m1_subset_1(C_1172, k1_zfmisc_1(u1_struct_0(A_1171))) | ~m1_subset_1(B_1170, k1_zfmisc_1(u1_struct_0(A_1171))) | ~l1_pre_topc(A_1171))), inference(cnfTransformation, [status(thm)], [f_150])).
% 27.59/18.39  tff(c_114449, plain, (![B_1170]: (r1_tarski(B_1170, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_1170, '#skF_2') | ~v3_pre_topc(B_1170, '#skF_1') | ~m1_subset_1(B_1170, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_114436])).
% 27.59/18.39  tff(c_115961, plain, (![B_1202]: (r1_tarski(B_1202, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_1202, '#skF_2') | ~v3_pre_topc(B_1202, '#skF_1') | ~m1_subset_1(B_1202, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_114449])).
% 27.59/18.39  tff(c_115980, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_115961])).
% 27.59/18.39  tff(c_115993, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108901, c_10, c_115980])).
% 27.59/18.39  tff(c_116000, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_115993, c_6])).
% 27.59/18.39  tff(c_116010, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_113891, c_116000])).
% 27.59/18.39  tff(c_62, plain, (![A_60, B_62]: (k7_subset_1(u1_struct_0(A_60), k2_pre_topc(A_60, B_62), k1_tops_1(A_60, B_62))=k2_tops_1(A_60, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_136])).
% 27.59/18.39  tff(c_116043, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_116010, c_62])).
% 27.59/18.39  tff(c_116047, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_116043])).
% 27.59/18.39  tff(c_116049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109055, c_116047])).
% 27.59/18.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.59/18.39  
% 27.59/18.39  Inference rules
% 27.59/18.39  ----------------------
% 27.59/18.39  #Ref     : 0
% 27.59/18.39  #Sup     : 28908
% 27.59/18.39  #Fact    : 0
% 27.59/18.39  #Define  : 0
% 27.59/18.39  #Split   : 9
% 27.59/18.39  #Chain   : 0
% 27.59/18.39  #Close   : 0
% 27.59/18.39  
% 27.59/18.39  Ordering : KBO
% 27.59/18.39  
% 27.59/18.39  Simplification rules
% 27.59/18.39  ----------------------
% 27.59/18.39  #Subsume      : 1296
% 27.59/18.39  #Demod        : 29769
% 27.59/18.39  #Tautology    : 19331
% 27.59/18.39  #SimpNegUnit  : 32
% 27.59/18.39  #BackRed      : 105
% 27.59/18.39  
% 27.59/18.39  #Partial instantiations: 0
% 27.59/18.39  #Strategies tried      : 1
% 27.59/18.39  
% 27.59/18.39  Timing (in seconds)
% 27.59/18.39  ----------------------
% 27.59/18.39  Preprocessing        : 0.37
% 27.59/18.39  Parsing              : 0.20
% 27.59/18.39  CNF conversion       : 0.03
% 27.59/18.39  Main loop            : 17.23
% 27.59/18.39  Inferencing          : 1.87
% 27.59/18.39  Reduction            : 10.82
% 27.59/18.39  Demodulation         : 9.79
% 27.59/18.39  BG Simplification    : 0.19
% 27.59/18.39  Subsumption          : 3.57
% 27.59/18.39  Abstraction          : 0.35
% 27.59/18.39  MUC search           : 0.00
% 27.59/18.39  Cooper               : 0.00
% 27.59/18.39  Total                : 17.66
% 27.59/18.39  Index Insertion      : 0.00
% 27.59/18.39  Index Deletion       : 0.00
% 27.59/18.39  Index Matching       : 0.00
% 27.59/18.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
