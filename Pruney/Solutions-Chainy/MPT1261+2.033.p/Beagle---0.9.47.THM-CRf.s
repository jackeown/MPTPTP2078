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
% DateTime   : Thu Dec  3 10:21:16 EST 2020

% Result     : Theorem 14.83s
% Output     : CNFRefutation 14.83s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 278 expanded)
%              Number of leaves         :   49 ( 112 expanded)
%              Depth                    :   10
%              Number of atoms          :  185 ( 491 expanded)
%              Number of equality atoms :   81 ( 172 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_95,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
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

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_20836,plain,(
    ! [A_519,B_520,C_521] :
      ( k7_subset_1(A_519,B_520,C_521) = k4_xboole_0(B_520,C_521)
      | ~ m1_subset_1(B_520,k1_zfmisc_1(A_519)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20845,plain,(
    ! [C_521] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_521) = k4_xboole_0('#skF_2',C_521) ),
    inference(resolution,[status(thm)],[c_62,c_20836])).

tff(c_74,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_148,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_214,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_4952,plain,(
    ! [A_254,B_255] :
      ( k4_subset_1(u1_struct_0(A_254),B_255,k2_tops_1(A_254,B_255)) = k2_pre_topc(A_254,B_255)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ l1_pre_topc(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4962,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_4952])).

tff(c_4968,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4962])).

tff(c_2876,plain,(
    ! [A_187,B_188,C_189] :
      ( k7_subset_1(A_187,B_188,C_189) = k4_xboole_0(B_188,C_189)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(A_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3026,plain,(
    ! [C_195] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_195) = k4_xboole_0('#skF_2',C_195) ),
    inference(resolution,[status(thm)],[c_62,c_2876])).

tff(c_3038,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_3026])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_164,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,B_80) = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_171,plain,(
    ! [A_13,B_14] : k3_xboole_0(k4_xboole_0(A_13,B_14),A_13) = k4_xboole_0(A_13,B_14) ),
    inference(resolution,[status(thm)],[c_14,c_164])).

tff(c_26,plain,(
    ! [B_29,A_28] : k2_tarski(B_29,A_28) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_149,plain,(
    ! [A_77,B_78] : k1_setfam_1(k2_tarski(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_223,plain,(
    ! [A_89,B_90] : k1_setfam_1(k2_tarski(A_89,B_90)) = k3_xboole_0(B_90,A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_149])).

tff(c_44,plain,(
    ! [A_47,B_48] : k1_setfam_1(k2_tarski(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_229,plain,(
    ! [B_90,A_89] : k3_xboole_0(B_90,A_89) = k3_xboole_0(A_89,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_44])).

tff(c_173,plain,(
    ! [A_81,B_82] : k3_tarski(k2_tarski(A_81,B_82)) = k2_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_336,plain,(
    ! [A_97,B_98] : k3_tarski(k2_tarski(A_97,B_98)) = k2_xboole_0(B_98,A_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_173])).

tff(c_28,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_342,plain,(
    ! [B_98,A_97] : k2_xboole_0(B_98,A_97) = k2_xboole_0(A_97,B_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_28])).

tff(c_24,plain,(
    ! [A_26,B_27] : k2_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_860,plain,(
    ! [A_120,B_121,C_122] : k2_xboole_0(k2_xboole_0(A_120,B_121),C_122) = k2_xboole_0(A_120,k2_xboole_0(B_121,C_122)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1101,plain,(
    ! [A_137,C_138] : k2_xboole_0(A_137,k2_xboole_0(A_137,C_138)) = k2_xboole_0(A_137,C_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_860])).

tff(c_1150,plain,(
    ! [A_26,B_27] : k2_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = k2_xboole_0(k3_xboole_0(A_26,B_27),A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1101])).

tff(c_1172,plain,(
    ! [A_139,B_140] : k2_xboole_0(A_139,k3_xboole_0(A_139,B_140)) = A_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_24,c_1150])).

tff(c_1648,plain,(
    ! [A_152,B_153] : k2_xboole_0(A_152,k3_xboole_0(B_153,A_152)) = A_152 ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_1172])).

tff(c_1698,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = A_13 ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_1648])).

tff(c_3605,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3038,c_1698])).

tff(c_1730,plain,(
    ! [A_154,B_155,C_156] :
      ( r1_tarski(A_154,k2_xboole_0(B_155,C_156))
      | ~ r1_tarski(k4_xboole_0(A_154,B_155),C_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1760,plain,(
    ! [A_157,B_158] : r1_tarski(A_157,k2_xboole_0(B_158,A_157)) ),
    inference(resolution,[status(thm)],[c_14,c_1730])).

tff(c_1801,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1760])).

tff(c_3635,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3038,c_14])).

tff(c_189,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(A_85,B_86)
      | ~ m1_subset_1(A_85,k1_zfmisc_1(B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_193,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_189])).

tff(c_558,plain,(
    ! [A_108,C_109,B_110] :
      ( r1_tarski(A_108,C_109)
      | ~ r1_tarski(B_110,C_109)
      | ~ r1_tarski(A_108,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_577,plain,(
    ! [A_111] :
      ( r1_tarski(A_111,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_111,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_193,c_558])).

tff(c_10,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_583,plain,(
    ! [A_8,A_111] :
      ( r1_tarski(A_8,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_8,A_111)
      | ~ r1_tarski(A_111,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_577,c_10])).

tff(c_3641,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_3635,c_583])).

tff(c_3649,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1801,c_3641])).

tff(c_48,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(A_49,k1_zfmisc_1(B_50))
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3756,plain,(
    ! [A_216,B_217,C_218] :
      ( k4_subset_1(A_216,B_217,C_218) = k2_xboole_0(B_217,C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(A_216))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(A_216)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_17245,plain,(
    ! [B_395,B_396,A_397] :
      ( k4_subset_1(B_395,B_396,A_397) = k2_xboole_0(B_396,A_397)
      | ~ m1_subset_1(B_396,k1_zfmisc_1(B_395))
      | ~ r1_tarski(A_397,B_395) ) ),
    inference(resolution,[status(thm)],[c_48,c_3756])).

tff(c_17996,plain,(
    ! [A_403] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_403) = k2_xboole_0('#skF_2',A_403)
      | ~ r1_tarski(A_403,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_62,c_17245])).

tff(c_18051,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3649,c_17996])).

tff(c_18126,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4968,c_3605,c_18051])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3471,plain,(
    ! [A_210,B_211] :
      ( v4_pre_topc(k2_pre_topc(A_210,B_211),A_210)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ l1_pre_topc(A_210)
      | ~ v2_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3481,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_3471])).

tff(c_3487,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3481])).

tff(c_18150,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18126,c_3487])).

tff(c_18152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_18150])).

tff(c_18153,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_18418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_18153])).

tff(c_18419,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_18482,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18419,c_68])).

tff(c_20888,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20845,c_18482])).

tff(c_22281,plain,(
    ! [A_574,B_575] :
      ( r1_tarski(k2_tops_1(A_574,B_575),B_575)
      | ~ v4_pre_topc(B_575,A_574)
      | ~ m1_subset_1(B_575,k1_zfmisc_1(u1_struct_0(A_574)))
      | ~ l1_pre_topc(A_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_22291,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_22281])).

tff(c_22297,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_18419,c_22291])).

tff(c_23575,plain,(
    ! [A_603,B_604] :
      ( k7_subset_1(u1_struct_0(A_603),B_604,k2_tops_1(A_603,B_604)) = k1_tops_1(A_603,B_604)
      | ~ m1_subset_1(B_604,k1_zfmisc_1(u1_struct_0(A_603)))
      | ~ l1_pre_topc(A_603) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_23585,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_23575])).

tff(c_23591,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20845,c_23585])).

tff(c_19449,plain,(
    ! [A_474,B_475] :
      ( k4_xboole_0(A_474,B_475) = k3_subset_1(A_474,B_475)
      | ~ m1_subset_1(B_475,k1_zfmisc_1(A_474)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_25908,plain,(
    ! [B_632,A_633] :
      ( k4_xboole_0(B_632,A_633) = k3_subset_1(B_632,A_633)
      | ~ r1_tarski(A_633,B_632) ) ),
    inference(resolution,[status(thm)],[c_48,c_19449])).

tff(c_25971,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22297,c_25908])).

tff(c_26086,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23591,c_25971])).

tff(c_20082,plain,(
    ! [A_499,B_500] :
      ( k3_subset_1(A_499,k3_subset_1(A_499,B_500)) = B_500
      | ~ m1_subset_1(B_500,k1_zfmisc_1(A_499)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20090,plain,(
    ! [B_50,A_49] :
      ( k3_subset_1(B_50,k3_subset_1(B_50,A_49)) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_48,c_20082])).

tff(c_26741,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26086,c_20090])).

tff(c_26749,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22297,c_26741])).

tff(c_18446,plain,(
    ! [A_425,B_426] : k1_setfam_1(k2_tarski(A_425,B_426)) = k3_xboole_0(A_425,B_426) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18496,plain,(
    ! [B_431,A_432] : k1_setfam_1(k2_tarski(B_431,A_432)) = k3_xboole_0(A_432,B_431) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_18446])).

tff(c_18502,plain,(
    ! [B_431,A_432] : k3_xboole_0(B_431,A_432) = k3_xboole_0(A_432,B_431) ),
    inference(superposition,[status(thm),theory(equality)],[c_18496,c_44])).

tff(c_18421,plain,(
    ! [A_419,B_420] :
      ( k3_xboole_0(A_419,B_420) = A_419
      | ~ r1_tarski(A_419,B_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18428,plain,(
    ! [A_13,B_14] : k3_xboole_0(k4_xboole_0(A_13,B_14),A_13) = k4_xboole_0(A_13,B_14) ),
    inference(resolution,[status(thm)],[c_14,c_18421])).

tff(c_23857,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_23591,c_18428])).

tff(c_23870,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23591,c_18502,c_23857])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18854,plain,(
    ! [A_454,B_455] : k3_xboole_0(k3_xboole_0(A_454,B_455),A_454) = k3_xboole_0(A_454,B_455) ),
    inference(resolution,[status(thm)],[c_6,c_18421])).

tff(c_28406,plain,(
    ! [A_673,B_674] : k3_xboole_0(A_673,k3_xboole_0(A_673,B_674)) = k3_xboole_0(A_673,B_674) ),
    inference(superposition,[status(thm),theory(equality)],[c_18854,c_18502])).

tff(c_28517,plain,(
    ! [A_673,B_674] : k5_xboole_0(A_673,k3_xboole_0(A_673,B_674)) = k4_xboole_0(A_673,k3_xboole_0(A_673,B_674)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28406,c_4])).

tff(c_28619,plain,(
    ! [A_673,B_674] : k4_xboole_0(A_673,k3_xboole_0(A_673,B_674)) = k4_xboole_0(A_673,B_674) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_28517])).

tff(c_26121,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k3_subset_1(A_5,k3_xboole_0(A_5,B_6)) ),
    inference(resolution,[status(thm)],[c_6,c_25908])).

tff(c_59270,plain,(
    ! [A_941,B_942] : k3_subset_1(A_941,k3_xboole_0(A_941,B_942)) = k4_xboole_0(A_941,B_942) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28619,c_26121])).

tff(c_59409,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23870,c_59270])).

tff(c_59483,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26749,c_59409])).

tff(c_59485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20888,c_59483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.83/7.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.83/7.75  
% 14.83/7.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.83/7.76  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 14.83/7.76  
% 14.83/7.76  %Foreground sorts:
% 14.83/7.76  
% 14.83/7.76  
% 14.83/7.76  %Background operators:
% 14.83/7.76  
% 14.83/7.76  
% 14.83/7.76  %Foreground operators:
% 14.83/7.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.83/7.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.83/7.76  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 14.83/7.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.83/7.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.83/7.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.83/7.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.83/7.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.83/7.76  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.83/7.76  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.83/7.76  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 14.83/7.76  tff('#skF_2', type, '#skF_2': $i).
% 14.83/7.76  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 14.83/7.76  tff('#skF_1', type, '#skF_1': $i).
% 14.83/7.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.83/7.76  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 14.83/7.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.83/7.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.83/7.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.83/7.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.83/7.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.83/7.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.83/7.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.83/7.76  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.83/7.76  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 14.83/7.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.83/7.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.83/7.76  
% 14.83/7.78  tff(f_155, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 14.83/7.78  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 14.83/7.78  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 14.83/7.78  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.83/7.78  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.83/7.78  tff(f_63, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 14.83/7.78  tff(f_95, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 14.83/7.78  tff(f_65, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 14.83/7.78  tff(f_61, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 14.83/7.78  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 14.83/7.78  tff(f_59, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 14.83/7.78  tff(f_57, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 14.83/7.78  tff(f_99, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.83/7.78  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 14.83/7.78  tff(f_85, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 14.83/7.78  tff(f_113, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 14.83/7.78  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 14.83/7.78  tff(f_143, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 14.83/7.78  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 14.83/7.78  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 14.83/7.78  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.83/7.78  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 14.83/7.78  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 14.83/7.78  tff(c_20836, plain, (![A_519, B_520, C_521]: (k7_subset_1(A_519, B_520, C_521)=k4_xboole_0(B_520, C_521) | ~m1_subset_1(B_520, k1_zfmisc_1(A_519)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.83/7.78  tff(c_20845, plain, (![C_521]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_521)=k4_xboole_0('#skF_2', C_521))), inference(resolution, [status(thm)], [c_62, c_20836])).
% 14.83/7.78  tff(c_74, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 14.83/7.78  tff(c_148, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_74])).
% 14.83/7.78  tff(c_68, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 14.83/7.78  tff(c_214, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_68])).
% 14.83/7.78  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 14.83/7.78  tff(c_4952, plain, (![A_254, B_255]: (k4_subset_1(u1_struct_0(A_254), B_255, k2_tops_1(A_254, B_255))=k2_pre_topc(A_254, B_255) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_254))) | ~l1_pre_topc(A_254))), inference(cnfTransformation, [status(thm)], [f_127])).
% 14.83/7.78  tff(c_4962, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_4952])).
% 14.83/7.78  tff(c_4968, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4962])).
% 14.83/7.78  tff(c_2876, plain, (![A_187, B_188, C_189]: (k7_subset_1(A_187, B_188, C_189)=k4_xboole_0(B_188, C_189) | ~m1_subset_1(B_188, k1_zfmisc_1(A_187)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.83/7.78  tff(c_3026, plain, (![C_195]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_195)=k4_xboole_0('#skF_2', C_195))), inference(resolution, [status(thm)], [c_62, c_2876])).
% 14.83/7.78  tff(c_3038, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_148, c_3026])).
% 14.83/7.78  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.83/7.78  tff(c_164, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.83/7.78  tff(c_171, plain, (![A_13, B_14]: (k3_xboole_0(k4_xboole_0(A_13, B_14), A_13)=k4_xboole_0(A_13, B_14))), inference(resolution, [status(thm)], [c_14, c_164])).
% 14.83/7.78  tff(c_26, plain, (![B_29, A_28]: (k2_tarski(B_29, A_28)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.83/7.78  tff(c_149, plain, (![A_77, B_78]: (k1_setfam_1(k2_tarski(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.83/7.78  tff(c_223, plain, (![A_89, B_90]: (k1_setfam_1(k2_tarski(A_89, B_90))=k3_xboole_0(B_90, A_89))), inference(superposition, [status(thm), theory('equality')], [c_26, c_149])).
% 14.83/7.78  tff(c_44, plain, (![A_47, B_48]: (k1_setfam_1(k2_tarski(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.83/7.78  tff(c_229, plain, (![B_90, A_89]: (k3_xboole_0(B_90, A_89)=k3_xboole_0(A_89, B_90))), inference(superposition, [status(thm), theory('equality')], [c_223, c_44])).
% 14.83/7.78  tff(c_173, plain, (![A_81, B_82]: (k3_tarski(k2_tarski(A_81, B_82))=k2_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.83/7.78  tff(c_336, plain, (![A_97, B_98]: (k3_tarski(k2_tarski(A_97, B_98))=k2_xboole_0(B_98, A_97))), inference(superposition, [status(thm), theory('equality')], [c_26, c_173])).
% 14.83/7.78  tff(c_28, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.83/7.78  tff(c_342, plain, (![B_98, A_97]: (k2_xboole_0(B_98, A_97)=k2_xboole_0(A_97, B_98))), inference(superposition, [status(thm), theory('equality')], [c_336, c_28])).
% 14.83/7.78  tff(c_24, plain, (![A_26, B_27]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.83/7.78  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.83/7.78  tff(c_860, plain, (![A_120, B_121, C_122]: (k2_xboole_0(k2_xboole_0(A_120, B_121), C_122)=k2_xboole_0(A_120, k2_xboole_0(B_121, C_122)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.83/7.78  tff(c_1101, plain, (![A_137, C_138]: (k2_xboole_0(A_137, k2_xboole_0(A_137, C_138))=k2_xboole_0(A_137, C_138))), inference(superposition, [status(thm), theory('equality')], [c_2, c_860])).
% 14.83/7.78  tff(c_1150, plain, (![A_26, B_27]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=k2_xboole_0(k3_xboole_0(A_26, B_27), A_26))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1101])).
% 14.83/7.78  tff(c_1172, plain, (![A_139, B_140]: (k2_xboole_0(A_139, k3_xboole_0(A_139, B_140))=A_139)), inference(demodulation, [status(thm), theory('equality')], [c_342, c_24, c_1150])).
% 14.83/7.78  tff(c_1648, plain, (![A_152, B_153]: (k2_xboole_0(A_152, k3_xboole_0(B_153, A_152))=A_152)), inference(superposition, [status(thm), theory('equality')], [c_229, c_1172])).
% 14.83/7.78  tff(c_1698, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(A_13, B_14))=A_13)), inference(superposition, [status(thm), theory('equality')], [c_171, c_1648])).
% 14.83/7.78  tff(c_3605, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3038, c_1698])).
% 14.83/7.78  tff(c_1730, plain, (![A_154, B_155, C_156]: (r1_tarski(A_154, k2_xboole_0(B_155, C_156)) | ~r1_tarski(k4_xboole_0(A_154, B_155), C_156))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.83/7.78  tff(c_1760, plain, (![A_157, B_158]: (r1_tarski(A_157, k2_xboole_0(B_158, A_157)))), inference(resolution, [status(thm)], [c_14, c_1730])).
% 14.83/7.78  tff(c_1801, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1760])).
% 14.83/7.78  tff(c_3635, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3038, c_14])).
% 14.83/7.78  tff(c_189, plain, (![A_85, B_86]: (r1_tarski(A_85, B_86) | ~m1_subset_1(A_85, k1_zfmisc_1(B_86)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.83/7.78  tff(c_193, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_189])).
% 14.83/7.78  tff(c_558, plain, (![A_108, C_109, B_110]: (r1_tarski(A_108, C_109) | ~r1_tarski(B_110, C_109) | ~r1_tarski(A_108, B_110))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.83/7.78  tff(c_577, plain, (![A_111]: (r1_tarski(A_111, u1_struct_0('#skF_1')) | ~r1_tarski(A_111, '#skF_2'))), inference(resolution, [status(thm)], [c_193, c_558])).
% 14.83/7.78  tff(c_10, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.83/7.78  tff(c_583, plain, (![A_8, A_111]: (r1_tarski(A_8, u1_struct_0('#skF_1')) | ~r1_tarski(A_8, A_111) | ~r1_tarski(A_111, '#skF_2'))), inference(resolution, [status(thm)], [c_577, c_10])).
% 14.83/7.78  tff(c_3641, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_3635, c_583])).
% 14.83/7.78  tff(c_3649, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1801, c_3641])).
% 14.83/7.78  tff(c_48, plain, (![A_49, B_50]: (m1_subset_1(A_49, k1_zfmisc_1(B_50)) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.83/7.78  tff(c_3756, plain, (![A_216, B_217, C_218]: (k4_subset_1(A_216, B_217, C_218)=k2_xboole_0(B_217, C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(A_216)) | ~m1_subset_1(B_217, k1_zfmisc_1(A_216)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.83/7.78  tff(c_17245, plain, (![B_395, B_396, A_397]: (k4_subset_1(B_395, B_396, A_397)=k2_xboole_0(B_396, A_397) | ~m1_subset_1(B_396, k1_zfmisc_1(B_395)) | ~r1_tarski(A_397, B_395))), inference(resolution, [status(thm)], [c_48, c_3756])).
% 14.83/7.78  tff(c_17996, plain, (![A_403]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_403)=k2_xboole_0('#skF_2', A_403) | ~r1_tarski(A_403, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_62, c_17245])).
% 14.83/7.78  tff(c_18051, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3649, c_17996])).
% 14.83/7.78  tff(c_18126, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4968, c_3605, c_18051])).
% 14.83/7.78  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 14.83/7.78  tff(c_3471, plain, (![A_210, B_211]: (v4_pre_topc(k2_pre_topc(A_210, B_211), A_210) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_210))) | ~l1_pre_topc(A_210) | ~v2_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.83/7.78  tff(c_3481, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_3471])).
% 14.83/7.78  tff(c_3487, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3481])).
% 14.83/7.78  tff(c_18150, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18126, c_3487])).
% 14.83/7.78  tff(c_18152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_18150])).
% 14.83/7.78  tff(c_18153, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_68])).
% 14.83/7.78  tff(c_18418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_18153])).
% 14.83/7.78  tff(c_18419, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_74])).
% 14.83/7.78  tff(c_18482, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18419, c_68])).
% 14.83/7.78  tff(c_20888, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20845, c_18482])).
% 14.83/7.78  tff(c_22281, plain, (![A_574, B_575]: (r1_tarski(k2_tops_1(A_574, B_575), B_575) | ~v4_pre_topc(B_575, A_574) | ~m1_subset_1(B_575, k1_zfmisc_1(u1_struct_0(A_574))) | ~l1_pre_topc(A_574))), inference(cnfTransformation, [status(thm)], [f_136])).
% 14.83/7.78  tff(c_22291, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_22281])).
% 14.83/7.78  tff(c_22297, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_18419, c_22291])).
% 14.83/7.78  tff(c_23575, plain, (![A_603, B_604]: (k7_subset_1(u1_struct_0(A_603), B_604, k2_tops_1(A_603, B_604))=k1_tops_1(A_603, B_604) | ~m1_subset_1(B_604, k1_zfmisc_1(u1_struct_0(A_603))) | ~l1_pre_topc(A_603))), inference(cnfTransformation, [status(thm)], [f_143])).
% 14.83/7.78  tff(c_23585, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_23575])).
% 14.83/7.78  tff(c_23591, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_20845, c_23585])).
% 14.83/7.78  tff(c_19449, plain, (![A_474, B_475]: (k4_xboole_0(A_474, B_475)=k3_subset_1(A_474, B_475) | ~m1_subset_1(B_475, k1_zfmisc_1(A_474)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.83/7.78  tff(c_25908, plain, (![B_632, A_633]: (k4_xboole_0(B_632, A_633)=k3_subset_1(B_632, A_633) | ~r1_tarski(A_633, B_632))), inference(resolution, [status(thm)], [c_48, c_19449])).
% 14.83/7.78  tff(c_25971, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22297, c_25908])).
% 14.83/7.78  tff(c_26086, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_23591, c_25971])).
% 14.83/7.78  tff(c_20082, plain, (![A_499, B_500]: (k3_subset_1(A_499, k3_subset_1(A_499, B_500))=B_500 | ~m1_subset_1(B_500, k1_zfmisc_1(A_499)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.83/7.78  tff(c_20090, plain, (![B_50, A_49]: (k3_subset_1(B_50, k3_subset_1(B_50, A_49))=A_49 | ~r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_48, c_20082])).
% 14.83/7.78  tff(c_26741, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26086, c_20090])).
% 14.83/7.78  tff(c_26749, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22297, c_26741])).
% 14.83/7.78  tff(c_18446, plain, (![A_425, B_426]: (k1_setfam_1(k2_tarski(A_425, B_426))=k3_xboole_0(A_425, B_426))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.83/7.78  tff(c_18496, plain, (![B_431, A_432]: (k1_setfam_1(k2_tarski(B_431, A_432))=k3_xboole_0(A_432, B_431))), inference(superposition, [status(thm), theory('equality')], [c_26, c_18446])).
% 14.83/7.78  tff(c_18502, plain, (![B_431, A_432]: (k3_xboole_0(B_431, A_432)=k3_xboole_0(A_432, B_431))), inference(superposition, [status(thm), theory('equality')], [c_18496, c_44])).
% 14.83/7.78  tff(c_18421, plain, (![A_419, B_420]: (k3_xboole_0(A_419, B_420)=A_419 | ~r1_tarski(A_419, B_420))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.83/7.78  tff(c_18428, plain, (![A_13, B_14]: (k3_xboole_0(k4_xboole_0(A_13, B_14), A_13)=k4_xboole_0(A_13, B_14))), inference(resolution, [status(thm)], [c_14, c_18421])).
% 14.83/7.78  tff(c_23857, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_23591, c_18428])).
% 14.83/7.78  tff(c_23870, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_23591, c_18502, c_23857])).
% 14.83/7.78  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.83/7.78  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.83/7.78  tff(c_18854, plain, (![A_454, B_455]: (k3_xboole_0(k3_xboole_0(A_454, B_455), A_454)=k3_xboole_0(A_454, B_455))), inference(resolution, [status(thm)], [c_6, c_18421])).
% 14.83/7.78  tff(c_28406, plain, (![A_673, B_674]: (k3_xboole_0(A_673, k3_xboole_0(A_673, B_674))=k3_xboole_0(A_673, B_674))), inference(superposition, [status(thm), theory('equality')], [c_18854, c_18502])).
% 14.83/7.78  tff(c_28517, plain, (![A_673, B_674]: (k5_xboole_0(A_673, k3_xboole_0(A_673, B_674))=k4_xboole_0(A_673, k3_xboole_0(A_673, B_674)))), inference(superposition, [status(thm), theory('equality')], [c_28406, c_4])).
% 14.83/7.78  tff(c_28619, plain, (![A_673, B_674]: (k4_xboole_0(A_673, k3_xboole_0(A_673, B_674))=k4_xboole_0(A_673, B_674))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_28517])).
% 14.83/7.78  tff(c_26121, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k3_subset_1(A_5, k3_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_6, c_25908])).
% 14.83/7.78  tff(c_59270, plain, (![A_941, B_942]: (k3_subset_1(A_941, k3_xboole_0(A_941, B_942))=k4_xboole_0(A_941, B_942))), inference(demodulation, [status(thm), theory('equality')], [c_28619, c_26121])).
% 14.83/7.78  tff(c_59409, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_23870, c_59270])).
% 14.83/7.78  tff(c_59483, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26749, c_59409])).
% 14.83/7.78  tff(c_59485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20888, c_59483])).
% 14.83/7.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.83/7.78  
% 14.83/7.78  Inference rules
% 14.83/7.78  ----------------------
% 14.83/7.78  #Ref     : 0
% 14.83/7.78  #Sup     : 14546
% 14.83/7.78  #Fact    : 0
% 14.83/7.78  #Define  : 0
% 14.83/7.78  #Split   : 5
% 14.83/7.78  #Chain   : 0
% 14.83/7.78  #Close   : 0
% 14.83/7.78  
% 14.83/7.78  Ordering : KBO
% 14.83/7.78  
% 14.83/7.78  Simplification rules
% 14.83/7.78  ----------------------
% 14.83/7.78  #Subsume      : 475
% 14.83/7.78  #Demod        : 13572
% 14.83/7.78  #Tautology    : 9957
% 14.83/7.78  #SimpNegUnit  : 2
% 14.83/7.78  #BackRed      : 20
% 14.83/7.78  
% 14.83/7.78  #Partial instantiations: 0
% 14.83/7.78  #Strategies tried      : 1
% 14.83/7.78  
% 14.83/7.78  Timing (in seconds)
% 14.83/7.78  ----------------------
% 14.83/7.78  Preprocessing        : 0.34
% 14.83/7.78  Parsing              : 0.18
% 14.83/7.78  CNF conversion       : 0.02
% 14.83/7.78  Main loop            : 6.62
% 14.83/7.78  Inferencing          : 1.12
% 14.83/7.78  Reduction            : 3.77
% 14.83/7.78  Demodulation         : 3.32
% 14.83/7.78  BG Simplification    : 0.12
% 14.83/7.78  Subsumption          : 1.27
% 14.83/7.78  Abstraction          : 0.21
% 14.83/7.78  MUC search           : 0.00
% 14.83/7.78  Cooper               : 0.00
% 14.83/7.78  Total                : 7.00
% 14.83/7.78  Index Insertion      : 0.00
% 14.83/7.78  Index Deletion       : 0.00
% 14.83/7.78  Index Matching       : 0.00
% 14.83/7.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
