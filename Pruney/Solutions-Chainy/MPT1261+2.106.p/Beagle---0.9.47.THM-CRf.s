%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:27 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 195 expanded)
%              Number of leaves         :   36 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 ( 403 expanded)
%              Number of equality atoms :   46 (  98 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1416,plain,(
    ! [A_180,B_181,C_182] :
      ( k7_subset_1(A_180,B_181,C_182) = k4_xboole_0(B_181,C_182)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(A_180)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1422,plain,(
    ! [C_182] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_182) = k4_xboole_0('#skF_2',C_182) ),
    inference(resolution,[status(thm)],[c_36,c_1416])).

tff(c_48,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_104,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_178,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_717,plain,(
    ! [A_107,B_108] :
      ( k4_subset_1(u1_struct_0(A_107),B_108,k2_tops_1(A_107,B_108)) = k2_pre_topc(A_107,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_722,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_717])).

tff(c_726,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_722])).

tff(c_278,plain,(
    ! [A_74,B_75,C_76] :
      ( k7_subset_1(A_74,B_75,C_76) = k4_xboole_0(B_75,C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_285,plain,(
    ! [C_77] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_77) = k4_xboole_0('#skF_2',C_77) ),
    inference(resolution,[status(thm)],[c_36,c_278])).

tff(c_291,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_104])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_105,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,B_48) = B_48
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_127,plain,(
    ! [A_50,B_51] : k2_xboole_0(k4_xboole_0(A_50,B_51),A_50) = A_50 ),
    inference(resolution,[status(thm)],[c_16,c_105])).

tff(c_147,plain,(
    ! [A_1,B_51] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_51)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_315,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_147])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_321,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_16])).

tff(c_95,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_103,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_95])).

tff(c_190,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(A_58,C_59)
      | ~ r1_tarski(B_60,C_59)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_200,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_61,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_103,c_190])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_665,plain,(
    ! [A_105,A_106] :
      ( r1_tarski(A_105,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_105,A_106)
      | ~ r1_tarski(A_106,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_200,c_14])).

tff(c_673,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_321,c_665])).

tff(c_693,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_673])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_604,plain,(
    ! [A_96,B_97,C_98] :
      ( k4_subset_1(A_96,B_97,C_98) = k2_xboole_0(B_97,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_96))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1130,plain,(
    ! [B_140,B_141,A_142] :
      ( k4_subset_1(B_140,B_141,A_142) = k2_xboole_0(B_141,A_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(B_140))
      | ~ r1_tarski(A_142,B_140) ) ),
    inference(resolution,[status(thm)],[c_26,c_604])).

tff(c_1140,plain,(
    ! [A_143] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_143) = k2_xboole_0('#skF_2',A_143)
      | ~ r1_tarski(A_143,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_36,c_1130])).

tff(c_1152,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_693,c_1140])).

tff(c_1180,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_726,c_315,c_1152])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_390,plain,(
    ! [A_80,B_81] :
      ( v4_pre_topc(k2_pre_topc(A_80,B_81),A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_395,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_390])).

tff(c_399,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_395])).

tff(c_1190,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_399])).

tff(c_1192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_1190])).

tff(c_1193,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1193])).

tff(c_1295,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1311,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_42])).

tff(c_1439,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1422,c_1311])).

tff(c_1943,plain,(
    ! [A_233,B_234] :
      ( k4_subset_1(u1_struct_0(A_233),B_234,k2_tops_1(A_233,B_234)) = k2_pre_topc(A_233,B_234)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1948,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1943])).

tff(c_1952,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1948])).

tff(c_1809,plain,(
    ! [A_229,B_230] :
      ( r1_tarski(k2_tops_1(A_229,B_230),B_230)
      | ~ v4_pre_topc(B_230,A_229)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_pre_topc(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1814,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1809])).

tff(c_1818,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1295,c_1814])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1836,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1818,c_12])).

tff(c_1840,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1836,c_2])).

tff(c_1383,plain,(
    ! [A_173,C_174,B_175] :
      ( r1_tarski(A_173,C_174)
      | ~ r1_tarski(B_175,C_174)
      | ~ r1_tarski(A_173,B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1393,plain,(
    ! [A_176] :
      ( r1_tarski(A_176,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_176,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_103,c_1383])).

tff(c_1401,plain,(
    ! [A_9,A_176] :
      ( r1_tarski(A_9,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_9,A_176)
      | ~ r1_tarski(A_176,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1393,c_14])).

tff(c_1820,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_1818,c_1401])).

tff(c_1832,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1820])).

tff(c_1664,plain,(
    ! [A_207,B_208,C_209] :
      ( k4_subset_1(A_207,B_208,C_209) = k2_xboole_0(B_208,C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(A_207))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(A_207)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2220,plain,(
    ! [B_255,B_256,A_257] :
      ( k4_subset_1(B_255,B_256,A_257) = k2_xboole_0(B_256,A_257)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(B_255))
      | ~ r1_tarski(A_257,B_255) ) ),
    inference(resolution,[status(thm)],[c_26,c_1664])).

tff(c_2260,plain,(
    ! [A_259] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_259) = k2_xboole_0('#skF_2',A_259)
      | ~ r1_tarski(A_259,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_36,c_2220])).

tff(c_2269,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1832,c_2260])).

tff(c_2300,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_1840,c_2269])).

tff(c_30,plain,(
    ! [A_26,B_28] :
      ( k7_subset_1(u1_struct_0(A_26),k2_pre_topc(A_26,B_28),k1_tops_1(A_26,B_28)) = k2_tops_1(A_26,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2319,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2300,c_30])).

tff(c_2325,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1422,c_2319])).

tff(c_2327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1439,c_2325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.83/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.68  
% 3.83/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.69  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 3.83/1.69  
% 3.83/1.69  %Foreground sorts:
% 3.83/1.69  
% 3.83/1.69  
% 3.83/1.69  %Background operators:
% 3.83/1.69  
% 3.83/1.69  
% 3.83/1.69  %Foreground operators:
% 3.83/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.83/1.69  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.83/1.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.83/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.83/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.83/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.83/1.69  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.83/1.69  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.83/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.83/1.69  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.83/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.83/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.83/1.69  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.83/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.83/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.83/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.83/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.83/1.69  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.83/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.83/1.69  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.83/1.69  
% 4.08/1.71  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.08/1.71  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.08/1.71  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.08/1.71  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.08/1.71  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.08/1.71  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.08/1.71  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.08/1.71  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.08/1.71  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.08/1.71  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.08/1.71  tff(f_71, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 4.08/1.71  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 4.08/1.71  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.08/1.71  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.08/1.71  tff(c_1416, plain, (![A_180, B_181, C_182]: (k7_subset_1(A_180, B_181, C_182)=k4_xboole_0(B_181, C_182) | ~m1_subset_1(B_181, k1_zfmisc_1(A_180)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.08/1.71  tff(c_1422, plain, (![C_182]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_182)=k4_xboole_0('#skF_2', C_182))), inference(resolution, [status(thm)], [c_36, c_1416])).
% 4.08/1.71  tff(c_48, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.08/1.71  tff(c_104, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 4.08/1.71  tff(c_42, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.08/1.71  tff(c_178, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 4.08/1.71  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.08/1.71  tff(c_717, plain, (![A_107, B_108]: (k4_subset_1(u1_struct_0(A_107), B_108, k2_tops_1(A_107, B_108))=k2_pre_topc(A_107, B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.08/1.71  tff(c_722, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_717])).
% 4.08/1.71  tff(c_726, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_722])).
% 4.08/1.71  tff(c_278, plain, (![A_74, B_75, C_76]: (k7_subset_1(A_74, B_75, C_76)=k4_xboole_0(B_75, C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.08/1.71  tff(c_285, plain, (![C_77]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_77)=k4_xboole_0('#skF_2', C_77))), inference(resolution, [status(thm)], [c_36, c_278])).
% 4.08/1.71  tff(c_291, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_285, c_104])).
% 4.08/1.71  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.08/1.71  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.08/1.71  tff(c_105, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.08/1.71  tff(c_127, plain, (![A_50, B_51]: (k2_xboole_0(k4_xboole_0(A_50, B_51), A_50)=A_50)), inference(resolution, [status(thm)], [c_16, c_105])).
% 4.08/1.71  tff(c_147, plain, (![A_1, B_51]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_51))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_127])).
% 4.08/1.71  tff(c_315, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_291, c_147])).
% 4.08/1.71  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.08/1.71  tff(c_321, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_291, c_16])).
% 4.08/1.71  tff(c_95, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.08/1.71  tff(c_103, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_95])).
% 4.08/1.71  tff(c_190, plain, (![A_58, C_59, B_60]: (r1_tarski(A_58, C_59) | ~r1_tarski(B_60, C_59) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.08/1.71  tff(c_200, plain, (![A_61]: (r1_tarski(A_61, u1_struct_0('#skF_1')) | ~r1_tarski(A_61, '#skF_2'))), inference(resolution, [status(thm)], [c_103, c_190])).
% 4.08/1.71  tff(c_14, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.08/1.71  tff(c_665, plain, (![A_105, A_106]: (r1_tarski(A_105, u1_struct_0('#skF_1')) | ~r1_tarski(A_105, A_106) | ~r1_tarski(A_106, '#skF_2'))), inference(resolution, [status(thm)], [c_200, c_14])).
% 4.08/1.71  tff(c_673, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_321, c_665])).
% 4.08/1.71  tff(c_693, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_673])).
% 4.08/1.71  tff(c_26, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.08/1.71  tff(c_604, plain, (![A_96, B_97, C_98]: (k4_subset_1(A_96, B_97, C_98)=k2_xboole_0(B_97, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(A_96)) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.08/1.71  tff(c_1130, plain, (![B_140, B_141, A_142]: (k4_subset_1(B_140, B_141, A_142)=k2_xboole_0(B_141, A_142) | ~m1_subset_1(B_141, k1_zfmisc_1(B_140)) | ~r1_tarski(A_142, B_140))), inference(resolution, [status(thm)], [c_26, c_604])).
% 4.08/1.71  tff(c_1140, plain, (![A_143]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_143)=k2_xboole_0('#skF_2', A_143) | ~r1_tarski(A_143, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_1130])).
% 4.08/1.71  tff(c_1152, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_693, c_1140])).
% 4.08/1.71  tff(c_1180, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_726, c_315, c_1152])).
% 4.08/1.71  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.08/1.71  tff(c_390, plain, (![A_80, B_81]: (v4_pre_topc(k2_pre_topc(A_80, B_81), A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.08/1.71  tff(c_395, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_390])).
% 4.08/1.71  tff(c_399, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_395])).
% 4.08/1.71  tff(c_1190, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1180, c_399])).
% 4.08/1.71  tff(c_1192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_1190])).
% 4.08/1.71  tff(c_1193, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 4.08/1.71  tff(c_1294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_1193])).
% 4.08/1.71  tff(c_1295, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 4.08/1.71  tff(c_1311, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_42])).
% 4.08/1.71  tff(c_1439, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1422, c_1311])).
% 4.08/1.71  tff(c_1943, plain, (![A_233, B_234]: (k4_subset_1(u1_struct_0(A_233), B_234, k2_tops_1(A_233, B_234))=k2_pre_topc(A_233, B_234) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.08/1.71  tff(c_1948, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1943])).
% 4.08/1.71  tff(c_1952, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1948])).
% 4.08/1.71  tff(c_1809, plain, (![A_229, B_230]: (r1_tarski(k2_tops_1(A_229, B_230), B_230) | ~v4_pre_topc(B_230, A_229) | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0(A_229))) | ~l1_pre_topc(A_229))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.08/1.71  tff(c_1814, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1809])).
% 4.08/1.71  tff(c_1818, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1295, c_1814])).
% 4.08/1.71  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.08/1.71  tff(c_1836, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_1818, c_12])).
% 4.08/1.71  tff(c_1840, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1836, c_2])).
% 4.08/1.71  tff(c_1383, plain, (![A_173, C_174, B_175]: (r1_tarski(A_173, C_174) | ~r1_tarski(B_175, C_174) | ~r1_tarski(A_173, B_175))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.08/1.71  tff(c_1393, plain, (![A_176]: (r1_tarski(A_176, u1_struct_0('#skF_1')) | ~r1_tarski(A_176, '#skF_2'))), inference(resolution, [status(thm)], [c_103, c_1383])).
% 4.08/1.71  tff(c_1401, plain, (![A_9, A_176]: (r1_tarski(A_9, u1_struct_0('#skF_1')) | ~r1_tarski(A_9, A_176) | ~r1_tarski(A_176, '#skF_2'))), inference(resolution, [status(thm)], [c_1393, c_14])).
% 4.08/1.71  tff(c_1820, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_1818, c_1401])).
% 4.08/1.71  tff(c_1832, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1820])).
% 4.08/1.71  tff(c_1664, plain, (![A_207, B_208, C_209]: (k4_subset_1(A_207, B_208, C_209)=k2_xboole_0(B_208, C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(A_207)) | ~m1_subset_1(B_208, k1_zfmisc_1(A_207)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.08/1.71  tff(c_2220, plain, (![B_255, B_256, A_257]: (k4_subset_1(B_255, B_256, A_257)=k2_xboole_0(B_256, A_257) | ~m1_subset_1(B_256, k1_zfmisc_1(B_255)) | ~r1_tarski(A_257, B_255))), inference(resolution, [status(thm)], [c_26, c_1664])).
% 4.08/1.71  tff(c_2260, plain, (![A_259]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_259)=k2_xboole_0('#skF_2', A_259) | ~r1_tarski(A_259, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_2220])).
% 4.08/1.71  tff(c_2269, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1832, c_2260])).
% 4.08/1.71  tff(c_2300, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_1840, c_2269])).
% 4.08/1.71  tff(c_30, plain, (![A_26, B_28]: (k7_subset_1(u1_struct_0(A_26), k2_pre_topc(A_26, B_28), k1_tops_1(A_26, B_28))=k2_tops_1(A_26, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.08/1.71  tff(c_2319, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2300, c_30])).
% 4.08/1.71  tff(c_2325, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1422, c_2319])).
% 4.08/1.71  tff(c_2327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1439, c_2325])).
% 4.08/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.71  
% 4.08/1.71  Inference rules
% 4.08/1.71  ----------------------
% 4.08/1.71  #Ref     : 0
% 4.08/1.71  #Sup     : 547
% 4.08/1.71  #Fact    : 0
% 4.08/1.71  #Define  : 0
% 4.08/1.71  #Split   : 7
% 4.08/1.71  #Chain   : 0
% 4.08/1.71  #Close   : 0
% 4.08/1.71  
% 4.08/1.71  Ordering : KBO
% 4.08/1.71  
% 4.08/1.71  Simplification rules
% 4.08/1.71  ----------------------
% 4.08/1.71  #Subsume      : 49
% 4.08/1.71  #Demod        : 177
% 4.08/1.71  #Tautology    : 265
% 4.08/1.71  #SimpNegUnit  : 2
% 4.08/1.71  #BackRed      : 5
% 4.08/1.71  
% 4.08/1.71  #Partial instantiations: 0
% 4.08/1.71  #Strategies tried      : 1
% 4.08/1.71  
% 4.08/1.71  Timing (in seconds)
% 4.08/1.71  ----------------------
% 4.08/1.71  Preprocessing        : 0.33
% 4.08/1.71  Parsing              : 0.18
% 4.08/1.71  CNF conversion       : 0.02
% 4.08/1.71  Main loop            : 0.62
% 4.08/1.71  Inferencing          : 0.22
% 4.08/1.71  Reduction            : 0.21
% 4.08/1.71  Demodulation         : 0.16
% 4.08/1.71  BG Simplification    : 0.03
% 4.08/1.71  Subsumption          : 0.11
% 4.08/1.71  Abstraction          : 0.03
% 4.08/1.71  MUC search           : 0.00
% 4.08/1.71  Cooper               : 0.00
% 4.08/1.71  Total                : 0.99
% 4.08/1.71  Index Insertion      : 0.00
% 4.08/1.71  Index Deletion       : 0.00
% 4.08/1.71  Index Matching       : 0.00
% 4.08/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
