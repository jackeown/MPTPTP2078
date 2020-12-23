%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:31 EST 2020

% Result     : Theorem 26.87s
% Output     : CNFRefutation 27.11s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 866 expanded)
%              Number of leaves         :   38 ( 306 expanded)
%              Depth                    :   28
%              Number of atoms          :  213 (1171 expanded)
%              Number of equality atoms :  125 ( 643 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_117,negated_conjecture,(
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

tff(f_76,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_82,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_115387,plain,(
    ! [A_783,B_784,C_785] :
      ( k7_subset_1(A_783,B_784,C_785) = k4_xboole_0(B_784,C_785)
      | ~ m1_subset_1(B_784,k1_zfmisc_1(A_783)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_115390,plain,(
    ! [C_785] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_785) = k4_xboole_0('#skF_2',C_785) ),
    inference(resolution,[status(thm)],[c_40,c_115387])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_127,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1495,plain,(
    ! [B_105,A_106] :
      ( v4_pre_topc(B_105,A_106)
      | k2_pre_topc(A_106,B_105) != B_105
      | ~ v2_pre_topc(A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1501,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1495])).

tff(c_1505,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1501])).

tff(c_1506,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_1505])).

tff(c_1979,plain,(
    ! [A_115,B_116] :
      ( k4_subset_1(u1_struct_0(A_115),B_116,k2_tops_1(A_115,B_116)) = k2_pre_topc(A_115,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1983,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1979])).

tff(c_1987,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1983])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k2_tops_1(A_28,B_29),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1014,plain,(
    ! [A_93,B_94,C_95] :
      ( k4_subset_1(A_93,B_94,C_95) = k2_xboole_0(B_94,C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(A_93))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_9407,plain,(
    ! [A_255,B_256,B_257] :
      ( k4_subset_1(u1_struct_0(A_255),B_256,k2_tops_1(A_255,B_257)) = k2_xboole_0(B_256,k2_tops_1(A_255,B_257))
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255) ) ),
    inference(resolution,[status(thm)],[c_32,c_1014])).

tff(c_9411,plain,(
    ! [B_257] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_257)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_257))
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_9407])).

tff(c_9692,plain,(
    ! [B_261] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_261)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_261))
      | ~ m1_subset_1(B_261,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_9411])).

tff(c_9699,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_9692])).

tff(c_9704,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1987,c_9699])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_161,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_169,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_161])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_189,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,B_48) = B_48
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_128,plain,(
    ! [A_49,B_50] : k2_xboole_0(k4_xboole_0(A_49,B_50),A_49) = A_49 ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_135,plain,(
    ! [B_50] : k4_xboole_0(k1_xboole_0,B_50) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_14])).

tff(c_222,plain,(
    ! [B_59] : k3_xboole_0(k1_xboole_0,B_59) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_135])).

tff(c_244,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_222])).

tff(c_349,plain,(
    ! [A_64,B_65] : r1_tarski(k3_xboole_0(A_64,B_65),A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_18])).

tff(c_378,plain,(
    ! [B_66] : r1_tarski(k1_xboole_0,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_349])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_390,plain,(
    ! [B_66] : k2_xboole_0(k1_xboole_0,B_66) = B_66 ),
    inference(resolution,[status(thm)],[c_378,c_12])).

tff(c_305,plain,(
    ! [A_61,B_62,C_63] : k4_xboole_0(k4_xboole_0(A_61,B_62),C_63) = k4_xboole_0(A_61,k2_xboole_0(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2684,plain,(
    ! [A_126,B_127,C_128] : r1_tarski(k4_xboole_0(A_126,k2_xboole_0(B_127,C_128)),k4_xboole_0(A_126,B_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_18])).

tff(c_2773,plain,(
    ! [A_129,B_130] : r1_tarski(k4_xboole_0(A_129,B_130),k4_xboole_0(A_129,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_2684])).

tff(c_2831,plain,(
    ! [A_131,B_132] : r1_tarski(k3_xboole_0(A_131,B_132),k4_xboole_0(A_131,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2773])).

tff(c_2921,plain,(
    ! [B_133] : r1_tarski(B_133,k4_xboole_0(B_133,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_2831])).

tff(c_170,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_175,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,k4_xboole_0(A_12,B_13)) ) ),
    inference(resolution,[status(thm)],[c_18,c_170])).

tff(c_2944,plain,(
    ! [B_133] : k4_xboole_0(B_133,k1_xboole_0) = B_133 ),
    inference(resolution,[status(thm)],[c_2921,c_175])).

tff(c_2973,plain,(
    ! [B_134] : k4_xboole_0(B_134,k1_xboole_0) = B_134 ),
    inference(resolution,[status(thm)],[c_2921,c_175])).

tff(c_3006,plain,(
    ! [B_134] : k4_xboole_0(B_134,B_134) = k3_xboole_0(B_134,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2973,c_22])).

tff(c_3050,plain,(
    ! [B_135] : k4_xboole_0(B_135,B_135) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_3006])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k4_xboole_0(A_14,B_15),C_16) = k4_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3081,plain,(
    ! [B_135,C_16] : k4_xboole_0(B_135,k2_xboole_0(B_135,C_16)) = k4_xboole_0(k1_xboole_0,C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_3050,c_20])).

tff(c_4035,plain,(
    ! [B_150,C_151] : k4_xboole_0(B_150,k2_xboole_0(B_150,C_151)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_3081])).

tff(c_4074,plain,(
    ! [B_150,C_151] : k3_xboole_0(B_150,k2_xboole_0(B_150,C_151)) = k4_xboole_0(B_150,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4035,c_22])).

tff(c_4136,plain,(
    ! [B_150,C_151] : k3_xboole_0(B_150,k2_xboole_0(B_150,C_151)) = B_150 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2944,c_4074])).

tff(c_11050,plain,(
    k3_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_9704,c_4136])).

tff(c_391,plain,(
    ! [A_67,B_68,C_69] :
      ( k7_subset_1(A_67,B_68,C_69) = k4_xboole_0(B_68,C_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_580,plain,(
    ! [C_80] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_80) = k4_xboole_0('#skF_2',C_80) ),
    inference(resolution,[status(thm)],[c_40,c_391])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_253,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_52])).

tff(c_586,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_253])).

tff(c_124,plain,(
    ! [A_12,B_13] : k2_xboole_0(k4_xboole_0(A_12,B_13),A_12) = A_12 ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_3038,plain,(
    ! [B_134] : k4_xboole_0(B_134,B_134) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_3006])).

tff(c_168,plain,(
    ! [A_12,B_13] : k3_xboole_0(k4_xboole_0(A_12,B_13),A_12) = k4_xboole_0(A_12,B_13) ),
    inference(resolution,[status(thm)],[c_18,c_161])).

tff(c_596,plain,(
    ! [A_81,B_82] : k3_xboole_0(k4_xboole_0(A_81,B_82),A_81) = k4_xboole_0(A_81,B_82) ),
    inference(resolution,[status(thm)],[c_18,c_161])).

tff(c_618,plain,(
    ! [A_81,B_82] : k3_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_2])).

tff(c_192,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,k4_xboole_0(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_22])).

tff(c_3170,plain,(
    ! [A_136,B_137] : k4_xboole_0(A_136,k3_xboole_0(A_136,B_137)) = k4_xboole_0(A_136,B_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_192])).

tff(c_3258,plain,(
    ! [A_12,B_13] : k4_xboole_0(k4_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = k4_xboole_0(k4_xboole_0(A_12,B_13),A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_3170])).

tff(c_3566,plain,(
    ! [A_142,B_143] : k4_xboole_0(A_142,k2_xboole_0(B_143,A_142)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3038,c_20,c_3258])).

tff(c_3603,plain,(
    ! [A_142,B_143] : k3_xboole_0(A_142,k2_xboole_0(B_143,A_142)) = k4_xboole_0(A_142,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3566,c_22])).

tff(c_3718,plain,(
    ! [A_144,B_145] : k3_xboole_0(A_144,k2_xboole_0(B_145,A_144)) = A_144 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2944,c_3603])).

tff(c_488,plain,(
    ! [A_74,B_75] : k2_xboole_0(k3_xboole_0(A_74,B_75),A_74) = A_74 ),
    inference(resolution,[status(thm)],[c_349,c_12])).

tff(c_513,plain,(
    ! [A_1,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_2),B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_488])).

tff(c_3771,plain,(
    ! [A_144,B_145] : k2_xboole_0(A_144,k2_xboole_0(B_145,A_144)) = k2_xboole_0(B_145,A_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_3718,c_513])).

tff(c_327,plain,(
    ! [A_14,B_15,C_16,C_63] : k4_xboole_0(k4_xboole_0(A_14,k2_xboole_0(B_15,C_16)),C_63) = k4_xboole_0(k4_xboole_0(A_14,B_15),k2_xboole_0(C_16,C_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_305])).

tff(c_344,plain,(
    ! [A_14,B_15,C_16,C_63] : k4_xboole_0(A_14,k2_xboole_0(k2_xboole_0(B_15,C_16),C_63)) = k4_xboole_0(A_14,k2_xboole_0(B_15,k2_xboole_0(C_16,C_63))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_327])).

tff(c_3306,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(B_13,A_12)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3038,c_20,c_3258])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_337,plain,(
    ! [A_61,B_62,B_18] : k4_xboole_0(A_61,k2_xboole_0(B_62,k4_xboole_0(k4_xboole_0(A_61,B_62),B_18))) = k3_xboole_0(k4_xboole_0(A_61,B_62),B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_305])).

tff(c_7544,plain,(
    ! [A_204,B_205,B_206] : k4_xboole_0(A_204,k2_xboole_0(B_205,k4_xboole_0(A_204,k2_xboole_0(B_205,B_206)))) = k3_xboole_0(k4_xboole_0(A_204,B_205),B_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_337])).

tff(c_7734,plain,(
    ! [A_14,B_15,B_205,B_206] : k4_xboole_0(k4_xboole_0(A_14,B_15),k2_xboole_0(B_205,k4_xboole_0(A_14,k2_xboole_0(B_15,k2_xboole_0(B_205,B_206))))) = k3_xboole_0(k4_xboole_0(k4_xboole_0(A_14,B_15),B_205),B_206) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_7544])).

tff(c_87357,plain,(
    ! [A_666,B_667,B_668,B_669] : k4_xboole_0(k4_xboole_0(A_666,B_667),k2_xboole_0(B_668,k4_xboole_0(A_666,k2_xboole_0(B_667,k2_xboole_0(B_668,B_669))))) = k3_xboole_0(k4_xboole_0(A_666,k2_xboole_0(B_667,B_668)),B_669) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_7734])).

tff(c_88255,plain,(
    ! [A_666,B_668,B_669] : k4_xboole_0(k4_xboole_0(A_666,k2_xboole_0(B_668,B_669)),k2_xboole_0(B_668,k4_xboole_0(A_666,k2_xboole_0(B_668,B_669)))) = k3_xboole_0(k4_xboole_0(A_666,k2_xboole_0(k2_xboole_0(B_668,B_669),B_668)),B_669) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_87357])).

tff(c_88482,plain,(
    ! [B_670,A_671,B_672] : k3_xboole_0(B_670,k4_xboole_0(A_671,k2_xboole_0(B_670,B_672))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3771,c_344,c_3306,c_2,c_88255])).

tff(c_424,plain,(
    ! [A_71,B_72] : r1_tarski(k3_xboole_0(A_71,B_72),B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_349])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1305,plain,(
    ! [A_103,B_104] : k3_xboole_0(k3_xboole_0(A_103,B_104),B_104) = k3_xboole_0(A_103,B_104) ),
    inference(resolution,[status(thm)],[c_424,c_16])).

tff(c_1507,plain,(
    ! [A_107,B_108] : k3_xboole_0(k3_xboole_0(A_107,B_108),A_107) = k3_xboole_0(B_108,A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1305])).

tff(c_1567,plain,(
    ! [A_107,B_108] : k3_xboole_0(A_107,k3_xboole_0(A_107,B_108)) = k3_xboole_0(B_108,A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_1507,c_2])).

tff(c_88872,plain,(
    ! [A_671,B_670,B_672] : k3_xboole_0(k4_xboole_0(A_671,k2_xboole_0(B_670,B_672)),B_670) = k3_xboole_0(B_670,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_88482,c_1567])).

tff(c_90161,plain,(
    ! [A_676,B_677,B_678] : k3_xboole_0(k4_xboole_0(A_676,k2_xboole_0(B_677,B_678)),B_677) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_88872])).

tff(c_100971,plain,(
    ! [A_706,A_707,B_708] : k3_xboole_0(k4_xboole_0(A_706,A_707),k4_xboole_0(A_707,B_708)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_90161])).

tff(c_105564,plain,(
    ! [A_718] : k3_xboole_0(k4_xboole_0(A_718,'#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_100971])).

tff(c_3169,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_192])).

tff(c_314,plain,(
    ! [A_61,B_62,C_63] : k4_xboole_0(k4_xboole_0(A_61,B_62),k4_xboole_0(A_61,k2_xboole_0(B_62,C_63))) = k3_xboole_0(k4_xboole_0(A_61,B_62),C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_22])).

tff(c_7568,plain,(
    ! [A_204,B_205,B_206] : k4_xboole_0(k4_xboole_0(A_204,B_205),k3_xboole_0(k4_xboole_0(A_204,B_205),B_206)) = k3_xboole_0(k4_xboole_0(A_204,B_205),k4_xboole_0(A_204,k2_xboole_0(B_205,B_206))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7544,c_314])).

tff(c_7758,plain,(
    ! [A_204,B_205,B_206] : k3_xboole_0(k4_xboole_0(A_204,B_205),k4_xboole_0(A_204,k2_xboole_0(B_205,B_206))) = k4_xboole_0(A_204,k2_xboole_0(B_205,B_206)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3169,c_7568])).

tff(c_346,plain,(
    ! [A_61,B_62,B_18] : k4_xboole_0(A_61,k2_xboole_0(B_62,k4_xboole_0(A_61,k2_xboole_0(B_62,B_18)))) = k3_xboole_0(k4_xboole_0(A_61,B_62),B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_337])).

tff(c_7547,plain,(
    ! [A_204,B_205,B_206] : k4_xboole_0(A_204,k2_xboole_0(B_205,k3_xboole_0(k4_xboole_0(A_204,B_205),B_206))) = k3_xboole_0(k4_xboole_0(A_204,B_205),k4_xboole_0(A_204,k2_xboole_0(B_205,B_206))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7544,c_346])).

tff(c_60397,plain,(
    ! [A_204,B_205,B_206] : k4_xboole_0(A_204,k2_xboole_0(B_205,k3_xboole_0(k4_xboole_0(A_204,B_205),B_206))) = k4_xboole_0(A_204,k2_xboole_0(B_205,B_206)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7758,c_7547])).

tff(c_105695,plain,(
    ! [A_718] : k4_xboole_0(A_718,k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k4_xboole_0(A_718,k2_xboole_0('#skF_2',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_105564,c_60397])).

tff(c_114060,plain,(
    ! [A_758] : k4_xboole_0(A_758,k2_pre_topc('#skF_1','#skF_2')) = k4_xboole_0(A_758,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9704,c_14,c_105695])).

tff(c_114480,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_114060,c_3038])).

tff(c_449,plain,(
    ! [A_71,B_72] : k3_xboole_0(k3_xboole_0(A_71,B_72),B_72) = k3_xboole_0(A_71,B_72) ),
    inference(resolution,[status(thm)],[c_424,c_16])).

tff(c_3240,plain,(
    ! [A_71,B_72] : k4_xboole_0(k3_xboole_0(A_71,B_72),k3_xboole_0(A_71,B_72)) = k4_xboole_0(k3_xboole_0(A_71,B_72),B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_3170])).

tff(c_3301,plain,(
    ! [A_71,B_72] : k4_xboole_0(k3_xboole_0(A_71,B_72),B_72) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3038,c_3240])).

tff(c_4351,plain,(
    ! [A_156,B_157,C_158] : k4_xboole_0(A_156,k2_xboole_0(k4_xboole_0(A_156,B_157),C_158)) = k4_xboole_0(k3_xboole_0(A_156,B_157),C_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_305])).

tff(c_32036,plain,(
    ! [A_408,B_409,C_410] : k4_xboole_0(A_408,k4_xboole_0(k3_xboole_0(A_408,B_409),C_410)) = k3_xboole_0(A_408,k2_xboole_0(k4_xboole_0(A_408,B_409),C_410)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4351,c_22])).

tff(c_32408,plain,(
    ! [A_71,B_72] : k3_xboole_0(A_71,k2_xboole_0(k4_xboole_0(A_71,B_72),B_72)) = k4_xboole_0(A_71,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3301,c_32036])).

tff(c_33499,plain,(
    ! [A_415,B_416] : k3_xboole_0(A_415,k2_xboole_0(k4_xboole_0(A_415,B_416),B_416)) = A_415 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2944,c_32408])).

tff(c_1412,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1305])).

tff(c_33718,plain,(
    ! [A_415,B_416] : k3_xboole_0(k2_xboole_0(k4_xboole_0(A_415,B_416),B_416),A_415) = k3_xboole_0(A_415,A_415) ),
    inference(superposition,[status(thm),theory(equality)],[c_33499,c_1412])).

tff(c_34008,plain,(
    ! [A_415,B_416] : k3_xboole_0(k2_xboole_0(k4_xboole_0(A_415,B_416),B_416),A_415) = A_415 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_33718])).

tff(c_114821,plain,(
    k3_xboole_0(k2_xboole_0(k1_xboole_0,'#skF_2'),k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_114480,c_34008])).

tff(c_114992,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11050,c_390,c_114821])).

tff(c_114994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1506,c_114992])).

tff(c_114995,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_115442,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115390,c_114995])).

tff(c_114996,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_115746,plain,(
    ! [A_801,B_802] :
      ( r1_tarski(k2_tops_1(A_801,B_802),B_802)
      | ~ v4_pre_topc(B_802,A_801)
      | ~ m1_subset_1(B_802,k1_zfmisc_1(u1_struct_0(A_801)))
      | ~ l1_pre_topc(A_801) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_115750,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_115746])).

tff(c_115754,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_114996,c_115750])).

tff(c_115764,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_115754,c_16])).

tff(c_115791,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_115764,c_2])).

tff(c_116737,plain,(
    ! [A_825,B_826] :
      ( k7_subset_1(u1_struct_0(A_825),B_826,k2_tops_1(A_825,B_826)) = k1_tops_1(A_825,B_826)
      | ~ m1_subset_1(B_826,k1_zfmisc_1(u1_struct_0(A_825)))
      | ~ l1_pre_topc(A_825) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_116741,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_116737])).

tff(c_116745,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_115390,c_116741])).

tff(c_116758,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_116745,c_22])).

tff(c_116769,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115791,c_116758])).

tff(c_116771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115442,c_116769])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:38:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.87/19.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.87/19.03  
% 26.87/19.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.87/19.03  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 26.87/19.03  
% 26.87/19.03  %Foreground sorts:
% 26.87/19.03  
% 26.87/19.03  
% 26.87/19.03  %Background operators:
% 26.87/19.03  
% 26.87/19.03  
% 26.87/19.03  %Foreground operators:
% 26.87/19.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.87/19.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.87/19.03  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 26.87/19.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.87/19.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 26.87/19.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.87/19.03  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 26.87/19.03  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 26.87/19.03  tff('#skF_2', type, '#skF_2': $i).
% 26.87/19.03  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 26.87/19.03  tff('#skF_1', type, '#skF_1': $i).
% 26.87/19.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 26.87/19.03  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 26.87/19.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.87/19.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.87/19.03  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 26.87/19.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 26.87/19.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 26.87/19.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 26.87/19.03  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 26.87/19.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.87/19.03  
% 27.11/19.06  tff(f_117, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 27.11/19.06  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 27.11/19.06  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 27.11/19.06  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 27.11/19.06  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 27.11/19.06  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 27.11/19.06  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.11/19.06  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 27.11/19.06  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 27.11/19.06  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 27.11/19.06  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 27.11/19.06  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 27.11/19.06  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 27.11/19.06  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 27.11/19.06  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 27.11/19.06  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 27.11/19.06  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 27.11/19.06  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 27.11/19.06  tff(c_115387, plain, (![A_783, B_784, C_785]: (k7_subset_1(A_783, B_784, C_785)=k4_xboole_0(B_784, C_785) | ~m1_subset_1(B_784, k1_zfmisc_1(A_783)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 27.11/19.06  tff(c_115390, plain, (![C_785]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_785)=k4_xboole_0('#skF_2', C_785))), inference(resolution, [status(thm)], [c_40, c_115387])).
% 27.11/19.06  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 27.11/19.06  tff(c_127, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 27.11/19.06  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 27.11/19.06  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 27.11/19.06  tff(c_1495, plain, (![B_105, A_106]: (v4_pre_topc(B_105, A_106) | k2_pre_topc(A_106, B_105)!=B_105 | ~v2_pre_topc(A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_76])).
% 27.11/19.06  tff(c_1501, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1495])).
% 27.11/19.06  tff(c_1505, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1501])).
% 27.11/19.06  tff(c_1506, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_127, c_1505])).
% 27.11/19.06  tff(c_1979, plain, (![A_115, B_116]: (k4_subset_1(u1_struct_0(A_115), B_116, k2_tops_1(A_115, B_116))=k2_pre_topc(A_115, B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_89])).
% 27.11/19.06  tff(c_1983, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1979])).
% 27.11/19.06  tff(c_1987, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1983])).
% 27.11/19.06  tff(c_32, plain, (![A_28, B_29]: (m1_subset_1(k2_tops_1(A_28, B_29), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_82])).
% 27.11/19.06  tff(c_1014, plain, (![A_93, B_94, C_95]: (k4_subset_1(A_93, B_94, C_95)=k2_xboole_0(B_94, C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(A_93)) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 27.11/19.06  tff(c_9407, plain, (![A_255, B_256, B_257]: (k4_subset_1(u1_struct_0(A_255), B_256, k2_tops_1(A_255, B_257))=k2_xboole_0(B_256, k2_tops_1(A_255, B_257)) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255))), inference(resolution, [status(thm)], [c_32, c_1014])).
% 27.11/19.06  tff(c_9411, plain, (![B_257]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_257))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_257)) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_9407])).
% 27.11/19.06  tff(c_9692, plain, (![B_261]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_261))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_261)) | ~m1_subset_1(B_261, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_9411])).
% 27.11/19.06  tff(c_9699, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_9692])).
% 27.11/19.06  tff(c_9704, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1987, c_9699])).
% 27.11/19.06  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 27.11/19.06  tff(c_161, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 27.11/19.06  tff(c_169, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_161])).
% 27.11/19.06  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 27.11/19.06  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.11/19.06  tff(c_189, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_51])).
% 27.11/19.06  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 27.11/19.06  tff(c_117, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_39])).
% 27.11/19.06  tff(c_128, plain, (![A_49, B_50]: (k2_xboole_0(k4_xboole_0(A_49, B_50), A_49)=A_49)), inference(resolution, [status(thm)], [c_18, c_117])).
% 27.11/19.06  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 27.11/19.06  tff(c_135, plain, (![B_50]: (k4_xboole_0(k1_xboole_0, B_50)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_128, c_14])).
% 27.11/19.06  tff(c_222, plain, (![B_59]: (k3_xboole_0(k1_xboole_0, B_59)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_189, c_135])).
% 27.11/19.06  tff(c_244, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_222])).
% 27.11/19.06  tff(c_349, plain, (![A_64, B_65]: (r1_tarski(k3_xboole_0(A_64, B_65), A_64))), inference(superposition, [status(thm), theory('equality')], [c_189, c_18])).
% 27.11/19.06  tff(c_378, plain, (![B_66]: (r1_tarski(k1_xboole_0, B_66))), inference(superposition, [status(thm), theory('equality')], [c_244, c_349])).
% 27.11/19.06  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 27.11/19.06  tff(c_390, plain, (![B_66]: (k2_xboole_0(k1_xboole_0, B_66)=B_66)), inference(resolution, [status(thm)], [c_378, c_12])).
% 27.11/19.06  tff(c_305, plain, (![A_61, B_62, C_63]: (k4_xboole_0(k4_xboole_0(A_61, B_62), C_63)=k4_xboole_0(A_61, k2_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.11/19.06  tff(c_2684, plain, (![A_126, B_127, C_128]: (r1_tarski(k4_xboole_0(A_126, k2_xboole_0(B_127, C_128)), k4_xboole_0(A_126, B_127)))), inference(superposition, [status(thm), theory('equality')], [c_305, c_18])).
% 27.11/19.06  tff(c_2773, plain, (![A_129, B_130]: (r1_tarski(k4_xboole_0(A_129, B_130), k4_xboole_0(A_129, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_390, c_2684])).
% 27.11/19.06  tff(c_2831, plain, (![A_131, B_132]: (r1_tarski(k3_xboole_0(A_131, B_132), k4_xboole_0(A_131, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2773])).
% 27.11/19.06  tff(c_2921, plain, (![B_133]: (r1_tarski(B_133, k4_xboole_0(B_133, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_169, c_2831])).
% 27.11/19.06  tff(c_170, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 27.11/19.06  tff(c_175, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, k4_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_18, c_170])).
% 27.11/19.06  tff(c_2944, plain, (![B_133]: (k4_xboole_0(B_133, k1_xboole_0)=B_133)), inference(resolution, [status(thm)], [c_2921, c_175])).
% 27.11/19.06  tff(c_2973, plain, (![B_134]: (k4_xboole_0(B_134, k1_xboole_0)=B_134)), inference(resolution, [status(thm)], [c_2921, c_175])).
% 27.11/19.06  tff(c_3006, plain, (![B_134]: (k4_xboole_0(B_134, B_134)=k3_xboole_0(B_134, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2973, c_22])).
% 27.11/19.06  tff(c_3050, plain, (![B_135]: (k4_xboole_0(B_135, B_135)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_244, c_3006])).
% 27.11/19.06  tff(c_20, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k4_xboole_0(A_14, B_15), C_16)=k4_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.11/19.06  tff(c_3081, plain, (![B_135, C_16]: (k4_xboole_0(B_135, k2_xboole_0(B_135, C_16))=k4_xboole_0(k1_xboole_0, C_16))), inference(superposition, [status(thm), theory('equality')], [c_3050, c_20])).
% 27.11/19.06  tff(c_4035, plain, (![B_150, C_151]: (k4_xboole_0(B_150, k2_xboole_0(B_150, C_151))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_3081])).
% 27.11/19.06  tff(c_4074, plain, (![B_150, C_151]: (k3_xboole_0(B_150, k2_xboole_0(B_150, C_151))=k4_xboole_0(B_150, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4035, c_22])).
% 27.11/19.06  tff(c_4136, plain, (![B_150, C_151]: (k3_xboole_0(B_150, k2_xboole_0(B_150, C_151))=B_150)), inference(demodulation, [status(thm), theory('equality')], [c_2944, c_4074])).
% 27.11/19.06  tff(c_11050, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_9704, c_4136])).
% 27.11/19.06  tff(c_391, plain, (![A_67, B_68, C_69]: (k7_subset_1(A_67, B_68, C_69)=k4_xboole_0(B_68, C_69) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 27.11/19.06  tff(c_580, plain, (![C_80]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_80)=k4_xboole_0('#skF_2', C_80))), inference(resolution, [status(thm)], [c_40, c_391])).
% 27.11/19.06  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 27.11/19.06  tff(c_253, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_127, c_52])).
% 27.11/19.06  tff(c_586, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_580, c_253])).
% 27.11/19.06  tff(c_124, plain, (![A_12, B_13]: (k2_xboole_0(k4_xboole_0(A_12, B_13), A_12)=A_12)), inference(resolution, [status(thm)], [c_18, c_117])).
% 27.11/19.06  tff(c_3038, plain, (![B_134]: (k4_xboole_0(B_134, B_134)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_244, c_3006])).
% 27.11/19.06  tff(c_168, plain, (![A_12, B_13]: (k3_xboole_0(k4_xboole_0(A_12, B_13), A_12)=k4_xboole_0(A_12, B_13))), inference(resolution, [status(thm)], [c_18, c_161])).
% 27.11/19.06  tff(c_596, plain, (![A_81, B_82]: (k3_xboole_0(k4_xboole_0(A_81, B_82), A_81)=k4_xboole_0(A_81, B_82))), inference(resolution, [status(thm)], [c_18, c_161])).
% 27.11/19.06  tff(c_618, plain, (![A_81, B_82]: (k3_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(superposition, [status(thm), theory('equality')], [c_596, c_2])).
% 27.11/19.06  tff(c_192, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k3_xboole_0(A_57, k4_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_22])).
% 27.11/19.06  tff(c_3170, plain, (![A_136, B_137]: (k4_xboole_0(A_136, k3_xboole_0(A_136, B_137))=k4_xboole_0(A_136, B_137))), inference(demodulation, [status(thm), theory('equality')], [c_618, c_192])).
% 27.11/19.06  tff(c_3258, plain, (![A_12, B_13]: (k4_xboole_0(k4_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=k4_xboole_0(k4_xboole_0(A_12, B_13), A_12))), inference(superposition, [status(thm), theory('equality')], [c_168, c_3170])).
% 27.11/19.06  tff(c_3566, plain, (![A_142, B_143]: (k4_xboole_0(A_142, k2_xboole_0(B_143, A_142))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3038, c_20, c_3258])).
% 27.11/19.06  tff(c_3603, plain, (![A_142, B_143]: (k3_xboole_0(A_142, k2_xboole_0(B_143, A_142))=k4_xboole_0(A_142, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3566, c_22])).
% 27.11/19.06  tff(c_3718, plain, (![A_144, B_145]: (k3_xboole_0(A_144, k2_xboole_0(B_145, A_144))=A_144)), inference(demodulation, [status(thm), theory('equality')], [c_2944, c_3603])).
% 27.11/19.06  tff(c_488, plain, (![A_74, B_75]: (k2_xboole_0(k3_xboole_0(A_74, B_75), A_74)=A_74)), inference(resolution, [status(thm)], [c_349, c_12])).
% 27.11/19.06  tff(c_513, plain, (![A_1, B_2]: (k2_xboole_0(k3_xboole_0(A_1, B_2), B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_488])).
% 27.11/19.06  tff(c_3771, plain, (![A_144, B_145]: (k2_xboole_0(A_144, k2_xboole_0(B_145, A_144))=k2_xboole_0(B_145, A_144))), inference(superposition, [status(thm), theory('equality')], [c_3718, c_513])).
% 27.11/19.06  tff(c_327, plain, (![A_14, B_15, C_16, C_63]: (k4_xboole_0(k4_xboole_0(A_14, k2_xboole_0(B_15, C_16)), C_63)=k4_xboole_0(k4_xboole_0(A_14, B_15), k2_xboole_0(C_16, C_63)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_305])).
% 27.11/19.06  tff(c_344, plain, (![A_14, B_15, C_16, C_63]: (k4_xboole_0(A_14, k2_xboole_0(k2_xboole_0(B_15, C_16), C_63))=k4_xboole_0(A_14, k2_xboole_0(B_15, k2_xboole_0(C_16, C_63))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_327])).
% 27.11/19.06  tff(c_3306, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(B_13, A_12))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3038, c_20, c_3258])).
% 27.11/19.06  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 27.11/19.06  tff(c_337, plain, (![A_61, B_62, B_18]: (k4_xboole_0(A_61, k2_xboole_0(B_62, k4_xboole_0(k4_xboole_0(A_61, B_62), B_18)))=k3_xboole_0(k4_xboole_0(A_61, B_62), B_18))), inference(superposition, [status(thm), theory('equality')], [c_22, c_305])).
% 27.11/19.06  tff(c_7544, plain, (![A_204, B_205, B_206]: (k4_xboole_0(A_204, k2_xboole_0(B_205, k4_xboole_0(A_204, k2_xboole_0(B_205, B_206))))=k3_xboole_0(k4_xboole_0(A_204, B_205), B_206))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_337])).
% 27.11/19.06  tff(c_7734, plain, (![A_14, B_15, B_205, B_206]: (k4_xboole_0(k4_xboole_0(A_14, B_15), k2_xboole_0(B_205, k4_xboole_0(A_14, k2_xboole_0(B_15, k2_xboole_0(B_205, B_206)))))=k3_xboole_0(k4_xboole_0(k4_xboole_0(A_14, B_15), B_205), B_206))), inference(superposition, [status(thm), theory('equality')], [c_20, c_7544])).
% 27.11/19.06  tff(c_87357, plain, (![A_666, B_667, B_668, B_669]: (k4_xboole_0(k4_xboole_0(A_666, B_667), k2_xboole_0(B_668, k4_xboole_0(A_666, k2_xboole_0(B_667, k2_xboole_0(B_668, B_669)))))=k3_xboole_0(k4_xboole_0(A_666, k2_xboole_0(B_667, B_668)), B_669))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_7734])).
% 27.11/19.06  tff(c_88255, plain, (![A_666, B_668, B_669]: (k4_xboole_0(k4_xboole_0(A_666, k2_xboole_0(B_668, B_669)), k2_xboole_0(B_668, k4_xboole_0(A_666, k2_xboole_0(B_668, B_669))))=k3_xboole_0(k4_xboole_0(A_666, k2_xboole_0(k2_xboole_0(B_668, B_669), B_668)), B_669))), inference(superposition, [status(thm), theory('equality')], [c_4, c_87357])).
% 27.11/19.06  tff(c_88482, plain, (![B_670, A_671, B_672]: (k3_xboole_0(B_670, k4_xboole_0(A_671, k2_xboole_0(B_670, B_672)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3771, c_344, c_3306, c_2, c_88255])).
% 27.11/19.06  tff(c_424, plain, (![A_71, B_72]: (r1_tarski(k3_xboole_0(A_71, B_72), B_72))), inference(superposition, [status(thm), theory('equality')], [c_2, c_349])).
% 27.11/19.06  tff(c_16, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 27.11/19.06  tff(c_1305, plain, (![A_103, B_104]: (k3_xboole_0(k3_xboole_0(A_103, B_104), B_104)=k3_xboole_0(A_103, B_104))), inference(resolution, [status(thm)], [c_424, c_16])).
% 27.11/19.06  tff(c_1507, plain, (![A_107, B_108]: (k3_xboole_0(k3_xboole_0(A_107, B_108), A_107)=k3_xboole_0(B_108, A_107))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1305])).
% 27.11/19.06  tff(c_1567, plain, (![A_107, B_108]: (k3_xboole_0(A_107, k3_xboole_0(A_107, B_108))=k3_xboole_0(B_108, A_107))), inference(superposition, [status(thm), theory('equality')], [c_1507, c_2])).
% 27.11/19.06  tff(c_88872, plain, (![A_671, B_670, B_672]: (k3_xboole_0(k4_xboole_0(A_671, k2_xboole_0(B_670, B_672)), B_670)=k3_xboole_0(B_670, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_88482, c_1567])).
% 27.11/19.06  tff(c_90161, plain, (![A_676, B_677, B_678]: (k3_xboole_0(k4_xboole_0(A_676, k2_xboole_0(B_677, B_678)), B_677)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_244, c_88872])).
% 27.11/19.06  tff(c_100971, plain, (![A_706, A_707, B_708]: (k3_xboole_0(k4_xboole_0(A_706, A_707), k4_xboole_0(A_707, B_708))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_124, c_90161])).
% 27.11/19.06  tff(c_105564, plain, (![A_718]: (k3_xboole_0(k4_xboole_0(A_718, '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_586, c_100971])).
% 27.11/19.06  tff(c_3169, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(demodulation, [status(thm), theory('equality')], [c_618, c_192])).
% 27.11/19.06  tff(c_314, plain, (![A_61, B_62, C_63]: (k4_xboole_0(k4_xboole_0(A_61, B_62), k4_xboole_0(A_61, k2_xboole_0(B_62, C_63)))=k3_xboole_0(k4_xboole_0(A_61, B_62), C_63))), inference(superposition, [status(thm), theory('equality')], [c_305, c_22])).
% 27.11/19.06  tff(c_7568, plain, (![A_204, B_205, B_206]: (k4_xboole_0(k4_xboole_0(A_204, B_205), k3_xboole_0(k4_xboole_0(A_204, B_205), B_206))=k3_xboole_0(k4_xboole_0(A_204, B_205), k4_xboole_0(A_204, k2_xboole_0(B_205, B_206))))), inference(superposition, [status(thm), theory('equality')], [c_7544, c_314])).
% 27.11/19.06  tff(c_7758, plain, (![A_204, B_205, B_206]: (k3_xboole_0(k4_xboole_0(A_204, B_205), k4_xboole_0(A_204, k2_xboole_0(B_205, B_206)))=k4_xboole_0(A_204, k2_xboole_0(B_205, B_206)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3169, c_7568])).
% 27.11/19.06  tff(c_346, plain, (![A_61, B_62, B_18]: (k4_xboole_0(A_61, k2_xboole_0(B_62, k4_xboole_0(A_61, k2_xboole_0(B_62, B_18))))=k3_xboole_0(k4_xboole_0(A_61, B_62), B_18))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_337])).
% 27.11/19.06  tff(c_7547, plain, (![A_204, B_205, B_206]: (k4_xboole_0(A_204, k2_xboole_0(B_205, k3_xboole_0(k4_xboole_0(A_204, B_205), B_206)))=k3_xboole_0(k4_xboole_0(A_204, B_205), k4_xboole_0(A_204, k2_xboole_0(B_205, B_206))))), inference(superposition, [status(thm), theory('equality')], [c_7544, c_346])).
% 27.11/19.06  tff(c_60397, plain, (![A_204, B_205, B_206]: (k4_xboole_0(A_204, k2_xboole_0(B_205, k3_xboole_0(k4_xboole_0(A_204, B_205), B_206)))=k4_xboole_0(A_204, k2_xboole_0(B_205, B_206)))), inference(demodulation, [status(thm), theory('equality')], [c_7758, c_7547])).
% 27.11/19.06  tff(c_105695, plain, (![A_718]: (k4_xboole_0(A_718, k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k4_xboole_0(A_718, k2_xboole_0('#skF_2', k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_105564, c_60397])).
% 27.11/19.06  tff(c_114060, plain, (![A_758]: (k4_xboole_0(A_758, k2_pre_topc('#skF_1', '#skF_2'))=k4_xboole_0(A_758, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9704, c_14, c_105695])).
% 27.11/19.06  tff(c_114480, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_114060, c_3038])).
% 27.11/19.06  tff(c_449, plain, (![A_71, B_72]: (k3_xboole_0(k3_xboole_0(A_71, B_72), B_72)=k3_xboole_0(A_71, B_72))), inference(resolution, [status(thm)], [c_424, c_16])).
% 27.11/19.06  tff(c_3240, plain, (![A_71, B_72]: (k4_xboole_0(k3_xboole_0(A_71, B_72), k3_xboole_0(A_71, B_72))=k4_xboole_0(k3_xboole_0(A_71, B_72), B_72))), inference(superposition, [status(thm), theory('equality')], [c_449, c_3170])).
% 27.11/19.06  tff(c_3301, plain, (![A_71, B_72]: (k4_xboole_0(k3_xboole_0(A_71, B_72), B_72)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3038, c_3240])).
% 27.11/19.06  tff(c_4351, plain, (![A_156, B_157, C_158]: (k4_xboole_0(A_156, k2_xboole_0(k4_xboole_0(A_156, B_157), C_158))=k4_xboole_0(k3_xboole_0(A_156, B_157), C_158))), inference(superposition, [status(thm), theory('equality')], [c_22, c_305])).
% 27.11/19.06  tff(c_32036, plain, (![A_408, B_409, C_410]: (k4_xboole_0(A_408, k4_xboole_0(k3_xboole_0(A_408, B_409), C_410))=k3_xboole_0(A_408, k2_xboole_0(k4_xboole_0(A_408, B_409), C_410)))), inference(superposition, [status(thm), theory('equality')], [c_4351, c_22])).
% 27.11/19.06  tff(c_32408, plain, (![A_71, B_72]: (k3_xboole_0(A_71, k2_xboole_0(k4_xboole_0(A_71, B_72), B_72))=k4_xboole_0(A_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3301, c_32036])).
% 27.11/19.06  tff(c_33499, plain, (![A_415, B_416]: (k3_xboole_0(A_415, k2_xboole_0(k4_xboole_0(A_415, B_416), B_416))=A_415)), inference(demodulation, [status(thm), theory('equality')], [c_2944, c_32408])).
% 27.11/19.06  tff(c_1412, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1305])).
% 27.11/19.06  tff(c_33718, plain, (![A_415, B_416]: (k3_xboole_0(k2_xboole_0(k4_xboole_0(A_415, B_416), B_416), A_415)=k3_xboole_0(A_415, A_415))), inference(superposition, [status(thm), theory('equality')], [c_33499, c_1412])).
% 27.11/19.06  tff(c_34008, plain, (![A_415, B_416]: (k3_xboole_0(k2_xboole_0(k4_xboole_0(A_415, B_416), B_416), A_415)=A_415)), inference(demodulation, [status(thm), theory('equality')], [c_169, c_33718])).
% 27.11/19.06  tff(c_114821, plain, (k3_xboole_0(k2_xboole_0(k1_xboole_0, '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_114480, c_34008])).
% 27.11/19.06  tff(c_114992, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11050, c_390, c_114821])).
% 27.11/19.06  tff(c_114994, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1506, c_114992])).
% 27.11/19.06  tff(c_114995, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 27.11/19.06  tff(c_115442, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_115390, c_114995])).
% 27.11/19.06  tff(c_114996, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 27.11/19.06  tff(c_115746, plain, (![A_801, B_802]: (r1_tarski(k2_tops_1(A_801, B_802), B_802) | ~v4_pre_topc(B_802, A_801) | ~m1_subset_1(B_802, k1_zfmisc_1(u1_struct_0(A_801))) | ~l1_pre_topc(A_801))), inference(cnfTransformation, [status(thm)], [f_98])).
% 27.11/19.06  tff(c_115750, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_115746])).
% 27.11/19.06  tff(c_115754, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_114996, c_115750])).
% 27.11/19.06  tff(c_115764, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_115754, c_16])).
% 27.11/19.06  tff(c_115791, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_115764, c_2])).
% 27.11/19.06  tff(c_116737, plain, (![A_825, B_826]: (k7_subset_1(u1_struct_0(A_825), B_826, k2_tops_1(A_825, B_826))=k1_tops_1(A_825, B_826) | ~m1_subset_1(B_826, k1_zfmisc_1(u1_struct_0(A_825))) | ~l1_pre_topc(A_825))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.11/19.06  tff(c_116741, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_116737])).
% 27.11/19.06  tff(c_116745, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_115390, c_116741])).
% 27.11/19.06  tff(c_116758, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116745, c_22])).
% 27.11/19.06  tff(c_116769, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_115791, c_116758])).
% 27.11/19.06  tff(c_116771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115442, c_116769])).
% 27.11/19.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.11/19.06  
% 27.11/19.06  Inference rules
% 27.11/19.06  ----------------------
% 27.11/19.06  #Ref     : 0
% 27.11/19.06  #Sup     : 28815
% 27.11/19.06  #Fact    : 0
% 27.11/19.06  #Define  : 0
% 27.11/19.06  #Split   : 5
% 27.11/19.06  #Chain   : 0
% 27.11/19.06  #Close   : 0
% 27.11/19.06  
% 27.11/19.06  Ordering : KBO
% 27.11/19.06  
% 27.11/19.06  Simplification rules
% 27.11/19.06  ----------------------
% 27.11/19.06  #Subsume      : 672
% 27.11/19.06  #Demod        : 37826
% 27.11/19.06  #Tautology    : 19573
% 27.11/19.06  #SimpNegUnit  : 9
% 27.11/19.06  #BackRed      : 16
% 27.11/19.06  
% 27.11/19.06  #Partial instantiations: 0
% 27.11/19.06  #Strategies tried      : 1
% 27.11/19.06  
% 27.11/19.06  Timing (in seconds)
% 27.11/19.06  ----------------------
% 27.11/19.07  Preprocessing        : 0.33
% 27.11/19.07  Parsing              : 0.18
% 27.11/19.07  CNF conversion       : 0.02
% 27.11/19.07  Main loop            : 17.94
% 27.11/19.07  Inferencing          : 1.88
% 27.11/19.07  Reduction            : 12.18
% 27.11/19.07  Demodulation         : 11.26
% 27.11/19.07  BG Simplification    : 0.25
% 27.11/19.07  Subsumption          : 3.03
% 27.11/19.07  Abstraction          : 0.52
% 27.11/19.07  MUC search           : 0.00
% 27.11/19.07  Cooper               : 0.00
% 27.11/19.07  Total                : 18.33
% 27.11/19.07  Index Insertion      : 0.00
% 27.11/19.07  Index Deletion       : 0.00
% 27.11/19.07  Index Matching       : 0.00
% 27.11/19.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
