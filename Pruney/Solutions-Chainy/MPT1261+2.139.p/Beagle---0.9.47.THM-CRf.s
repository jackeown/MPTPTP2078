%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:31 EST 2020

% Result     : Theorem 17.82s
% Output     : CNFRefutation 17.82s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 310 expanded)
%              Number of leaves         :   37 ( 117 expanded)
%              Depth                    :   13
%              Number of atoms          :  200 ( 528 expanded)
%              Number of equality atoms :   71 ( 191 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_65,axiom,(
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

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_66108,plain,(
    ! [A_687,B_688,C_689] :
      ( k7_subset_1(A_687,B_688,C_689) = k4_xboole_0(B_688,C_689)
      | ~ m1_subset_1(B_688,k1_zfmisc_1(A_687)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_66111,plain,(
    ! [C_689] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_689) = k4_xboole_0('#skF_2',C_689) ),
    inference(resolution,[status(thm)],[c_40,c_66108])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_116,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2270,plain,(
    ! [B_132,A_133] :
      ( v4_pre_topc(B_132,A_133)
      | k2_pre_topc(A_133,B_132) != B_132
      | ~ v2_pre_topc(A_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2276,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2270])).

tff(c_2280,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_2276])).

tff(c_2281,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_2280])).

tff(c_2975,plain,(
    ! [A_154,B_155] :
      ( k4_subset_1(u1_struct_0(A_154),B_155,k2_tops_1(A_154,B_155)) = k2_pre_topc(A_154,B_155)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2979,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_2975])).

tff(c_2983,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2979])).

tff(c_32,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k2_tops_1(A_31,B_32),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1764,plain,(
    ! [A_117,B_118,C_119] :
      ( k4_subset_1(A_117,B_118,C_119) = k2_xboole_0(B_118,C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_15240,plain,(
    ! [A_349,B_350,B_351] :
      ( k4_subset_1(u1_struct_0(A_349),B_350,k2_tops_1(A_349,B_351)) = k2_xboole_0(B_350,k2_tops_1(A_349,B_351))
      | ~ m1_subset_1(B_350,k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ m1_subset_1(B_351,k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ l1_pre_topc(A_349) ) ),
    inference(resolution,[status(thm)],[c_32,c_1764])).

tff(c_15244,plain,(
    ! [B_351] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_351)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_351))
      | ~ m1_subset_1(B_351,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_15240])).

tff(c_15252,plain,(
    ! [B_352] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_352)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_352))
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_15244])).

tff(c_15259,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_15252])).

tff(c_15264,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2983,c_15259])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_89,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),A_9) = A_9 ),
    inference(resolution,[status(thm)],[c_14,c_89])).

tff(c_22,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_396,plain,(
    ! [A_80,B_81,C_82] : k4_xboole_0(k4_xboole_0(A_80,B_81),C_82) = k4_xboole_0(A_80,k2_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4681,plain,(
    ! [A_175,B_176,C_177] : k4_xboole_0(A_175,k2_xboole_0(k4_xboole_0(A_175,B_176),C_177)) = k4_xboole_0(k3_xboole_0(A_175,B_176),C_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_396])).

tff(c_8682,plain,(
    ! [A_251,B_252] : k4_xboole_0(k3_xboole_0(A_251,B_252),A_251) = k4_xboole_0(A_251,A_251) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_4681])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4819,plain,(
    ! [A_178,B_179,C_180] : r1_tarski(k4_xboole_0(k3_xboole_0(A_178,B_179),C_180),A_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_4681,c_14])).

tff(c_4935,plain,(
    ! [B_2,A_1,C_180] : r1_tarski(k4_xboole_0(k3_xboole_0(B_2,A_1),C_180),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4819])).

tff(c_8943,plain,(
    ! [A_253,B_254] : r1_tarski(k4_xboole_0(A_253,A_253),B_254) ),
    inference(superposition,[status(thm),theory(equality)],[c_8682,c_4935])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(A_17,k2_xboole_0(B_18,C_19))
      | ~ r1_tarski(k4_xboole_0(A_17,B_18),C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8989,plain,(
    ! [A_253,B_254] : r1_tarski(A_253,k2_xboole_0(A_253,B_254)) ),
    inference(resolution,[status(thm)],[c_8943,c_20])).

tff(c_15305,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15264,c_8989])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_15369,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_15305,c_4])).

tff(c_15378,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_2281,c_15369])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_355,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_tarski(k4_xboole_0(A_75,B_76),C_77)
      | ~ r1_tarski(A_75,k2_xboole_0(B_76,C_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4021,plain,(
    ! [A_166,B_167,C_168] :
      ( k2_xboole_0(k4_xboole_0(A_166,B_167),C_168) = C_168
      | ~ r1_tarski(A_166,k2_xboole_0(B_167,C_168)) ) ),
    inference(resolution,[status(thm)],[c_355,c_10])).

tff(c_4104,plain,(
    ! [B_167,C_168] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_167,C_168),B_167),C_168) = C_168 ),
    inference(resolution,[status(thm)],[c_8,c_4021])).

tff(c_8998,plain,(
    ! [A_255,B_256] : r1_tarski(A_255,k2_xboole_0(A_255,B_256)) ),
    inference(resolution,[status(thm)],[c_8943,c_20])).

tff(c_9022,plain,(
    ! [B_167,C_168] : r1_tarski(k4_xboole_0(k2_xboole_0(B_167,C_168),B_167),C_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_4104,c_8998])).

tff(c_15296,plain,(
    r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15264,c_9022])).

tff(c_614,plain,(
    ! [A_91,B_92,C_93] :
      ( k7_subset_1(A_91,B_92,C_93) = k4_xboole_0(B_92,C_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_618,plain,(
    ! [C_94] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_94) = k4_xboole_0('#skF_2',C_94) ),
    inference(resolution,[status(thm)],[c_40,c_614])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_250,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_52])).

tff(c_624,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_250])).

tff(c_786,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_96])).

tff(c_97,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_89])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7060,plain,(
    ! [A_226,B_227,C_228] :
      ( k3_xboole_0(k4_xboole_0(A_226,B_227),C_228) = k4_xboole_0(A_226,B_227)
      | ~ r1_tarski(A_226,k2_xboole_0(B_227,C_228)) ) ),
    inference(resolution,[status(thm)],[c_355,c_12])).

tff(c_7173,plain,(
    ! [A_226,B_4] :
      ( k3_xboole_0(k4_xboole_0(A_226,B_4),B_4) = k4_xboole_0(A_226,B_4)
      | ~ r1_tarski(A_226,B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_7060])).

tff(c_7222,plain,(
    ! [B_4,A_226] :
      ( k3_xboole_0(B_4,k4_xboole_0(A_226,B_4)) = k4_xboole_0(A_226,B_4)
      | ~ r1_tarski(A_226,B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7173])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k4_xboole_0(A_11,B_12),C_13) = k4_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_437,plain,(
    ! [A_80,B_81,B_21] : k4_xboole_0(A_80,k2_xboole_0(B_81,k4_xboole_0(k4_xboole_0(A_80,B_81),B_21))) = k3_xboole_0(k4_xboole_0(A_80,B_81),B_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_396])).

tff(c_7769,plain,(
    ! [A_241,B_242,B_243] : k4_xboole_0(A_241,k2_xboole_0(B_242,k4_xboole_0(A_241,k2_xboole_0(B_242,B_243)))) = k3_xboole_0(k4_xboole_0(A_241,B_242),B_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_437])).

tff(c_7933,plain,(
    ! [A_241,B_4] : k4_xboole_0(A_241,k2_xboole_0(B_4,k4_xboole_0(A_241,B_4))) = k3_xboole_0(k4_xboole_0(A_241,B_4),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_7769])).

tff(c_29934,plain,(
    ! [A_452,B_453] : k4_xboole_0(A_452,k2_xboole_0(B_453,k4_xboole_0(A_452,B_453))) = k3_xboole_0(B_453,k4_xboole_0(A_452,B_453)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7933])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_tarski(k4_xboole_0(A_14,B_15),C_16)
      | ~ r1_tarski(A_14,k2_xboole_0(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_408,plain,(
    ! [A_80,B_81,C_82,C_16] :
      ( r1_tarski(k4_xboole_0(A_80,k2_xboole_0(B_81,C_82)),C_16)
      | ~ r1_tarski(k4_xboole_0(A_80,B_81),k2_xboole_0(C_82,C_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_18])).

tff(c_30052,plain,(
    ! [B_453,A_452,C_16] :
      ( r1_tarski(k3_xboole_0(B_453,k4_xboole_0(A_452,B_453)),C_16)
      | ~ r1_tarski(k4_xboole_0(A_452,B_453),k2_xboole_0(k4_xboole_0(A_452,B_453),C_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29934,c_408])).

tff(c_30344,plain,(
    ! [B_454,A_455,C_456] : r1_tarski(k3_xboole_0(B_454,k4_xboole_0(A_455,B_454)),C_456) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8989,c_30052])).

tff(c_31434,plain,(
    ! [A_463,B_464,C_465] :
      ( r1_tarski(k4_xboole_0(A_463,B_464),C_465)
      | ~ r1_tarski(A_463,B_464) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7222,c_30344])).

tff(c_34289,plain,(
    ! [A_483,B_484,C_485] :
      ( r1_tarski(A_483,k2_xboole_0(B_484,C_485))
      | ~ r1_tarski(A_483,B_484) ) ),
    inference(resolution,[status(thm)],[c_31434,c_20])).

tff(c_65099,plain,(
    ! [A_640] :
      ( r1_tarski(A_640,'#skF_2')
      | ~ r1_tarski(A_640,k2_tops_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_34289])).

tff(c_65251,plain,(
    r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_15296,c_65099])).

tff(c_145,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_179,plain,(
    ! [A_63,B_64] : r1_tarski(k3_xboole_0(A_63,B_64),A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_14])).

tff(c_226,plain,(
    ! [B_67,A_68] : r1_tarski(k3_xboole_0(B_67,A_68),A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_179])).

tff(c_246,plain,(
    ! [B_67,A_68] : k2_xboole_0(k3_xboole_0(B_67,A_68),A_68) = A_68 ),
    inference(resolution,[status(thm)],[c_226,c_10])).

tff(c_117,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_444,plain,(
    ! [A_83,B_84] : k3_xboole_0(k4_xboole_0(A_83,B_84),A_83) = k4_xboole_0(A_83,B_84) ),
    inference(resolution,[status(thm)],[c_14,c_117])).

tff(c_462,plain,(
    ! [A_83,B_84] : k3_xboole_0(A_83,k4_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_2])).

tff(c_166,plain,(
    ! [A_60,B_61,C_62] :
      ( r1_tarski(A_60,k2_xboole_0(B_61,C_62))
      | ~ r1_tarski(k4_xboole_0(A_60,B_61),C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6393,plain,(
    ! [A_210,B_211,C_212] :
      ( r1_tarski(A_210,k2_xboole_0(k4_xboole_0(A_210,B_211),C_212))
      | ~ r1_tarski(k3_xboole_0(A_210,B_211),C_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_166])).

tff(c_6442,plain,(
    ! [A_20,B_21,C_212] :
      ( r1_tarski(A_20,k2_xboole_0(k3_xboole_0(A_20,B_21),C_212))
      | ~ r1_tarski(k3_xboole_0(A_20,k4_xboole_0(A_20,B_21)),C_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_6393])).

tff(c_33198,plain,(
    ! [A_476,B_477,C_478] :
      ( r1_tarski(A_476,k2_xboole_0(k3_xboole_0(A_476,B_477),C_478))
      | ~ r1_tarski(k4_xboole_0(A_476,B_477),C_478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_6442])).

tff(c_33372,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(B_67,A_68)
      | ~ r1_tarski(k4_xboole_0(B_67,A_68),A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_33198])).

tff(c_65280,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_65251,c_33372])).

tff(c_65295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15378,c_65280])).

tff(c_65296,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_66112,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66111,c_65296])).

tff(c_65297,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_66785,plain,(
    ! [A_709,B_710] :
      ( r1_tarski(k2_tops_1(A_709,B_710),B_710)
      | ~ v4_pre_topc(B_710,A_709)
      | ~ m1_subset_1(B_710,k1_zfmisc_1(u1_struct_0(A_709)))
      | ~ l1_pre_topc(A_709) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_66789,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_66785])).

tff(c_66793,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_65297,c_66789])).

tff(c_66803,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66793,c_12])).

tff(c_66867,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_66803,c_2])).

tff(c_67169,plain,(
    ! [A_718,B_719] :
      ( k7_subset_1(u1_struct_0(A_718),B_719,k2_tops_1(A_718,B_719)) = k1_tops_1(A_718,B_719)
      | ~ m1_subset_1(B_719,k1_zfmisc_1(u1_struct_0(A_718)))
      | ~ l1_pre_topc(A_718) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_67173,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_67169])).

tff(c_67177,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_66111,c_67173])).

tff(c_67202,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_67177,c_22])).

tff(c_67213,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66867,c_67202])).

tff(c_67215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66112,c_67213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:15:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.82/9.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.82/9.81  
% 17.82/9.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.82/9.82  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 17.82/9.82  
% 17.82/9.82  %Foreground sorts:
% 17.82/9.82  
% 17.82/9.82  
% 17.82/9.82  %Background operators:
% 17.82/9.82  
% 17.82/9.82  
% 17.82/9.82  %Foreground operators:
% 17.82/9.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.82/9.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.82/9.82  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 17.82/9.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 17.82/9.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.82/9.82  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 17.82/9.82  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 17.82/9.82  tff('#skF_2', type, '#skF_2': $i).
% 17.82/9.82  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 17.82/9.82  tff('#skF_1', type, '#skF_1': $i).
% 17.82/9.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.82/9.82  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 17.82/9.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.82/9.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.82/9.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 17.82/9.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.82/9.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.82/9.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 17.82/9.82  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 17.82/9.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.82/9.82  
% 17.82/9.84  tff(f_121, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 17.82/9.84  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 17.82/9.84  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 17.82/9.84  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 17.82/9.84  tff(f_86, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 17.82/9.84  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 17.82/9.84  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 17.82/9.84  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 17.82/9.84  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 17.82/9.84  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 17.82/9.84  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 17.82/9.84  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 17.82/9.84  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.82/9.84  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 17.82/9.84  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 17.82/9.84  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 17.82/9.84  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 17.82/9.84  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.82/9.84  tff(c_66108, plain, (![A_687, B_688, C_689]: (k7_subset_1(A_687, B_688, C_689)=k4_xboole_0(B_688, C_689) | ~m1_subset_1(B_688, k1_zfmisc_1(A_687)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.82/9.84  tff(c_66111, plain, (![C_689]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_689)=k4_xboole_0('#skF_2', C_689))), inference(resolution, [status(thm)], [c_40, c_66108])).
% 17.82/9.84  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.82/9.84  tff(c_116, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 17.82/9.84  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.82/9.84  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.82/9.84  tff(c_2270, plain, (![B_132, A_133]: (v4_pre_topc(B_132, A_133) | k2_pre_topc(A_133, B_132)!=B_132 | ~v2_pre_topc(A_133) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_80])).
% 17.82/9.84  tff(c_2276, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2270])).
% 17.82/9.84  tff(c_2280, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_2276])).
% 17.82/9.84  tff(c_2281, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_116, c_2280])).
% 17.82/9.84  tff(c_2975, plain, (![A_154, B_155]: (k4_subset_1(u1_struct_0(A_154), B_155, k2_tops_1(A_154, B_155))=k2_pre_topc(A_154, B_155) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_93])).
% 17.82/9.84  tff(c_2979, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_2975])).
% 17.82/9.84  tff(c_2983, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2979])).
% 17.82/9.84  tff(c_32, plain, (![A_31, B_32]: (m1_subset_1(k2_tops_1(A_31, B_32), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_86])).
% 17.82/9.84  tff(c_1764, plain, (![A_117, B_118, C_119]: (k4_subset_1(A_117, B_118, C_119)=k2_xboole_0(B_118, C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(A_117)) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.82/9.84  tff(c_15240, plain, (![A_349, B_350, B_351]: (k4_subset_1(u1_struct_0(A_349), B_350, k2_tops_1(A_349, B_351))=k2_xboole_0(B_350, k2_tops_1(A_349, B_351)) | ~m1_subset_1(B_350, k1_zfmisc_1(u1_struct_0(A_349))) | ~m1_subset_1(B_351, k1_zfmisc_1(u1_struct_0(A_349))) | ~l1_pre_topc(A_349))), inference(resolution, [status(thm)], [c_32, c_1764])).
% 17.82/9.84  tff(c_15244, plain, (![B_351]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_351))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_351)) | ~m1_subset_1(B_351, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_15240])).
% 17.82/9.84  tff(c_15252, plain, (![B_352]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_352))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_352)) | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_15244])).
% 17.82/9.84  tff(c_15259, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_15252])).
% 17.82/9.84  tff(c_15264, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2983, c_15259])).
% 17.82/9.84  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.82/9.84  tff(c_89, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.82/9.84  tff(c_96, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), A_9)=A_9)), inference(resolution, [status(thm)], [c_14, c_89])).
% 17.82/9.84  tff(c_22, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 17.82/9.84  tff(c_396, plain, (![A_80, B_81, C_82]: (k4_xboole_0(k4_xboole_0(A_80, B_81), C_82)=k4_xboole_0(A_80, k2_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.82/9.84  tff(c_4681, plain, (![A_175, B_176, C_177]: (k4_xboole_0(A_175, k2_xboole_0(k4_xboole_0(A_175, B_176), C_177))=k4_xboole_0(k3_xboole_0(A_175, B_176), C_177))), inference(superposition, [status(thm), theory('equality')], [c_22, c_396])).
% 17.82/9.84  tff(c_8682, plain, (![A_251, B_252]: (k4_xboole_0(k3_xboole_0(A_251, B_252), A_251)=k4_xboole_0(A_251, A_251))), inference(superposition, [status(thm), theory('equality')], [c_96, c_4681])).
% 17.82/9.84  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.82/9.84  tff(c_4819, plain, (![A_178, B_179, C_180]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_178, B_179), C_180), A_178))), inference(superposition, [status(thm), theory('equality')], [c_4681, c_14])).
% 17.82/9.84  tff(c_4935, plain, (![B_2, A_1, C_180]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_2, A_1), C_180), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4819])).
% 17.82/9.84  tff(c_8943, plain, (![A_253, B_254]: (r1_tarski(k4_xboole_0(A_253, A_253), B_254))), inference(superposition, [status(thm), theory('equality')], [c_8682, c_4935])).
% 17.82/9.84  tff(c_20, plain, (![A_17, B_18, C_19]: (r1_tarski(A_17, k2_xboole_0(B_18, C_19)) | ~r1_tarski(k4_xboole_0(A_17, B_18), C_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.82/9.84  tff(c_8989, plain, (![A_253, B_254]: (r1_tarski(A_253, k2_xboole_0(A_253, B_254)))), inference(resolution, [status(thm)], [c_8943, c_20])).
% 17.82/9.84  tff(c_15305, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_15264, c_8989])).
% 17.82/9.84  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 17.82/9.84  tff(c_15369, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_15305, c_4])).
% 17.82/9.84  tff(c_15378, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_2281, c_15369])).
% 17.82/9.84  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 17.82/9.84  tff(c_355, plain, (![A_75, B_76, C_77]: (r1_tarski(k4_xboole_0(A_75, B_76), C_77) | ~r1_tarski(A_75, k2_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.82/9.84  tff(c_10, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.82/9.84  tff(c_4021, plain, (![A_166, B_167, C_168]: (k2_xboole_0(k4_xboole_0(A_166, B_167), C_168)=C_168 | ~r1_tarski(A_166, k2_xboole_0(B_167, C_168)))), inference(resolution, [status(thm)], [c_355, c_10])).
% 17.82/9.84  tff(c_4104, plain, (![B_167, C_168]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_167, C_168), B_167), C_168)=C_168)), inference(resolution, [status(thm)], [c_8, c_4021])).
% 17.82/9.84  tff(c_8998, plain, (![A_255, B_256]: (r1_tarski(A_255, k2_xboole_0(A_255, B_256)))), inference(resolution, [status(thm)], [c_8943, c_20])).
% 17.82/9.84  tff(c_9022, plain, (![B_167, C_168]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_167, C_168), B_167), C_168))), inference(superposition, [status(thm), theory('equality')], [c_4104, c_8998])).
% 17.82/9.84  tff(c_15296, plain, (r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_15264, c_9022])).
% 17.82/9.84  tff(c_614, plain, (![A_91, B_92, C_93]: (k7_subset_1(A_91, B_92, C_93)=k4_xboole_0(B_92, C_93) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.82/9.84  tff(c_618, plain, (![C_94]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_94)=k4_xboole_0('#skF_2', C_94))), inference(resolution, [status(thm)], [c_40, c_614])).
% 17.82/9.84  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.82/9.84  tff(c_250, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_116, c_52])).
% 17.82/9.84  tff(c_624, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_618, c_250])).
% 17.82/9.84  tff(c_786, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_624, c_96])).
% 17.82/9.84  tff(c_97, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_89])).
% 17.82/9.84  tff(c_12, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.82/9.84  tff(c_7060, plain, (![A_226, B_227, C_228]: (k3_xboole_0(k4_xboole_0(A_226, B_227), C_228)=k4_xboole_0(A_226, B_227) | ~r1_tarski(A_226, k2_xboole_0(B_227, C_228)))), inference(resolution, [status(thm)], [c_355, c_12])).
% 17.82/9.84  tff(c_7173, plain, (![A_226, B_4]: (k3_xboole_0(k4_xboole_0(A_226, B_4), B_4)=k4_xboole_0(A_226, B_4) | ~r1_tarski(A_226, B_4))), inference(superposition, [status(thm), theory('equality')], [c_97, c_7060])).
% 17.82/9.84  tff(c_7222, plain, (![B_4, A_226]: (k3_xboole_0(B_4, k4_xboole_0(A_226, B_4))=k4_xboole_0(A_226, B_4) | ~r1_tarski(A_226, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7173])).
% 17.82/9.84  tff(c_16, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k4_xboole_0(A_11, B_12), C_13)=k4_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.82/9.84  tff(c_437, plain, (![A_80, B_81, B_21]: (k4_xboole_0(A_80, k2_xboole_0(B_81, k4_xboole_0(k4_xboole_0(A_80, B_81), B_21)))=k3_xboole_0(k4_xboole_0(A_80, B_81), B_21))), inference(superposition, [status(thm), theory('equality')], [c_22, c_396])).
% 17.82/9.84  tff(c_7769, plain, (![A_241, B_242, B_243]: (k4_xboole_0(A_241, k2_xboole_0(B_242, k4_xboole_0(A_241, k2_xboole_0(B_242, B_243))))=k3_xboole_0(k4_xboole_0(A_241, B_242), B_243))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_437])).
% 17.82/9.84  tff(c_7933, plain, (![A_241, B_4]: (k4_xboole_0(A_241, k2_xboole_0(B_4, k4_xboole_0(A_241, B_4)))=k3_xboole_0(k4_xboole_0(A_241, B_4), B_4))), inference(superposition, [status(thm), theory('equality')], [c_97, c_7769])).
% 17.82/9.84  tff(c_29934, plain, (![A_452, B_453]: (k4_xboole_0(A_452, k2_xboole_0(B_453, k4_xboole_0(A_452, B_453)))=k3_xboole_0(B_453, k4_xboole_0(A_452, B_453)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7933])).
% 17.82/9.84  tff(c_18, plain, (![A_14, B_15, C_16]: (r1_tarski(k4_xboole_0(A_14, B_15), C_16) | ~r1_tarski(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.82/9.84  tff(c_408, plain, (![A_80, B_81, C_82, C_16]: (r1_tarski(k4_xboole_0(A_80, k2_xboole_0(B_81, C_82)), C_16) | ~r1_tarski(k4_xboole_0(A_80, B_81), k2_xboole_0(C_82, C_16)))), inference(superposition, [status(thm), theory('equality')], [c_396, c_18])).
% 17.82/9.84  tff(c_30052, plain, (![B_453, A_452, C_16]: (r1_tarski(k3_xboole_0(B_453, k4_xboole_0(A_452, B_453)), C_16) | ~r1_tarski(k4_xboole_0(A_452, B_453), k2_xboole_0(k4_xboole_0(A_452, B_453), C_16)))), inference(superposition, [status(thm), theory('equality')], [c_29934, c_408])).
% 17.82/9.84  tff(c_30344, plain, (![B_454, A_455, C_456]: (r1_tarski(k3_xboole_0(B_454, k4_xboole_0(A_455, B_454)), C_456))), inference(demodulation, [status(thm), theory('equality')], [c_8989, c_30052])).
% 17.82/9.84  tff(c_31434, plain, (![A_463, B_464, C_465]: (r1_tarski(k4_xboole_0(A_463, B_464), C_465) | ~r1_tarski(A_463, B_464))), inference(superposition, [status(thm), theory('equality')], [c_7222, c_30344])).
% 17.82/9.84  tff(c_34289, plain, (![A_483, B_484, C_485]: (r1_tarski(A_483, k2_xboole_0(B_484, C_485)) | ~r1_tarski(A_483, B_484))), inference(resolution, [status(thm)], [c_31434, c_20])).
% 17.82/9.84  tff(c_65099, plain, (![A_640]: (r1_tarski(A_640, '#skF_2') | ~r1_tarski(A_640, k2_tops_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_786, c_34289])).
% 17.82/9.84  tff(c_65251, plain, (r1_tarski(k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_15296, c_65099])).
% 17.82/9.84  tff(c_145, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 17.82/9.84  tff(c_179, plain, (![A_63, B_64]: (r1_tarski(k3_xboole_0(A_63, B_64), A_63))), inference(superposition, [status(thm), theory('equality')], [c_145, c_14])).
% 17.82/9.84  tff(c_226, plain, (![B_67, A_68]: (r1_tarski(k3_xboole_0(B_67, A_68), A_68))), inference(superposition, [status(thm), theory('equality')], [c_2, c_179])).
% 17.82/9.84  tff(c_246, plain, (![B_67, A_68]: (k2_xboole_0(k3_xboole_0(B_67, A_68), A_68)=A_68)), inference(resolution, [status(thm)], [c_226, c_10])).
% 17.82/9.84  tff(c_117, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.82/9.84  tff(c_444, plain, (![A_83, B_84]: (k3_xboole_0(k4_xboole_0(A_83, B_84), A_83)=k4_xboole_0(A_83, B_84))), inference(resolution, [status(thm)], [c_14, c_117])).
% 17.82/9.84  tff(c_462, plain, (![A_83, B_84]: (k3_xboole_0(A_83, k4_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(superposition, [status(thm), theory('equality')], [c_444, c_2])).
% 17.82/9.84  tff(c_166, plain, (![A_60, B_61, C_62]: (r1_tarski(A_60, k2_xboole_0(B_61, C_62)) | ~r1_tarski(k4_xboole_0(A_60, B_61), C_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.82/9.84  tff(c_6393, plain, (![A_210, B_211, C_212]: (r1_tarski(A_210, k2_xboole_0(k4_xboole_0(A_210, B_211), C_212)) | ~r1_tarski(k3_xboole_0(A_210, B_211), C_212))), inference(superposition, [status(thm), theory('equality')], [c_22, c_166])).
% 17.82/9.84  tff(c_6442, plain, (![A_20, B_21, C_212]: (r1_tarski(A_20, k2_xboole_0(k3_xboole_0(A_20, B_21), C_212)) | ~r1_tarski(k3_xboole_0(A_20, k4_xboole_0(A_20, B_21)), C_212))), inference(superposition, [status(thm), theory('equality')], [c_22, c_6393])).
% 17.82/9.84  tff(c_33198, plain, (![A_476, B_477, C_478]: (r1_tarski(A_476, k2_xboole_0(k3_xboole_0(A_476, B_477), C_478)) | ~r1_tarski(k4_xboole_0(A_476, B_477), C_478))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_6442])).
% 17.82/9.84  tff(c_33372, plain, (![B_67, A_68]: (r1_tarski(B_67, A_68) | ~r1_tarski(k4_xboole_0(B_67, A_68), A_68))), inference(superposition, [status(thm), theory('equality')], [c_246, c_33198])).
% 17.82/9.84  tff(c_65280, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_65251, c_33372])).
% 17.82/9.84  tff(c_65295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15378, c_65280])).
% 17.82/9.84  tff(c_65296, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 17.82/9.84  tff(c_66112, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66111, c_65296])).
% 17.82/9.84  tff(c_65297, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 17.82/9.84  tff(c_66785, plain, (![A_709, B_710]: (r1_tarski(k2_tops_1(A_709, B_710), B_710) | ~v4_pre_topc(B_710, A_709) | ~m1_subset_1(B_710, k1_zfmisc_1(u1_struct_0(A_709))) | ~l1_pre_topc(A_709))), inference(cnfTransformation, [status(thm)], [f_102])).
% 17.82/9.84  tff(c_66789, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_66785])).
% 17.82/9.84  tff(c_66793, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_65297, c_66789])).
% 17.82/9.84  tff(c_66803, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66793, c_12])).
% 17.82/9.84  tff(c_66867, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_66803, c_2])).
% 17.82/9.84  tff(c_67169, plain, (![A_718, B_719]: (k7_subset_1(u1_struct_0(A_718), B_719, k2_tops_1(A_718, B_719))=k1_tops_1(A_718, B_719) | ~m1_subset_1(B_719, k1_zfmisc_1(u1_struct_0(A_718))) | ~l1_pre_topc(A_718))), inference(cnfTransformation, [status(thm)], [f_109])).
% 17.82/9.84  tff(c_67173, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_67169])).
% 17.82/9.84  tff(c_67177, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_66111, c_67173])).
% 17.82/9.84  tff(c_67202, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_67177, c_22])).
% 17.82/9.84  tff(c_67213, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66867, c_67202])).
% 17.82/9.84  tff(c_67215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66112, c_67213])).
% 17.82/9.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.82/9.84  
% 17.82/9.84  Inference rules
% 17.82/9.84  ----------------------
% 17.82/9.84  #Ref     : 0
% 17.82/9.84  #Sup     : 16912
% 17.82/9.84  #Fact    : 0
% 17.82/9.84  #Define  : 0
% 17.82/9.84  #Split   : 4
% 17.82/9.84  #Chain   : 0
% 17.82/9.84  #Close   : 0
% 17.82/9.84  
% 17.82/9.84  Ordering : KBO
% 17.82/9.84  
% 17.82/9.84  Simplification rules
% 17.82/9.84  ----------------------
% 17.82/9.84  #Subsume      : 1170
% 17.82/9.84  #Demod        : 14798
% 17.82/9.84  #Tautology    : 8957
% 17.82/9.84  #SimpNegUnit  : 6
% 17.82/9.84  #BackRed      : 12
% 17.82/9.84  
% 17.82/9.84  #Partial instantiations: 0
% 17.82/9.84  #Strategies tried      : 1
% 17.82/9.84  
% 17.82/9.84  Timing (in seconds)
% 17.82/9.84  ----------------------
% 17.82/9.84  Preprocessing        : 0.34
% 17.82/9.84  Parsing              : 0.19
% 17.82/9.84  CNF conversion       : 0.02
% 17.82/9.84  Main loop            : 8.72
% 17.82/9.84  Inferencing          : 1.18
% 17.82/9.84  Reduction            : 5.19
% 17.82/9.84  Demodulation         : 4.70
% 17.82/9.84  BG Simplification    : 0.16
% 17.82/9.84  Subsumption          : 1.78
% 17.82/9.84  Abstraction          : 0.26
% 17.82/9.84  MUC search           : 0.00
% 17.82/9.84  Cooper               : 0.00
% 17.82/9.84  Total                : 9.11
% 17.82/9.84  Index Insertion      : 0.00
% 17.82/9.84  Index Deletion       : 0.00
% 17.82/9.84  Index Matching       : 0.00
% 17.82/9.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
