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
% DateTime   : Thu Dec  3 10:21:55 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 109 expanded)
%              Number of leaves         :   34 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 174 expanded)
%              Number of equality atoms :   40 (  44 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_77,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_58,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_106,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_261,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_52])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2208,plain,(
    ! [B_166,A_167] :
      ( v2_tops_1(B_166,A_167)
      | k1_tops_1(A_167,B_166) != k1_xboole_0
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2219,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_2208])).

tff(c_2224,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2219])).

tff(c_2225,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_2224])).

tff(c_10,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1196,plain,(
    ! [A_130,B_131,C_132] :
      ( r1_tarski(k4_xboole_0(A_130,B_131),C_132)
      | ~ r1_tarski(A_130,k2_xboole_0(B_131,C_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1219,plain,(
    ! [A_130,B_131] :
      ( k4_xboole_0(A_130,B_131) = k1_xboole_0
      | ~ r1_tarski(A_130,k2_xboole_0(B_131,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1196,c_18])).

tff(c_1252,plain,(
    ! [A_133,B_134] :
      ( k4_xboole_0(A_133,B_134) = k1_xboole_0
      | ~ r1_tarski(A_133,B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1219])).

tff(c_1322,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_1252])).

tff(c_1599,plain,(
    ! [A_143,B_144,C_145] :
      ( k7_subset_1(A_143,B_144,C_145) = k4_xboole_0(B_144,C_145)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1608,plain,(
    ! [C_145] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_145) = k4_xboole_0('#skF_2',C_145) ),
    inference(resolution,[status(thm)],[c_48,c_1599])).

tff(c_2608,plain,(
    ! [A_179,B_180] :
      ( k7_subset_1(u1_struct_0(A_179),B_180,k2_tops_1(A_179,B_180)) = k1_tops_1(A_179,B_180)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2616,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_2608])).

tff(c_2621,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1322,c_1608,c_2616])).

tff(c_2623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2225,c_2621])).

tff(c_2625,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_16,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2624,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4273,plain,(
    ! [A_274,B_275] :
      ( k1_tops_1(A_274,B_275) = k1_xboole_0
      | ~ v2_tops_1(B_275,A_274)
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ l1_pre_topc(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4284,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_4273])).

tff(c_4289,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2624,c_4284])).

tff(c_4044,plain,(
    ! [A_260,B_261,C_262] :
      ( k7_subset_1(A_260,B_261,C_262) = k4_xboole_0(B_261,C_262)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(A_260)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4053,plain,(
    ! [C_262] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_262) = k4_xboole_0('#skF_2',C_262) ),
    inference(resolution,[status(thm)],[c_48,c_4044])).

tff(c_4939,plain,(
    ! [A_305,B_306] :
      ( k7_subset_1(u1_struct_0(A_305),B_306,k2_tops_1(A_305,B_306)) = k1_tops_1(A_305,B_306)
      | ~ m1_subset_1(B_306,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ l1_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4947,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_4939])).

tff(c_4952,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4289,c_4053,c_4947])).

tff(c_22,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4959,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4952,c_22])).

tff(c_4966,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4959])).

tff(c_26,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2805,plain,(
    ! [A_195,B_196] : k1_setfam_1(k2_tarski(A_195,B_196)) = k3_xboole_0(A_195,B_196) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2820,plain,(
    ! [B_197,A_198] : k1_setfam_1(k2_tarski(B_197,A_198)) = k3_xboole_0(A_198,B_197) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2805])).

tff(c_34,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2843,plain,(
    ! [B_199,A_200] : k3_xboole_0(B_199,A_200) = k3_xboole_0(A_200,B_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_2820,c_34])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2869,plain,(
    ! [A_200,B_199] : r1_tarski(k3_xboole_0(A_200,B_199),B_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_2843,c_8])).

tff(c_5008,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4966,c_2869])).

tff(c_5026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2625,c_5008])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.90  
% 4.71/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.91  %$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.71/1.91  
% 4.71/1.91  %Foreground sorts:
% 4.71/1.91  
% 4.71/1.91  
% 4.71/1.91  %Background operators:
% 4.71/1.91  
% 4.71/1.91  
% 4.71/1.91  %Foreground operators:
% 4.71/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.71/1.91  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.71/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.71/1.91  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.71/1.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.71/1.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.71/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.71/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.71/1.91  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.71/1.91  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.71/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.71/1.91  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.71/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.71/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.71/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.71/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.71/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.71/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.71/1.91  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.71/1.91  
% 4.71/1.92  tff(f_114, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 4.71/1.92  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 4.71/1.92  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.71/1.92  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 4.71/1.92  tff(f_53, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.71/1.92  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.71/1.92  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 4.71/1.92  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.71/1.92  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.71/1.92  tff(f_63, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.71/1.92  tff(f_77, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.71/1.92  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.71/1.92  tff(c_58, plain, (v2_tops_1('#skF_2', '#skF_1') | r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.71/1.92  tff(c_106, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_58])).
% 4.71/1.92  tff(c_52, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.71/1.92  tff(c_261, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_52])).
% 4.71/1.92  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.71/1.92  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.71/1.92  tff(c_2208, plain, (![B_166, A_167]: (v2_tops_1(B_166, A_167) | k1_tops_1(A_167, B_166)!=k1_xboole_0 | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.71/1.92  tff(c_2219, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_2208])).
% 4.71/1.92  tff(c_2224, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2219])).
% 4.71/1.92  tff(c_2225, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_261, c_2224])).
% 4.71/1.92  tff(c_10, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.71/1.92  tff(c_1196, plain, (![A_130, B_131, C_132]: (r1_tarski(k4_xboole_0(A_130, B_131), C_132) | ~r1_tarski(A_130, k2_xboole_0(B_131, C_132)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.71/1.92  tff(c_18, plain, (![A_17]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.71/1.92  tff(c_1219, plain, (![A_130, B_131]: (k4_xboole_0(A_130, B_131)=k1_xboole_0 | ~r1_tarski(A_130, k2_xboole_0(B_131, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1196, c_18])).
% 4.71/1.92  tff(c_1252, plain, (![A_133, B_134]: (k4_xboole_0(A_133, B_134)=k1_xboole_0 | ~r1_tarski(A_133, B_134))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1219])).
% 4.71/1.92  tff(c_1322, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_106, c_1252])).
% 4.71/1.92  tff(c_1599, plain, (![A_143, B_144, C_145]: (k7_subset_1(A_143, B_144, C_145)=k4_xboole_0(B_144, C_145) | ~m1_subset_1(B_144, k1_zfmisc_1(A_143)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.71/1.92  tff(c_1608, plain, (![C_145]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_145)=k4_xboole_0('#skF_2', C_145))), inference(resolution, [status(thm)], [c_48, c_1599])).
% 4.71/1.92  tff(c_2608, plain, (![A_179, B_180]: (k7_subset_1(u1_struct_0(A_179), B_180, k2_tops_1(A_179, B_180))=k1_tops_1(A_179, B_180) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.71/1.92  tff(c_2616, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_2608])).
% 4.71/1.92  tff(c_2621, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1322, c_1608, c_2616])).
% 4.71/1.92  tff(c_2623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2225, c_2621])).
% 4.71/1.92  tff(c_2625, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_58])).
% 4.71/1.92  tff(c_16, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.71/1.92  tff(c_2624, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 4.71/1.92  tff(c_4273, plain, (![A_274, B_275]: (k1_tops_1(A_274, B_275)=k1_xboole_0 | ~v2_tops_1(B_275, A_274) | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0(A_274))) | ~l1_pre_topc(A_274))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.71/1.92  tff(c_4284, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_4273])).
% 4.71/1.92  tff(c_4289, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2624, c_4284])).
% 4.71/1.92  tff(c_4044, plain, (![A_260, B_261, C_262]: (k7_subset_1(A_260, B_261, C_262)=k4_xboole_0(B_261, C_262) | ~m1_subset_1(B_261, k1_zfmisc_1(A_260)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.71/1.92  tff(c_4053, plain, (![C_262]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_262)=k4_xboole_0('#skF_2', C_262))), inference(resolution, [status(thm)], [c_48, c_4044])).
% 4.71/1.92  tff(c_4939, plain, (![A_305, B_306]: (k7_subset_1(u1_struct_0(A_305), B_306, k2_tops_1(A_305, B_306))=k1_tops_1(A_305, B_306) | ~m1_subset_1(B_306, k1_zfmisc_1(u1_struct_0(A_305))) | ~l1_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.71/1.92  tff(c_4947, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_4939])).
% 4.71/1.92  tff(c_4952, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4289, c_4053, c_4947])).
% 4.71/1.92  tff(c_22, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.71/1.92  tff(c_4959, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4952, c_22])).
% 4.71/1.92  tff(c_4966, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4959])).
% 4.71/1.92  tff(c_26, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.71/1.92  tff(c_2805, plain, (![A_195, B_196]: (k1_setfam_1(k2_tarski(A_195, B_196))=k3_xboole_0(A_195, B_196))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.71/1.92  tff(c_2820, plain, (![B_197, A_198]: (k1_setfam_1(k2_tarski(B_197, A_198))=k3_xboole_0(A_198, B_197))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2805])).
% 4.71/1.92  tff(c_34, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.71/1.92  tff(c_2843, plain, (![B_199, A_200]: (k3_xboole_0(B_199, A_200)=k3_xboole_0(A_200, B_199))), inference(superposition, [status(thm), theory('equality')], [c_2820, c_34])).
% 4.71/1.92  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.71/1.92  tff(c_2869, plain, (![A_200, B_199]: (r1_tarski(k3_xboole_0(A_200, B_199), B_199))), inference(superposition, [status(thm), theory('equality')], [c_2843, c_8])).
% 4.71/1.92  tff(c_5008, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4966, c_2869])).
% 4.71/1.92  tff(c_5026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2625, c_5008])).
% 4.71/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.92  
% 4.71/1.92  Inference rules
% 4.71/1.92  ----------------------
% 4.71/1.92  #Ref     : 0
% 4.71/1.92  #Sup     : 1210
% 4.71/1.92  #Fact    : 0
% 4.71/1.92  #Define  : 0
% 4.71/1.92  #Split   : 3
% 4.71/1.92  #Chain   : 0
% 4.71/1.92  #Close   : 0
% 4.71/1.92  
% 4.71/1.92  Ordering : KBO
% 4.71/1.92  
% 4.71/1.92  Simplification rules
% 4.71/1.92  ----------------------
% 4.71/1.92  #Subsume      : 59
% 4.71/1.92  #Demod        : 664
% 4.71/1.92  #Tautology    : 813
% 4.71/1.92  #SimpNegUnit  : 3
% 4.71/1.92  #BackRed      : 1
% 4.71/1.92  
% 4.71/1.92  #Partial instantiations: 0
% 4.71/1.92  #Strategies tried      : 1
% 4.71/1.92  
% 4.71/1.92  Timing (in seconds)
% 4.71/1.92  ----------------------
% 4.71/1.92  Preprocessing        : 0.34
% 4.71/1.92  Parsing              : 0.18
% 4.71/1.92  CNF conversion       : 0.02
% 4.71/1.92  Main loop            : 0.82
% 4.71/1.92  Inferencing          : 0.26
% 4.71/1.92  Reduction            : 0.33
% 4.71/1.92  Demodulation         : 0.26
% 4.71/1.92  BG Simplification    : 0.03
% 4.71/1.92  Subsumption          : 0.14
% 4.71/1.92  Abstraction          : 0.04
% 4.71/1.92  MUC search           : 0.00
% 4.71/1.92  Cooper               : 0.00
% 4.71/1.92  Total                : 1.19
% 4.71/1.92  Index Insertion      : 0.00
% 4.71/1.92  Index Deletion       : 0.00
% 4.71/1.92  Index Matching       : 0.00
% 4.71/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
