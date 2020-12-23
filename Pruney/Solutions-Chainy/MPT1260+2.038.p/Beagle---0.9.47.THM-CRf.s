%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:05 EST 2020

% Result     : Theorem 56.54s
% Output     : CNFRefutation 56.71s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 445 expanded)
%              Number of leaves         :   60 ( 170 expanded)
%              Depth                    :   11
%              Number of atoms          :  305 ( 855 expanded)
%              Number of equality atoms :  122 ( 285 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_193,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_181,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_174,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_84,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_167,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_160,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_146,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_86,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_129,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_4053,plain,(
    ! [A_232,B_233,C_234] :
      ( k7_subset_1(A_232,B_233,C_234) = k4_xboole_0(B_233,C_234)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(A_232)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4068,plain,(
    ! [C_234] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_234) = k4_xboole_0('#skF_3',C_234) ),
    inference(resolution,[status(thm)],[c_80,c_4053])).

tff(c_6853,plain,(
    ! [A_314,B_315] :
      ( k7_subset_1(u1_struct_0(A_314),B_315,k2_tops_1(A_314,B_315)) = k1_tops_1(A_314,B_315)
      | ~ m1_subset_1(B_315,k1_zfmisc_1(u1_struct_0(A_314)))
      | ~ l1_pre_topc(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_6868,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_6853])).

tff(c_6879,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4068,c_6868])).

tff(c_26,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1196,plain,(
    ! [B_144,A_145] :
      ( B_144 = A_145
      | ~ r1_tarski(B_144,A_145)
      | ~ r1_tarski(A_145,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_13933,plain,(
    ! [A_410,B_411] :
      ( k4_xboole_0(A_410,B_411) = A_410
      | ~ r1_tarski(A_410,k4_xboole_0(A_410,B_411)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1196])).

tff(c_13966,plain,
    ( k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6879,c_13933])).

tff(c_14035,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6879,c_13966])).

tff(c_101108,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_14035])).

tff(c_101116,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_101108])).

tff(c_7195,plain,(
    ! [A_316,B_317] :
      ( k4_subset_1(u1_struct_0(A_316),B_317,k2_tops_1(A_316,B_317)) = k2_pre_topc(A_316,B_317)
      | ~ m1_subset_1(B_317,k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ l1_pre_topc(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_7210,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_7195])).

tff(c_7221,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_7210])).

tff(c_42,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(k3_subset_1(A_36,B_37),k1_zfmisc_1(A_36))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    ! [A_38] : m1_subset_1('#skF_1'(A_38),A_38) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1903,plain,(
    ! [A_168,B_169,C_170] :
      ( k9_subset_1(A_168,B_169,B_169) = B_169
      | ~ m1_subset_1(C_170,k1_zfmisc_1(A_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1915,plain,(
    ! [A_168,B_169] : k9_subset_1(A_168,B_169,B_169) = B_169 ),
    inference(resolution,[status(thm)],[c_44,c_1903])).

tff(c_7304,plain,(
    ! [A_319,B_320,C_321] :
      ( k9_subset_1(A_319,B_320,k3_subset_1(A_319,C_321)) = k7_subset_1(A_319,B_320,C_321)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(A_319))
      | ~ m1_subset_1(B_320,k1_zfmisc_1(A_319)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_7328,plain,(
    ! [B_322] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_322,k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k7_subset_1(u1_struct_0('#skF_2'),B_322,'#skF_3')
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_7304])).

tff(c_7342,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1915,c_7328])).

tff(c_12290,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_7342])).

tff(c_13766,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_42,c_12290])).

tff(c_13773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_13766])).

tff(c_13775,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_7342])).

tff(c_6746,plain,(
    ! [A_309,B_310] :
      ( k2_tops_1(A_309,k3_subset_1(u1_struct_0(A_309),B_310)) = k2_tops_1(A_309,B_310)
      | ~ m1_subset_1(B_310,k1_zfmisc_1(u1_struct_0(A_309)))
      | ~ l1_pre_topc(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_6761,plain,
    ( k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_6746])).

tff(c_6772,plain,(
    k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6761])).

tff(c_5813,plain,(
    ! [A_282,B_283] :
      ( m1_subset_1(k2_tops_1(A_282,B_283),k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_pre_topc(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_60,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28321,plain,(
    ! [A_551,B_552] :
      ( r1_tarski(k2_tops_1(A_551,B_552),u1_struct_0(A_551))
      | ~ m1_subset_1(B_552,k1_zfmisc_1(u1_struct_0(A_551)))
      | ~ l1_pre_topc(A_551) ) ),
    inference(resolution,[status(thm)],[c_5813,c_60])).

tff(c_28354,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6772,c_28321])).

tff(c_28370,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_13775,c_28354])).

tff(c_62,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(A_59,k1_zfmisc_1(B_60))
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6559,plain,(
    ! [A_302,B_303,C_304] :
      ( k4_subset_1(A_302,B_303,C_304) = k2_xboole_0(B_303,C_304)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(A_302))
      | ~ m1_subset_1(B_303,k1_zfmisc_1(A_302)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_33365,plain,(
    ! [B_597,B_598,A_599] :
      ( k4_subset_1(B_597,B_598,A_599) = k2_xboole_0(B_598,A_599)
      | ~ m1_subset_1(B_598,k1_zfmisc_1(B_597))
      | ~ r1_tarski(A_599,B_597) ) ),
    inference(resolution,[status(thm)],[c_62,c_6559])).

tff(c_33398,plain,(
    ! [A_600] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_600) = k2_xboole_0('#skF_3',A_600)
      | ~ r1_tarski(A_600,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_80,c_33365])).

tff(c_33413,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28370,c_33398])).

tff(c_33602,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7221,c_33413])).

tff(c_175,plain,(
    ! [B_99,A_100] : k2_xboole_0(B_99,A_100) = k2_xboole_0(A_100,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_197,plain,(
    ! [A_100] : k2_xboole_0(k1_xboole_0,A_100) = A_100 ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_20])).

tff(c_994,plain,(
    ! [A_138,B_139] : k2_xboole_0(A_138,k4_xboole_0(B_139,A_138)) = k2_xboole_0(A_138,B_139) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1008,plain,(
    ! [B_139] : k4_xboole_0(B_139,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_197])).

tff(c_1052,plain,(
    ! [B_139] : k4_xboole_0(B_139,k1_xboole_0) = B_139 ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_1008])).

tff(c_116,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k2_xboole_0(A_93,B_94)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_121,plain,(
    ! [A_93] : r1_tarski(k1_xboole_0,A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_26])).

tff(c_1342,plain,(
    ! [A_151,C_152,B_153] :
      ( r1_tarski(A_151,C_152)
      | ~ r1_tarski(B_153,C_152)
      | ~ r1_tarski(A_151,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1361,plain,(
    ! [A_154,A_155] :
      ( r1_tarski(A_154,A_155)
      | ~ r1_tarski(A_154,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_121,c_1342])).

tff(c_1364,plain,(
    ! [A_7,A_155] :
      ( r1_tarski(A_7,A_155)
      | k4_xboole_0(A_7,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_1361])).

tff(c_1389,plain,(
    ! [A_156,A_157] :
      ( r1_tarski(A_156,A_157)
      | k1_xboole_0 != A_156 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_1364])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1432,plain,(
    ! [A_157] : k2_xboole_0(k1_xboole_0,A_157) = A_157 ),
    inference(resolution,[status(thm)],[c_1389,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_228,plain,(
    ! [A_101,B_102] : k2_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = A_101 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_240,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_228])).

tff(c_1254,plain,(
    ! [A_147,B_148] : k4_xboole_0(A_147,k3_xboole_0(A_147,B_148)) = k4_xboole_0(A_147,B_148) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8762,plain,(
    ! [A_349,B_350] : k4_xboole_0(A_349,k3_xboole_0(B_350,A_349)) = k4_xboole_0(A_349,B_350) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1254])).

tff(c_28,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8836,plain,(
    ! [B_350,A_349] : k2_xboole_0(k3_xboole_0(B_350,A_349),k4_xboole_0(A_349,B_350)) = k2_xboole_0(k3_xboole_0(B_350,A_349),A_349) ),
    inference(superposition,[status(thm),theory(equality)],[c_8762,c_28])).

tff(c_17706,plain,(
    ! [B_471,A_472] : k2_xboole_0(k3_xboole_0(B_471,A_472),k4_xboole_0(A_472,B_471)) = A_472 ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_2,c_8836])).

tff(c_17895,plain,(
    ! [A_29,B_30] : k2_xboole_0(k3_xboole_0(k2_xboole_0(A_29,B_30),A_29),k1_xboole_0) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_17706])).

tff(c_17939,plain,(
    ! [A_29,B_30] : k3_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1432,c_2,c_4,c_17895])).

tff(c_34203,plain,(
    k3_xboole_0('#skF_3',k2_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_33602,c_17939])).

tff(c_5245,plain,(
    ! [A_265,B_266] :
      ( m1_subset_1(k2_pre_topc(A_265,B_266),k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_52,plain,(
    ! [A_48,B_49,C_50] :
      ( k7_subset_1(A_48,B_49,C_50) = k4_xboole_0(B_49,C_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_45117,plain,(
    ! [A_700,B_701,C_702] :
      ( k7_subset_1(u1_struct_0(A_700),k2_pre_topc(A_700,B_701),C_702) = k4_xboole_0(k2_pre_topc(A_700,B_701),C_702)
      | ~ m1_subset_1(B_701,k1_zfmisc_1(u1_struct_0(A_700)))
      | ~ l1_pre_topc(A_700) ) ),
    inference(resolution,[status(thm)],[c_5245,c_52])).

tff(c_45137,plain,(
    ! [C_702] :
      ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_702) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_702)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_80,c_45117])).

tff(c_45730,plain,(
    ! [C_706] : k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_706) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_706) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_45137])).

tff(c_92,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_297,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_92])).

tff(c_45744,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_45730,c_297])).

tff(c_2139,plain,(
    ! [A_178,B_179,C_180] :
      ( r1_tarski(A_178,k2_xboole_0(B_179,C_180))
      | ~ r1_tarski(k4_xboole_0(A_178,B_179),C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2225,plain,(
    ! [A_181,B_182] : r1_tarski(A_181,k2_xboole_0(B_182,A_181)) ),
    inference(resolution,[status(thm)],[c_26,c_2139])).

tff(c_2269,plain,(
    ! [B_4,A_3] : r1_tarski(k3_xboole_0(B_4,A_3),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_2225])).

tff(c_1292,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1254])).

tff(c_2891,plain,(
    ! [A_199,B_200] :
      ( k4_xboole_0(A_199,B_200) = k3_subset_1(A_199,B_200)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(A_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_11835,plain,(
    ! [B_385,A_386] :
      ( k4_xboole_0(B_385,A_386) = k3_subset_1(B_385,A_386)
      | ~ r1_tarski(A_386,B_385) ) ),
    inference(resolution,[status(thm)],[c_62,c_2891])).

tff(c_12006,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k3_subset_1(A_3,k3_xboole_0(B_4,A_3)) ),
    inference(resolution,[status(thm)],[c_2269,c_11835])).

tff(c_39442,plain,(
    ! [A_659,B_660] : k3_subset_1(A_659,k3_xboole_0(B_660,A_659)) = k4_xboole_0(A_659,B_660) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1292,c_12006])).

tff(c_2959,plain,(
    ! [A_201,B_202] :
      ( k3_subset_1(A_201,k3_subset_1(A_201,B_202)) = B_202
      | ~ m1_subset_1(B_202,k1_zfmisc_1(A_201)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2972,plain,(
    ! [B_60,A_59] :
      ( k3_subset_1(B_60,k3_subset_1(B_60,A_59)) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_62,c_2959])).

tff(c_39472,plain,(
    ! [A_659,B_660] :
      ( k3_subset_1(A_659,k4_xboole_0(A_659,B_660)) = k3_xboole_0(B_660,A_659)
      | ~ r1_tarski(k3_xboole_0(B_660,A_659),A_659) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39442,c_2972])).

tff(c_39583,plain,(
    ! [A_659,B_660] : k3_subset_1(A_659,k4_xboole_0(A_659,B_660)) = k3_xboole_0(B_660,A_659) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2269,c_39472])).

tff(c_45784,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = k3_xboole_0('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_45744,c_39583])).

tff(c_45899,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34203,c_45784])).

tff(c_6919,plain,(
    k2_xboole_0(k2_tops_1('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3')) = k2_xboole_0(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6879,c_28])).

tff(c_6940,plain,(
    k2_xboole_0(k2_tops_1('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6919])).

tff(c_205783,plain,(
    k2_xboole_0(k2_tops_1('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33602,c_6940])).

tff(c_2222,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(B_20,A_19)) ),
    inference(resolution,[status(thm)],[c_26,c_2139])).

tff(c_12091,plain,(
    ! [B_20,A_19] : k4_xboole_0(k2_xboole_0(B_20,A_19),A_19) = k3_subset_1(k2_xboole_0(B_20,A_19),A_19) ),
    inference(resolution,[status(thm)],[c_2222,c_11835])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3006,plain,(
    ! [A_206,B_207,C_208] :
      ( r1_tarski(k4_xboole_0(A_206,B_207),C_208)
      | ~ r1_tarski(A_206,k2_xboole_0(B_207,C_208)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18211,plain,(
    ! [A_475,B_476,C_477] :
      ( k4_xboole_0(k4_xboole_0(A_475,B_476),C_477) = k1_xboole_0
      | ~ r1_tarski(A_475,k2_xboole_0(B_476,C_477)) ) ),
    inference(resolution,[status(thm)],[c_3006,c_14])).

tff(c_23374,plain,(
    ! [B_516,C_517] : k4_xboole_0(k4_xboole_0(k2_xboole_0(B_516,C_517),B_516),C_517) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_18211])).

tff(c_23576,plain,(
    ! [A_1,B_2] : k4_xboole_0(k4_xboole_0(k2_xboole_0(A_1,B_2),B_2),A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_23374])).

tff(c_123734,plain,(
    ! [A_1117,B_1118] : k4_xboole_0(k3_subset_1(k2_xboole_0(A_1117,B_1118),B_1118),A_1117) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12091,c_23576])).

tff(c_124225,plain,(
    ! [A_1,B_2] : k4_xboole_0(k3_subset_1(k2_xboole_0(A_1,B_2),A_1),B_2) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_123734])).

tff(c_205851,plain,(
    k4_xboole_0(k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')),k1_tops_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_205783,c_124225])).

tff(c_206124,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_45899,c_205851])).

tff(c_206126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101116,c_206124])).

tff(c_206127,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14035])).

tff(c_84,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_4656,plain,(
    ! [A_249,B_250] :
      ( v3_pre_topc(k1_tops_1(A_249,B_250),A_249)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4667,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_4656])).

tff(c_4676,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_4667])).

tff(c_206157,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206127,c_4676])).

tff(c_206183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_206157])).

tff(c_206184,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_209154,plain,(
    ! [A_1508,B_1509,C_1510] :
      ( k7_subset_1(A_1508,B_1509,C_1510) = k4_xboole_0(B_1509,C_1510)
      | ~ m1_subset_1(B_1509,k1_zfmisc_1(A_1508)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_209169,plain,(
    ! [C_1510] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_1510) = k4_xboole_0('#skF_3',C_1510) ),
    inference(resolution,[status(thm)],[c_80,c_209154])).

tff(c_212806,plain,(
    ! [A_1611,B_1612] :
      ( k7_subset_1(u1_struct_0(A_1611),B_1612,k2_tops_1(A_1611,B_1612)) = k1_tops_1(A_1611,B_1612)
      | ~ m1_subset_1(B_1612,k1_zfmisc_1(u1_struct_0(A_1611)))
      | ~ l1_pre_topc(A_1611) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_212821,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_212806])).

tff(c_212832,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_209169,c_212821])).

tff(c_206669,plain,(
    ! [A_1418,B_1419] :
      ( k4_xboole_0(A_1418,B_1419) = k1_xboole_0
      | ~ r1_tarski(A_1418,B_1419) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_206685,plain,(
    ! [A_19,B_20] : k4_xboole_0(k4_xboole_0(A_19,B_20),A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_206669])).

tff(c_212968,plain,(
    k4_xboole_0(k1_tops_1('#skF_2','#skF_3'),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_212832,c_206685])).

tff(c_206185,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_213381,plain,(
    ! [B_1620,A_1621,C_1622] :
      ( r1_tarski(B_1620,k1_tops_1(A_1621,C_1622))
      | ~ r1_tarski(B_1620,C_1622)
      | ~ v3_pre_topc(B_1620,A_1621)
      | ~ m1_subset_1(C_1622,k1_zfmisc_1(u1_struct_0(A_1621)))
      | ~ m1_subset_1(B_1620,k1_zfmisc_1(u1_struct_0(A_1621)))
      | ~ l1_pre_topc(A_1621) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_213396,plain,(
    ! [B_1620] :
      ( r1_tarski(B_1620,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_1620,'#skF_3')
      | ~ v3_pre_topc(B_1620,'#skF_2')
      | ~ m1_subset_1(B_1620,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_80,c_213381])).

tff(c_216934,plain,(
    ! [B_1668] :
      ( r1_tarski(B_1668,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_1668,'#skF_3')
      | ~ v3_pre_topc(B_1668,'#skF_2')
      | ~ m1_subset_1(B_1668,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_213396])).

tff(c_216961,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_216934])).

tff(c_216980,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206185,c_10,c_216961])).

tff(c_207288,plain,(
    ! [B_1443,A_1444] :
      ( B_1443 = A_1444
      | ~ r1_tarski(B_1443,A_1444)
      | ~ r1_tarski(A_1444,B_1443) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_207303,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_207288])).

tff(c_216984,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | k4_xboole_0(k1_tops_1('#skF_2','#skF_3'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_216980,c_207303])).

tff(c_217000,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212968,c_216984])).

tff(c_70,plain,(
    ! [A_67,B_69] :
      ( k7_subset_1(u1_struct_0(A_67),k2_pre_topc(A_67,B_69),k1_tops_1(A_67,B_69)) = k2_tops_1(A_67,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_217040,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_217000,c_70])).

tff(c_217044,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_217040])).

tff(c_217046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_206184,c_217044])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 56.54/45.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.54/45.83  
% 56.54/45.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.54/45.84  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 56.54/45.84  
% 56.54/45.84  %Foreground sorts:
% 56.54/45.84  
% 56.54/45.84  
% 56.54/45.84  %Background operators:
% 56.54/45.84  
% 56.54/45.84  
% 56.54/45.84  %Foreground operators:
% 56.54/45.84  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 56.54/45.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 56.54/45.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 56.54/45.84  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 56.54/45.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 56.54/45.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 56.54/45.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 56.54/45.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 56.54/45.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 56.54/45.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 56.54/45.84  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 56.54/45.84  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 56.54/45.84  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 56.54/45.84  tff('#skF_2', type, '#skF_2': $i).
% 56.54/45.84  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 56.54/45.84  tff('#skF_3', type, '#skF_3': $i).
% 56.54/45.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 56.54/45.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 56.54/45.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 56.54/45.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 56.54/45.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 56.54/45.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 56.54/45.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 56.54/45.84  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 56.54/45.84  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 56.54/45.84  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 56.54/45.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 56.54/45.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 56.54/45.84  
% 56.71/45.87  tff(f_193, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 56.71/45.87  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 56.71/45.87  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 56.71/45.87  tff(f_181, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 56.71/45.87  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 56.71/45.87  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 56.71/45.87  tff(f_174, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 56.71/45.87  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 56.71/45.87  tff(f_84, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 56.71/45.87  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 56.71/45.87  tff(f_113, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 56.71/45.87  tff(f_167, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 56.71/45.87  tff(f_131, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 56.71/45.87  tff(f_119, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 56.71/45.87  tff(f_98, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 56.71/45.87  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 56.71/45.87  tff(f_47, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 56.71/45.87  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 56.71/45.87  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 56.71/45.87  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 56.71/45.87  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 56.71/45.87  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 56.71/45.87  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 56.71/45.87  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 56.71/45.87  tff(f_125, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 56.71/45.87  tff(f_67, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 56.71/45.87  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 56.71/45.87  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 56.71/45.87  tff(f_63, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 56.71/45.87  tff(f_139, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 56.71/45.87  tff(f_160, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 56.71/45.87  tff(f_146, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 56.71/45.87  tff(c_86, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 56.71/45.87  tff(c_129, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_86])).
% 56.71/45.87  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 56.71/45.87  tff(c_82, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 56.71/45.87  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 56.71/45.87  tff(c_4053, plain, (![A_232, B_233, C_234]: (k7_subset_1(A_232, B_233, C_234)=k4_xboole_0(B_233, C_234) | ~m1_subset_1(B_233, k1_zfmisc_1(A_232)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 56.71/45.87  tff(c_4068, plain, (![C_234]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_234)=k4_xboole_0('#skF_3', C_234))), inference(resolution, [status(thm)], [c_80, c_4053])).
% 56.71/45.87  tff(c_6853, plain, (![A_314, B_315]: (k7_subset_1(u1_struct_0(A_314), B_315, k2_tops_1(A_314, B_315))=k1_tops_1(A_314, B_315) | ~m1_subset_1(B_315, k1_zfmisc_1(u1_struct_0(A_314))) | ~l1_pre_topc(A_314))), inference(cnfTransformation, [status(thm)], [f_181])).
% 56.71/45.87  tff(c_6868, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_80, c_6853])).
% 56.71/45.87  tff(c_6879, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4068, c_6868])).
% 56.71/45.87  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 56.71/45.87  tff(c_1196, plain, (![B_144, A_145]: (B_144=A_145 | ~r1_tarski(B_144, A_145) | ~r1_tarski(A_145, B_144))), inference(cnfTransformation, [status(thm)], [f_35])).
% 56.71/45.87  tff(c_13933, plain, (![A_410, B_411]: (k4_xboole_0(A_410, B_411)=A_410 | ~r1_tarski(A_410, k4_xboole_0(A_410, B_411)))), inference(resolution, [status(thm)], [c_26, c_1196])).
% 56.71/45.87  tff(c_13966, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6879, c_13933])).
% 56.71/45.87  tff(c_14035, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6879, c_13966])).
% 56.71/45.87  tff(c_101108, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_14035])).
% 56.71/45.87  tff(c_101116, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_101108])).
% 56.71/45.87  tff(c_7195, plain, (![A_316, B_317]: (k4_subset_1(u1_struct_0(A_316), B_317, k2_tops_1(A_316, B_317))=k2_pre_topc(A_316, B_317) | ~m1_subset_1(B_317, k1_zfmisc_1(u1_struct_0(A_316))) | ~l1_pre_topc(A_316))), inference(cnfTransformation, [status(thm)], [f_174])).
% 56.71/45.87  tff(c_7210, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_80, c_7195])).
% 56.71/45.87  tff(c_7221, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_7210])).
% 56.71/45.87  tff(c_42, plain, (![A_36, B_37]: (m1_subset_1(k3_subset_1(A_36, B_37), k1_zfmisc_1(A_36)) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 56.71/45.87  tff(c_44, plain, (![A_38]: (m1_subset_1('#skF_1'(A_38), A_38))), inference(cnfTransformation, [status(thm)], [f_84])).
% 56.71/45.87  tff(c_1903, plain, (![A_168, B_169, C_170]: (k9_subset_1(A_168, B_169, B_169)=B_169 | ~m1_subset_1(C_170, k1_zfmisc_1(A_168)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 56.71/45.87  tff(c_1915, plain, (![A_168, B_169]: (k9_subset_1(A_168, B_169, B_169)=B_169)), inference(resolution, [status(thm)], [c_44, c_1903])).
% 56.71/45.87  tff(c_7304, plain, (![A_319, B_320, C_321]: (k9_subset_1(A_319, B_320, k3_subset_1(A_319, C_321))=k7_subset_1(A_319, B_320, C_321) | ~m1_subset_1(C_321, k1_zfmisc_1(A_319)) | ~m1_subset_1(B_320, k1_zfmisc_1(A_319)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 56.71/45.87  tff(c_7328, plain, (![B_322]: (k9_subset_1(u1_struct_0('#skF_2'), B_322, k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k7_subset_1(u1_struct_0('#skF_2'), B_322, '#skF_3') | ~m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_80, c_7304])).
% 56.71/45.87  tff(c_7342, plain, (k7_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1915, c_7328])).
% 56.71/45.87  tff(c_12290, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_7342])).
% 56.71/45.87  tff(c_13766, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_42, c_12290])).
% 56.71/45.87  tff(c_13773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_13766])).
% 56.71/45.87  tff(c_13775, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_7342])).
% 56.71/45.87  tff(c_6746, plain, (![A_309, B_310]: (k2_tops_1(A_309, k3_subset_1(u1_struct_0(A_309), B_310))=k2_tops_1(A_309, B_310) | ~m1_subset_1(B_310, k1_zfmisc_1(u1_struct_0(A_309))) | ~l1_pre_topc(A_309))), inference(cnfTransformation, [status(thm)], [f_167])).
% 56.71/45.87  tff(c_6761, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_80, c_6746])).
% 56.71/45.87  tff(c_6772, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_6761])).
% 56.71/45.87  tff(c_5813, plain, (![A_282, B_283]: (m1_subset_1(k2_tops_1(A_282, B_283), k1_zfmisc_1(u1_struct_0(A_282))) | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0(A_282))) | ~l1_pre_topc(A_282))), inference(cnfTransformation, [status(thm)], [f_131])).
% 56.71/45.87  tff(c_60, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~m1_subset_1(A_59, k1_zfmisc_1(B_60)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 56.71/45.87  tff(c_28321, plain, (![A_551, B_552]: (r1_tarski(k2_tops_1(A_551, B_552), u1_struct_0(A_551)) | ~m1_subset_1(B_552, k1_zfmisc_1(u1_struct_0(A_551))) | ~l1_pre_topc(A_551))), inference(resolution, [status(thm)], [c_5813, c_60])).
% 56.71/45.87  tff(c_28354, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6772, c_28321])).
% 56.71/45.87  tff(c_28370, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_13775, c_28354])).
% 56.71/45.87  tff(c_62, plain, (![A_59, B_60]: (m1_subset_1(A_59, k1_zfmisc_1(B_60)) | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_119])).
% 56.71/45.87  tff(c_6559, plain, (![A_302, B_303, C_304]: (k4_subset_1(A_302, B_303, C_304)=k2_xboole_0(B_303, C_304) | ~m1_subset_1(C_304, k1_zfmisc_1(A_302)) | ~m1_subset_1(B_303, k1_zfmisc_1(A_302)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 56.71/45.87  tff(c_33365, plain, (![B_597, B_598, A_599]: (k4_subset_1(B_597, B_598, A_599)=k2_xboole_0(B_598, A_599) | ~m1_subset_1(B_598, k1_zfmisc_1(B_597)) | ~r1_tarski(A_599, B_597))), inference(resolution, [status(thm)], [c_62, c_6559])).
% 56.71/45.87  tff(c_33398, plain, (![A_600]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_600)=k2_xboole_0('#skF_3', A_600) | ~r1_tarski(A_600, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_80, c_33365])).
% 56.71/45.87  tff(c_33413, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_28370, c_33398])).
% 56.71/45.87  tff(c_33602, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7221, c_33413])).
% 56.71/45.87  tff(c_175, plain, (![B_99, A_100]: (k2_xboole_0(B_99, A_100)=k2_xboole_0(A_100, B_99))), inference(cnfTransformation, [status(thm)], [f_27])).
% 56.71/45.87  tff(c_20, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 56.71/45.87  tff(c_197, plain, (![A_100]: (k2_xboole_0(k1_xboole_0, A_100)=A_100)), inference(superposition, [status(thm), theory('equality')], [c_175, c_20])).
% 56.71/45.87  tff(c_994, plain, (![A_138, B_139]: (k2_xboole_0(A_138, k4_xboole_0(B_139, A_138))=k2_xboole_0(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_59])).
% 56.71/45.87  tff(c_1008, plain, (![B_139]: (k4_xboole_0(B_139, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_139))), inference(superposition, [status(thm), theory('equality')], [c_994, c_197])).
% 56.71/45.87  tff(c_1052, plain, (![B_139]: (k4_xboole_0(B_139, k1_xboole_0)=B_139)), inference(demodulation, [status(thm), theory('equality')], [c_197, c_1008])).
% 56.71/45.87  tff(c_116, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k2_xboole_0(A_93, B_94))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 56.71/45.87  tff(c_121, plain, (![A_93]: (r1_tarski(k1_xboole_0, A_93))), inference(superposition, [status(thm), theory('equality')], [c_116, c_26])).
% 56.71/45.87  tff(c_1342, plain, (![A_151, C_152, B_153]: (r1_tarski(A_151, C_152) | ~r1_tarski(B_153, C_152) | ~r1_tarski(A_151, B_153))), inference(cnfTransformation, [status(thm)], [f_53])).
% 56.71/45.87  tff(c_1361, plain, (![A_154, A_155]: (r1_tarski(A_154, A_155) | ~r1_tarski(A_154, k1_xboole_0))), inference(resolution, [status(thm)], [c_121, c_1342])).
% 56.71/45.87  tff(c_1364, plain, (![A_7, A_155]: (r1_tarski(A_7, A_155) | k4_xboole_0(A_7, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_1361])).
% 56.71/45.87  tff(c_1389, plain, (![A_156, A_157]: (r1_tarski(A_156, A_157) | k1_xboole_0!=A_156)), inference(demodulation, [status(thm), theory('equality')], [c_1052, c_1364])).
% 56.71/45.87  tff(c_18, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 56.71/45.87  tff(c_1432, plain, (![A_157]: (k2_xboole_0(k1_xboole_0, A_157)=A_157)), inference(resolution, [status(thm)], [c_1389, c_18])).
% 56.71/45.87  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 56.71/45.87  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 56.71/45.87  tff(c_34, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k2_xboole_0(A_29, B_30))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 56.71/45.87  tff(c_228, plain, (![A_101, B_102]: (k2_xboole_0(A_101, k3_xboole_0(A_101, B_102))=A_101)), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.71/45.87  tff(c_240, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(B_4, A_3))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_228])).
% 56.71/45.87  tff(c_1254, plain, (![A_147, B_148]: (k4_xboole_0(A_147, k3_xboole_0(A_147, B_148))=k4_xboole_0(A_147, B_148))), inference(cnfTransformation, [status(thm)], [f_71])).
% 56.71/45.87  tff(c_8762, plain, (![A_349, B_350]: (k4_xboole_0(A_349, k3_xboole_0(B_350, A_349))=k4_xboole_0(A_349, B_350))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1254])).
% 56.71/45.87  tff(c_28, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 56.71/45.87  tff(c_8836, plain, (![B_350, A_349]: (k2_xboole_0(k3_xboole_0(B_350, A_349), k4_xboole_0(A_349, B_350))=k2_xboole_0(k3_xboole_0(B_350, A_349), A_349))), inference(superposition, [status(thm), theory('equality')], [c_8762, c_28])).
% 56.71/45.87  tff(c_17706, plain, (![B_471, A_472]: (k2_xboole_0(k3_xboole_0(B_471, A_472), k4_xboole_0(A_472, B_471))=A_472)), inference(demodulation, [status(thm), theory('equality')], [c_240, c_2, c_8836])).
% 56.71/45.87  tff(c_17895, plain, (![A_29, B_30]: (k2_xboole_0(k3_xboole_0(k2_xboole_0(A_29, B_30), A_29), k1_xboole_0)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_34, c_17706])).
% 56.71/45.87  tff(c_17939, plain, (![A_29, B_30]: (k3_xboole_0(A_29, k2_xboole_0(A_29, B_30))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_1432, c_2, c_4, c_17895])).
% 56.71/45.87  tff(c_34203, plain, (k3_xboole_0('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_33602, c_17939])).
% 56.71/45.87  tff(c_5245, plain, (![A_265, B_266]: (m1_subset_1(k2_pre_topc(A_265, B_266), k1_zfmisc_1(u1_struct_0(A_265))) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265))), inference(cnfTransformation, [status(thm)], [f_125])).
% 56.71/45.87  tff(c_52, plain, (![A_48, B_49, C_50]: (k7_subset_1(A_48, B_49, C_50)=k4_xboole_0(B_49, C_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 56.71/45.87  tff(c_45117, plain, (![A_700, B_701, C_702]: (k7_subset_1(u1_struct_0(A_700), k2_pre_topc(A_700, B_701), C_702)=k4_xboole_0(k2_pre_topc(A_700, B_701), C_702) | ~m1_subset_1(B_701, k1_zfmisc_1(u1_struct_0(A_700))) | ~l1_pre_topc(A_700))), inference(resolution, [status(thm)], [c_5245, c_52])).
% 56.71/45.87  tff(c_45137, plain, (![C_702]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_702)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_702) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_80, c_45117])).
% 56.71/45.87  tff(c_45730, plain, (![C_706]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_706)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_706))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_45137])).
% 56.71/45.87  tff(c_92, plain, (v3_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_193])).
% 56.71/45.87  tff(c_297, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_129, c_92])).
% 56.71/45.87  tff(c_45744, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_45730, c_297])).
% 56.71/45.87  tff(c_2139, plain, (![A_178, B_179, C_180]: (r1_tarski(A_178, k2_xboole_0(B_179, C_180)) | ~r1_tarski(k4_xboole_0(A_178, B_179), C_180))), inference(cnfTransformation, [status(thm)], [f_67])).
% 56.71/45.87  tff(c_2225, plain, (![A_181, B_182]: (r1_tarski(A_181, k2_xboole_0(B_182, A_181)))), inference(resolution, [status(thm)], [c_26, c_2139])).
% 56.71/45.87  tff(c_2269, plain, (![B_4, A_3]: (r1_tarski(k3_xboole_0(B_4, A_3), A_3))), inference(superposition, [status(thm), theory('equality')], [c_240, c_2225])).
% 56.71/45.87  tff(c_1292, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1254])).
% 56.71/45.87  tff(c_2891, plain, (![A_199, B_200]: (k4_xboole_0(A_199, B_200)=k3_subset_1(A_199, B_200) | ~m1_subset_1(B_200, k1_zfmisc_1(A_199)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 56.71/45.87  tff(c_11835, plain, (![B_385, A_386]: (k4_xboole_0(B_385, A_386)=k3_subset_1(B_385, A_386) | ~r1_tarski(A_386, B_385))), inference(resolution, [status(thm)], [c_62, c_2891])).
% 56.71/45.87  tff(c_12006, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k3_subset_1(A_3, k3_xboole_0(B_4, A_3)))), inference(resolution, [status(thm)], [c_2269, c_11835])).
% 56.71/45.87  tff(c_39442, plain, (![A_659, B_660]: (k3_subset_1(A_659, k3_xboole_0(B_660, A_659))=k4_xboole_0(A_659, B_660))), inference(demodulation, [status(thm), theory('equality')], [c_1292, c_12006])).
% 56.71/45.87  tff(c_2959, plain, (![A_201, B_202]: (k3_subset_1(A_201, k3_subset_1(A_201, B_202))=B_202 | ~m1_subset_1(B_202, k1_zfmisc_1(A_201)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 56.71/45.87  tff(c_2972, plain, (![B_60, A_59]: (k3_subset_1(B_60, k3_subset_1(B_60, A_59))=A_59 | ~r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_62, c_2959])).
% 56.71/45.87  tff(c_39472, plain, (![A_659, B_660]: (k3_subset_1(A_659, k4_xboole_0(A_659, B_660))=k3_xboole_0(B_660, A_659) | ~r1_tarski(k3_xboole_0(B_660, A_659), A_659))), inference(superposition, [status(thm), theory('equality')], [c_39442, c_2972])).
% 56.71/45.87  tff(c_39583, plain, (![A_659, B_660]: (k3_subset_1(A_659, k4_xboole_0(A_659, B_660))=k3_xboole_0(B_660, A_659))), inference(demodulation, [status(thm), theory('equality')], [c_2269, c_39472])).
% 56.71/45.87  tff(c_45784, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))=k3_xboole_0('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_45744, c_39583])).
% 56.71/45.87  tff(c_45899, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34203, c_45784])).
% 56.71/45.87  tff(c_6919, plain, (k2_xboole_0(k2_tops_1('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3'))=k2_xboole_0(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6879, c_28])).
% 56.71/45.87  tff(c_6940, plain, (k2_xboole_0(k2_tops_1('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6919])).
% 56.71/45.87  tff(c_205783, plain, (k2_xboole_0(k2_tops_1('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33602, c_6940])).
% 56.71/45.87  tff(c_2222, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(B_20, A_19)))), inference(resolution, [status(thm)], [c_26, c_2139])).
% 56.71/45.87  tff(c_12091, plain, (![B_20, A_19]: (k4_xboole_0(k2_xboole_0(B_20, A_19), A_19)=k3_subset_1(k2_xboole_0(B_20, A_19), A_19))), inference(resolution, [status(thm)], [c_2222, c_11835])).
% 56.71/45.87  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 56.71/45.87  tff(c_3006, plain, (![A_206, B_207, C_208]: (r1_tarski(k4_xboole_0(A_206, B_207), C_208) | ~r1_tarski(A_206, k2_xboole_0(B_207, C_208)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 56.71/45.87  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 56.71/45.87  tff(c_18211, plain, (![A_475, B_476, C_477]: (k4_xboole_0(k4_xboole_0(A_475, B_476), C_477)=k1_xboole_0 | ~r1_tarski(A_475, k2_xboole_0(B_476, C_477)))), inference(resolution, [status(thm)], [c_3006, c_14])).
% 56.71/45.87  tff(c_23374, plain, (![B_516, C_517]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(B_516, C_517), B_516), C_517)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_18211])).
% 56.71/45.87  tff(c_23576, plain, (![A_1, B_2]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(A_1, B_2), B_2), A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_23374])).
% 56.71/45.87  tff(c_123734, plain, (![A_1117, B_1118]: (k4_xboole_0(k3_subset_1(k2_xboole_0(A_1117, B_1118), B_1118), A_1117)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12091, c_23576])).
% 56.71/45.87  tff(c_124225, plain, (![A_1, B_2]: (k4_xboole_0(k3_subset_1(k2_xboole_0(A_1, B_2), A_1), B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_123734])).
% 56.71/45.87  tff(c_205851, plain, (k4_xboole_0(k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3')), k1_tops_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_205783, c_124225])).
% 56.71/45.87  tff(c_206124, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_45899, c_205851])).
% 56.71/45.87  tff(c_206126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101116, c_206124])).
% 56.71/45.87  tff(c_206127, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_14035])).
% 56.71/45.87  tff(c_84, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 56.71/45.87  tff(c_4656, plain, (![A_249, B_250]: (v3_pre_topc(k1_tops_1(A_249, B_250), A_249) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_139])).
% 56.71/45.87  tff(c_4667, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_80, c_4656])).
% 56.71/45.87  tff(c_4676, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_4667])).
% 56.71/45.87  tff(c_206157, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_206127, c_4676])).
% 56.71/45.87  tff(c_206183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_206157])).
% 56.71/45.87  tff(c_206184, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_86])).
% 56.71/45.87  tff(c_209154, plain, (![A_1508, B_1509, C_1510]: (k7_subset_1(A_1508, B_1509, C_1510)=k4_xboole_0(B_1509, C_1510) | ~m1_subset_1(B_1509, k1_zfmisc_1(A_1508)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 56.71/45.87  tff(c_209169, plain, (![C_1510]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_1510)=k4_xboole_0('#skF_3', C_1510))), inference(resolution, [status(thm)], [c_80, c_209154])).
% 56.71/45.87  tff(c_212806, plain, (![A_1611, B_1612]: (k7_subset_1(u1_struct_0(A_1611), B_1612, k2_tops_1(A_1611, B_1612))=k1_tops_1(A_1611, B_1612) | ~m1_subset_1(B_1612, k1_zfmisc_1(u1_struct_0(A_1611))) | ~l1_pre_topc(A_1611))), inference(cnfTransformation, [status(thm)], [f_181])).
% 56.71/45.87  tff(c_212821, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_80, c_212806])).
% 56.71/45.87  tff(c_212832, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_209169, c_212821])).
% 56.71/45.87  tff(c_206669, plain, (![A_1418, B_1419]: (k4_xboole_0(A_1418, B_1419)=k1_xboole_0 | ~r1_tarski(A_1418, B_1419))), inference(cnfTransformation, [status(thm)], [f_39])).
% 56.71/45.87  tff(c_206685, plain, (![A_19, B_20]: (k4_xboole_0(k4_xboole_0(A_19, B_20), A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_206669])).
% 56.71/45.87  tff(c_212968, plain, (k4_xboole_0(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_212832, c_206685])).
% 56.71/45.87  tff(c_206185, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_86])).
% 56.71/45.87  tff(c_213381, plain, (![B_1620, A_1621, C_1622]: (r1_tarski(B_1620, k1_tops_1(A_1621, C_1622)) | ~r1_tarski(B_1620, C_1622) | ~v3_pre_topc(B_1620, A_1621) | ~m1_subset_1(C_1622, k1_zfmisc_1(u1_struct_0(A_1621))) | ~m1_subset_1(B_1620, k1_zfmisc_1(u1_struct_0(A_1621))) | ~l1_pre_topc(A_1621))), inference(cnfTransformation, [status(thm)], [f_160])).
% 56.71/45.87  tff(c_213396, plain, (![B_1620]: (r1_tarski(B_1620, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_1620, '#skF_3') | ~v3_pre_topc(B_1620, '#skF_2') | ~m1_subset_1(B_1620, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_80, c_213381])).
% 56.71/45.87  tff(c_216934, plain, (![B_1668]: (r1_tarski(B_1668, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_1668, '#skF_3') | ~v3_pre_topc(B_1668, '#skF_2') | ~m1_subset_1(B_1668, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_213396])).
% 56.71/45.87  tff(c_216961, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_216934])).
% 56.71/45.87  tff(c_216980, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_206185, c_10, c_216961])).
% 56.71/45.87  tff(c_207288, plain, (![B_1443, A_1444]: (B_1443=A_1444 | ~r1_tarski(B_1443, A_1444) | ~r1_tarski(A_1444, B_1443))), inference(cnfTransformation, [status(thm)], [f_35])).
% 56.71/45.87  tff(c_207303, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_207288])).
% 56.71/45.87  tff(c_216984, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | k4_xboole_0(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_216980, c_207303])).
% 56.71/45.87  tff(c_217000, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_212968, c_216984])).
% 56.71/45.87  tff(c_70, plain, (![A_67, B_69]: (k7_subset_1(u1_struct_0(A_67), k2_pre_topc(A_67, B_69), k1_tops_1(A_67, B_69))=k2_tops_1(A_67, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_146])).
% 56.71/45.87  tff(c_217040, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_217000, c_70])).
% 56.71/45.87  tff(c_217044, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_217040])).
% 56.71/45.87  tff(c_217046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_206184, c_217044])).
% 56.71/45.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.71/45.87  
% 56.71/45.87  Inference rules
% 56.71/45.87  ----------------------
% 56.71/45.87  #Ref     : 5
% 56.71/45.87  #Sup     : 55126
% 56.71/45.87  #Fact    : 0
% 56.71/45.87  #Define  : 0
% 56.71/45.87  #Split   : 10
% 56.71/45.87  #Chain   : 0
% 56.71/45.87  #Close   : 0
% 56.71/45.87  
% 56.71/45.87  Ordering : KBO
% 56.71/45.87  
% 56.71/45.87  Simplification rules
% 56.71/45.87  ----------------------
% 56.71/45.87  #Subsume      : 9678
% 56.71/45.87  #Demod        : 42466
% 56.71/45.87  #Tautology    : 29153
% 56.71/45.87  #SimpNegUnit  : 529
% 56.71/45.87  #BackRed      : 54
% 56.71/45.87  
% 56.71/45.87  #Partial instantiations: 0
% 56.71/45.87  #Strategies tried      : 1
% 56.71/45.87  
% 56.71/45.87  Timing (in seconds)
% 56.71/45.87  ----------------------
% 56.84/45.87  Preprocessing        : 0.40
% 56.84/45.87  Parsing              : 0.22
% 56.84/45.87  CNF conversion       : 0.03
% 56.84/45.87  Main loop            : 44.62
% 56.84/45.87  Inferencing          : 3.49
% 56.84/45.87  Reduction            : 28.77
% 56.84/45.87  Demodulation         : 25.74
% 56.84/45.87  BG Simplification    : 0.37
% 56.84/45.87  Subsumption          : 10.47
% 56.84/45.87  Abstraction          : 0.70
% 56.84/45.87  MUC search           : 0.00
% 56.84/45.87  Cooper               : 0.00
% 56.84/45.87  Total                : 45.09
% 56.84/45.87  Index Insertion      : 0.00
% 56.84/45.87  Index Deletion       : 0.00
% 56.84/45.87  Index Matching       : 0.00
% 56.84/45.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
