%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:06 EST 2020

% Result     : Timeout 58.47s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  213 ( 634 expanded)
%              Number of leaves         :   58 ( 238 expanded)
%              Depth                    :   17
%              Number of atoms          :  320 (1194 expanded)
%              Number of equality atoms :  131 ( 404 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(f_215,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_203,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_189,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_153,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_196,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_161,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_182,axiom,(
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

tff(f_168,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_94,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_126,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_90,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_3074,plain,(
    ! [A_242,B_243,C_244] :
      ( k7_subset_1(A_242,B_243,C_244) = k4_xboole_0(B_243,C_244)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(A_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3103,plain,(
    ! [C_244] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_244) = k4_xboole_0('#skF_3',C_244) ),
    inference(resolution,[status(thm)],[c_88,c_3074])).

tff(c_6186,plain,(
    ! [A_323,B_324] :
      ( k7_subset_1(u1_struct_0(A_323),B_324,k2_tops_1(A_323,B_324)) = k1_tops_1(A_323,B_324)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ l1_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_6224,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_6186])).

tff(c_6257,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3103,c_6224])).

tff(c_26,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6321,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k3_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6257,c_26])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_624,plain,(
    ! [B_138,A_139] :
      ( B_138 = A_139
      | ~ r1_tarski(B_138,A_139)
      | ~ r1_tarski(A_139,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12156,plain,(
    ! [A_397,B_398] :
      ( k4_xboole_0(A_397,B_398) = A_397
      | ~ r1_tarski(A_397,k4_xboole_0(A_397,B_398)) ) ),
    inference(resolution,[status(thm)],[c_22,c_624])).

tff(c_12180,plain,
    ( k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6257,c_12156])).

tff(c_12262,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6257,c_12180])).

tff(c_110954,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_12262])).

tff(c_110962,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_110954])).

tff(c_138668,plain,(
    k3_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6321,c_110962])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1972,plain,(
    ! [A_202,B_203] :
      ( k4_xboole_0(A_202,B_203) = k3_subset_1(A_202,B_203)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(A_202)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1994,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_1972])).

tff(c_207,plain,(
    ! [A_112,B_113] :
      ( k3_xboole_0(A_112,B_113) = A_112
      | ~ r1_tarski(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_214,plain,(
    ! [A_16,B_17] : k3_xboole_0(k4_xboole_0(A_16,B_17),A_16) = k4_xboole_0(A_16,B_17) ),
    inference(resolution,[status(thm)],[c_22,c_207])).

tff(c_30,plain,(
    ! [A_24] : k2_subset_1(A_24) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_27] : m1_subset_1(k2_subset_1(A_27),k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_101,plain,(
    ! [A_27] : m1_subset_1(A_27,k1_zfmisc_1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_2219,plain,(
    ! [A_211,B_212,C_213] :
      ( k9_subset_1(A_211,B_212,C_213) = k3_xboole_0(B_212,C_213)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(A_211)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2237,plain,(
    ! [A_27,B_212] : k9_subset_1(A_27,B_212,A_27) = k3_xboole_0(B_212,A_27) ),
    inference(resolution,[status(thm)],[c_101,c_2219])).

tff(c_2692,plain,(
    ! [A_229,B_230,C_231] :
      ( m1_subset_1(k9_subset_1(A_229,B_230,C_231),k1_zfmisc_1(A_229))
      | ~ m1_subset_1(C_231,k1_zfmisc_1(A_229)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2710,plain,(
    ! [B_212,A_27] :
      ( m1_subset_1(k3_xboole_0(B_212,A_27),k1_zfmisc_1(A_27))
      | ~ m1_subset_1(A_27,k1_zfmisc_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2237,c_2692])).

tff(c_2728,plain,(
    ! [B_232,A_233] : m1_subset_1(k3_xboole_0(B_232,A_233),k1_zfmisc_1(A_233)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2710])).

tff(c_2782,plain,(
    ! [A_234,B_235] : m1_subset_1(k4_xboole_0(A_234,B_235),k1_zfmisc_1(A_234)) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_2728])).

tff(c_2797,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1994,c_2782])).

tff(c_5746,plain,(
    ! [A_315,B_316] :
      ( k2_tops_1(A_315,k3_subset_1(u1_struct_0(A_315),B_316)) = k2_tops_1(A_315,B_316)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ l1_pre_topc(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_5782,plain,
    ( k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_5746])).

tff(c_5812,plain,(
    k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_5782])).

tff(c_74,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k2_tops_1(A_74,B_75),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_5913,plain,
    ( m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5812,c_74])).

tff(c_5917,plain,(
    m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2797,c_5913])).

tff(c_6056,plain,(
    ! [A_320,B_321] :
      ( k4_subset_1(u1_struct_0(A_320),B_321,k2_tops_1(A_320,B_321)) = k2_pre_topc(A_320,B_321)
      | ~ m1_subset_1(B_321,k1_zfmisc_1(u1_struct_0(A_320)))
      | ~ l1_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_6094,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_6056])).

tff(c_6127,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_6094])).

tff(c_38,plain,(
    ! [A_30,B_31,C_32] :
      ( m1_subset_1(k4_subset_1(A_30,B_31,C_32),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7799,plain,
    ( m1_subset_1(k2_pre_topc('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6127,c_38])).

tff(c_7805,plain,(
    m1_subset_1(k2_pre_topc('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5917,c_7799])).

tff(c_7335,plain,(
    ! [A_339,B_340,C_341] :
      ( r1_tarski(k3_subset_1(A_339,k4_subset_1(A_339,B_340,C_341)),k3_subset_1(A_339,B_340))
      | ~ m1_subset_1(C_341,k1_zfmisc_1(A_339))
      | ~ m1_subset_1(B_340,k1_zfmisc_1(A_339)) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_56,plain,(
    ! [B_55,C_57,A_54] :
      ( r1_tarski(B_55,C_57)
      | ~ r1_tarski(k3_subset_1(A_54,C_57),k3_subset_1(A_54,B_55))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_54))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_71942,plain,(
    ! [B_939,A_940,C_941] :
      ( r1_tarski(B_939,k4_subset_1(A_940,B_939,C_941))
      | ~ m1_subset_1(k4_subset_1(A_940,B_939,C_941),k1_zfmisc_1(A_940))
      | ~ m1_subset_1(C_941,k1_zfmisc_1(A_940))
      | ~ m1_subset_1(B_939,k1_zfmisc_1(A_940)) ) ),
    inference(resolution,[status(thm)],[c_7335,c_56])).

tff(c_72083,plain,
    ( r1_tarski('#skF_3',k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6127,c_71942])).

tff(c_72234,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5917,c_7805,c_6127,c_72083])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_72281,plain,(
    k3_xboole_0('#skF_3',k2_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_72234,c_20])).

tff(c_68,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_7856,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7805,c_68])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7873,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7856,c_12])).

tff(c_100,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_241,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_100])).

tff(c_70,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(A_69,k1_zfmisc_1(B_70))
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_22370,plain,(
    ! [B_498,A_499,C_500] :
      ( k7_subset_1(B_498,A_499,C_500) = k4_xboole_0(A_499,C_500)
      | ~ r1_tarski(A_499,B_498) ) ),
    inference(resolution,[status(thm)],[c_70,c_3074])).

tff(c_167849,plain,(
    ! [B_1319,A_1320,C_1321] :
      ( k7_subset_1(B_1319,A_1320,C_1321) = k4_xboole_0(A_1320,C_1321)
      | k4_xboole_0(A_1320,B_1319) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_22370])).

tff(c_167954,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3')
    | k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_167849])).

tff(c_168002,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7873,c_167954])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_710,plain,(
    ! [A_143,B_144] : k4_xboole_0(A_143,k4_xboole_0(A_143,B_144)) = k3_xboole_0(A_143,B_144) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_784,plain,(
    ! [A_148,B_149] : r1_tarski(k3_xboole_0(A_148,B_149),A_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_22])).

tff(c_7543,plain,(
    ! [A_345,B_346] : k3_xboole_0(k3_xboole_0(A_345,B_346),A_345) = k3_xboole_0(A_345,B_346) ),
    inference(resolution,[status(thm)],[c_784,c_20])).

tff(c_12951,plain,(
    ! [A_403,B_404] : k3_xboole_0(k3_xboole_0(A_403,B_404),B_404) = k3_xboole_0(B_404,A_403) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7543])).

tff(c_593,plain,(
    ! [A_136,B_137] : k5_xboole_0(A_136,k3_xboole_0(A_136,B_137)) = k4_xboole_0(A_136,B_137) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_614,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_593])).

tff(c_13077,plain,(
    ! [B_404,A_403] : k5_xboole_0(B_404,k3_xboole_0(B_404,A_403)) = k4_xboole_0(B_404,k3_xboole_0(A_403,B_404)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12951,c_614])).

tff(c_13244,plain,(
    ! [B_404,A_403] : k4_xboole_0(B_404,k3_xboole_0(A_403,B_404)) = k4_xboole_0(B_404,A_403) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_13077])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_247,plain,(
    ! [A_116,B_117] :
      ( k4_xboole_0(A_116,B_117) = k1_xboole_0
      | ~ r1_tarski(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_255,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_247])).

tff(c_1988,plain,(
    ! [A_27] : k4_xboole_0(A_27,A_27) = k3_subset_1(A_27,A_27) ),
    inference(resolution,[status(thm)],[c_101,c_1972])).

tff(c_1997,plain,(
    ! [A_27] : k3_subset_1(A_27,A_27) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_1988])).

tff(c_2306,plain,(
    ! [A_219,B_220] : k3_xboole_0(k4_xboole_0(A_219,B_220),A_219) = k4_xboole_0(A_219,B_220) ),
    inference(resolution,[status(thm)],[c_22,c_207])).

tff(c_2419,plain,(
    ! [A_1,B_220] : k3_xboole_0(A_1,k4_xboole_0(A_1,B_220)) = k4_xboole_0(A_1,B_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2306])).

tff(c_1674,plain,(
    ! [A_191,B_192] :
      ( k3_subset_1(A_191,k3_subset_1(A_191,B_192)) = B_192
      | ~ m1_subset_1(B_192,k1_zfmisc_1(A_191)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1692,plain,(
    ! [A_27] : k3_subset_1(A_27,k3_subset_1(A_27,A_27)) = A_27 ),
    inference(resolution,[status(thm)],[c_101,c_1674])).

tff(c_2000,plain,(
    ! [A_27] : k3_subset_1(A_27,k1_xboole_0) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1997,c_1692])).

tff(c_24,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_256,plain,(
    ! [B_118] : k4_xboole_0(B_118,B_118) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_247])).

tff(c_261,plain,(
    ! [B_118] : r1_tarski(k1_xboole_0,B_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_22])).

tff(c_765,plain,(
    ! [A_145,C_146,B_147] :
      ( r1_tarski(A_145,C_146)
      | ~ r1_tarski(B_147,C_146)
      | ~ r1_tarski(A_145,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1001,plain,(
    ! [A_157,B_158] :
      ( r1_tarski(A_157,B_158)
      | ~ r1_tarski(A_157,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_261,c_765])).

tff(c_1010,plain,(
    ! [A_5,B_158] :
      ( r1_tarski(A_5,B_158)
      | k4_xboole_0(A_5,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_1001])).

tff(c_1028,plain,(
    ! [A_5,B_158] :
      ( r1_tarski(A_5,B_158)
      | k1_xboole_0 != A_5 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1010])).

tff(c_11009,plain,(
    ! [B_389,A_390] :
      ( k4_xboole_0(B_389,A_390) = k3_subset_1(B_389,A_390)
      | ~ r1_tarski(A_390,B_389) ) ),
    inference(resolution,[status(thm)],[c_70,c_1972])).

tff(c_27073,plain,(
    ! [B_158] : k4_xboole_0(B_158,k1_xboole_0) = k3_subset_1(B_158,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1028,c_11009])).

tff(c_215,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_207])).

tff(c_254,plain,(
    ! [A_16,B_17] : k4_xboole_0(k4_xboole_0(A_16,B_17),A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_247])).

tff(c_3839,plain,(
    ! [A_266,B_267,C_268] : k2_xboole_0(k4_xboole_0(A_266,B_267),k3_xboole_0(A_266,C_268)) = k4_xboole_0(A_266,k4_xboole_0(B_267,C_268)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_35752,plain,(
    ! [A_625,B_626,C_627] : k4_xboole_0(A_625,k4_xboole_0(k4_xboole_0(A_625,B_626),C_627)) = k2_xboole_0(k3_xboole_0(A_625,B_626),k3_xboole_0(A_625,C_627)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3839])).

tff(c_36261,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_xboole_0(A_16,B_17),k3_xboole_0(A_16,A_16)) = k4_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_35752])).

tff(c_36352,plain,(
    ! [A_628,B_629] : k2_xboole_0(k3_xboole_0(A_628,B_629),A_628) = A_628 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_27073,c_215,c_36261])).

tff(c_36412,plain,(
    ! [A_1,B_220] : k2_xboole_0(k4_xboole_0(A_1,B_220),A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2419,c_36352])).

tff(c_3915,plain,(
    ! [B_4,B_267] : k4_xboole_0(B_4,k4_xboole_0(B_267,B_4)) = k2_xboole_0(k4_xboole_0(B_4,B_267),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_3839])).

tff(c_115520,plain,(
    ! [B_1161,B_1162] : k4_xboole_0(B_1161,k4_xboole_0(B_1162,B_1161)) = B_1161 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36412,c_3915])).

tff(c_11153,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_subset_1(A_16,k4_xboole_0(A_16,B_17)) ),
    inference(resolution,[status(thm)],[c_22,c_11009])).

tff(c_11207,plain,(
    ! [A_16,B_17] : k3_subset_1(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_11153])).

tff(c_115844,plain,(
    ! [B_1161,B_1162] : k3_xboole_0(B_1161,k4_xboole_0(B_1162,B_1161)) = k3_subset_1(B_1161,B_1161) ),
    inference(superposition,[status(thm),theory(equality)],[c_115520,c_11207])).

tff(c_116456,plain,(
    ! [B_1163,B_1164] : k3_xboole_0(B_1163,k4_xboole_0(B_1164,B_1163)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1997,c_115844])).

tff(c_127216,plain,(
    ! [A_1189,B_1190] : k3_xboole_0(k3_xboole_0(A_1189,B_1190),k4_xboole_0(B_1190,A_1189)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13244,c_116456])).

tff(c_2399,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(k3_xboole_0(A_19,B_20),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2306])).

tff(c_9250,plain,(
    ! [A_366,B_367] : k3_xboole_0(A_366,k3_xboole_0(A_366,B_367)) = k3_xboole_0(A_366,B_367) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2,c_2399])).

tff(c_9447,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9250])).

tff(c_827,plain,(
    ! [B_150,A_151] : r1_tarski(k3_xboole_0(B_150,A_151),A_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_784])).

tff(c_864,plain,(
    ! [B_150,A_151] : k4_xboole_0(k3_xboole_0(B_150,A_151),A_151) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_827,c_12])).

tff(c_12243,plain,(
    ! [A_5,B_398] :
      ( k4_xboole_0(A_5,B_398) = A_5
      | k4_xboole_0(A_5,k4_xboole_0(A_5,B_398)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_12156])).

tff(c_12308,plain,(
    ! [A_399,B_400] :
      ( k4_xboole_0(A_399,B_400) = A_399
      | k3_xboole_0(A_399,B_400) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12243])).

tff(c_12559,plain,(
    ! [B_150,A_151] :
      ( k3_xboole_0(B_150,A_151) = k1_xboole_0
      | k3_xboole_0(k3_xboole_0(B_150,A_151),A_151) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_12308])).

tff(c_12647,plain,(
    ! [B_150,A_151] :
      ( k3_xboole_0(B_150,A_151) = k1_xboole_0
      | k3_xboole_0(A_151,B_150) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9447,c_2,c_12559])).

tff(c_128134,plain,(
    ! [B_1190,A_1189] : k3_xboole_0(k4_xboole_0(B_1190,A_1189),k3_xboole_0(A_1189,B_1190)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_127216,c_12647])).

tff(c_174651,plain,(
    k3_xboole_0(k2_tops_1('#skF_2','#skF_3'),k3_xboole_0('#skF_3',k2_pre_topc('#skF_2','#skF_3'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_168002,c_128134])).

tff(c_174873,plain,(
    k3_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_72281,c_174651])).

tff(c_174875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138668,c_174873])).

tff(c_174876,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12262])).

tff(c_92,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_2235,plain,(
    ! [B_212] : k9_subset_1(u1_struct_0('#skF_2'),B_212,'#skF_3') = k3_xboole_0(B_212,'#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_2219])).

tff(c_2707,plain,(
    ! [B_212] :
      ( m1_subset_1(k3_xboole_0(B_212,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2235,c_2692])).

tff(c_2723,plain,(
    ! [B_212] : m1_subset_1(k3_xboole_0(B_212,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2707])).

tff(c_4597,plain,(
    ! [A_284,B_285] :
      ( v3_pre_topc(k1_tops_1(A_284,B_285),A_284)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284)
      | ~ v2_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_4605,plain,(
    ! [B_212] :
      ( v3_pre_topc(k1_tops_1('#skF_2',k3_xboole_0(B_212,'#skF_3')),'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2723,c_4597])).

tff(c_4659,plain,(
    ! [B_286] : v3_pre_topc(k1_tops_1('#skF_2',k3_xboole_0(B_286,'#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_4605])).

tff(c_4663,plain,(
    ! [B_17] : v3_pre_topc(k1_tops_1('#skF_2',k4_xboole_0('#skF_3',B_17)),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_4659])).

tff(c_6275,plain,(
    v3_pre_topc(k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_3')),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6257,c_4663])).

tff(c_174901,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174876,c_174876,c_6275])).

tff(c_174935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_174901])).

tff(c_174936,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_178577,plain,(
    ! [A_1518,B_1519,C_1520] :
      ( k7_subset_1(A_1518,B_1519,C_1520) = k4_xboole_0(B_1519,C_1520)
      | ~ m1_subset_1(B_1519,k1_zfmisc_1(A_1518)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_178612,plain,(
    ! [C_1520] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_1520) = k4_xboole_0('#skF_3',C_1520) ),
    inference(resolution,[status(thm)],[c_88,c_178577])).

tff(c_181523,plain,(
    ! [A_1585,B_1586] :
      ( k7_subset_1(u1_struct_0(A_1585),B_1586,k2_tops_1(A_1585,B_1586)) = k1_tops_1(A_1585,B_1586)
      | ~ m1_subset_1(B_1586,k1_zfmisc_1(u1_struct_0(A_1585)))
      | ~ l1_pre_topc(A_1585) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_181563,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_181523])).

tff(c_181599,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_178612,c_181563])).

tff(c_175021,plain,(
    ! [A_1371,B_1372] :
      ( k4_xboole_0(A_1371,B_1372) = k1_xboole_0
      | ~ r1_tarski(A_1371,B_1372) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_175032,plain,(
    ! [A_16,B_17] : k4_xboole_0(k4_xboole_0(A_16,B_17),A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_175021])).

tff(c_181757,plain,(
    k4_xboole_0(k1_tops_1('#skF_2','#skF_3'),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_181599,c_175032])).

tff(c_174937,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_184811,plain,(
    ! [B_1633,A_1634,C_1635] :
      ( r1_tarski(B_1633,k1_tops_1(A_1634,C_1635))
      | ~ r1_tarski(B_1633,C_1635)
      | ~ v3_pre_topc(B_1633,A_1634)
      | ~ m1_subset_1(C_1635,k1_zfmisc_1(u1_struct_0(A_1634)))
      | ~ m1_subset_1(B_1633,k1_zfmisc_1(u1_struct_0(A_1634)))
      | ~ l1_pre_topc(A_1634) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_184855,plain,(
    ! [B_1633] :
      ( r1_tarski(B_1633,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_1633,'#skF_3')
      | ~ v3_pre_topc(B_1633,'#skF_2')
      | ~ m1_subset_1(B_1633,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_88,c_184811])).

tff(c_203968,plain,(
    ! [B_1821] :
      ( r1_tarski(B_1821,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_1821,'#skF_3')
      | ~ v3_pre_topc(B_1821,'#skF_2')
      | ~ m1_subset_1(B_1821,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_184855])).

tff(c_204057,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_203968])).

tff(c_204104,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174937,c_8,c_204057])).

tff(c_175578,plain,(
    ! [B_1403,A_1404] :
      ( B_1403 = A_1404
      | ~ r1_tarski(B_1403,A_1404)
      | ~ r1_tarski(A_1404,B_1403) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_175600,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_175578])).

tff(c_204117,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | k4_xboole_0(k1_tops_1('#skF_2','#skF_3'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_204104,c_175600])).

tff(c_204143,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181757,c_204117])).

tff(c_78,plain,(
    ! [A_78,B_80] :
      ( k7_subset_1(u1_struct_0(A_78),k2_pre_topc(A_78,B_80),k1_tops_1(A_78,B_80)) = k2_tops_1(A_78,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_204207,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_204143,c_78])).

tff(c_204216,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_204207])).

tff(c_204218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174936,c_204216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:26:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 58.47/47.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.58/47.42  
% 58.58/47.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.58/47.43  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 58.58/47.43  
% 58.58/47.43  %Foreground sorts:
% 58.58/47.43  
% 58.58/47.43  
% 58.58/47.43  %Background operators:
% 58.58/47.43  
% 58.58/47.43  
% 58.58/47.43  %Foreground operators:
% 58.58/47.43  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 58.58/47.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 58.58/47.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 58.58/47.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 58.58/47.43  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 58.58/47.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 58.58/47.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 58.58/47.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 58.58/47.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 58.58/47.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 58.58/47.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 58.58/47.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 58.58/47.43  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 58.58/47.43  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 58.58/47.43  tff('#skF_2', type, '#skF_2': $i).
% 58.58/47.43  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 58.58/47.43  tff('#skF_3', type, '#skF_3': $i).
% 58.58/47.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 58.58/47.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 58.58/47.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 58.58/47.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 58.58/47.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 58.58/47.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 58.58/47.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 58.58/47.43  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 58.58/47.43  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 58.58/47.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 58.58/47.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 58.58/47.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 58.58/47.43  
% 58.58/47.46  tff(f_215, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 58.58/47.46  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 58.58/47.46  tff(f_203, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 58.58/47.46  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 58.58/47.46  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 58.58/47.46  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 58.58/47.46  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 58.58/47.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 58.58/47.46  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 58.58/47.46  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 58.58/47.46  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 58.58/47.46  tff(f_67, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 58.58/47.46  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 58.58/47.46  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 58.58/47.46  tff(f_189, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 58.58/47.46  tff(f_153, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 58.58/47.46  tff(f_196, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 58.58/47.46  tff(f_77, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 58.58/47.46  tff(f_133, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 58.58/47.46  tff(f_119, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 58.58/47.46  tff(f_141, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 58.58/47.46  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 58.58/47.46  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 58.58/47.46  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 58.58/47.46  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 58.58/47.46  tff(f_59, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 58.58/47.46  tff(f_161, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 58.58/47.46  tff(f_182, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 58.58/47.46  tff(f_168, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 58.58/47.46  tff(c_94, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 58.58/47.46  tff(c_126, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_94])).
% 58.58/47.46  tff(c_90, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 58.58/47.46  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_215])).
% 58.58/47.46  tff(c_3074, plain, (![A_242, B_243, C_244]: (k7_subset_1(A_242, B_243, C_244)=k4_xboole_0(B_243, C_244) | ~m1_subset_1(B_243, k1_zfmisc_1(A_242)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 58.58/47.46  tff(c_3103, plain, (![C_244]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_244)=k4_xboole_0('#skF_3', C_244))), inference(resolution, [status(thm)], [c_88, c_3074])).
% 58.58/47.46  tff(c_6186, plain, (![A_323, B_324]: (k7_subset_1(u1_struct_0(A_323), B_324, k2_tops_1(A_323, B_324))=k1_tops_1(A_323, B_324) | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0(A_323))) | ~l1_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_203])).
% 58.58/47.46  tff(c_6224, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_88, c_6186])).
% 58.58/47.46  tff(c_6257, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3103, c_6224])).
% 58.58/47.46  tff(c_26, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 58.58/47.46  tff(c_6321, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k3_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6257, c_26])).
% 58.58/47.46  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 58.58/47.46  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 58.58/47.46  tff(c_624, plain, (![B_138, A_139]: (B_138=A_139 | ~r1_tarski(B_138, A_139) | ~r1_tarski(A_139, B_138))), inference(cnfTransformation, [status(thm)], [f_33])).
% 58.58/47.46  tff(c_12156, plain, (![A_397, B_398]: (k4_xboole_0(A_397, B_398)=A_397 | ~r1_tarski(A_397, k4_xboole_0(A_397, B_398)))), inference(resolution, [status(thm)], [c_22, c_624])).
% 58.58/47.46  tff(c_12180, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6257, c_12156])).
% 58.58/47.46  tff(c_12262, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6257, c_12180])).
% 58.58/47.46  tff(c_110954, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_12262])).
% 58.58/47.46  tff(c_110962, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_110954])).
% 58.58/47.46  tff(c_138668, plain, (k3_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6321, c_110962])).
% 58.58/47.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 58.58/47.46  tff(c_1972, plain, (![A_202, B_203]: (k4_xboole_0(A_202, B_203)=k3_subset_1(A_202, B_203) | ~m1_subset_1(B_203, k1_zfmisc_1(A_202)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 58.58/47.46  tff(c_1994, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_88, c_1972])).
% 58.58/47.46  tff(c_207, plain, (![A_112, B_113]: (k3_xboole_0(A_112, B_113)=A_112 | ~r1_tarski(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_51])).
% 58.58/47.46  tff(c_214, plain, (![A_16, B_17]: (k3_xboole_0(k4_xboole_0(A_16, B_17), A_16)=k4_xboole_0(A_16, B_17))), inference(resolution, [status(thm)], [c_22, c_207])).
% 58.58/47.46  tff(c_30, plain, (![A_24]: (k2_subset_1(A_24)=A_24)), inference(cnfTransformation, [status(thm)], [f_61])).
% 58.58/47.46  tff(c_34, plain, (![A_27]: (m1_subset_1(k2_subset_1(A_27), k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 58.58/47.46  tff(c_101, plain, (![A_27]: (m1_subset_1(A_27, k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 58.58/47.46  tff(c_2219, plain, (![A_211, B_212, C_213]: (k9_subset_1(A_211, B_212, C_213)=k3_xboole_0(B_212, C_213) | ~m1_subset_1(C_213, k1_zfmisc_1(A_211)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 58.58/47.46  tff(c_2237, plain, (![A_27, B_212]: (k9_subset_1(A_27, B_212, A_27)=k3_xboole_0(B_212, A_27))), inference(resolution, [status(thm)], [c_101, c_2219])).
% 58.58/47.46  tff(c_2692, plain, (![A_229, B_230, C_231]: (m1_subset_1(k9_subset_1(A_229, B_230, C_231), k1_zfmisc_1(A_229)) | ~m1_subset_1(C_231, k1_zfmisc_1(A_229)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 58.58/47.46  tff(c_2710, plain, (![B_212, A_27]: (m1_subset_1(k3_xboole_0(B_212, A_27), k1_zfmisc_1(A_27)) | ~m1_subset_1(A_27, k1_zfmisc_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_2237, c_2692])).
% 58.58/47.46  tff(c_2728, plain, (![B_232, A_233]: (m1_subset_1(k3_xboole_0(B_232, A_233), k1_zfmisc_1(A_233)))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_2710])).
% 58.58/47.46  tff(c_2782, plain, (![A_234, B_235]: (m1_subset_1(k4_xboole_0(A_234, B_235), k1_zfmisc_1(A_234)))), inference(superposition, [status(thm), theory('equality')], [c_214, c_2728])).
% 58.58/47.46  tff(c_2797, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1994, c_2782])).
% 58.58/47.46  tff(c_5746, plain, (![A_315, B_316]: (k2_tops_1(A_315, k3_subset_1(u1_struct_0(A_315), B_316))=k2_tops_1(A_315, B_316) | ~m1_subset_1(B_316, k1_zfmisc_1(u1_struct_0(A_315))) | ~l1_pre_topc(A_315))), inference(cnfTransformation, [status(thm)], [f_189])).
% 58.58/47.46  tff(c_5782, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_88, c_5746])).
% 58.58/47.46  tff(c_5812, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_5782])).
% 58.58/47.46  tff(c_74, plain, (![A_74, B_75]: (m1_subset_1(k2_tops_1(A_74, B_75), k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_153])).
% 58.58/47.46  tff(c_5913, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5812, c_74])).
% 58.58/47.46  tff(c_5917, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2797, c_5913])).
% 58.58/47.46  tff(c_6056, plain, (![A_320, B_321]: (k4_subset_1(u1_struct_0(A_320), B_321, k2_tops_1(A_320, B_321))=k2_pre_topc(A_320, B_321) | ~m1_subset_1(B_321, k1_zfmisc_1(u1_struct_0(A_320))) | ~l1_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_196])).
% 58.58/47.46  tff(c_6094, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_88, c_6056])).
% 58.58/47.46  tff(c_6127, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_6094])).
% 58.58/47.46  tff(c_38, plain, (![A_30, B_31, C_32]: (m1_subset_1(k4_subset_1(A_30, B_31, C_32), k1_zfmisc_1(A_30)) | ~m1_subset_1(C_32, k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 58.58/47.46  tff(c_7799, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_6127, c_38])).
% 58.58/47.46  tff(c_7805, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5917, c_7799])).
% 58.58/47.46  tff(c_7335, plain, (![A_339, B_340, C_341]: (r1_tarski(k3_subset_1(A_339, k4_subset_1(A_339, B_340, C_341)), k3_subset_1(A_339, B_340)) | ~m1_subset_1(C_341, k1_zfmisc_1(A_339)) | ~m1_subset_1(B_340, k1_zfmisc_1(A_339)))), inference(cnfTransformation, [status(thm)], [f_133])).
% 58.58/47.46  tff(c_56, plain, (![B_55, C_57, A_54]: (r1_tarski(B_55, C_57) | ~r1_tarski(k3_subset_1(A_54, C_57), k3_subset_1(A_54, B_55)) | ~m1_subset_1(C_57, k1_zfmisc_1(A_54)) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 58.58/47.46  tff(c_71942, plain, (![B_939, A_940, C_941]: (r1_tarski(B_939, k4_subset_1(A_940, B_939, C_941)) | ~m1_subset_1(k4_subset_1(A_940, B_939, C_941), k1_zfmisc_1(A_940)) | ~m1_subset_1(C_941, k1_zfmisc_1(A_940)) | ~m1_subset_1(B_939, k1_zfmisc_1(A_940)))), inference(resolution, [status(thm)], [c_7335, c_56])).
% 58.58/47.46  tff(c_72083, plain, (r1_tarski('#skF_3', k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))) | ~m1_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_6127, c_71942])).
% 58.58/47.46  tff(c_72234, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5917, c_7805, c_6127, c_72083])).
% 58.58/47.46  tff(c_20, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 58.58/47.46  tff(c_72281, plain, (k3_xboole_0('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_72234, c_20])).
% 58.58/47.46  tff(c_68, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | ~m1_subset_1(A_69, k1_zfmisc_1(B_70)))), inference(cnfTransformation, [status(thm)], [f_141])).
% 58.58/47.46  tff(c_7856, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_7805, c_68])).
% 58.58/47.46  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 58.58/47.46  tff(c_7873, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_7856, c_12])).
% 58.58/47.46  tff(c_100, plain, (v3_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_215])).
% 58.58/47.46  tff(c_241, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_126, c_100])).
% 58.58/47.46  tff(c_70, plain, (![A_69, B_70]: (m1_subset_1(A_69, k1_zfmisc_1(B_70)) | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_141])).
% 58.58/47.46  tff(c_22370, plain, (![B_498, A_499, C_500]: (k7_subset_1(B_498, A_499, C_500)=k4_xboole_0(A_499, C_500) | ~r1_tarski(A_499, B_498))), inference(resolution, [status(thm)], [c_70, c_3074])).
% 58.58/47.46  tff(c_167849, plain, (![B_1319, A_1320, C_1321]: (k7_subset_1(B_1319, A_1320, C_1321)=k4_xboole_0(A_1320, C_1321) | k4_xboole_0(A_1320, B_1319)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_22370])).
% 58.58/47.46  tff(c_167954, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3') | k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_241, c_167849])).
% 58.58/47.46  tff(c_168002, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7873, c_167954])).
% 58.58/47.46  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 58.58/47.46  tff(c_710, plain, (![A_143, B_144]: (k4_xboole_0(A_143, k4_xboole_0(A_143, B_144))=k3_xboole_0(A_143, B_144))), inference(cnfTransformation, [status(thm)], [f_57])).
% 58.58/47.46  tff(c_784, plain, (![A_148, B_149]: (r1_tarski(k3_xboole_0(A_148, B_149), A_148))), inference(superposition, [status(thm), theory('equality')], [c_710, c_22])).
% 58.58/47.46  tff(c_7543, plain, (![A_345, B_346]: (k3_xboole_0(k3_xboole_0(A_345, B_346), A_345)=k3_xboole_0(A_345, B_346))), inference(resolution, [status(thm)], [c_784, c_20])).
% 58.58/47.46  tff(c_12951, plain, (![A_403, B_404]: (k3_xboole_0(k3_xboole_0(A_403, B_404), B_404)=k3_xboole_0(B_404, A_403))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7543])).
% 58.58/47.46  tff(c_593, plain, (![A_136, B_137]: (k5_xboole_0(A_136, k3_xboole_0(A_136, B_137))=k4_xboole_0(A_136, B_137))), inference(cnfTransformation, [status(thm)], [f_39])).
% 58.58/47.46  tff(c_614, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_593])).
% 58.58/47.46  tff(c_13077, plain, (![B_404, A_403]: (k5_xboole_0(B_404, k3_xboole_0(B_404, A_403))=k4_xboole_0(B_404, k3_xboole_0(A_403, B_404)))), inference(superposition, [status(thm), theory('equality')], [c_12951, c_614])).
% 58.58/47.46  tff(c_13244, plain, (![B_404, A_403]: (k4_xboole_0(B_404, k3_xboole_0(A_403, B_404))=k4_xboole_0(B_404, A_403))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_13077])).
% 58.58/47.46  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 58.58/47.46  tff(c_247, plain, (![A_116, B_117]: (k4_xboole_0(A_116, B_117)=k1_xboole_0 | ~r1_tarski(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_37])).
% 58.58/47.46  tff(c_255, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_247])).
% 58.58/47.46  tff(c_1988, plain, (![A_27]: (k4_xboole_0(A_27, A_27)=k3_subset_1(A_27, A_27))), inference(resolution, [status(thm)], [c_101, c_1972])).
% 58.58/47.46  tff(c_1997, plain, (![A_27]: (k3_subset_1(A_27, A_27)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_255, c_1988])).
% 58.58/47.46  tff(c_2306, plain, (![A_219, B_220]: (k3_xboole_0(k4_xboole_0(A_219, B_220), A_219)=k4_xboole_0(A_219, B_220))), inference(resolution, [status(thm)], [c_22, c_207])).
% 58.58/47.46  tff(c_2419, plain, (![A_1, B_220]: (k3_xboole_0(A_1, k4_xboole_0(A_1, B_220))=k4_xboole_0(A_1, B_220))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2306])).
% 58.58/47.46  tff(c_1674, plain, (![A_191, B_192]: (k3_subset_1(A_191, k3_subset_1(A_191, B_192))=B_192 | ~m1_subset_1(B_192, k1_zfmisc_1(A_191)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 58.58/47.46  tff(c_1692, plain, (![A_27]: (k3_subset_1(A_27, k3_subset_1(A_27, A_27))=A_27)), inference(resolution, [status(thm)], [c_101, c_1674])).
% 58.58/47.46  tff(c_2000, plain, (![A_27]: (k3_subset_1(A_27, k1_xboole_0)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_1997, c_1692])).
% 58.58/47.46  tff(c_24, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_55])).
% 58.58/47.46  tff(c_256, plain, (![B_118]: (k4_xboole_0(B_118, B_118)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_247])).
% 58.58/47.46  tff(c_261, plain, (![B_118]: (r1_tarski(k1_xboole_0, B_118))), inference(superposition, [status(thm), theory('equality')], [c_256, c_22])).
% 58.58/47.46  tff(c_765, plain, (![A_145, C_146, B_147]: (r1_tarski(A_145, C_146) | ~r1_tarski(B_147, C_146) | ~r1_tarski(A_145, B_147))), inference(cnfTransformation, [status(thm)], [f_45])).
% 58.58/47.46  tff(c_1001, plain, (![A_157, B_158]: (r1_tarski(A_157, B_158) | ~r1_tarski(A_157, k1_xboole_0))), inference(resolution, [status(thm)], [c_261, c_765])).
% 58.58/47.46  tff(c_1010, plain, (![A_5, B_158]: (r1_tarski(A_5, B_158) | k4_xboole_0(A_5, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_1001])).
% 58.58/47.46  tff(c_1028, plain, (![A_5, B_158]: (r1_tarski(A_5, B_158) | k1_xboole_0!=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1010])).
% 58.58/47.46  tff(c_11009, plain, (![B_389, A_390]: (k4_xboole_0(B_389, A_390)=k3_subset_1(B_389, A_390) | ~r1_tarski(A_390, B_389))), inference(resolution, [status(thm)], [c_70, c_1972])).
% 58.58/47.46  tff(c_27073, plain, (![B_158]: (k4_xboole_0(B_158, k1_xboole_0)=k3_subset_1(B_158, k1_xboole_0))), inference(resolution, [status(thm)], [c_1028, c_11009])).
% 58.58/47.46  tff(c_215, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_207])).
% 58.58/47.46  tff(c_254, plain, (![A_16, B_17]: (k4_xboole_0(k4_xboole_0(A_16, B_17), A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_247])).
% 58.58/47.46  tff(c_3839, plain, (![A_266, B_267, C_268]: (k2_xboole_0(k4_xboole_0(A_266, B_267), k3_xboole_0(A_266, C_268))=k4_xboole_0(A_266, k4_xboole_0(B_267, C_268)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 58.58/47.46  tff(c_35752, plain, (![A_625, B_626, C_627]: (k4_xboole_0(A_625, k4_xboole_0(k4_xboole_0(A_625, B_626), C_627))=k2_xboole_0(k3_xboole_0(A_625, B_626), k3_xboole_0(A_625, C_627)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3839])).
% 58.58/47.46  tff(c_36261, plain, (![A_16, B_17]: (k2_xboole_0(k3_xboole_0(A_16, B_17), k3_xboole_0(A_16, A_16))=k4_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_254, c_35752])).
% 58.58/47.46  tff(c_36352, plain, (![A_628, B_629]: (k2_xboole_0(k3_xboole_0(A_628, B_629), A_628)=A_628)), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_27073, c_215, c_36261])).
% 58.58/47.46  tff(c_36412, plain, (![A_1, B_220]: (k2_xboole_0(k4_xboole_0(A_1, B_220), A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2419, c_36352])).
% 58.58/47.46  tff(c_3915, plain, (![B_4, B_267]: (k4_xboole_0(B_4, k4_xboole_0(B_267, B_4))=k2_xboole_0(k4_xboole_0(B_4, B_267), B_4))), inference(superposition, [status(thm), theory('equality')], [c_215, c_3839])).
% 58.58/47.46  tff(c_115520, plain, (![B_1161, B_1162]: (k4_xboole_0(B_1161, k4_xboole_0(B_1162, B_1161))=B_1161)), inference(demodulation, [status(thm), theory('equality')], [c_36412, c_3915])).
% 58.58/47.46  tff(c_11153, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_subset_1(A_16, k4_xboole_0(A_16, B_17)))), inference(resolution, [status(thm)], [c_22, c_11009])).
% 58.58/47.46  tff(c_11207, plain, (![A_16, B_17]: (k3_subset_1(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_11153])).
% 58.58/47.46  tff(c_115844, plain, (![B_1161, B_1162]: (k3_xboole_0(B_1161, k4_xboole_0(B_1162, B_1161))=k3_subset_1(B_1161, B_1161))), inference(superposition, [status(thm), theory('equality')], [c_115520, c_11207])).
% 58.58/47.46  tff(c_116456, plain, (![B_1163, B_1164]: (k3_xboole_0(B_1163, k4_xboole_0(B_1164, B_1163))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1997, c_115844])).
% 58.58/47.46  tff(c_127216, plain, (![A_1189, B_1190]: (k3_xboole_0(k3_xboole_0(A_1189, B_1190), k4_xboole_0(B_1190, A_1189))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13244, c_116456])).
% 58.58/47.46  tff(c_2399, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(k3_xboole_0(A_19, B_20), A_19))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2306])).
% 58.58/47.46  tff(c_9250, plain, (![A_366, B_367]: (k3_xboole_0(A_366, k3_xboole_0(A_366, B_367))=k3_xboole_0(A_366, B_367))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2, c_2399])).
% 58.58/47.46  tff(c_9447, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9250])).
% 58.58/47.46  tff(c_827, plain, (![B_150, A_151]: (r1_tarski(k3_xboole_0(B_150, A_151), A_151))), inference(superposition, [status(thm), theory('equality')], [c_2, c_784])).
% 58.58/47.46  tff(c_864, plain, (![B_150, A_151]: (k4_xboole_0(k3_xboole_0(B_150, A_151), A_151)=k1_xboole_0)), inference(resolution, [status(thm)], [c_827, c_12])).
% 58.58/47.46  tff(c_12243, plain, (![A_5, B_398]: (k4_xboole_0(A_5, B_398)=A_5 | k4_xboole_0(A_5, k4_xboole_0(A_5, B_398))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_12156])).
% 58.58/47.46  tff(c_12308, plain, (![A_399, B_400]: (k4_xboole_0(A_399, B_400)=A_399 | k3_xboole_0(A_399, B_400)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12243])).
% 58.58/47.46  tff(c_12559, plain, (![B_150, A_151]: (k3_xboole_0(B_150, A_151)=k1_xboole_0 | k3_xboole_0(k3_xboole_0(B_150, A_151), A_151)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_864, c_12308])).
% 58.58/47.46  tff(c_12647, plain, (![B_150, A_151]: (k3_xboole_0(B_150, A_151)=k1_xboole_0 | k3_xboole_0(A_151, B_150)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9447, c_2, c_12559])).
% 58.58/47.46  tff(c_128134, plain, (![B_1190, A_1189]: (k3_xboole_0(k4_xboole_0(B_1190, A_1189), k3_xboole_0(A_1189, B_1190))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_127216, c_12647])).
% 58.58/47.46  tff(c_174651, plain, (k3_xboole_0(k2_tops_1('#skF_2', '#skF_3'), k3_xboole_0('#skF_3', k2_pre_topc('#skF_2', '#skF_3')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_168002, c_128134])).
% 58.58/47.46  tff(c_174873, plain, (k3_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_72281, c_174651])).
% 58.58/47.46  tff(c_174875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138668, c_174873])).
% 58.58/47.46  tff(c_174876, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_12262])).
% 58.58/47.46  tff(c_92, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 58.58/47.46  tff(c_2235, plain, (![B_212]: (k9_subset_1(u1_struct_0('#skF_2'), B_212, '#skF_3')=k3_xboole_0(B_212, '#skF_3'))), inference(resolution, [status(thm)], [c_88, c_2219])).
% 58.58/47.46  tff(c_2707, plain, (![B_212]: (m1_subset_1(k3_xboole_0(B_212, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_2235, c_2692])).
% 58.58/47.46  tff(c_2723, plain, (![B_212]: (m1_subset_1(k3_xboole_0(B_212, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2707])).
% 58.58/47.46  tff(c_4597, plain, (![A_284, B_285]: (v3_pre_topc(k1_tops_1(A_284, B_285), A_284) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284) | ~v2_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_161])).
% 58.58/47.46  tff(c_4605, plain, (![B_212]: (v3_pre_topc(k1_tops_1('#skF_2', k3_xboole_0(B_212, '#skF_3')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_2723, c_4597])).
% 58.58/47.46  tff(c_4659, plain, (![B_286]: (v3_pre_topc(k1_tops_1('#skF_2', k3_xboole_0(B_286, '#skF_3')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_4605])).
% 58.58/47.46  tff(c_4663, plain, (![B_17]: (v3_pre_topc(k1_tops_1('#skF_2', k4_xboole_0('#skF_3', B_17)), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_214, c_4659])).
% 58.58/47.46  tff(c_6275, plain, (v3_pre_topc(k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_3')), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6257, c_4663])).
% 58.58/47.46  tff(c_174901, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_174876, c_174876, c_6275])).
% 58.58/47.46  tff(c_174935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_174901])).
% 58.58/47.46  tff(c_174936, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_94])).
% 58.58/47.46  tff(c_178577, plain, (![A_1518, B_1519, C_1520]: (k7_subset_1(A_1518, B_1519, C_1520)=k4_xboole_0(B_1519, C_1520) | ~m1_subset_1(B_1519, k1_zfmisc_1(A_1518)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 58.58/47.46  tff(c_178612, plain, (![C_1520]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_1520)=k4_xboole_0('#skF_3', C_1520))), inference(resolution, [status(thm)], [c_88, c_178577])).
% 58.58/47.46  tff(c_181523, plain, (![A_1585, B_1586]: (k7_subset_1(u1_struct_0(A_1585), B_1586, k2_tops_1(A_1585, B_1586))=k1_tops_1(A_1585, B_1586) | ~m1_subset_1(B_1586, k1_zfmisc_1(u1_struct_0(A_1585))) | ~l1_pre_topc(A_1585))), inference(cnfTransformation, [status(thm)], [f_203])).
% 58.58/47.46  tff(c_181563, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_88, c_181523])).
% 58.58/47.46  tff(c_181599, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_178612, c_181563])).
% 58.58/47.46  tff(c_175021, plain, (![A_1371, B_1372]: (k4_xboole_0(A_1371, B_1372)=k1_xboole_0 | ~r1_tarski(A_1371, B_1372))), inference(cnfTransformation, [status(thm)], [f_37])).
% 58.58/47.46  tff(c_175032, plain, (![A_16, B_17]: (k4_xboole_0(k4_xboole_0(A_16, B_17), A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_175021])).
% 58.58/47.46  tff(c_181757, plain, (k4_xboole_0(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_181599, c_175032])).
% 58.58/47.46  tff(c_174937, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_94])).
% 58.58/47.46  tff(c_184811, plain, (![B_1633, A_1634, C_1635]: (r1_tarski(B_1633, k1_tops_1(A_1634, C_1635)) | ~r1_tarski(B_1633, C_1635) | ~v3_pre_topc(B_1633, A_1634) | ~m1_subset_1(C_1635, k1_zfmisc_1(u1_struct_0(A_1634))) | ~m1_subset_1(B_1633, k1_zfmisc_1(u1_struct_0(A_1634))) | ~l1_pre_topc(A_1634))), inference(cnfTransformation, [status(thm)], [f_182])).
% 58.58/47.46  tff(c_184855, plain, (![B_1633]: (r1_tarski(B_1633, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_1633, '#skF_3') | ~v3_pre_topc(B_1633, '#skF_2') | ~m1_subset_1(B_1633, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_88, c_184811])).
% 58.58/47.46  tff(c_203968, plain, (![B_1821]: (r1_tarski(B_1821, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_1821, '#skF_3') | ~v3_pre_topc(B_1821, '#skF_2') | ~m1_subset_1(B_1821, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_184855])).
% 58.58/47.46  tff(c_204057, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_88, c_203968])).
% 58.58/47.46  tff(c_204104, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_174937, c_8, c_204057])).
% 58.58/47.46  tff(c_175578, plain, (![B_1403, A_1404]: (B_1403=A_1404 | ~r1_tarski(B_1403, A_1404) | ~r1_tarski(A_1404, B_1403))), inference(cnfTransformation, [status(thm)], [f_33])).
% 58.58/47.46  tff(c_175600, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_175578])).
% 58.58/47.46  tff(c_204117, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | k4_xboole_0(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_204104, c_175600])).
% 58.58/47.46  tff(c_204143, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_181757, c_204117])).
% 58.58/47.46  tff(c_78, plain, (![A_78, B_80]: (k7_subset_1(u1_struct_0(A_78), k2_pre_topc(A_78, B_80), k1_tops_1(A_78, B_80))=k2_tops_1(A_78, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_168])).
% 58.58/47.46  tff(c_204207, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_204143, c_78])).
% 58.58/47.46  tff(c_204216, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_204207])).
% 58.58/47.46  tff(c_204218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174936, c_204216])).
% 58.58/47.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.58/47.46  
% 58.58/47.46  Inference rules
% 58.58/47.46  ----------------------
% 58.58/47.46  #Ref     : 7
% 58.58/47.46  #Sup     : 50759
% 58.58/47.46  #Fact    : 0
% 58.58/47.46  #Define  : 0
% 58.58/47.46  #Split   : 8
% 58.58/47.46  #Chain   : 0
% 58.58/47.46  #Close   : 0
% 58.58/47.46  
% 58.58/47.46  Ordering : KBO
% 58.58/47.46  
% 58.58/47.46  Simplification rules
% 58.58/47.46  ----------------------
% 58.58/47.46  #Subsume      : 9710
% 58.58/47.46  #Demod        : 45671
% 58.58/47.46  #Tautology    : 24548
% 58.58/47.46  #SimpNegUnit  : 268
% 58.58/47.46  #BackRed      : 82
% 58.58/47.46  
% 58.58/47.46  #Partial instantiations: 0
% 58.58/47.46  #Strategies tried      : 1
% 58.58/47.46  
% 58.58/47.46  Timing (in seconds)
% 58.58/47.46  ----------------------
% 58.58/47.46  Preprocessing        : 0.51
% 58.58/47.46  Parsing              : 0.25
% 58.58/47.46  CNF conversion       : 0.04
% 58.58/47.46  Main loop            : 46.09
% 58.58/47.46  Inferencing          : 3.94
% 58.58/47.46  Reduction            : 29.94
% 58.58/47.46  Demodulation         : 26.98
% 58.58/47.46  BG Simplification    : 0.47
% 58.58/47.46  Subsumption          : 10.07
% 58.58/47.46  Abstraction          : 0.89
% 58.58/47.46  MUC search           : 0.00
% 58.58/47.46  Cooper               : 0.00
% 58.58/47.46  Total                : 46.67
% 58.58/47.46  Index Insertion      : 0.00
% 58.58/47.46  Index Deletion       : 0.00
% 58.58/47.46  Index Matching       : 0.00
% 58.58/47.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
