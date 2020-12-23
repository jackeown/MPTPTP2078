%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:52 EST 2020

% Result     : Theorem 17.59s
% Output     : CNFRefutation 17.71s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 241 expanded)
%              Number of leaves         :   40 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  158 ( 489 expanded)
%              Number of equality atoms :   40 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_627,plain,(
    ! [A_111,B_112] :
      ( r1_tarski(A_111,B_112)
      | k4_xboole_0(A_111,B_112) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_643,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_627,c_68])).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_72,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_4529,plain,(
    ! [A_220,B_221] :
      ( k4_subset_1(u1_struct_0(A_220),B_221,k2_tops_1(A_220,B_221)) = k2_pre_topc(A_220,B_221)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_4542,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_4529])).

tff(c_4549,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4542])).

tff(c_42,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k3_subset_1(A_35,B_36),k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2884,plain,(
    ! [A_179,B_180] :
      ( k3_subset_1(A_179,k3_subset_1(A_179,B_180)) = B_180
      | ~ m1_subset_1(B_180,k1_zfmisc_1(A_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2893,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_72,c_2884])).

tff(c_5811,plain,(
    ! [A_250,B_251,C_252] :
      ( r1_tarski(k3_subset_1(A_250,k4_subset_1(A_250,B_251,C_252)),k3_subset_1(A_250,B_251))
      | ~ m1_subset_1(C_252,k1_zfmisc_1(A_250))
      | ~ m1_subset_1(B_251,k1_zfmisc_1(A_250)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5835,plain,(
    ! [C_252] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_252)),'#skF_2')
      | ~ m1_subset_1(C_252,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2893,c_5811])).

tff(c_13230,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5835])).

tff(c_13606,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_42,c_13230])).

tff(c_13613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_13606])).

tff(c_13615,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_5835])).

tff(c_4977,plain,(
    ! [A_230,C_231,B_232] :
      ( r1_tarski(k3_subset_1(A_230,C_231),B_232)
      | ~ r1_tarski(k3_subset_1(A_230,B_232),C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(A_230))
      | ~ m1_subset_1(B_232,k1_zfmisc_1(A_230)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4984,plain,(
    ! [C_231] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),C_231),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
      | ~ r1_tarski('#skF_2',C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2893,c_4977])).

tff(c_12944,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4984])).

tff(c_15168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13615,c_12944])).

tff(c_15170,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_4984])).

tff(c_4028,plain,(
    ! [A_212,B_213] :
      ( k2_tops_1(A_212,k3_subset_1(u1_struct_0(A_212),B_213)) = k2_tops_1(A_212,B_213)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_4041,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_4028])).

tff(c_4048,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4041])).

tff(c_3179,plain,(
    ! [A_188,B_189] :
      ( m1_subset_1(k2_tops_1(A_188,B_189),k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_56,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_21720,plain,(
    ! [A_450,B_451] :
      ( r1_tarski(k2_tops_1(A_450,B_451),u1_struct_0(A_450))
      | ~ m1_subset_1(B_451,k1_zfmisc_1(u1_struct_0(A_450)))
      | ~ l1_pre_topc(A_450) ) ),
    inference(resolution,[status(thm)],[c_3179,c_56])).

tff(c_21751,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4048,c_21720])).

tff(c_21767,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_15170,c_21751])).

tff(c_58,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(A_55,k1_zfmisc_1(B_56))
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3597,plain,(
    ! [A_201,B_202,C_203] :
      ( k4_subset_1(A_201,B_202,C_203) = k2_xboole_0(B_202,C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(A_201))
      | ~ m1_subset_1(B_202,k1_zfmisc_1(A_201)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34311,plain,(
    ! [B_530,B_531,A_532] :
      ( k4_subset_1(B_530,B_531,A_532) = k2_xboole_0(B_531,A_532)
      | ~ m1_subset_1(B_531,k1_zfmisc_1(B_530))
      | ~ r1_tarski(A_532,B_530) ) ),
    inference(resolution,[status(thm)],[c_58,c_3597])).

tff(c_34333,plain,(
    ! [A_533] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_533) = k2_xboole_0('#skF_2',A_533)
      | ~ r1_tarski(A_533,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_72,c_34311])).

tff(c_34340,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_21767,c_34333])).

tff(c_34454,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4549,c_34340])).

tff(c_70,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6302,plain,(
    ! [A_262,C_263,B_264] :
      ( r1_tarski(k2_pre_topc(A_262,C_263),B_264)
      | ~ r1_tarski(C_263,B_264)
      | ~ v4_pre_topc(B_264,A_262)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_6315,plain,(
    ! [B_264] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_264)
      | ~ r1_tarski('#skF_2',B_264)
      | ~ v4_pre_topc(B_264,'#skF_1')
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_72,c_6302])).

tff(c_12433,plain,(
    ! [B_363] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_363)
      | ~ r1_tarski('#skF_2',B_363)
      | ~ v4_pre_topc(B_363,'#skF_1')
      | ~ m1_subset_1(B_363,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6315])).

tff(c_12452,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_12433])).

tff(c_12461,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8,c_12452])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12491,plain,(
    k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12461,c_16])).

tff(c_24,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_176,plain,(
    ! [A_88,B_89] :
      ( k2_xboole_0(A_88,B_89) = B_89
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_199,plain,(
    ! [A_18] : k2_xboole_0(k1_xboole_0,A_18) = A_18 ),
    inference(resolution,[status(thm)],[c_24,c_176])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_315,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(A_95,B_96) = k1_xboole_0
      | ~ r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_335,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_315])).

tff(c_1552,plain,(
    ! [A_145,B_146] : k2_xboole_0(A_145,k4_xboole_0(B_146,A_145)) = k2_xboole_0(A_145,B_146) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1600,plain,(
    ! [A_29,B_30] : k2_xboole_0(k2_xboole_0(A_29,B_30),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_29,B_30),A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_1552])).

tff(c_1631,plain,(
    ! [A_29,B_30] : k2_xboole_0(k2_xboole_0(A_29,B_30),A_29) = k2_xboole_0(A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_2,c_1600])).

tff(c_36379,plain,(
    k2_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34454,c_1631])).

tff(c_36489,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34454,c_12491,c_36379])).

tff(c_36501,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36489,c_34454])).

tff(c_94,plain,(
    ! [B_82,A_83] : k2_xboole_0(B_82,A_83) = k2_xboole_0(A_83,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_109,plain,(
    ! [A_83,B_82] : r1_tarski(A_83,k2_xboole_0(B_82,A_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_36])).

tff(c_334,plain,(
    ! [A_83,B_82] : k4_xboole_0(A_83,k2_xboole_0(B_82,A_83)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_315])).

tff(c_36658,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36501,c_334])).

tff(c_36708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_643,c_36658])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:16:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.59/8.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.59/8.94  
% 17.59/8.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.59/8.95  %$ v4_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 17.59/8.95  
% 17.59/8.95  %Foreground sorts:
% 17.59/8.95  
% 17.59/8.95  
% 17.59/8.95  %Background operators:
% 17.59/8.95  
% 17.59/8.95  
% 17.59/8.95  %Foreground operators:
% 17.59/8.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.59/8.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.59/8.95  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 17.59/8.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.59/8.95  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 17.59/8.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.59/8.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.59/8.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.59/8.95  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 17.59/8.95  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 17.59/8.95  tff('#skF_2', type, '#skF_2': $i).
% 17.59/8.95  tff('#skF_1', type, '#skF_1': $i).
% 17.59/8.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.59/8.95  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 17.59/8.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.59/8.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.59/8.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.59/8.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.59/8.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 17.59/8.95  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 17.59/8.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.59/8.95  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 17.59/8.95  
% 17.71/8.96  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 17.71/8.96  tff(f_161, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 17.71/8.96  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 17.71/8.96  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 17.71/8.96  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 17.71/8.96  tff(f_111, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 17.71/8.96  tff(f_104, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 17.71/8.96  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 17.71/8.96  tff(f_123, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 17.71/8.96  tff(f_117, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 17.71/8.96  tff(f_95, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 17.71/8.96  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.71/8.96  tff(f_137, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 17.71/8.96  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 17.71/8.96  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 17.71/8.96  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 17.71/8.96  tff(f_69, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 17.71/8.96  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 17.71/8.96  tff(c_627, plain, (![A_111, B_112]: (r1_tarski(A_111, B_112) | k4_xboole_0(A_111, B_112)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.71/8.96  tff(c_68, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 17.71/8.96  tff(c_643, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_627, c_68])).
% 17.71/8.96  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 17.71/8.96  tff(c_72, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 17.71/8.96  tff(c_4529, plain, (![A_220, B_221]: (k4_subset_1(u1_struct_0(A_220), B_221, k2_tops_1(A_220, B_221))=k2_pre_topc(A_220, B_221) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220))), inference(cnfTransformation, [status(thm)], [f_151])).
% 17.71/8.96  tff(c_4542, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72, c_4529])).
% 17.71/8.96  tff(c_4549, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4542])).
% 17.71/8.96  tff(c_42, plain, (![A_35, B_36]: (m1_subset_1(k3_subset_1(A_35, B_36), k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.71/8.96  tff(c_2884, plain, (![A_179, B_180]: (k3_subset_1(A_179, k3_subset_1(A_179, B_180))=B_180 | ~m1_subset_1(B_180, k1_zfmisc_1(A_179)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.71/8.96  tff(c_2893, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_72, c_2884])).
% 17.71/8.96  tff(c_5811, plain, (![A_250, B_251, C_252]: (r1_tarski(k3_subset_1(A_250, k4_subset_1(A_250, B_251, C_252)), k3_subset_1(A_250, B_251)) | ~m1_subset_1(C_252, k1_zfmisc_1(A_250)) | ~m1_subset_1(B_251, k1_zfmisc_1(A_250)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 17.71/8.96  tff(c_5835, plain, (![C_252]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_252)), '#skF_2') | ~m1_subset_1(C_252, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2893, c_5811])).
% 17.71/8.96  tff(c_13230, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_5835])).
% 17.71/8.96  tff(c_13606, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_13230])).
% 17.71/8.96  tff(c_13613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_13606])).
% 17.71/8.96  tff(c_13615, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_5835])).
% 17.71/8.96  tff(c_4977, plain, (![A_230, C_231, B_232]: (r1_tarski(k3_subset_1(A_230, C_231), B_232) | ~r1_tarski(k3_subset_1(A_230, B_232), C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(A_230)) | ~m1_subset_1(B_232, k1_zfmisc_1(A_230)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 17.71/8.96  tff(c_4984, plain, (![C_231]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), C_231), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~r1_tarski('#skF_2', C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2893, c_4977])).
% 17.71/8.96  tff(c_12944, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_4984])).
% 17.71/8.96  tff(c_15168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13615, c_12944])).
% 17.71/8.96  tff(c_15170, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_4984])).
% 17.71/8.96  tff(c_4028, plain, (![A_212, B_213]: (k2_tops_1(A_212, k3_subset_1(u1_struct_0(A_212), B_213))=k2_tops_1(A_212, B_213) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_144])).
% 17.71/8.96  tff(c_4041, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72, c_4028])).
% 17.71/8.96  tff(c_4048, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4041])).
% 17.71/8.96  tff(c_3179, plain, (![A_188, B_189]: (m1_subset_1(k2_tops_1(A_188, B_189), k1_zfmisc_1(u1_struct_0(A_188))) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_123])).
% 17.71/8.96  tff(c_56, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 17.71/8.96  tff(c_21720, plain, (![A_450, B_451]: (r1_tarski(k2_tops_1(A_450, B_451), u1_struct_0(A_450)) | ~m1_subset_1(B_451, k1_zfmisc_1(u1_struct_0(A_450))) | ~l1_pre_topc(A_450))), inference(resolution, [status(thm)], [c_3179, c_56])).
% 17.71/8.96  tff(c_21751, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4048, c_21720])).
% 17.71/8.96  tff(c_21767, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_15170, c_21751])).
% 17.71/8.96  tff(c_58, plain, (![A_55, B_56]: (m1_subset_1(A_55, k1_zfmisc_1(B_56)) | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_117])).
% 17.71/8.96  tff(c_3597, plain, (![A_201, B_202, C_203]: (k4_subset_1(A_201, B_202, C_203)=k2_xboole_0(B_202, C_203) | ~m1_subset_1(C_203, k1_zfmisc_1(A_201)) | ~m1_subset_1(B_202, k1_zfmisc_1(A_201)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 17.71/8.96  tff(c_34311, plain, (![B_530, B_531, A_532]: (k4_subset_1(B_530, B_531, A_532)=k2_xboole_0(B_531, A_532) | ~m1_subset_1(B_531, k1_zfmisc_1(B_530)) | ~r1_tarski(A_532, B_530))), inference(resolution, [status(thm)], [c_58, c_3597])).
% 17.71/8.96  tff(c_34333, plain, (![A_533]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_533)=k2_xboole_0('#skF_2', A_533) | ~r1_tarski(A_533, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_72, c_34311])).
% 17.71/8.96  tff(c_34340, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_21767, c_34333])).
% 17.71/8.96  tff(c_34454, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4549, c_34340])).
% 17.71/8.96  tff(c_70, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 17.71/8.96  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 17.71/8.96  tff(c_6302, plain, (![A_262, C_263, B_264]: (r1_tarski(k2_pre_topc(A_262, C_263), B_264) | ~r1_tarski(C_263, B_264) | ~v4_pre_topc(B_264, A_262) | ~m1_subset_1(C_263, k1_zfmisc_1(u1_struct_0(A_262))) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262))), inference(cnfTransformation, [status(thm)], [f_137])).
% 17.71/8.96  tff(c_6315, plain, (![B_264]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_264) | ~r1_tarski('#skF_2', B_264) | ~v4_pre_topc(B_264, '#skF_1') | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_72, c_6302])).
% 17.71/8.96  tff(c_12433, plain, (![B_363]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_363) | ~r1_tarski('#skF_2', B_363) | ~v4_pre_topc(B_363, '#skF_1') | ~m1_subset_1(B_363, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6315])).
% 17.71/8.96  tff(c_12452, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_12433])).
% 17.71/8.96  tff(c_12461, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_8, c_12452])).
% 17.71/8.96  tff(c_16, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.71/8.96  tff(c_12491, plain, (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_12461, c_16])).
% 17.71/8.96  tff(c_24, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.71/8.96  tff(c_176, plain, (![A_88, B_89]: (k2_xboole_0(A_88, B_89)=B_89 | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.71/8.96  tff(c_199, plain, (![A_18]: (k2_xboole_0(k1_xboole_0, A_18)=A_18)), inference(resolution, [status(thm)], [c_24, c_176])).
% 17.71/8.96  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.71/8.96  tff(c_36, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 17.71/8.96  tff(c_315, plain, (![A_95, B_96]: (k4_xboole_0(A_95, B_96)=k1_xboole_0 | ~r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.71/8.96  tff(c_335, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k2_xboole_0(A_29, B_30))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_315])).
% 17.71/8.96  tff(c_1552, plain, (![A_145, B_146]: (k2_xboole_0(A_145, k4_xboole_0(B_146, A_145))=k2_xboole_0(A_145, B_146))), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.71/8.96  tff(c_1600, plain, (![A_29, B_30]: (k2_xboole_0(k2_xboole_0(A_29, B_30), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_29, B_30), A_29))), inference(superposition, [status(thm), theory('equality')], [c_335, c_1552])).
% 17.71/8.96  tff(c_1631, plain, (![A_29, B_30]: (k2_xboole_0(k2_xboole_0(A_29, B_30), A_29)=k2_xboole_0(A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_2, c_1600])).
% 17.71/8.96  tff(c_36379, plain, (k2_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34454, c_1631])).
% 17.71/8.96  tff(c_36489, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34454, c_12491, c_36379])).
% 17.71/8.96  tff(c_36501, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36489, c_34454])).
% 17.71/8.96  tff(c_94, plain, (![B_82, A_83]: (k2_xboole_0(B_82, A_83)=k2_xboole_0(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.71/8.96  tff(c_109, plain, (![A_83, B_82]: (r1_tarski(A_83, k2_xboole_0(B_82, A_83)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_36])).
% 17.71/8.96  tff(c_334, plain, (![A_83, B_82]: (k4_xboole_0(A_83, k2_xboole_0(B_82, A_83))=k1_xboole_0)), inference(resolution, [status(thm)], [c_109, c_315])).
% 17.71/8.96  tff(c_36658, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_36501, c_334])).
% 17.71/8.96  tff(c_36708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_643, c_36658])).
% 17.71/8.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.71/8.96  
% 17.71/8.96  Inference rules
% 17.71/8.96  ----------------------
% 17.71/8.96  #Ref     : 1
% 17.71/8.96  #Sup     : 9314
% 17.71/8.96  #Fact    : 0
% 17.71/8.96  #Define  : 0
% 17.71/8.96  #Split   : 5
% 17.71/8.96  #Chain   : 0
% 17.71/8.96  #Close   : 0
% 17.71/8.96  
% 17.71/8.96  Ordering : KBO
% 17.71/8.96  
% 17.71/8.96  Simplification rules
% 17.71/8.96  ----------------------
% 17.71/8.96  #Subsume      : 1223
% 17.71/8.96  #Demod        : 7363
% 17.71/8.96  #Tautology    : 5276
% 17.71/8.96  #SimpNegUnit  : 92
% 17.71/8.96  #BackRed      : 17
% 17.71/8.96  
% 17.71/8.96  #Partial instantiations: 0
% 17.71/8.96  #Strategies tried      : 1
% 17.71/8.96  
% 17.71/8.96  Timing (in seconds)
% 17.71/8.96  ----------------------
% 17.71/8.97  Preprocessing        : 0.72
% 17.71/8.97  Parsing              : 0.41
% 17.71/8.97  CNF conversion       : 0.04
% 17.71/8.97  Main loop            : 7.30
% 17.71/8.97  Inferencing          : 1.25
% 17.71/8.97  Reduction            : 4.19
% 17.71/8.97  Demodulation         : 3.60
% 17.71/8.97  BG Simplification    : 0.15
% 17.71/8.97  Subsumption          : 1.37
% 17.71/8.97  Abstraction          : 0.25
% 17.71/8.97  MUC search           : 0.00
% 17.71/8.97  Cooper               : 0.00
% 17.71/8.97  Total                : 8.07
% 17.71/8.97  Index Insertion      : 0.00
% 17.71/8.97  Index Deletion       : 0.00
% 17.71/8.97  Index Matching       : 0.00
% 17.71/8.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
