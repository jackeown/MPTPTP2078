%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:49 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   67 (  93 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 192 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tops_2)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( r1_tarski(C,B)
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k3_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    ! [A_43] :
      ( l1_struct_0(A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_224,plain,(
    ! [C_114,A_115,B_116] :
      ( m1_subset_1(C_114,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_115))))
      | ~ r1_tarski(C_114,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_115))))
      | ~ l1_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_293,plain,(
    ! [A_133,C_134,A_135,B_136] :
      ( m1_subset_1(k3_xboole_0(A_133,C_134),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_135))))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_135))))
      | ~ l1_struct_0(A_135)
      | ~ r1_tarski(A_133,B_136) ) ),
    inference(resolution,[status(thm)],[c_10,c_224])).

tff(c_298,plain,(
    ! [A_133,C_134] :
      ( m1_subset_1(k3_xboole_0(A_133,C_134),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_struct_0('#skF_1')
      | ~ r1_tarski(A_133,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_293])).

tff(c_300,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_303,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_300])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_303])).

tff(c_309,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(k5_xboole_0(A_8,C_10),B_9)
      | ~ r1_tarski(C_10,B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_310,plain,(
    ! [A_137,C_138,A_139,B_140] :
      ( m1_subset_1(k5_xboole_0(A_137,C_138),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_139))))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_139))))
      | ~ l1_struct_0(A_139)
      | ~ r1_tarski(C_138,B_140)
      | ~ r1_tarski(A_137,B_140) ) ),
    inference(resolution,[status(thm)],[c_12,c_224])).

tff(c_314,plain,(
    ! [A_137,C_138] :
      ( m1_subset_1(k5_xboole_0(A_137,C_138),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_struct_0('#skF_1')
      | ~ r1_tarski(C_138,'#skF_2')
      | ~ r1_tarski(A_137,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_310])).

tff(c_320,plain,(
    ! [A_137,C_138] :
      ( m1_subset_1(k5_xboole_0(A_137,C_138),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(C_138,'#skF_2')
      | ~ r1_tarski(A_137,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_314])).

tff(c_38,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_280,plain,(
    ! [B_130,A_131,C_132] :
      ( v1_tops_2(B_130,A_131)
      | ~ v1_tops_2(C_132,A_131)
      | ~ r1_tarski(B_130,C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131))))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131))))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_567,plain,(
    ! [A_181,C_182,A_183,B_184] :
      ( v1_tops_2(k5_xboole_0(A_181,C_182),A_183)
      | ~ v1_tops_2(B_184,A_183)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_183))))
      | ~ m1_subset_1(k5_xboole_0(A_181,C_182),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_183))))
      | ~ l1_pre_topc(A_183)
      | ~ r1_tarski(C_182,B_184)
      | ~ r1_tarski(A_181,B_184) ) ),
    inference(resolution,[status(thm)],[c_12,c_280])).

tff(c_587,plain,(
    ! [A_181,C_182] :
      ( v1_tops_2(k5_xboole_0(A_181,C_182),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1(k5_xboole_0(A_181,C_182),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(C_182,'#skF_2')
      | ~ r1_tarski(A_181,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_567])).

tff(c_676,plain,(
    ! [A_199,C_200] :
      ( v1_tops_2(k5_xboole_0(A_199,C_200),'#skF_1')
      | ~ m1_subset_1(k5_xboole_0(A_199,C_200),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(C_200,'#skF_2')
      | ~ r1_tarski(A_199,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_587])).

tff(c_689,plain,(
    ! [A_201,C_202] :
      ( v1_tops_2(k5_xboole_0(A_201,C_202),'#skF_1')
      | ~ r1_tarski(C_202,'#skF_2')
      | ~ r1_tarski(A_201,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_320,c_676])).

tff(c_693,plain,(
    ! [A_203,B_204] :
      ( v1_tops_2(k4_xboole_0(A_203,B_204),'#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_203,B_204),'#skF_2')
      | ~ r1_tarski(A_203,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_689])).

tff(c_95,plain,(
    ! [A_78,B_79,C_80] :
      ( k7_subset_1(A_78,B_79,C_80) = k4_xboole_0(B_79,C_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_101,plain,(
    ! [C_80] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_80) = k4_xboole_0('#skF_2',C_80) ),
    inference(resolution,[status(thm)],[c_42,c_95])).

tff(c_36,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_120,plain,(
    ~ v1_tops_2(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_36])).

tff(c_696,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_693,c_120])).

tff(c_699,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_696])).

tff(c_702,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_699])).

tff(c_706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_702])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:02:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.46  
% 2.75/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.46  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.75/1.46  
% 2.75/1.46  %Foreground sorts:
% 2.75/1.46  
% 2.75/1.46  
% 2.75/1.46  %Background operators:
% 2.75/1.46  
% 2.75/1.46  
% 2.75/1.46  %Foreground operators:
% 2.75/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.46  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.75/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.75/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.75/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.75/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.75/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.75/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.46  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.75/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.75/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.75/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.75/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.75/1.46  
% 3.15/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/1.47  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 3.15/1.47  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.15/1.47  tff(f_102, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tops_2)).
% 3.15/1.47  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.15/1.47  tff(f_89, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_tops_2)).
% 3.15/1.47  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 3.15/1.47  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tops_2)).
% 3.15/1.47  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.15/1.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.47  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k3_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.47  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.47  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.15/1.47  tff(c_30, plain, (![A_43]: (l1_struct_0(A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.47  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.15/1.47  tff(c_224, plain, (![C_114, A_115, B_116]: (m1_subset_1(C_114, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_115)))) | ~r1_tarski(C_114, B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_115)))) | ~l1_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.15/1.47  tff(c_293, plain, (![A_133, C_134, A_135, B_136]: (m1_subset_1(k3_xboole_0(A_133, C_134), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_135)))) | ~m1_subset_1(B_136, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_135)))) | ~l1_struct_0(A_135) | ~r1_tarski(A_133, B_136))), inference(resolution, [status(thm)], [c_10, c_224])).
% 3.15/1.47  tff(c_298, plain, (![A_133, C_134]: (m1_subset_1(k3_xboole_0(A_133, C_134), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_struct_0('#skF_1') | ~r1_tarski(A_133, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_293])).
% 3.15/1.47  tff(c_300, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_298])).
% 3.15/1.47  tff(c_303, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_300])).
% 3.15/1.47  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_303])).
% 3.15/1.47  tff(c_309, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_298])).
% 3.15/1.47  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.15/1.47  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_tarski(k5_xboole_0(A_8, C_10), B_9) | ~r1_tarski(C_10, B_9) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.15/1.47  tff(c_310, plain, (![A_137, C_138, A_139, B_140]: (m1_subset_1(k5_xboole_0(A_137, C_138), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_139)))) | ~m1_subset_1(B_140, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_139)))) | ~l1_struct_0(A_139) | ~r1_tarski(C_138, B_140) | ~r1_tarski(A_137, B_140))), inference(resolution, [status(thm)], [c_12, c_224])).
% 3.15/1.47  tff(c_314, plain, (![A_137, C_138]: (m1_subset_1(k5_xboole_0(A_137, C_138), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_struct_0('#skF_1') | ~r1_tarski(C_138, '#skF_2') | ~r1_tarski(A_137, '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_310])).
% 3.15/1.47  tff(c_320, plain, (![A_137, C_138]: (m1_subset_1(k5_xboole_0(A_137, C_138), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(C_138, '#skF_2') | ~r1_tarski(A_137, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_314])).
% 3.15/1.47  tff(c_38, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.15/1.47  tff(c_280, plain, (![B_130, A_131, C_132]: (v1_tops_2(B_130, A_131) | ~v1_tops_2(C_132, A_131) | ~r1_tarski(B_130, C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131)))) | ~m1_subset_1(B_130, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131)))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.15/1.47  tff(c_567, plain, (![A_181, C_182, A_183, B_184]: (v1_tops_2(k5_xboole_0(A_181, C_182), A_183) | ~v1_tops_2(B_184, A_183) | ~m1_subset_1(B_184, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_183)))) | ~m1_subset_1(k5_xboole_0(A_181, C_182), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_183)))) | ~l1_pre_topc(A_183) | ~r1_tarski(C_182, B_184) | ~r1_tarski(A_181, B_184))), inference(resolution, [status(thm)], [c_12, c_280])).
% 3.15/1.47  tff(c_587, plain, (![A_181, C_182]: (v1_tops_2(k5_xboole_0(A_181, C_182), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1(k5_xboole_0(A_181, C_182), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(C_182, '#skF_2') | ~r1_tarski(A_181, '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_567])).
% 3.15/1.47  tff(c_676, plain, (![A_199, C_200]: (v1_tops_2(k5_xboole_0(A_199, C_200), '#skF_1') | ~m1_subset_1(k5_xboole_0(A_199, C_200), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(C_200, '#skF_2') | ~r1_tarski(A_199, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_587])).
% 3.15/1.47  tff(c_689, plain, (![A_201, C_202]: (v1_tops_2(k5_xboole_0(A_201, C_202), '#skF_1') | ~r1_tarski(C_202, '#skF_2') | ~r1_tarski(A_201, '#skF_2'))), inference(resolution, [status(thm)], [c_320, c_676])).
% 3.15/1.47  tff(c_693, plain, (![A_203, B_204]: (v1_tops_2(k4_xboole_0(A_203, B_204), '#skF_1') | ~r1_tarski(k3_xboole_0(A_203, B_204), '#skF_2') | ~r1_tarski(A_203, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_689])).
% 3.15/1.47  tff(c_95, plain, (![A_78, B_79, C_80]: (k7_subset_1(A_78, B_79, C_80)=k4_xboole_0(B_79, C_80) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.15/1.47  tff(c_101, plain, (![C_80]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_80)=k4_xboole_0('#skF_2', C_80))), inference(resolution, [status(thm)], [c_42, c_95])).
% 3.15/1.47  tff(c_36, plain, (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.15/1.47  tff(c_120, plain, (~v1_tops_2(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_36])).
% 3.15/1.47  tff(c_696, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_693, c_120])).
% 3.15/1.47  tff(c_699, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_696])).
% 3.15/1.47  tff(c_702, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_699])).
% 3.15/1.47  tff(c_706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_702])).
% 3.15/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.47  
% 3.15/1.47  Inference rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Ref     : 0
% 3.15/1.47  #Sup     : 142
% 3.15/1.47  #Fact    : 0
% 3.15/1.47  #Define  : 0
% 3.15/1.47  #Split   : 2
% 3.15/1.47  #Chain   : 0
% 3.15/1.47  #Close   : 0
% 3.15/1.47  
% 3.15/1.47  Ordering : KBO
% 3.15/1.47  
% 3.15/1.47  Simplification rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Subsume      : 6
% 3.15/1.47  #Demod        : 53
% 3.15/1.47  #Tautology    : 33
% 3.15/1.47  #SimpNegUnit  : 0
% 3.15/1.47  #BackRed      : 1
% 3.15/1.47  
% 3.15/1.47  #Partial instantiations: 0
% 3.15/1.47  #Strategies tried      : 1
% 3.15/1.47  
% 3.15/1.47  Timing (in seconds)
% 3.15/1.47  ----------------------
% 3.15/1.48  Preprocessing        : 0.33
% 3.15/1.48  Parsing              : 0.18
% 3.15/1.48  CNF conversion       : 0.02
% 3.15/1.48  Main loop            : 0.35
% 3.15/1.48  Inferencing          : 0.13
% 3.15/1.48  Reduction            : 0.11
% 3.15/1.48  Demodulation         : 0.08
% 3.15/1.48  BG Simplification    : 0.02
% 3.15/1.48  Subsumption          : 0.07
% 3.15/1.48  Abstraction          : 0.02
% 3.23/1.48  MUC search           : 0.00
% 3.23/1.48  Cooper               : 0.00
% 3.23/1.48  Total                : 0.72
% 3.23/1.48  Index Insertion      : 0.00
% 3.23/1.48  Index Deletion       : 0.00
% 3.23/1.48  Index Matching       : 0.00
% 3.23/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
