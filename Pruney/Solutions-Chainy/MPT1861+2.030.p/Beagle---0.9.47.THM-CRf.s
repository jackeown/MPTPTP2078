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
% DateTime   : Thu Dec  3 10:29:13 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 119 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 238 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_106,plain,(
    ! [A_75,B_76,C_77] :
      ( k9_subset_1(A_75,B_76,C_77) = k3_xboole_0(B_76,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_119,plain,(
    ! [B_76] : k9_subset_1(u1_struct_0('#skF_1'),B_76,'#skF_3') = k3_xboole_0(B_76,'#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_106])).

tff(c_32,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_189,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_32])).

tff(c_34,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_53,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_190,plain,(
    ! [B_91] : k9_subset_1(u1_struct_0('#skF_1'),B_91,'#skF_3') = k3_xboole_0(B_91,'#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_106])).

tff(c_20,plain,(
    ! [A_32,B_33,C_34] :
      ( m1_subset_1(k9_subset_1(A_32,B_33,C_34),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_199,plain,(
    ! [B_91] :
      ( m1_subset_1(k3_xboole_0(B_91,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_20])).

tff(c_207,plain,(
    ! [B_91] : m1_subset_1(k3_xboole_0(B_91,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_199])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_744,plain,(
    ! [C_187,A_188,B_189] :
      ( v2_tex_2(C_187,A_188)
      | ~ v2_tex_2(B_189,A_188)
      | ~ r1_tarski(C_187,B_189)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_913,plain,(
    ! [A_217,B_218,A_219] :
      ( v2_tex_2(k3_xboole_0(A_217,B_218),A_219)
      | ~ v2_tex_2(A_217,A_219)
      | ~ m1_subset_1(k3_xboole_0(A_217,B_218),k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ m1_subset_1(A_217,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219) ) ),
    inference(resolution,[status(thm)],[c_2,c_744])).

tff(c_944,plain,(
    ! [B_91] :
      ( v2_tex_2(k3_xboole_0(B_91,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_91,'#skF_1')
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_207,c_913])).

tff(c_979,plain,(
    ! [B_220] :
      ( v2_tex_2(k3_xboole_0(B_220,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_220,'#skF_1')
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_944])).

tff(c_1031,plain,
    ( v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_979])).

tff(c_1052,plain,(
    v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_1031])).

tff(c_1054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_1052])).

tff(c_1055,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1108,plain,(
    ! [A_236,B_237,C_238] :
      ( k9_subset_1(A_236,B_237,C_238) = k3_xboole_0(B_237,C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(A_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1180,plain,(
    ! [B_252] : k9_subset_1(u1_struct_0('#skF_1'),B_252,'#skF_3') = k3_xboole_0(B_252,'#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1108])).

tff(c_1186,plain,(
    ! [B_252] :
      ( m1_subset_1(k3_xboole_0(B_252,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1180,c_20])).

tff(c_1192,plain,(
    ! [B_252] : m1_subset_1(k3_xboole_0(B_252,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1186])).

tff(c_16,plain,(
    ! [A_30] : k2_subset_1(A_30) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_31] : m1_subset_1(k2_subset_1(A_31),k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_41,plain,(
    ! [A_31] : m1_subset_1(A_31,k1_zfmisc_1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_1123,plain,(
    ! [A_31,B_237] : k9_subset_1(A_31,B_237,A_31) = k3_xboole_0(B_237,A_31) ),
    inference(resolution,[status(thm)],[c_41,c_1108])).

tff(c_1103,plain,(
    ! [A_233,B_234,C_235] :
      ( m1_subset_1(k9_subset_1(A_233,B_234,C_235),k1_zfmisc_1(A_233))
      | ~ m1_subset_1(C_235,k1_zfmisc_1(A_233)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1107,plain,(
    ! [A_233,B_234,C_235] :
      ( r1_tarski(k9_subset_1(A_233,B_234,C_235),A_233)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(A_233)) ) ),
    inference(resolution,[status(thm)],[c_1103,c_26])).

tff(c_1685,plain,(
    ! [C_347,A_348,B_349] :
      ( v2_tex_2(C_347,A_348)
      | ~ v2_tex_2(B_349,A_348)
      | ~ r1_tarski(C_347,B_349)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ m1_subset_1(B_349,k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ l1_pre_topc(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2364,plain,(
    ! [A_414,B_415,C_416,A_417] :
      ( v2_tex_2(k9_subset_1(A_414,B_415,C_416),A_417)
      | ~ v2_tex_2(A_414,A_417)
      | ~ m1_subset_1(k9_subset_1(A_414,B_415,C_416),k1_zfmisc_1(u1_struct_0(A_417)))
      | ~ m1_subset_1(A_414,k1_zfmisc_1(u1_struct_0(A_417)))
      | ~ l1_pre_topc(A_417)
      | ~ m1_subset_1(C_416,k1_zfmisc_1(A_414)) ) ),
    inference(resolution,[status(thm)],[c_1107,c_1685])).

tff(c_2403,plain,(
    ! [A_31,B_237,A_417] :
      ( v2_tex_2(k9_subset_1(A_31,B_237,A_31),A_417)
      | ~ v2_tex_2(A_31,A_417)
      | ~ m1_subset_1(k3_xboole_0(B_237,A_31),k1_zfmisc_1(u1_struct_0(A_417)))
      | ~ m1_subset_1(A_31,k1_zfmisc_1(u1_struct_0(A_417)))
      | ~ l1_pre_topc(A_417)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1123,c_2364])).

tff(c_2697,plain,(
    ! [B_467,A_468,A_469] :
      ( v2_tex_2(k3_xboole_0(B_467,A_468),A_469)
      | ~ v2_tex_2(A_468,A_469)
      | ~ m1_subset_1(k3_xboole_0(B_467,A_468),k1_zfmisc_1(u1_struct_0(A_469)))
      | ~ m1_subset_1(A_468,k1_zfmisc_1(u1_struct_0(A_469)))
      | ~ l1_pre_topc(A_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_1123,c_2403])).

tff(c_2742,plain,(
    ! [B_252] :
      ( v2_tex_2(k3_xboole_0(B_252,'#skF_3'),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1192,c_2697])).

tff(c_2785,plain,(
    ! [B_252] : v2_tex_2(k3_xboole_0(B_252,'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_1055,c_2742])).

tff(c_1121,plain,(
    ! [B_237] : k9_subset_1(u1_struct_0('#skF_1'),B_237,'#skF_3') = k3_xboole_0(B_237,'#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1108])).

tff(c_1179,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_32])).

tff(c_2807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2785,c_1179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.86  
% 4.69/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.86  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.69/1.86  
% 4.69/1.86  %Foreground sorts:
% 4.69/1.86  
% 4.69/1.86  
% 4.69/1.86  %Background operators:
% 4.69/1.86  
% 4.69/1.86  
% 4.69/1.86  %Foreground operators:
% 4.69/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.69/1.86  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.69/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.69/1.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.69/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.69/1.86  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.69/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.69/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.69/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.69/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.69/1.86  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.69/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.69/1.86  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.69/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.69/1.86  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.69/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.69/1.86  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.69/1.86  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.69/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.69/1.86  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.69/1.86  
% 4.69/1.87  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 4.69/1.87  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.69/1.87  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 4.69/1.87  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.69/1.87  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 4.69/1.87  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.69/1.87  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.69/1.87  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.69/1.87  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.69/1.87  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.69/1.87  tff(c_106, plain, (![A_75, B_76, C_77]: (k9_subset_1(A_75, B_76, C_77)=k3_xboole_0(B_76, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.69/1.87  tff(c_119, plain, (![B_76]: (k9_subset_1(u1_struct_0('#skF_1'), B_76, '#skF_3')=k3_xboole_0(B_76, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_106])).
% 4.69/1.87  tff(c_32, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.69/1.87  tff(c_189, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_32])).
% 4.69/1.87  tff(c_34, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.69/1.87  tff(c_53, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 4.69/1.87  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.69/1.87  tff(c_190, plain, (![B_91]: (k9_subset_1(u1_struct_0('#skF_1'), B_91, '#skF_3')=k3_xboole_0(B_91, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_106])).
% 4.69/1.87  tff(c_20, plain, (![A_32, B_33, C_34]: (m1_subset_1(k9_subset_1(A_32, B_33, C_34), k1_zfmisc_1(A_32)) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.69/1.87  tff(c_199, plain, (![B_91]: (m1_subset_1(k3_xboole_0(B_91, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_190, c_20])).
% 4.69/1.87  tff(c_207, plain, (![B_91]: (m1_subset_1(k3_xboole_0(B_91, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_199])).
% 4.69/1.87  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.69/1.87  tff(c_744, plain, (![C_187, A_188, B_189]: (v2_tex_2(C_187, A_188) | ~v2_tex_2(B_189, A_188) | ~r1_tarski(C_187, B_189) | ~m1_subset_1(C_187, k1_zfmisc_1(u1_struct_0(A_188))) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.69/1.87  tff(c_913, plain, (![A_217, B_218, A_219]: (v2_tex_2(k3_xboole_0(A_217, B_218), A_219) | ~v2_tex_2(A_217, A_219) | ~m1_subset_1(k3_xboole_0(A_217, B_218), k1_zfmisc_1(u1_struct_0(A_219))) | ~m1_subset_1(A_217, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219))), inference(resolution, [status(thm)], [c_2, c_744])).
% 4.69/1.87  tff(c_944, plain, (![B_91]: (v2_tex_2(k3_xboole_0(B_91, '#skF_3'), '#skF_1') | ~v2_tex_2(B_91, '#skF_1') | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_207, c_913])).
% 4.69/1.87  tff(c_979, plain, (![B_220]: (v2_tex_2(k3_xboole_0(B_220, '#skF_3'), '#skF_1') | ~v2_tex_2(B_220, '#skF_1') | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_944])).
% 4.69/1.87  tff(c_1031, plain, (v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_979])).
% 4.69/1.87  tff(c_1052, plain, (v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_1031])).
% 4.69/1.87  tff(c_1054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_1052])).
% 4.69/1.87  tff(c_1055, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 4.69/1.87  tff(c_1108, plain, (![A_236, B_237, C_238]: (k9_subset_1(A_236, B_237, C_238)=k3_xboole_0(B_237, C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(A_236)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.69/1.87  tff(c_1180, plain, (![B_252]: (k9_subset_1(u1_struct_0('#skF_1'), B_252, '#skF_3')=k3_xboole_0(B_252, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_1108])).
% 4.69/1.87  tff(c_1186, plain, (![B_252]: (m1_subset_1(k3_xboole_0(B_252, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_1180, c_20])).
% 4.69/1.87  tff(c_1192, plain, (![B_252]: (m1_subset_1(k3_xboole_0(B_252, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1186])).
% 4.69/1.87  tff(c_16, plain, (![A_30]: (k2_subset_1(A_30)=A_30)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.69/1.87  tff(c_18, plain, (![A_31]: (m1_subset_1(k2_subset_1(A_31), k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.69/1.87  tff(c_41, plain, (![A_31]: (m1_subset_1(A_31, k1_zfmisc_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 4.69/1.87  tff(c_1123, plain, (![A_31, B_237]: (k9_subset_1(A_31, B_237, A_31)=k3_xboole_0(B_237, A_31))), inference(resolution, [status(thm)], [c_41, c_1108])).
% 4.69/1.87  tff(c_1103, plain, (![A_233, B_234, C_235]: (m1_subset_1(k9_subset_1(A_233, B_234, C_235), k1_zfmisc_1(A_233)) | ~m1_subset_1(C_235, k1_zfmisc_1(A_233)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.69/1.87  tff(c_26, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.69/1.87  tff(c_1107, plain, (![A_233, B_234, C_235]: (r1_tarski(k9_subset_1(A_233, B_234, C_235), A_233) | ~m1_subset_1(C_235, k1_zfmisc_1(A_233)))), inference(resolution, [status(thm)], [c_1103, c_26])).
% 4.69/1.87  tff(c_1685, plain, (![C_347, A_348, B_349]: (v2_tex_2(C_347, A_348) | ~v2_tex_2(B_349, A_348) | ~r1_tarski(C_347, B_349) | ~m1_subset_1(C_347, k1_zfmisc_1(u1_struct_0(A_348))) | ~m1_subset_1(B_349, k1_zfmisc_1(u1_struct_0(A_348))) | ~l1_pre_topc(A_348))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.69/1.87  tff(c_2364, plain, (![A_414, B_415, C_416, A_417]: (v2_tex_2(k9_subset_1(A_414, B_415, C_416), A_417) | ~v2_tex_2(A_414, A_417) | ~m1_subset_1(k9_subset_1(A_414, B_415, C_416), k1_zfmisc_1(u1_struct_0(A_417))) | ~m1_subset_1(A_414, k1_zfmisc_1(u1_struct_0(A_417))) | ~l1_pre_topc(A_417) | ~m1_subset_1(C_416, k1_zfmisc_1(A_414)))), inference(resolution, [status(thm)], [c_1107, c_1685])).
% 4.69/1.87  tff(c_2403, plain, (![A_31, B_237, A_417]: (v2_tex_2(k9_subset_1(A_31, B_237, A_31), A_417) | ~v2_tex_2(A_31, A_417) | ~m1_subset_1(k3_xboole_0(B_237, A_31), k1_zfmisc_1(u1_struct_0(A_417))) | ~m1_subset_1(A_31, k1_zfmisc_1(u1_struct_0(A_417))) | ~l1_pre_topc(A_417) | ~m1_subset_1(A_31, k1_zfmisc_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_1123, c_2364])).
% 4.69/1.87  tff(c_2697, plain, (![B_467, A_468, A_469]: (v2_tex_2(k3_xboole_0(B_467, A_468), A_469) | ~v2_tex_2(A_468, A_469) | ~m1_subset_1(k3_xboole_0(B_467, A_468), k1_zfmisc_1(u1_struct_0(A_469))) | ~m1_subset_1(A_468, k1_zfmisc_1(u1_struct_0(A_469))) | ~l1_pre_topc(A_469))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_1123, c_2403])).
% 4.69/1.87  tff(c_2742, plain, (![B_252]: (v2_tex_2(k3_xboole_0(B_252, '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_1192, c_2697])).
% 4.69/1.87  tff(c_2785, plain, (![B_252]: (v2_tex_2(k3_xboole_0(B_252, '#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_1055, c_2742])).
% 4.69/1.87  tff(c_1121, plain, (![B_237]: (k9_subset_1(u1_struct_0('#skF_1'), B_237, '#skF_3')=k3_xboole_0(B_237, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_1108])).
% 4.69/1.87  tff(c_1179, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_32])).
% 4.69/1.87  tff(c_2807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2785, c_1179])).
% 4.69/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.87  
% 4.69/1.87  Inference rules
% 4.69/1.87  ----------------------
% 4.69/1.87  #Ref     : 0
% 4.69/1.87  #Sup     : 600
% 4.69/1.87  #Fact    : 0
% 4.69/1.87  #Define  : 0
% 4.69/1.87  #Split   : 2
% 4.69/1.87  #Chain   : 0
% 4.69/1.87  #Close   : 0
% 4.69/1.87  
% 4.69/1.87  Ordering : KBO
% 4.69/1.87  
% 4.69/1.87  Simplification rules
% 4.69/1.87  ----------------------
% 4.69/1.87  #Subsume      : 34
% 4.69/1.87  #Demod        : 441
% 4.69/1.87  #Tautology    : 222
% 4.69/1.87  #SimpNegUnit  : 4
% 4.69/1.87  #BackRed      : 4
% 4.69/1.87  
% 4.69/1.87  #Partial instantiations: 0
% 4.69/1.87  #Strategies tried      : 1
% 4.69/1.87  
% 4.69/1.87  Timing (in seconds)
% 4.69/1.87  ----------------------
% 4.69/1.88  Preprocessing        : 0.32
% 4.69/1.88  Parsing              : 0.18
% 4.69/1.88  CNF conversion       : 0.02
% 4.69/1.88  Main loop            : 0.77
% 4.69/1.88  Inferencing          : 0.29
% 4.69/1.88  Reduction            : 0.27
% 4.69/1.88  Demodulation         : 0.21
% 4.69/1.88  BG Simplification    : 0.04
% 4.69/1.88  Subsumption          : 0.12
% 4.69/1.88  Abstraction          : 0.05
% 4.69/1.88  MUC search           : 0.00
% 4.69/1.88  Cooper               : 0.00
% 4.69/1.88  Total                : 1.12
% 4.69/1.88  Index Insertion      : 0.00
% 4.69/1.88  Index Deletion       : 0.00
% 4.69/1.88  Index Matching       : 0.00
% 4.69/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
