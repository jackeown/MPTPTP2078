%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:55 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 108 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   83 ( 181 expanded)
%              Number of equality atoms :    8 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

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

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tops_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( r1_tarski(C,B)
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    ! [A_41] :
      ( l1_struct_0(A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_18,plain,(
    ! [A_32,B_33] : k6_subset_1(A_32,B_33) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_30,B_31] : m1_subset_1(k6_subset_1(A_30,B_31),k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_43,plain,(
    ! [A_30,B_31] : m1_subset_1(k4_xboole_0(A_30,B_31),k1_zfmisc_1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16])).

tff(c_65,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_79,plain,(
    ! [A_30,B_31] : r1_tarski(k4_xboole_0(A_30,B_31),A_30) ),
    inference(resolution,[status(thm)],[c_43,c_65])).

tff(c_191,plain,(
    ! [C_106,A_107,B_108] :
      ( m1_subset_1(C_106,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107))))
      | ~ r1_tarski(C_106,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107))))
      | ~ l1_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_213,plain,(
    ! [A_113,B_114,A_115] :
      ( m1_subset_1(k4_xboole_0(A_113,B_114),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_115))))
      | ~ m1_subset_1(A_113,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_115))))
      | ~ l1_struct_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_79,c_191])).

tff(c_20,plain,(
    ! [A_34,B_35,C_36] :
      ( k7_subset_1(A_34,B_35,C_36) = k4_xboole_0(B_35,C_36)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_250,plain,(
    ! [A_129,A_130,B_131,C_132] :
      ( k7_subset_1(k1_zfmisc_1(u1_struct_0(A_129)),k4_xboole_0(A_130,B_131),C_132) = k4_xboole_0(k4_xboole_0(A_130,B_131),C_132)
      | ~ m1_subset_1(A_130,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_129))))
      | ~ l1_struct_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_213,c_20])).

tff(c_266,plain,(
    ! [B_131,C_132] :
      ( k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),k4_xboole_0('#skF_3',B_131),C_132) = k4_xboole_0(k4_xboole_0('#skF_3',B_131),C_132)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_250])).

tff(c_268,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_271,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_268])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_271])).

tff(c_277,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_36,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_200,plain,(
    ! [A_30,B_31,A_107] :
      ( m1_subset_1(k4_xboole_0(A_30,B_31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107))))
      | ~ m1_subset_1(A_30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107))))
      | ~ l1_struct_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_79,c_191])).

tff(c_237,plain,(
    ! [B_126,A_127,C_128] :
      ( v2_tops_2(B_126,A_127)
      | ~ v2_tops_2(C_128,A_127)
      | ~ r1_tarski(B_126,C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_127))))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_127))))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_381,plain,(
    ! [A_149,B_150,A_151] :
      ( v2_tops_2(k4_xboole_0(A_149,B_150),A_151)
      | ~ v2_tops_2(A_149,A_151)
      | ~ m1_subset_1(A_149,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_151))))
      | ~ m1_subset_1(k4_xboole_0(A_149,B_150),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_151))))
      | ~ l1_pre_topc(A_151) ) ),
    inference(resolution,[status(thm)],[c_79,c_237])).

tff(c_395,plain,(
    ! [A_152,B_153,A_154] :
      ( v2_tops_2(k4_xboole_0(A_152,B_153),A_154)
      | ~ v2_tops_2(A_152,A_154)
      | ~ l1_pre_topc(A_154)
      | ~ m1_subset_1(A_152,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_154))))
      | ~ l1_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_200,c_381])).

tff(c_407,plain,(
    ! [B_153] :
      ( v2_tops_2(k4_xboole_0('#skF_2',B_153),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_395])).

tff(c_416,plain,(
    ! [B_153] : v2_tops_2(k4_xboole_0('#skF_2',B_153),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_42,c_36,c_407])).

tff(c_110,plain,(
    ! [A_80,B_81,C_82] :
      ( k7_subset_1(A_80,B_81,C_82) = k4_xboole_0(B_81,C_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_122,plain,(
    ! [C_82] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_82) = k4_xboole_0('#skF_2',C_82) ),
    inference(resolution,[status(thm)],[c_40,c_110])).

tff(c_34,plain,(
    ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_132,plain,(
    ~ v2_tops_2(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_34])).

tff(c_424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.32  
% 2.57/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.32  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k7_subset_1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.57/1.32  
% 2.57/1.32  %Foreground sorts:
% 2.57/1.32  
% 2.57/1.32  
% 2.57/1.32  %Background operators:
% 2.57/1.32  
% 2.57/1.32  
% 2.57/1.32  %Foreground operators:
% 2.57/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.57/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.57/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.57/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.57/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.32  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.57/1.32  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.57/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.57/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.32  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.57/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.57/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.57/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.57/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.57/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.57/1.32  
% 2.57/1.33  tff(f_94, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tops_2)).
% 2.57/1.33  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.57/1.33  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.57/1.33  tff(f_41, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.57/1.33  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.57/1.33  tff(f_81, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_tops_2)).
% 2.57/1.33  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.57/1.33  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 2.57/1.33  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.57/1.33  tff(c_28, plain, (![A_41]: (l1_struct_0(A_41) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.57/1.33  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.57/1.33  tff(c_18, plain, (![A_32, B_33]: (k6_subset_1(A_32, B_33)=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.57/1.33  tff(c_16, plain, (![A_30, B_31]: (m1_subset_1(k6_subset_1(A_30, B_31), k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.57/1.33  tff(c_43, plain, (![A_30, B_31]: (m1_subset_1(k4_xboole_0(A_30, B_31), k1_zfmisc_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16])).
% 2.57/1.33  tff(c_65, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | ~m1_subset_1(A_69, k1_zfmisc_1(B_70)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.57/1.33  tff(c_79, plain, (![A_30, B_31]: (r1_tarski(k4_xboole_0(A_30, B_31), A_30))), inference(resolution, [status(thm)], [c_43, c_65])).
% 2.57/1.33  tff(c_191, plain, (![C_106, A_107, B_108]: (m1_subset_1(C_106, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107)))) | ~r1_tarski(C_106, B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107)))) | ~l1_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.57/1.33  tff(c_213, plain, (![A_113, B_114, A_115]: (m1_subset_1(k4_xboole_0(A_113, B_114), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_115)))) | ~m1_subset_1(A_113, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_115)))) | ~l1_struct_0(A_115))), inference(resolution, [status(thm)], [c_79, c_191])).
% 2.57/1.33  tff(c_20, plain, (![A_34, B_35, C_36]: (k7_subset_1(A_34, B_35, C_36)=k4_xboole_0(B_35, C_36) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.57/1.33  tff(c_250, plain, (![A_129, A_130, B_131, C_132]: (k7_subset_1(k1_zfmisc_1(u1_struct_0(A_129)), k4_xboole_0(A_130, B_131), C_132)=k4_xboole_0(k4_xboole_0(A_130, B_131), C_132) | ~m1_subset_1(A_130, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_129)))) | ~l1_struct_0(A_129))), inference(resolution, [status(thm)], [c_213, c_20])).
% 2.57/1.33  tff(c_266, plain, (![B_131, C_132]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), k4_xboole_0('#skF_3', B_131), C_132)=k4_xboole_0(k4_xboole_0('#skF_3', B_131), C_132) | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_250])).
% 2.57/1.33  tff(c_268, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_266])).
% 2.57/1.33  tff(c_271, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_268])).
% 2.57/1.33  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_271])).
% 2.57/1.33  tff(c_277, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_266])).
% 2.57/1.33  tff(c_36, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.57/1.33  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.57/1.33  tff(c_200, plain, (![A_30, B_31, A_107]: (m1_subset_1(k4_xboole_0(A_30, B_31), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107)))) | ~m1_subset_1(A_30, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107)))) | ~l1_struct_0(A_107))), inference(resolution, [status(thm)], [c_79, c_191])).
% 2.57/1.33  tff(c_237, plain, (![B_126, A_127, C_128]: (v2_tops_2(B_126, A_127) | ~v2_tops_2(C_128, A_127) | ~r1_tarski(B_126, C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_127)))) | ~m1_subset_1(B_126, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_127)))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.57/1.33  tff(c_381, plain, (![A_149, B_150, A_151]: (v2_tops_2(k4_xboole_0(A_149, B_150), A_151) | ~v2_tops_2(A_149, A_151) | ~m1_subset_1(A_149, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_151)))) | ~m1_subset_1(k4_xboole_0(A_149, B_150), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_151)))) | ~l1_pre_topc(A_151))), inference(resolution, [status(thm)], [c_79, c_237])).
% 2.57/1.33  tff(c_395, plain, (![A_152, B_153, A_154]: (v2_tops_2(k4_xboole_0(A_152, B_153), A_154) | ~v2_tops_2(A_152, A_154) | ~l1_pre_topc(A_154) | ~m1_subset_1(A_152, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_154)))) | ~l1_struct_0(A_154))), inference(resolution, [status(thm)], [c_200, c_381])).
% 2.57/1.33  tff(c_407, plain, (![B_153]: (v2_tops_2(k4_xboole_0('#skF_2', B_153), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_395])).
% 2.57/1.33  tff(c_416, plain, (![B_153]: (v2_tops_2(k4_xboole_0('#skF_2', B_153), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_277, c_42, c_36, c_407])).
% 2.57/1.33  tff(c_110, plain, (![A_80, B_81, C_82]: (k7_subset_1(A_80, B_81, C_82)=k4_xboole_0(B_81, C_82) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.57/1.33  tff(c_122, plain, (![C_82]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_82)=k4_xboole_0('#skF_2', C_82))), inference(resolution, [status(thm)], [c_40, c_110])).
% 2.57/1.33  tff(c_34, plain, (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.57/1.33  tff(c_132, plain, (~v2_tops_2(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_34])).
% 2.57/1.33  tff(c_424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_416, c_132])).
% 2.57/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.33  
% 2.57/1.33  Inference rules
% 2.57/1.33  ----------------------
% 2.57/1.33  #Ref     : 0
% 2.57/1.33  #Sup     : 81
% 2.57/1.33  #Fact    : 0
% 2.57/1.33  #Define  : 0
% 2.57/1.33  #Split   : 2
% 2.57/1.33  #Chain   : 0
% 2.57/1.33  #Close   : 0
% 2.57/1.33  
% 2.57/1.33  Ordering : KBO
% 2.57/1.33  
% 2.57/1.33  Simplification rules
% 2.57/1.33  ----------------------
% 2.57/1.33  #Subsume      : 1
% 2.57/1.33  #Demod        : 24
% 2.57/1.33  #Tautology    : 45
% 2.57/1.33  #SimpNegUnit  : 0
% 2.57/1.33  #BackRed      : 2
% 2.57/1.33  
% 2.57/1.33  #Partial instantiations: 0
% 2.57/1.33  #Strategies tried      : 1
% 2.57/1.33  
% 2.57/1.34  Timing (in seconds)
% 2.57/1.34  ----------------------
% 2.62/1.34  Preprocessing        : 0.32
% 2.62/1.34  Parsing              : 0.17
% 2.62/1.34  CNF conversion       : 0.02
% 2.62/1.34  Main loop            : 0.26
% 2.62/1.34  Inferencing          : 0.10
% 2.62/1.34  Reduction            : 0.08
% 2.62/1.34  Demodulation         : 0.06
% 2.62/1.34  BG Simplification    : 0.02
% 2.62/1.34  Subsumption          : 0.05
% 2.62/1.34  Abstraction          : 0.02
% 2.62/1.34  MUC search           : 0.00
% 2.62/1.34  Cooper               : 0.00
% 2.62/1.34  Total                : 0.61
% 2.62/1.34  Index Insertion      : 0.00
% 2.62/1.34  Index Deletion       : 0.00
% 2.62/1.34  Index Matching       : 0.00
% 2.62/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
