%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:53 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :   61 (  75 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 112 expanded)
%              Number of equality atoms :   24 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_72,axiom,(
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

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_78,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_36,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_439,plain,(
    ! [A_104,B_105] :
      ( k2_pre_topc(A_104,B_105) = B_105
      | ~ v4_pre_topc(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_442,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_439])).

tff(c_445,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_442])).

tff(c_822,plain,(
    ! [A_153,B_154] :
      ( k4_subset_1(u1_struct_0(A_153),B_154,k2_tops_1(A_153,B_154)) = k2_pre_topc(A_153,B_154)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_826,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_822])).

tff(c_830,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_445,c_826])).

tff(c_32,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k2_tops_1(A_43,B_44),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_611,plain,(
    ! [A_124,B_125,C_126] :
      ( k4_subset_1(A_124,B_125,C_126) = k2_xboole_0(B_125,C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(A_124))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(A_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1665,plain,(
    ! [A_249,B_250,B_251] :
      ( k4_subset_1(u1_struct_0(A_249),B_250,k2_tops_1(A_249,B_251)) = k2_xboole_0(B_250,k2_tops_1(A_249,B_251))
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249) ) ),
    inference(resolution,[status(thm)],[c_32,c_611])).

tff(c_1669,plain,(
    ! [B_251] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_251)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_251))
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_1665])).

tff(c_1677,plain,(
    ! [B_252] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_252)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_252))
      | ~ m1_subset_1(B_252,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1669])).

tff(c_1684,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_1677])).

tff(c_1689,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_1684])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_102,plain,(
    ! [B_56,A_57] : k3_tarski(k2_tarski(B_56,A_57)) = k2_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_78])).

tff(c_24,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_137,plain,(
    ! [B_63,A_64] : k2_xboole_0(B_63,A_64) = k2_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_24])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(A_58,C_59)
      | ~ r1_tarski(k2_xboole_0(A_58,B_60),C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [A_58,B_60] : r1_tarski(A_58,k2_xboole_0(A_58,B_60)) ),
    inference(resolution,[status(thm)],[c_6,c_125])).

tff(c_152,plain,(
    ! [A_64,B_63] : r1_tarski(A_64,k2_xboole_0(B_63,A_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_130])).

tff(c_1793,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1689,c_152])).

tff(c_1823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1793])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.85  
% 4.43/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.86  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.43/1.86  
% 4.43/1.86  %Foreground sorts:
% 4.43/1.86  
% 4.43/1.86  
% 4.43/1.86  %Background operators:
% 4.43/1.86  
% 4.43/1.86  
% 4.43/1.86  %Foreground operators:
% 4.43/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.43/1.86  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.43/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.43/1.86  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.43/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.43/1.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.43/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.43/1.86  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.43/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.43/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.43/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.43/1.86  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.43/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.43/1.86  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.43/1.86  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.43/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.43/1.86  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.43/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.43/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.43/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.43/1.86  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.43/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.43/1.86  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.43/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.43/1.86  
% 4.43/1.87  tff(f_95, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 4.43/1.87  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.43/1.87  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 4.43/1.87  tff(f_78, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.43/1.87  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.43/1.87  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.43/1.87  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.43/1.87  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.43/1.87  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.43/1.87  tff(c_36, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.43/1.87  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.43/1.87  tff(c_38, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.43/1.87  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.43/1.87  tff(c_439, plain, (![A_104, B_105]: (k2_pre_topc(A_104, B_105)=B_105 | ~v4_pre_topc(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.43/1.87  tff(c_442, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_439])).
% 4.43/1.87  tff(c_445, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_442])).
% 4.43/1.87  tff(c_822, plain, (![A_153, B_154]: (k4_subset_1(u1_struct_0(A_153), B_154, k2_tops_1(A_153, B_154))=k2_pre_topc(A_153, B_154) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.43/1.87  tff(c_826, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_822])).
% 4.43/1.87  tff(c_830, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_445, c_826])).
% 4.43/1.87  tff(c_32, plain, (![A_43, B_44]: (m1_subset_1(k2_tops_1(A_43, B_44), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.43/1.87  tff(c_611, plain, (![A_124, B_125, C_126]: (k4_subset_1(A_124, B_125, C_126)=k2_xboole_0(B_125, C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(A_124)) | ~m1_subset_1(B_125, k1_zfmisc_1(A_124)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.43/1.87  tff(c_1665, plain, (![A_249, B_250, B_251]: (k4_subset_1(u1_struct_0(A_249), B_250, k2_tops_1(A_249, B_251))=k2_xboole_0(B_250, k2_tops_1(A_249, B_251)) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249))), inference(resolution, [status(thm)], [c_32, c_611])).
% 4.43/1.87  tff(c_1669, plain, (![B_251]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_251))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_251)) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_1665])).
% 4.43/1.87  tff(c_1677, plain, (![B_252]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_252))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_252)) | ~m1_subset_1(B_252, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1669])).
% 4.43/1.87  tff(c_1684, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_1677])).
% 4.43/1.87  tff(c_1689, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_830, c_1684])).
% 4.43/1.87  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.43/1.87  tff(c_78, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.43/1.87  tff(c_102, plain, (![B_56, A_57]: (k3_tarski(k2_tarski(B_56, A_57))=k2_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_10, c_78])).
% 4.43/1.87  tff(c_24, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.43/1.87  tff(c_137, plain, (![B_63, A_64]: (k2_xboole_0(B_63, A_64)=k2_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_102, c_24])).
% 4.43/1.87  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.43/1.87  tff(c_125, plain, (![A_58, C_59, B_60]: (r1_tarski(A_58, C_59) | ~r1_tarski(k2_xboole_0(A_58, B_60), C_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.43/1.87  tff(c_130, plain, (![A_58, B_60]: (r1_tarski(A_58, k2_xboole_0(A_58, B_60)))), inference(resolution, [status(thm)], [c_6, c_125])).
% 4.43/1.87  tff(c_152, plain, (![A_64, B_63]: (r1_tarski(A_64, k2_xboole_0(B_63, A_64)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_130])).
% 4.43/1.87  tff(c_1793, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1689, c_152])).
% 4.43/1.87  tff(c_1823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1793])).
% 4.43/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.87  
% 4.43/1.87  Inference rules
% 4.43/1.87  ----------------------
% 4.43/1.87  #Ref     : 0
% 4.43/1.87  #Sup     : 407
% 4.43/1.87  #Fact    : 0
% 4.43/1.87  #Define  : 0
% 4.43/1.87  #Split   : 1
% 4.43/1.87  #Chain   : 0
% 4.43/1.87  #Close   : 0
% 4.43/1.87  
% 4.43/1.87  Ordering : KBO
% 4.43/1.87  
% 4.43/1.87  Simplification rules
% 4.43/1.87  ----------------------
% 4.43/1.87  #Subsume      : 12
% 4.43/1.87  #Demod        : 197
% 4.43/1.87  #Tautology    : 220
% 4.43/1.87  #SimpNegUnit  : 1
% 4.43/1.87  #BackRed      : 1
% 4.43/1.87  
% 4.43/1.87  #Partial instantiations: 0
% 4.43/1.87  #Strategies tried      : 1
% 4.43/1.87  
% 4.43/1.87  Timing (in seconds)
% 4.43/1.87  ----------------------
% 4.43/1.87  Preprocessing        : 0.43
% 4.43/1.87  Parsing              : 0.23
% 4.43/1.87  CNF conversion       : 0.02
% 4.43/1.87  Main loop            : 0.66
% 4.43/1.87  Inferencing          : 0.20
% 4.43/1.87  Reduction            : 0.27
% 4.43/1.87  Demodulation         : 0.23
% 4.43/1.87  BG Simplification    : 0.03
% 4.43/1.87  Subsumption          : 0.12
% 4.43/1.87  Abstraction          : 0.03
% 4.43/1.87  MUC search           : 0.00
% 4.43/1.87  Cooper               : 0.00
% 4.43/1.87  Total                : 1.12
% 4.43/1.87  Index Insertion      : 0.00
% 4.43/1.87  Index Deletion       : 0.00
% 4.43/1.87  Index Matching       : 0.00
% 4.43/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
