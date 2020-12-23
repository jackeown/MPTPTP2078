%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:13 EST 2020

% Result     : Theorem 6.43s
% Output     : CNFRefutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 154 expanded)
%              Number of leaves         :   29 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  101 ( 334 expanded)
%              Number of equality atoms :   21 (  42 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_463,plain,(
    ! [A_88,B_89] :
      ( k2_pre_topc(A_88,k1_tops_1(A_88,B_89)) = B_89
      | ~ v5_tops_1(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_469,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_463])).

tff(c_474,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_469])).

tff(c_24,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_475,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_24])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k1_tops_1(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_597,plain,(
    ! [A_101,B_102] :
      ( r1_tarski(k2_tops_1(A_101,k2_pre_topc(A_101,B_102)),k2_tops_1(A_101,B_102))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_604,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_597])).

tff(c_608,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_604])).

tff(c_1292,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_608])).

tff(c_1295,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1292])).

tff(c_1299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1295])).

tff(c_1300,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_608])).

tff(c_1301,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_608])).

tff(c_20,plain,(
    ! [A_20,B_22] :
      ( k4_subset_1(u1_struct_0(A_20),B_22,k2_tops_1(A_20,B_22)) = k2_pre_topc(A_20,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1303,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1301,c_20])).

tff(c_1319,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_474,c_1303])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k2_tops_1(A_18,B_19),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_319,plain,(
    ! [A_72,B_73,C_74] :
      ( k4_subset_1(A_72,B_73,C_74) = k2_xboole_0(B_73,C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1941,plain,(
    ! [A_208,B_209,B_210] :
      ( k4_subset_1(u1_struct_0(A_208),B_209,k2_tops_1(A_208,B_210)) = k2_xboole_0(B_209,k2_tops_1(A_208,B_210))
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ l1_pre_topc(A_208) ) ),
    inference(resolution,[status(thm)],[c_18,c_319])).

tff(c_1953,plain,(
    ! [A_16,B_17,B_210] :
      ( k4_subset_1(u1_struct_0(A_16),k1_tops_1(A_16,B_17),k2_tops_1(A_16,B_210)) = k2_xboole_0(k1_tops_1(A_16,B_17),k2_tops_1(A_16,B_210))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_1941])).

tff(c_3623,plain,
    ( k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2'
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1319,c_1953])).

tff(c_3636,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1301,c_3623])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [B_33,A_34] : k3_tarski(k2_tarski(B_33,A_34)) = k2_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_8,plain,(
    ! [A_8,B_9] : k3_tarski(k2_tarski(A_8,B_9)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [B_33,A_34] : k2_xboole_0(B_33,A_34) = k2_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_8])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_153,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(B_41,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [A_42,A_43,B_44] :
      ( r1_tarski(A_42,k2_xboole_0(A_43,B_44))
      | ~ r1_tarski(A_42,A_43) ) ),
    inference(resolution,[status(thm)],[c_4,c_153])).

tff(c_165,plain,(
    ! [A_42,B_33,A_34] :
      ( r1_tarski(A_42,k2_xboole_0(B_33,A_34))
      | ~ r1_tarski(A_42,A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_160])).

tff(c_4469,plain,(
    ! [A_333] :
      ( r1_tarski(A_333,'#skF_2')
      | ~ r1_tarski(A_333,k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3636,c_165])).

tff(c_4482,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1300,c_4469])).

tff(c_4495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_4482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.43/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.34  
% 6.43/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.34  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 6.43/2.34  
% 6.43/2.34  %Foreground sorts:
% 6.43/2.34  
% 6.43/2.34  
% 6.43/2.34  %Background operators:
% 6.43/2.34  
% 6.43/2.34  
% 6.43/2.34  %Foreground operators:
% 6.43/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.43/2.34  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.43/2.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.43/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.43/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.43/2.34  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.43/2.34  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.43/2.34  tff('#skF_2', type, '#skF_2': $i).
% 6.43/2.34  tff('#skF_1', type, '#skF_1': $i).
% 6.43/2.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.43/2.34  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 6.43/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.43/2.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.43/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.43/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.43/2.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.43/2.34  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.43/2.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.43/2.34  
% 6.43/2.35  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tops_1)).
% 6.43/2.35  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 6.43/2.35  tff(f_58, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 6.43/2.35  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_1)).
% 6.43/2.35  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 6.43/2.35  tff(f_64, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.43/2.35  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.43/2.35  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.43/2.35  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.43/2.35  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.43/2.35  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.43/2.35  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.43/2.35  tff(c_26, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.43/2.35  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.43/2.35  tff(c_463, plain, (![A_88, B_89]: (k2_pre_topc(A_88, k1_tops_1(A_88, B_89))=B_89 | ~v5_tops_1(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.43/2.35  tff(c_469, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_463])).
% 6.43/2.35  tff(c_474, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_469])).
% 6.43/2.35  tff(c_24, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.43/2.35  tff(c_475, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_474, c_24])).
% 6.43/2.35  tff(c_16, plain, (![A_16, B_17]: (m1_subset_1(k1_tops_1(A_16, B_17), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.43/2.35  tff(c_597, plain, (![A_101, B_102]: (r1_tarski(k2_tops_1(A_101, k2_pre_topc(A_101, B_102)), k2_tops_1(A_101, B_102)) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.43/2.35  tff(c_604, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_474, c_597])).
% 6.43/2.35  tff(c_608, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_604])).
% 6.43/2.35  tff(c_1292, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_608])).
% 6.43/2.35  tff(c_1295, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1292])).
% 6.43/2.35  tff(c_1299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1295])).
% 6.43/2.35  tff(c_1300, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_608])).
% 6.43/2.35  tff(c_1301, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_608])).
% 6.43/2.35  tff(c_20, plain, (![A_20, B_22]: (k4_subset_1(u1_struct_0(A_20), B_22, k2_tops_1(A_20, B_22))=k2_pre_topc(A_20, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.43/2.35  tff(c_1303, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1301, c_20])).
% 6.43/2.35  tff(c_1319, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_474, c_1303])).
% 6.43/2.35  tff(c_18, plain, (![A_18, B_19]: (m1_subset_1(k2_tops_1(A_18, B_19), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.43/2.35  tff(c_319, plain, (![A_72, B_73, C_74]: (k4_subset_1(A_72, B_73, C_74)=k2_xboole_0(B_73, C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.43/2.35  tff(c_1941, plain, (![A_208, B_209, B_210]: (k4_subset_1(u1_struct_0(A_208), B_209, k2_tops_1(A_208, B_210))=k2_xboole_0(B_209, k2_tops_1(A_208, B_210)) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_208))) | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0(A_208))) | ~l1_pre_topc(A_208))), inference(resolution, [status(thm)], [c_18, c_319])).
% 6.43/2.35  tff(c_1953, plain, (![A_16, B_17, B_210]: (k4_subset_1(u1_struct_0(A_16), k1_tops_1(A_16, B_17), k2_tops_1(A_16, B_210))=k2_xboole_0(k1_tops_1(A_16, B_17), k2_tops_1(A_16, B_210)) | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_16, c_1941])).
% 6.43/2.35  tff(c_3623, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2' | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1319, c_1953])).
% 6.43/2.35  tff(c_3636, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1301, c_3623])).
% 6.43/2.35  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.43/2.35  tff(c_65, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.43/2.35  tff(c_80, plain, (![B_33, A_34]: (k3_tarski(k2_tarski(B_33, A_34))=k2_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_6, c_65])).
% 6.43/2.35  tff(c_8, plain, (![A_8, B_9]: (k3_tarski(k2_tarski(A_8, B_9))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.43/2.35  tff(c_86, plain, (![B_33, A_34]: (k2_xboole_0(B_33, A_34)=k2_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_80, c_8])).
% 6.43/2.35  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.43/2.35  tff(c_153, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(B_41, C_40) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.43/2.35  tff(c_160, plain, (![A_42, A_43, B_44]: (r1_tarski(A_42, k2_xboole_0(A_43, B_44)) | ~r1_tarski(A_42, A_43))), inference(resolution, [status(thm)], [c_4, c_153])).
% 6.43/2.35  tff(c_165, plain, (![A_42, B_33, A_34]: (r1_tarski(A_42, k2_xboole_0(B_33, A_34)) | ~r1_tarski(A_42, A_34))), inference(superposition, [status(thm), theory('equality')], [c_86, c_160])).
% 6.43/2.35  tff(c_4469, plain, (![A_333]: (r1_tarski(A_333, '#skF_2') | ~r1_tarski(A_333, k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_3636, c_165])).
% 6.43/2.35  tff(c_4482, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1300, c_4469])).
% 6.43/2.35  tff(c_4495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_475, c_4482])).
% 6.43/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.35  
% 6.43/2.35  Inference rules
% 6.43/2.35  ----------------------
% 6.43/2.35  #Ref     : 0
% 6.43/2.35  #Sup     : 1127
% 6.43/2.35  #Fact    : 0
% 6.43/2.35  #Define  : 0
% 6.43/2.35  #Split   : 4
% 6.43/2.35  #Chain   : 0
% 6.43/2.35  #Close   : 0
% 6.43/2.35  
% 6.43/2.35  Ordering : KBO
% 6.43/2.35  
% 6.43/2.35  Simplification rules
% 6.43/2.35  ----------------------
% 6.43/2.35  #Subsume      : 31
% 6.43/2.35  #Demod        : 378
% 6.43/2.35  #Tautology    : 383
% 6.43/2.35  #SimpNegUnit  : 3
% 6.43/2.35  #BackRed      : 2
% 6.43/2.35  
% 6.43/2.35  #Partial instantiations: 0
% 6.43/2.35  #Strategies tried      : 1
% 6.43/2.35  
% 6.43/2.35  Timing (in seconds)
% 6.43/2.35  ----------------------
% 6.43/2.36  Preprocessing        : 0.33
% 6.43/2.36  Parsing              : 0.18
% 6.43/2.36  CNF conversion       : 0.02
% 6.43/2.36  Main loop            : 1.19
% 6.43/2.36  Inferencing          : 0.30
% 6.43/2.36  Reduction            : 0.51
% 6.43/2.36  Demodulation         : 0.43
% 6.43/2.36  BG Simplification    : 0.04
% 6.43/2.36  Subsumption          : 0.24
% 6.43/2.36  Abstraction          : 0.04
% 6.43/2.36  MUC search           : 0.00
% 6.43/2.36  Cooper               : 0.00
% 6.43/2.36  Total                : 1.55
% 6.43/2.36  Index Insertion      : 0.00
% 6.43/2.36  Index Deletion       : 0.00
% 6.43/2.36  Index Matching       : 0.00
% 6.43/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
