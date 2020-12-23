%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:35 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  100 ( 149 expanded)
%              Number of equality atoms :   32 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k1_tops_1(A,k1_struct_0(A)) = k1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tops_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48,plain,(
    ! [A_28] :
      ( k1_struct_0(A_28) = k1_xboole_0
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_53,plain,(
    ! [A_29] :
      ( k1_struct_0(A_29) = k1_xboole_0
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_26,c_48])).

tff(c_57,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_32,plain,(
    k1_tops_1('#skF_1',k1_struct_0('#skF_1')) != k1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_62,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_32])).

tff(c_8,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k3_subset_1(A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_110,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = k3_subset_1(A_8,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_104])).

tff(c_113,plain,(
    ! [A_8] : k3_subset_1(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_110])).

tff(c_97,plain,(
    ! [A_38,B_39] :
      ( k3_subset_1(A_38,k3_subset_1(A_38,B_39)) = B_39
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_103,plain,(
    ! [A_8] : k3_subset_1(A_8,k3_subset_1(A_8,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_97])).

tff(c_123,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_103])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_215,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k2_pre_topc(A_59,B_60),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_232,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k2_pre_topc(A_59,B_60),u1_struct_0(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_215,c_16])).

tff(c_205,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(B_57,k2_pre_topc(A_58,B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_233,plain,(
    ! [A_61,A_62] :
      ( r1_tarski(A_61,k2_pre_topc(A_62,A_61))
      | ~ l1_pre_topc(A_62)
      | ~ r1_tarski(A_61,u1_struct_0(A_62)) ) ),
    inference(resolution,[status(thm)],[c_18,c_205])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_249,plain,(
    ! [A_65,A_66] :
      ( k2_pre_topc(A_65,A_66) = A_66
      | ~ r1_tarski(k2_pre_topc(A_65,A_66),A_66)
      | ~ l1_pre_topc(A_65)
      | ~ r1_tarski(A_66,u1_struct_0(A_65)) ) ),
    inference(resolution,[status(thm)],[c_233,c_2])).

tff(c_253,plain,(
    ! [A_59] :
      ( k2_pre_topc(A_59,u1_struct_0(A_59)) = u1_struct_0(A_59)
      | ~ r1_tarski(u1_struct_0(A_59),u1_struct_0(A_59))
      | ~ m1_subset_1(u1_struct_0(A_59),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_232,c_249])).

tff(c_304,plain,(
    ! [A_70] :
      ( k2_pre_topc(A_70,u1_struct_0(A_70)) = u1_struct_0(A_70)
      | ~ m1_subset_1(u1_struct_0(A_70),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_253])).

tff(c_307,plain,(
    ! [A_70] :
      ( k2_pre_topc(A_70,u1_struct_0(A_70)) = u1_struct_0(A_70)
      | ~ l1_pre_topc(A_70)
      | ~ r1_tarski(u1_struct_0(A_70),u1_struct_0(A_70)) ) ),
    inference(resolution,[status(thm)],[c_18,c_304])).

tff(c_311,plain,(
    ! [A_71] :
      ( k2_pre_topc(A_71,u1_struct_0(A_71)) = u1_struct_0(A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_307])).

tff(c_257,plain,(
    ! [A_67,B_68] :
      ( k3_subset_1(u1_struct_0(A_67),k2_pre_topc(A_67,k3_subset_1(u1_struct_0(A_67),B_68))) = k1_tops_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_284,plain,(
    ! [A_67] :
      ( k3_subset_1(u1_struct_0(A_67),k2_pre_topc(A_67,u1_struct_0(A_67))) = k1_tops_1(A_67,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_257])).

tff(c_288,plain,(
    ! [A_67] :
      ( k3_subset_1(u1_struct_0(A_67),k2_pre_topc(A_67,u1_struct_0(A_67))) = k1_tops_1(A_67,k1_xboole_0)
      | ~ l1_pre_topc(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_284])).

tff(c_317,plain,(
    ! [A_71] :
      ( k3_subset_1(u1_struct_0(A_71),u1_struct_0(A_71)) = k1_tops_1(A_71,k1_xboole_0)
      | ~ l1_pre_topc(A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_288])).

tff(c_341,plain,(
    ! [A_72] :
      ( k1_tops_1(A_72,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_317])).

tff(c_343,plain,
    ( k1_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_341])).

tff(c_346,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_343])).

tff(c_348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.27  
% 2.22/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.27  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 2.22/1.27  
% 2.22/1.27  %Foreground sorts:
% 2.22/1.27  
% 2.22/1.27  
% 2.22/1.27  %Background operators:
% 2.22/1.27  
% 2.22/1.27  
% 2.22/1.27  %Foreground operators:
% 2.22/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.22/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.22/1.27  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.22/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.22/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.27  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.22/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.22/1.27  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.22/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.27  
% 2.22/1.28  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k1_tops_1(A, k1_struct_0(A)) = k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tops_1)).
% 2.22/1.28  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.22/1.28  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_struct_0)).
% 2.22/1.28  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.22/1.28  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.22/1.28  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.22/1.28  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.22/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.22/1.28  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.22/1.28  tff(f_63, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.22/1.28  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.22/1.28  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.22/1.28  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.22/1.28  tff(c_26, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.22/1.28  tff(c_48, plain, (![A_28]: (k1_struct_0(A_28)=k1_xboole_0 | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.22/1.28  tff(c_53, plain, (![A_29]: (k1_struct_0(A_29)=k1_xboole_0 | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_26, c_48])).
% 2.22/1.28  tff(c_57, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_53])).
% 2.22/1.28  tff(c_32, plain, (k1_tops_1('#skF_1', k1_struct_0('#skF_1'))!=k1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.22/1.28  tff(c_62, plain, (k1_tops_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_57, c_57, c_32])).
% 2.22/1.28  tff(c_8, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.28  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.28  tff(c_104, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k3_subset_1(A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.28  tff(c_110, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=k3_subset_1(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_104])).
% 2.22/1.28  tff(c_113, plain, (![A_8]: (k3_subset_1(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_110])).
% 2.22/1.28  tff(c_97, plain, (![A_38, B_39]: (k3_subset_1(A_38, k3_subset_1(A_38, B_39))=B_39 | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.22/1.28  tff(c_103, plain, (![A_8]: (k3_subset_1(A_8, k3_subset_1(A_8, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_97])).
% 2.22/1.28  tff(c_123, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_113, c_103])).
% 2.22/1.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.28  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.28  tff(c_215, plain, (![A_59, B_60]: (m1_subset_1(k2_pre_topc(A_59, B_60), k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.28  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.28  tff(c_232, plain, (![A_59, B_60]: (r1_tarski(k2_pre_topc(A_59, B_60), u1_struct_0(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_215, c_16])).
% 2.22/1.28  tff(c_205, plain, (![B_57, A_58]: (r1_tarski(B_57, k2_pre_topc(A_58, B_57)) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.22/1.28  tff(c_233, plain, (![A_61, A_62]: (r1_tarski(A_61, k2_pre_topc(A_62, A_61)) | ~l1_pre_topc(A_62) | ~r1_tarski(A_61, u1_struct_0(A_62)))), inference(resolution, [status(thm)], [c_18, c_205])).
% 2.22/1.28  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.28  tff(c_249, plain, (![A_65, A_66]: (k2_pre_topc(A_65, A_66)=A_66 | ~r1_tarski(k2_pre_topc(A_65, A_66), A_66) | ~l1_pre_topc(A_65) | ~r1_tarski(A_66, u1_struct_0(A_65)))), inference(resolution, [status(thm)], [c_233, c_2])).
% 2.22/1.28  tff(c_253, plain, (![A_59]: (k2_pre_topc(A_59, u1_struct_0(A_59))=u1_struct_0(A_59) | ~r1_tarski(u1_struct_0(A_59), u1_struct_0(A_59)) | ~m1_subset_1(u1_struct_0(A_59), k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_232, c_249])).
% 2.22/1.28  tff(c_304, plain, (![A_70]: (k2_pre_topc(A_70, u1_struct_0(A_70))=u1_struct_0(A_70) | ~m1_subset_1(u1_struct_0(A_70), k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_253])).
% 2.22/1.28  tff(c_307, plain, (![A_70]: (k2_pre_topc(A_70, u1_struct_0(A_70))=u1_struct_0(A_70) | ~l1_pre_topc(A_70) | ~r1_tarski(u1_struct_0(A_70), u1_struct_0(A_70)))), inference(resolution, [status(thm)], [c_18, c_304])).
% 2.22/1.28  tff(c_311, plain, (![A_71]: (k2_pre_topc(A_71, u1_struct_0(A_71))=u1_struct_0(A_71) | ~l1_pre_topc(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_307])).
% 2.22/1.28  tff(c_257, plain, (![A_67, B_68]: (k3_subset_1(u1_struct_0(A_67), k2_pre_topc(A_67, k3_subset_1(u1_struct_0(A_67), B_68)))=k1_tops_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.22/1.28  tff(c_284, plain, (![A_67]: (k3_subset_1(u1_struct_0(A_67), k2_pre_topc(A_67, u1_struct_0(A_67)))=k1_tops_1(A_67, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(superposition, [status(thm), theory('equality')], [c_113, c_257])).
% 2.22/1.28  tff(c_288, plain, (![A_67]: (k3_subset_1(u1_struct_0(A_67), k2_pre_topc(A_67, u1_struct_0(A_67)))=k1_tops_1(A_67, k1_xboole_0) | ~l1_pre_topc(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_284])).
% 2.22/1.28  tff(c_317, plain, (![A_71]: (k3_subset_1(u1_struct_0(A_71), u1_struct_0(A_71))=k1_tops_1(A_71, k1_xboole_0) | ~l1_pre_topc(A_71) | ~l1_pre_topc(A_71))), inference(superposition, [status(thm), theory('equality')], [c_311, c_288])).
% 2.22/1.28  tff(c_341, plain, (![A_72]: (k1_tops_1(A_72, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_72) | ~l1_pre_topc(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_317])).
% 2.22/1.28  tff(c_343, plain, (k1_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_341])).
% 2.22/1.28  tff(c_346, plain, (k1_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_343])).
% 2.22/1.28  tff(c_348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_346])).
% 2.22/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.28  
% 2.22/1.28  Inference rules
% 2.22/1.28  ----------------------
% 2.22/1.28  #Ref     : 0
% 2.22/1.28  #Sup     : 69
% 2.22/1.28  #Fact    : 0
% 2.22/1.28  #Define  : 0
% 2.22/1.28  #Split   : 0
% 2.22/1.28  #Chain   : 0
% 2.22/1.28  #Close   : 0
% 2.22/1.28  
% 2.22/1.28  Ordering : KBO
% 2.22/1.28  
% 2.22/1.28  Simplification rules
% 2.22/1.28  ----------------------
% 2.22/1.28  #Subsume      : 2
% 2.22/1.28  #Demod        : 24
% 2.22/1.28  #Tautology    : 36
% 2.22/1.28  #SimpNegUnit  : 1
% 2.22/1.28  #BackRed      : 0
% 2.22/1.28  
% 2.22/1.28  #Partial instantiations: 0
% 2.22/1.28  #Strategies tried      : 1
% 2.22/1.28  
% 2.22/1.28  Timing (in seconds)
% 2.22/1.28  ----------------------
% 2.22/1.29  Preprocessing        : 0.31
% 2.22/1.29  Parsing              : 0.16
% 2.22/1.29  CNF conversion       : 0.02
% 2.22/1.29  Main loop            : 0.21
% 2.22/1.29  Inferencing          : 0.08
% 2.22/1.29  Reduction            : 0.06
% 2.22/1.29  Demodulation         : 0.05
% 2.22/1.29  BG Simplification    : 0.02
% 2.22/1.29  Subsumption          : 0.04
% 2.22/1.29  Abstraction          : 0.02
% 2.22/1.29  MUC search           : 0.00
% 2.22/1.29  Cooper               : 0.00
% 2.22/1.29  Total                : 0.55
% 2.22/1.29  Index Insertion      : 0.00
% 2.22/1.29  Index Deletion       : 0.00
% 2.22/1.29  Index Matching       : 0.00
% 2.22/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
