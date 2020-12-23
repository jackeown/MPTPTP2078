%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:14 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 130 expanded)
%              Number of leaves         :   27 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :   74 ( 264 expanded)
%              Number of equality atoms :   20 (  37 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
           => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_18,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_242,plain,(
    ! [A_45,B_46] :
      ( k2_tops_1(A_45,k1_tops_1(A_45,B_46)) = k2_tops_1(A_45,B_46)
      | ~ v5_tops_1(B_46,A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_248,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_242])).

tff(c_253,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_248])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k1_tops_1(A_10,B_11),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k2_tops_1(A_12,B_13),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_257,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_12])).

tff(c_261,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_257])).

tff(c_263,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_266,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_263])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_266])).

tff(c_272,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_16,plain,(
    ! [A_17,B_19] :
      ( k4_subset_1(u1_struct_0(A_17),B_19,k2_tops_1(A_17,B_19)) = k2_pre_topc(A_17,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_312,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_272,c_16])).

tff(c_326,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_253,c_312])).

tff(c_271,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( k4_subset_1(A_7,B_8,C_9) = k2_xboole_0(B_8,C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_380,plain,(
    ! [B_49] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_49,k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(B_49,k2_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_271,c_8])).

tff(c_383,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_272,c_380])).

tff(c_399,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_383])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [A_25,B_26] : k3_tarski(k2_tarski(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [B_27,A_28] : k3_tarski(k2_tarski(B_27,A_28)) = k2_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_tarski(k2_tarski(A_5,B_6)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [A_30,B_29] : r1_tarski(A_30,k2_xboole_0(B_29,A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_2])).

tff(c_441,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_112])).

tff(c_448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:35:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.41  
% 2.48/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.41  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.48/1.41  
% 2.48/1.41  %Foreground sorts:
% 2.48/1.41  
% 2.48/1.41  
% 2.48/1.41  %Background operators:
% 2.48/1.41  
% 2.48/1.41  
% 2.48/1.41  %Foreground operators:
% 2.48/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.41  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.48/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.48/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.41  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.48/1.41  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.48/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.41  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.48/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.48/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.48/1.41  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.48/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.41  
% 2.48/1.42  tff(f_75, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 2.48/1.42  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tops_1)).
% 2.48/1.42  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.48/1.42  tff(f_49, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.48/1.42  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 2.48/1.42  tff(f_37, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.48/1.42  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.48/1.42  tff(f_31, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.48/1.42  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.48/1.42  tff(c_18, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.48/1.42  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.48/1.42  tff(c_20, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.48/1.42  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.48/1.42  tff(c_242, plain, (![A_45, B_46]: (k2_tops_1(A_45, k1_tops_1(A_45, B_46))=k2_tops_1(A_45, B_46) | ~v5_tops_1(B_46, A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.48/1.42  tff(c_248, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_242])).
% 2.48/1.42  tff(c_253, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_248])).
% 2.48/1.42  tff(c_10, plain, (![A_10, B_11]: (m1_subset_1(k1_tops_1(A_10, B_11), k1_zfmisc_1(u1_struct_0(A_10))) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.48/1.42  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(k2_tops_1(A_12, B_13), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.48/1.42  tff(c_257, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_253, c_12])).
% 2.48/1.42  tff(c_261, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_257])).
% 2.48/1.42  tff(c_263, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_261])).
% 2.48/1.42  tff(c_266, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_263])).
% 2.48/1.42  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_266])).
% 2.48/1.42  tff(c_272, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_261])).
% 2.48/1.42  tff(c_16, plain, (![A_17, B_19]: (k4_subset_1(u1_struct_0(A_17), B_19, k2_tops_1(A_17, B_19))=k2_pre_topc(A_17, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.48/1.42  tff(c_312, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_272, c_16])).
% 2.48/1.42  tff(c_326, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_253, c_312])).
% 2.48/1.42  tff(c_271, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_261])).
% 2.48/1.42  tff(c_8, plain, (![A_7, B_8, C_9]: (k4_subset_1(A_7, B_8, C_9)=k2_xboole_0(B_8, C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.48/1.42  tff(c_380, plain, (![B_49]: (k4_subset_1(u1_struct_0('#skF_1'), B_49, k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(B_49, k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_271, c_8])).
% 2.48/1.42  tff(c_383, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_272, c_380])).
% 2.48/1.42  tff(c_399, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_383])).
% 2.48/1.42  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.48/1.42  tff(c_59, plain, (![A_25, B_26]: (k3_tarski(k2_tarski(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.42  tff(c_74, plain, (![B_27, A_28]: (k3_tarski(k2_tarski(B_27, A_28))=k2_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 2.48/1.42  tff(c_6, plain, (![A_5, B_6]: (k3_tarski(k2_tarski(A_5, B_6))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.42  tff(c_97, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_74, c_6])).
% 2.48/1.42  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.42  tff(c_112, plain, (![A_30, B_29]: (r1_tarski(A_30, k2_xboole_0(B_29, A_30)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_2])).
% 2.48/1.42  tff(c_441, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_399, c_112])).
% 2.48/1.42  tff(c_448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_441])).
% 2.48/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.42  
% 2.48/1.42  Inference rules
% 2.48/1.42  ----------------------
% 2.48/1.42  #Ref     : 0
% 2.48/1.42  #Sup     : 106
% 2.48/1.42  #Fact    : 0
% 2.48/1.42  #Define  : 0
% 2.48/1.42  #Split   : 2
% 2.48/1.42  #Chain   : 0
% 2.48/1.42  #Close   : 0
% 2.48/1.42  
% 2.48/1.42  Ordering : KBO
% 2.48/1.42  
% 2.48/1.42  Simplification rules
% 2.48/1.42  ----------------------
% 2.48/1.42  #Subsume      : 3
% 2.48/1.42  #Demod        : 55
% 2.48/1.42  #Tautology    : 61
% 2.48/1.42  #SimpNegUnit  : 1
% 2.48/1.42  #BackRed      : 1
% 2.48/1.42  
% 2.48/1.42  #Partial instantiations: 0
% 2.48/1.42  #Strategies tried      : 1
% 2.48/1.42  
% 2.48/1.42  Timing (in seconds)
% 2.48/1.42  ----------------------
% 2.48/1.43  Preprocessing        : 0.32
% 2.48/1.43  Parsing              : 0.18
% 2.48/1.43  CNF conversion       : 0.02
% 2.48/1.43  Main loop            : 0.25
% 2.48/1.43  Inferencing          : 0.09
% 2.48/1.43  Reduction            : 0.09
% 2.48/1.43  Demodulation         : 0.07
% 2.48/1.43  BG Simplification    : 0.01
% 2.48/1.43  Subsumption          : 0.05
% 2.48/1.43  Abstraction          : 0.02
% 2.48/1.43  MUC search           : 0.00
% 2.48/1.43  Cooper               : 0.00
% 2.48/1.43  Total                : 0.60
% 2.48/1.43  Index Insertion      : 0.00
% 2.48/1.43  Index Deletion       : 0.00
% 2.48/1.43  Index Matching       : 0.00
% 2.48/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
