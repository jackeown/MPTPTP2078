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
% DateTime   : Thu Dec  3 10:22:16 EST 2020

% Result     : Theorem 8.20s
% Output     : CNFRefutation 8.25s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 124 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :   88 ( 271 expanded)
%              Number of equality atoms :   19 (  31 expanded)
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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
           => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_26,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_838,plain,(
    ! [A_165,B_166] :
      ( k2_tops_1(A_165,k1_tops_1(A_165,B_166)) = k2_tops_1(A_165,B_166)
      | ~ v5_tops_1(B_166,A_165)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_844,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_838])).

tff(c_849,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_844])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k1_tops_1(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_682,plain,(
    ! [A_143,B_144] :
      ( k4_subset_1(u1_struct_0(A_143),B_144,k2_tops_1(A_143,B_144)) = k2_pre_topc(A_143,B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1068,plain,(
    ! [A_169,B_170] :
      ( k4_subset_1(u1_struct_0(A_169),k1_tops_1(A_169,B_170),k2_tops_1(A_169,k1_tops_1(A_169,B_170))) = k2_pre_topc(A_169,k1_tops_1(A_169,B_170))
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(resolution,[status(thm)],[c_18,c_682])).

tff(c_1077,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_1068])).

tff(c_1081,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1077])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k2_tops_1(A_18,B_19),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_853,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_20])).

tff(c_857,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_853])).

tff(c_859,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_857])).

tff(c_862,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_859])).

tff(c_866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_862])).

tff(c_867,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_857])).

tff(c_868,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_857])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] :
      ( k4_subset_1(A_13,B_14,C_15) = k2_xboole_0(B_14,C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8336,plain,(
    ! [B_498] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_498,k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0(B_498,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_498,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_868,c_16])).

tff(c_8355,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_867,c_8336])).

tff(c_502,plain,(
    ! [A_118,C_119,B_120] :
      ( k4_subset_1(A_118,C_119,B_120) = k4_subset_1(A_118,B_120,C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(A_118))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2649,plain,(
    ! [A_244,B_245,B_246] :
      ( k4_subset_1(u1_struct_0(A_244),k1_tops_1(A_244,B_245),B_246) = k4_subset_1(u1_struct_0(A_244),B_246,k1_tops_1(A_244,B_245))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ l1_pre_topc(A_244) ) ),
    inference(resolution,[status(thm)],[c_18,c_502])).

tff(c_2667,plain,(
    ! [A_18,B_19,B_245] :
      ( k4_subset_1(u1_struct_0(A_18),k2_tops_1(A_18,B_19),k1_tops_1(A_18,B_245)) = k4_subset_1(u1_struct_0(A_18),k1_tops_1(A_18,B_245),k2_tops_1(A_18,B_19))
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_20,c_2649])).

tff(c_8383,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8355,c_2667])).

tff(c_8396,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_30,c_1081,c_8383])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8547,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8396,c_10])).

tff(c_8571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_8547])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:27:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.20/3.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.20/3.01  
% 8.20/3.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.20/3.02  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 8.20/3.02  
% 8.20/3.02  %Foreground sorts:
% 8.20/3.02  
% 8.20/3.02  
% 8.20/3.02  %Background operators:
% 8.20/3.02  
% 8.20/3.02  
% 8.20/3.02  %Foreground operators:
% 8.20/3.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.20/3.02  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.20/3.02  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.20/3.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.20/3.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.20/3.02  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.20/3.02  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.20/3.02  tff('#skF_2', type, '#skF_2': $i).
% 8.20/3.02  tff('#skF_1', type, '#skF_1': $i).
% 8.20/3.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.20/3.02  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 8.20/3.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.20/3.02  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.20/3.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.20/3.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.20/3.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.20/3.02  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.20/3.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.20/3.02  
% 8.25/3.03  tff(f_91, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 8.25/3.03  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tops_1)).
% 8.25/3.03  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 8.25/3.03  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 8.25/3.03  tff(f_65, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 8.25/3.03  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.25/3.03  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 8.25/3.03  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.25/3.03  tff(c_26, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.25/3.03  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.25/3.03  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.25/3.03  tff(c_28, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.25/3.03  tff(c_838, plain, (![A_165, B_166]: (k2_tops_1(A_165, k1_tops_1(A_165, B_166))=k2_tops_1(A_165, B_166) | ~v5_tops_1(B_166, A_165) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.25/3.03  tff(c_844, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_838])).
% 8.25/3.03  tff(c_849, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_844])).
% 8.25/3.03  tff(c_18, plain, (![A_16, B_17]: (m1_subset_1(k1_tops_1(A_16, B_17), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.25/3.03  tff(c_682, plain, (![A_143, B_144]: (k4_subset_1(u1_struct_0(A_143), B_144, k2_tops_1(A_143, B_144))=k2_pre_topc(A_143, B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.25/3.03  tff(c_1068, plain, (![A_169, B_170]: (k4_subset_1(u1_struct_0(A_169), k1_tops_1(A_169, B_170), k2_tops_1(A_169, k1_tops_1(A_169, B_170)))=k2_pre_topc(A_169, k1_tops_1(A_169, B_170)) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169))), inference(resolution, [status(thm)], [c_18, c_682])).
% 8.25/3.03  tff(c_1077, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_849, c_1068])).
% 8.25/3.03  tff(c_1081, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1077])).
% 8.25/3.03  tff(c_20, plain, (![A_18, B_19]: (m1_subset_1(k2_tops_1(A_18, B_19), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.25/3.03  tff(c_853, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_849, c_20])).
% 8.25/3.03  tff(c_857, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_853])).
% 8.25/3.03  tff(c_859, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_857])).
% 8.25/3.03  tff(c_862, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_859])).
% 8.25/3.03  tff(c_866, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_862])).
% 8.25/3.03  tff(c_867, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_857])).
% 8.25/3.03  tff(c_868, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_857])).
% 8.25/3.03  tff(c_16, plain, (![A_13, B_14, C_15]: (k4_subset_1(A_13, B_14, C_15)=k2_xboole_0(B_14, C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.25/3.03  tff(c_8336, plain, (![B_498]: (k4_subset_1(u1_struct_0('#skF_1'), B_498, k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(B_498, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_498, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_868, c_16])).
% 8.25/3.03  tff(c_8355, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_867, c_8336])).
% 8.25/3.03  tff(c_502, plain, (![A_118, C_119, B_120]: (k4_subset_1(A_118, C_119, B_120)=k4_subset_1(A_118, B_120, C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(A_118)) | ~m1_subset_1(B_120, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.25/3.03  tff(c_2649, plain, (![A_244, B_245, B_246]: (k4_subset_1(u1_struct_0(A_244), k1_tops_1(A_244, B_245), B_246)=k4_subset_1(u1_struct_0(A_244), B_246, k1_tops_1(A_244, B_245)) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_244))) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_244))) | ~l1_pre_topc(A_244))), inference(resolution, [status(thm)], [c_18, c_502])).
% 8.25/3.03  tff(c_2667, plain, (![A_18, B_19, B_245]: (k4_subset_1(u1_struct_0(A_18), k2_tops_1(A_18, B_19), k1_tops_1(A_18, B_245))=k4_subset_1(u1_struct_0(A_18), k1_tops_1(A_18, B_245), k2_tops_1(A_18, B_19)) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(resolution, [status(thm)], [c_20, c_2649])).
% 8.25/3.03  tff(c_8383, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8355, c_2667])).
% 8.25/3.03  tff(c_8396, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_30, c_1081, c_8383])).
% 8.25/3.03  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.25/3.03  tff(c_8547, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_8396, c_10])).
% 8.25/3.03  tff(c_8571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_8547])).
% 8.25/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.25/3.03  
% 8.25/3.03  Inference rules
% 8.25/3.03  ----------------------
% 8.25/3.03  #Ref     : 0
% 8.25/3.03  #Sup     : 2283
% 8.25/3.03  #Fact    : 0
% 8.25/3.03  #Define  : 0
% 8.25/3.03  #Split   : 8
% 8.25/3.03  #Chain   : 0
% 8.25/3.03  #Close   : 0
% 8.25/3.03  
% 8.25/3.03  Ordering : KBO
% 8.25/3.03  
% 8.25/3.03  Simplification rules
% 8.25/3.03  ----------------------
% 8.25/3.03  #Subsume      : 397
% 8.25/3.03  #Demod        : 576
% 8.25/3.03  #Tautology    : 428
% 8.25/3.03  #SimpNegUnit  : 18
% 8.25/3.03  #BackRed      : 4
% 8.25/3.03  
% 8.25/3.03  #Partial instantiations: 0
% 8.25/3.03  #Strategies tried      : 1
% 8.25/3.03  
% 8.25/3.03  Timing (in seconds)
% 8.25/3.03  ----------------------
% 8.25/3.04  Preprocessing        : 0.31
% 8.25/3.04  Parsing              : 0.16
% 8.25/3.04  CNF conversion       : 0.02
% 8.25/3.04  Main loop            : 1.97
% 8.25/3.04  Inferencing          : 0.46
% 8.25/3.04  Reduction            : 0.67
% 8.25/3.04  Demodulation         : 0.51
% 8.25/3.04  BG Simplification    : 0.06
% 8.25/3.04  Subsumption          : 0.64
% 8.25/3.04  Abstraction          : 0.09
% 8.25/3.04  MUC search           : 0.00
% 8.25/3.04  Cooper               : 0.00
% 8.25/3.04  Total                : 2.30
% 8.25/3.04  Index Insertion      : 0.00
% 8.25/3.04  Index Deletion       : 0.00
% 8.25/3.04  Index Matching       : 0.00
% 8.25/3.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
