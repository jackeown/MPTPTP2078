%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:17 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 122 expanded)
%              Number of leaves         :   24 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :   74 ( 263 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
           => k2_tops_1(A,k1_tops_1(A,B)) = k2_tops_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_164,plain,(
    ! [A_48,B_49] :
      ( k2_tops_1(A_48,k1_tops_1(A_48,B_49)) = k2_tops_1(A_48,B_49)
      | ~ v5_tops_1(B_49,A_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_170,plain,
    ( k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_164])).

tff(c_175,plain,(
    k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_170])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k1_tops_1(A_9,B_10),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k2_tops_1(A_11,B_12),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_179,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_14])).

tff(c_183,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_179])).

tff(c_185,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_188,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_185])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_188])).

tff(c_194,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_18,plain,(
    ! [A_16,B_18] :
      ( k4_subset_1(u1_struct_0(A_16),B_18,k2_tops_1(A_16,B_18)) = k2_pre_topc(A_16,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_249,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_194,c_18])).

tff(c_263,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_175,c_249])).

tff(c_193,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( k4_subset_1(A_6,B_7,C_8) = k2_xboole_0(B_7,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_354,plain,(
    ! [B_55] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_55,k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(B_55,k2_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_193,c_10])).

tff(c_357,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_194,c_354])).

tff(c_373,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_357])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_450,plain,(
    ! [A_59] :
      ( r1_tarski(A_59,k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ r1_tarski(A_59,k2_tops_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_8])).

tff(c_20,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_464,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_450,c_20])).

tff(c_473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_464])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:56:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.33  
% 2.59/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.34  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.59/1.34  
% 2.59/1.34  %Foreground sorts:
% 2.59/1.34  
% 2.59/1.34  
% 2.59/1.34  %Background operators:
% 2.59/1.34  
% 2.59/1.34  
% 2.59/1.34  %Foreground operators:
% 2.59/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.34  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.59/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.59/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.34  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.59/1.34  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.59/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.34  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.59/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.59/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.34  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.59/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.34  
% 2.59/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.59/1.35  tff(f_79, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tops_1)).
% 2.59/1.35  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => (k2_tops_1(A, k1_tops_1(A, B)) = k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tops_1)).
% 2.59/1.35  tff(f_47, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.59/1.35  tff(f_53, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.59/1.35  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 2.59/1.35  tff(f_41, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.59/1.35  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.59/1.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.35  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.59/1.35  tff(c_22, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.59/1.35  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.59/1.35  tff(c_164, plain, (![A_48, B_49]: (k2_tops_1(A_48, k1_tops_1(A_48, B_49))=k2_tops_1(A_48, B_49) | ~v5_tops_1(B_49, A_48) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.59/1.35  tff(c_170, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_164])).
% 2.59/1.35  tff(c_175, plain, (k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_170])).
% 2.59/1.35  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(k1_tops_1(A_9, B_10), k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.59/1.35  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(k2_tops_1(A_11, B_12), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.59/1.35  tff(c_179, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_175, c_14])).
% 2.59/1.35  tff(c_183, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_179])).
% 2.59/1.35  tff(c_185, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_183])).
% 2.59/1.35  tff(c_188, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_185])).
% 2.59/1.35  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_188])).
% 2.59/1.35  tff(c_194, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_183])).
% 2.59/1.35  tff(c_18, plain, (![A_16, B_18]: (k4_subset_1(u1_struct_0(A_16), B_18, k2_tops_1(A_16, B_18))=k2_pre_topc(A_16, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.59/1.35  tff(c_249, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_194, c_18])).
% 2.59/1.35  tff(c_263, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_175, c_249])).
% 2.59/1.35  tff(c_193, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_183])).
% 2.59/1.35  tff(c_10, plain, (![A_6, B_7, C_8]: (k4_subset_1(A_6, B_7, C_8)=k2_xboole_0(B_7, C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.59/1.35  tff(c_354, plain, (![B_55]: (k4_subset_1(u1_struct_0('#skF_1'), B_55, k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(B_55, k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_193, c_10])).
% 2.59/1.35  tff(c_357, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_194, c_354])).
% 2.59/1.35  tff(c_373, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_357])).
% 2.59/1.35  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.59/1.35  tff(c_450, plain, (![A_59]: (r1_tarski(A_59, k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~r1_tarski(A_59, k2_tops_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_373, c_8])).
% 2.59/1.35  tff(c_20, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.59/1.35  tff(c_464, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_450, c_20])).
% 2.59/1.35  tff(c_473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_464])).
% 2.59/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.35  
% 2.59/1.35  Inference rules
% 2.59/1.35  ----------------------
% 2.59/1.35  #Ref     : 0
% 2.59/1.35  #Sup     : 108
% 2.59/1.35  #Fact    : 0
% 2.59/1.35  #Define  : 0
% 2.59/1.35  #Split   : 3
% 2.59/1.35  #Chain   : 0
% 2.59/1.35  #Close   : 0
% 2.59/1.35  
% 2.59/1.35  Ordering : KBO
% 2.59/1.35  
% 2.59/1.35  Simplification rules
% 2.59/1.35  ----------------------
% 2.59/1.35  #Subsume      : 1
% 2.59/1.35  #Demod        : 57
% 2.59/1.35  #Tautology    : 43
% 2.59/1.35  #SimpNegUnit  : 0
% 2.59/1.35  #BackRed      : 0
% 2.59/1.35  
% 2.59/1.35  #Partial instantiations: 0
% 2.59/1.35  #Strategies tried      : 1
% 2.59/1.35  
% 2.59/1.35  Timing (in seconds)
% 2.59/1.35  ----------------------
% 2.59/1.35  Preprocessing        : 0.31
% 2.59/1.35  Parsing              : 0.17
% 2.59/1.35  CNF conversion       : 0.02
% 2.59/1.35  Main loop            : 0.29
% 2.59/1.35  Inferencing          : 0.10
% 2.59/1.35  Reduction            : 0.09
% 2.59/1.35  Demodulation         : 0.07
% 2.59/1.35  BG Simplification    : 0.02
% 2.59/1.35  Subsumption          : 0.06
% 2.59/1.35  Abstraction          : 0.02
% 2.59/1.35  MUC search           : 0.00
% 2.59/1.35  Cooper               : 0.00
% 2.59/1.35  Total                : 0.63
% 2.59/1.35  Index Insertion      : 0.00
% 2.59/1.35  Index Deletion       : 0.00
% 2.59/1.35  Index Matching       : 0.00
% 2.59/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
