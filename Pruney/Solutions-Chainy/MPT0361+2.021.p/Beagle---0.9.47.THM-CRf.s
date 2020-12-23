%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:30 EST 2020

% Result     : Theorem 5.77s
% Output     : CNFRefutation 5.77s
% Verified   : 
% Statistics : Number of formulae       :   48 (  71 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   57 ( 100 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_22,plain,(
    ! [B_22,A_23] : k2_xboole_0(B_22,A_23) = k2_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    ! [A_23,B_22] : r1_tarski(A_23,k2_xboole_0(B_22,A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k3_subset_1(A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_100,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_92])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_494,plain,(
    ! [A_59,B_60,C_61] :
      ( k4_subset_1(A_59,B_60,C_61) = k2_xboole_0(B_60,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_504,plain,(
    ! [B_62] :
      ( k4_subset_1('#skF_1',B_62,'#skF_3') = k2_xboole_0(B_62,'#skF_3')
      | ~ m1_subset_1(B_62,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_494])).

tff(c_514,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_504])).

tff(c_519,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_514])).

tff(c_12,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k4_subset_1(A_13,B_14,C_15),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_563,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_12])).

tff(c_567,plain,(
    m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_563])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_585,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k3_subset_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_567,c_10])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k4_xboole_0(k4_xboole_0(A_3,B_4),C_5) = k4_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [A_29,B_30,C_31] :
      ( r1_tarski(k4_xboole_0(A_29,B_30),C_31)
      | ~ r1_tarski(A_29,k2_xboole_0(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_230,plain,(
    ! [A_47,B_48,C_49,C_50] :
      ( r1_tarski(k4_xboole_0(A_47,k2_xboole_0(B_48,C_49)),C_50)
      | ~ r1_tarski(k4_xboole_0(A_47,B_48),k2_xboole_0(C_49,C_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_88])).

tff(c_974,plain,(
    ! [A_73,B_74,A_75,C_76] :
      ( r1_tarski(k4_xboole_0(A_73,k2_xboole_0(B_74,A_75)),C_76)
      | ~ r1_tarski(k4_xboole_0(A_73,A_75),k2_xboole_0(B_74,C_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_230])).

tff(c_980,plain,(
    ! [C_76] :
      ( r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')),C_76)
      | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_3',C_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_974])).

tff(c_3093,plain,(
    ! [C_129] :
      ( r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')),C_129)
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k2_xboole_0('#skF_3',C_129)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_980])).

tff(c_16,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k4_subset_1('#skF_1','#skF_2','#skF_3')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_559,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')),k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_16])).

tff(c_3096,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_3093,c_559])).

tff(c_3100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_3096])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:41:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.77/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.77/2.14  
% 5.77/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.77/2.14  %$ r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.77/2.14  
% 5.77/2.14  %Foreground sorts:
% 5.77/2.14  
% 5.77/2.14  
% 5.77/2.14  %Background operators:
% 5.77/2.14  
% 5.77/2.14  
% 5.77/2.14  %Foreground operators:
% 5.77/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.77/2.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.77/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.77/2.14  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.77/2.14  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.77/2.14  tff('#skF_2', type, '#skF_2': $i).
% 5.77/2.14  tff('#skF_3', type, '#skF_3': $i).
% 5.77/2.14  tff('#skF_1', type, '#skF_1': $i).
% 5.77/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.77/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.77/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.77/2.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.77/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.77/2.14  
% 5.77/2.15  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.77/2.15  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.77/2.15  tff(f_59, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 5.77/2.15  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.77/2.15  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.77/2.15  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 5.77/2.15  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.77/2.15  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.77/2.15  tff(c_22, plain, (![B_22, A_23]: (k2_xboole_0(B_22, A_23)=k2_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.77/2.15  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.77/2.15  tff(c_37, plain, (![A_23, B_22]: (r1_tarski(A_23, k2_xboole_0(B_22, A_23)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8])).
% 5.77/2.15  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.77/2.15  tff(c_92, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k3_subset_1(A_32, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.77/2.15  tff(c_100, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_92])).
% 5.77/2.15  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.77/2.15  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.77/2.15  tff(c_494, plain, (![A_59, B_60, C_61]: (k4_subset_1(A_59, B_60, C_61)=k2_xboole_0(B_60, C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.77/2.15  tff(c_504, plain, (![B_62]: (k4_subset_1('#skF_1', B_62, '#skF_3')=k2_xboole_0(B_62, '#skF_3') | ~m1_subset_1(B_62, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_494])).
% 5.77/2.15  tff(c_514, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_504])).
% 5.77/2.15  tff(c_519, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_3')=k2_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_514])).
% 5.77/2.15  tff(c_12, plain, (![A_13, B_14, C_15]: (m1_subset_1(k4_subset_1(A_13, B_14, C_15), k1_zfmisc_1(A_13)) | ~m1_subset_1(C_15, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.77/2.15  tff(c_563, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_519, c_12])).
% 5.77/2.15  tff(c_567, plain, (m1_subset_1(k2_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_563])).
% 5.77/2.15  tff(c_10, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.77/2.15  tff(c_585, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k3_subset_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_567, c_10])).
% 5.77/2.15  tff(c_4, plain, (![A_3, B_4, C_5]: (k4_xboole_0(k4_xboole_0(A_3, B_4), C_5)=k4_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.77/2.15  tff(c_88, plain, (![A_29, B_30, C_31]: (r1_tarski(k4_xboole_0(A_29, B_30), C_31) | ~r1_tarski(A_29, k2_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.77/2.15  tff(c_230, plain, (![A_47, B_48, C_49, C_50]: (r1_tarski(k4_xboole_0(A_47, k2_xboole_0(B_48, C_49)), C_50) | ~r1_tarski(k4_xboole_0(A_47, B_48), k2_xboole_0(C_49, C_50)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_88])).
% 5.77/2.15  tff(c_974, plain, (![A_73, B_74, A_75, C_76]: (r1_tarski(k4_xboole_0(A_73, k2_xboole_0(B_74, A_75)), C_76) | ~r1_tarski(k4_xboole_0(A_73, A_75), k2_xboole_0(B_74, C_76)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_230])).
% 5.77/2.15  tff(c_980, plain, (![C_76]: (r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')), C_76) | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_3', C_76)))), inference(superposition, [status(thm), theory('equality')], [c_585, c_974])).
% 5.77/2.15  tff(c_3093, plain, (![C_129]: (r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')), C_129) | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k2_xboole_0('#skF_3', C_129)))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_980])).
% 5.77/2.15  tff(c_16, plain, (~r1_tarski(k3_subset_1('#skF_1', k4_subset_1('#skF_1', '#skF_2', '#skF_3')), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.77/2.15  tff(c_559, plain, (~r1_tarski(k3_subset_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')), k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_16])).
% 5.77/2.15  tff(c_3096, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_3093, c_559])).
% 5.77/2.15  tff(c_3100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37, c_3096])).
% 5.77/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.77/2.15  
% 5.77/2.15  Inference rules
% 5.77/2.15  ----------------------
% 5.77/2.15  #Ref     : 0
% 5.77/2.15  #Sup     : 804
% 5.77/2.15  #Fact    : 0
% 5.77/2.15  #Define  : 0
% 5.77/2.15  #Split   : 0
% 5.77/2.15  #Chain   : 0
% 5.77/2.15  #Close   : 0
% 5.77/2.15  
% 5.77/2.15  Ordering : KBO
% 5.77/2.15  
% 5.77/2.15  Simplification rules
% 5.77/2.15  ----------------------
% 5.77/2.15  #Subsume      : 99
% 5.77/2.15  #Demod        : 310
% 5.77/2.15  #Tautology    : 143
% 5.77/2.15  #SimpNegUnit  : 0
% 5.77/2.15  #BackRed      : 2
% 5.77/2.15  
% 5.77/2.15  #Partial instantiations: 0
% 5.77/2.15  #Strategies tried      : 1
% 5.77/2.15  
% 5.77/2.15  Timing (in seconds)
% 5.77/2.15  ----------------------
% 5.77/2.15  Preprocessing        : 0.29
% 5.77/2.15  Parsing              : 0.16
% 5.77/2.15  CNF conversion       : 0.02
% 5.77/2.15  Main loop            : 1.10
% 5.77/2.15  Inferencing          : 0.30
% 5.77/2.16  Reduction            : 0.56
% 5.77/2.16  Demodulation         : 0.50
% 5.77/2.16  BG Simplification    : 0.04
% 5.77/2.16  Subsumption          : 0.15
% 5.77/2.16  Abstraction          : 0.06
% 5.77/2.16  MUC search           : 0.00
% 5.77/2.16  Cooper               : 0.00
% 5.77/2.16  Total                : 1.42
% 5.77/2.16  Index Insertion      : 0.00
% 5.77/2.16  Index Deletion       : 0.00
% 5.77/2.16  Index Matching       : 0.00
% 5.77/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
