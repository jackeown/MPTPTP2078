%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:25 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   36 (  36 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(c_6,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_52])).

tff(c_64,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_61])).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k3_subset_1(A_18,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = k3_subset_1(A_9,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_74])).

tff(c_79,plain,(
    ! [A_9] : k3_subset_1(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_77])).

tff(c_8,plain,(
    ! [A_5] : k1_subset_1(A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    k3_subset_1('#skF_1',k1_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17,plain,(
    k3_subset_1('#skF_1',k1_subset_1('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16])).

tff(c_18,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_17])).

tff(c_82,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.12  %$ m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1
% 1.64/1.12  
% 1.64/1.12  %Foreground sorts:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Background operators:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Foreground operators:
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.64/1.12  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.64/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.12  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.64/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.64/1.12  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.64/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.12  
% 1.64/1.12  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.64/1.12  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.64/1.12  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.64/1.12  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.64/1.12  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.64/1.12  tff(f_33, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.64/1.12  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 1.64/1.12  tff(f_44, negated_conjecture, ~(![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 1.64/1.12  tff(c_6, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.12  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.12  tff(c_52, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.12  tff(c_61, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_52])).
% 1.64/1.12  tff(c_64, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_61])).
% 1.64/1.12  tff(c_14, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.64/1.12  tff(c_74, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k3_subset_1(A_18, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.12  tff(c_77, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=k3_subset_1(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_74])).
% 1.64/1.12  tff(c_79, plain, (![A_9]: (k3_subset_1(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_77])).
% 1.64/1.12  tff(c_8, plain, (![A_5]: (k1_subset_1(A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.12  tff(c_10, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.64/1.12  tff(c_16, plain, (k3_subset_1('#skF_1', k1_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.12  tff(c_17, plain, (k3_subset_1('#skF_1', k1_subset_1('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16])).
% 1.64/1.12  tff(c_18, plain, (k3_subset_1('#skF_1', k1_xboole_0)!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_17])).
% 1.64/1.12  tff(c_82, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_18])).
% 1.64/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  Inference rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Ref     : 0
% 1.64/1.12  #Sup     : 14
% 1.64/1.12  #Fact    : 0
% 1.64/1.12  #Define  : 0
% 1.64/1.12  #Split   : 0
% 1.64/1.12  #Chain   : 0
% 1.64/1.12  #Close   : 0
% 1.64/1.12  
% 1.64/1.12  Ordering : KBO
% 1.64/1.12  
% 1.64/1.12  Simplification rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Subsume      : 0
% 1.64/1.12  #Demod        : 5
% 1.64/1.12  #Tautology    : 12
% 1.64/1.12  #SimpNegUnit  : 0
% 1.64/1.12  #BackRed      : 1
% 1.64/1.12  
% 1.64/1.12  #Partial instantiations: 0
% 1.64/1.12  #Strategies tried      : 1
% 1.64/1.12  
% 1.64/1.12  Timing (in seconds)
% 1.64/1.12  ----------------------
% 1.64/1.13  Preprocessing        : 0.28
% 1.64/1.13  Parsing              : 0.15
% 1.64/1.13  CNF conversion       : 0.01
% 1.64/1.13  Main loop            : 0.08
% 1.64/1.13  Inferencing          : 0.03
% 1.64/1.13  Reduction            : 0.03
% 1.64/1.13  Demodulation         : 0.02
% 1.64/1.13  BG Simplification    : 0.01
% 1.64/1.13  Subsumption          : 0.01
% 1.64/1.13  Abstraction          : 0.01
% 1.64/1.13  MUC search           : 0.00
% 1.64/1.13  Cooper               : 0.00
% 1.64/1.13  Total                : 0.37
% 1.64/1.13  Index Insertion      : 0.00
% 1.64/1.13  Index Deletion       : 0.00
% 1.64/1.13  Index Matching       : 0.00
% 1.64/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
