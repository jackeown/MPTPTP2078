%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:25 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  22 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k1_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_15,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_42,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = k3_subset_1(A_6,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_15,c_42])).

tff(c_47,plain,(
    ! [A_6] : k3_subset_1(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_45])).

tff(c_6,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    k3_subset_1('#skF_1',k1_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13,plain,(
    k3_subset_1('#skF_1',k1_subset_1('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_14,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_13])).

tff(c_50,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.15  
% 1.48/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.15  %$ m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1
% 1.48/1.15  
% 1.48/1.15  %Foreground sorts:
% 1.48/1.15  
% 1.48/1.15  
% 1.48/1.15  %Background operators:
% 1.48/1.15  
% 1.48/1.15  
% 1.48/1.15  %Foreground operators:
% 1.48/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.48/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.48/1.15  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.48/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.48/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.15  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.48/1.15  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.48/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.48/1.15  
% 1.60/1.16  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.60/1.16  tff(f_29, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.60/1.16  tff(f_37, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 1.60/1.16  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.60/1.16  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 1.60/1.16  tff(f_40, negated_conjecture, ~(![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 1.60/1.16  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.16  tff(c_4, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.16  tff(c_10, plain, (![A_6]: (m1_subset_1(k1_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.60/1.16  tff(c_15, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.60/1.16  tff(c_42, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.60/1.16  tff(c_45, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k3_subset_1(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_15, c_42])).
% 1.60/1.16  tff(c_47, plain, (![A_6]: (k3_subset_1(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_45])).
% 1.60/1.16  tff(c_6, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.16  tff(c_12, plain, (k3_subset_1('#skF_1', k1_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.60/1.16  tff(c_13, plain, (k3_subset_1('#skF_1', k1_subset_1('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 1.60/1.16  tff(c_14, plain, (k3_subset_1('#skF_1', k1_xboole_0)!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_13])).
% 1.60/1.16  tff(c_50, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_14])).
% 1.60/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.16  
% 1.60/1.16  Inference rules
% 1.60/1.16  ----------------------
% 1.60/1.16  #Ref     : 0
% 1.60/1.16  #Sup     : 7
% 1.60/1.16  #Fact    : 0
% 1.60/1.16  #Define  : 0
% 1.60/1.16  #Split   : 0
% 1.60/1.16  #Chain   : 0
% 1.60/1.16  #Close   : 0
% 1.60/1.16  
% 1.60/1.16  Ordering : KBO
% 1.60/1.16  
% 1.60/1.16  Simplification rules
% 1.60/1.16  ----------------------
% 1.60/1.16  #Subsume      : 0
% 1.60/1.16  #Demod        : 5
% 1.60/1.16  #Tautology    : 6
% 1.60/1.16  #SimpNegUnit  : 0
% 1.60/1.16  #BackRed      : 1
% 1.60/1.16  
% 1.60/1.16  #Partial instantiations: 0
% 1.60/1.16  #Strategies tried      : 1
% 1.60/1.16  
% 1.60/1.16  Timing (in seconds)
% 1.60/1.16  ----------------------
% 1.60/1.16  Preprocessing        : 0.25
% 1.60/1.16  Parsing              : 0.13
% 1.60/1.16  CNF conversion       : 0.01
% 1.60/1.16  Main loop            : 0.06
% 1.60/1.16  Inferencing          : 0.02
% 1.60/1.16  Reduction            : 0.02
% 1.60/1.16  Demodulation         : 0.02
% 1.60/1.16  BG Simplification    : 0.01
% 1.60/1.17  Subsumption          : 0.01
% 1.60/1.17  Abstraction          : 0.01
% 1.60/1.17  MUC search           : 0.00
% 1.60/1.17  Cooper               : 0.00
% 1.60/1.17  Total                : 0.33
% 1.60/1.17  Index Insertion      : 0.00
% 1.60/1.17  Index Deletion       : 0.00
% 1.60/1.17  Index Matching       : 0.00
% 1.60/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
