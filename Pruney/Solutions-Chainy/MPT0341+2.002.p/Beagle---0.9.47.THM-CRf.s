%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:15 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  15 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_4,plain,(
    ! [A_2] : v1_xboole_0('#skF_1'(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_2] : '#skF_1'(A_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_10])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1('#skF_1'(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6])).

tff(c_8,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.11  
% 1.57/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.12  %$ m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2
% 1.57/1.12  
% 1.57/1.12  %Foreground sorts:
% 1.57/1.12  
% 1.57/1.12  
% 1.57/1.12  %Background operators:
% 1.57/1.12  
% 1.57/1.12  
% 1.57/1.12  %Foreground operators:
% 1.57/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.57/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.57/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.57/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.57/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.57/1.12  
% 1.63/1.12  tff(f_34, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 1.63/1.12  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.63/1.12  tff(f_37, negated_conjecture, ~(![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.63/1.12  tff(c_4, plain, (![A_2]: (v1_xboole_0('#skF_1'(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.63/1.12  tff(c_10, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.12  tff(c_14, plain, (![A_2]: ('#skF_1'(A_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_10])).
% 1.63/1.12  tff(c_6, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.63/1.12  tff(c_28, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6])).
% 1.63/1.12  tff(c_8, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.12  tff(c_31, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_8])).
% 1.63/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.12  
% 1.63/1.12  Inference rules
% 1.63/1.12  ----------------------
% 1.63/1.12  #Ref     : 0
% 1.63/1.12  #Sup     : 4
% 1.63/1.12  #Fact    : 0
% 1.63/1.12  #Define  : 0
% 1.63/1.12  #Split   : 0
% 1.63/1.12  #Chain   : 0
% 1.63/1.12  #Close   : 0
% 1.63/1.12  
% 1.63/1.12  Ordering : KBO
% 1.63/1.12  
% 1.63/1.12  Simplification rules
% 1.63/1.12  ----------------------
% 1.63/1.12  #Subsume      : 0
% 1.63/1.12  #Demod        : 3
% 1.63/1.12  #Tautology    : 3
% 1.63/1.12  #SimpNegUnit  : 0
% 1.63/1.12  #BackRed      : 2
% 1.63/1.12  
% 1.63/1.12  #Partial instantiations: 0
% 1.63/1.12  #Strategies tried      : 1
% 1.63/1.12  
% 1.63/1.12  Timing (in seconds)
% 1.63/1.12  ----------------------
% 1.63/1.13  Preprocessing        : 0.25
% 1.63/1.13  Parsing              : 0.14
% 1.63/1.13  CNF conversion       : 0.01
% 1.63/1.13  Main loop            : 0.06
% 1.63/1.13  Inferencing          : 0.02
% 1.63/1.13  Reduction            : 0.02
% 1.63/1.13  Demodulation         : 0.02
% 1.63/1.13  BG Simplification    : 0.01
% 1.63/1.13  Subsumption          : 0.01
% 1.63/1.13  Abstraction          : 0.00
% 1.63/1.13  MUC search           : 0.00
% 1.63/1.13  Cooper               : 0.00
% 1.63/1.13  Total                : 0.34
% 1.63/1.13  Index Insertion      : 0.00
% 1.63/1.13  Index Deletion       : 0.00
% 1.63/1.13  Index Matching       : 0.00
% 1.63/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
