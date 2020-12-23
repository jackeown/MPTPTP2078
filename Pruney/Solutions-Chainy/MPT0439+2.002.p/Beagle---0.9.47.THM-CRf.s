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
% DateTime   : Thu Dec  3 09:58:18 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   42 (  43 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,k2_zfmisc_1(k1_relat_1(A_48),k2_relat_1(A_48)))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2269,plain,(
    ! [A_117] :
      ( k2_xboole_0(A_117,k2_zfmisc_1(k1_relat_1(A_117),k2_relat_1(A_117))) = k2_zfmisc_1(k1_relat_1(A_117),k2_relat_1(A_117))
      | ~ v1_relat_1(A_117) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_145,plain,(
    ! [A_56,B_57,C_58] : k5_xboole_0(k5_xboole_0(A_56,B_57),C_58) = k5_xboole_0(A_56,k5_xboole_0(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8,B_9] : k5_xboole_0(k5_xboole_0(A_8,B_9),k2_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_162,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k5_xboole_0(B_57,k2_xboole_0(A_56,B_57))) = k3_xboole_0(A_56,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_10])).

tff(c_2286,plain,(
    ! [A_117] :
      ( k5_xboole_0(A_117,k5_xboole_0(k2_zfmisc_1(k1_relat_1(A_117),k2_relat_1(A_117)),k2_zfmisc_1(k1_relat_1(A_117),k2_relat_1(A_117)))) = k3_xboole_0(A_117,k2_zfmisc_1(k1_relat_1(A_117),k2_relat_1(A_117)))
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2269,c_162])).

tff(c_2735,plain,(
    ! [A_123] :
      ( k3_xboole_0(A_123,k2_zfmisc_1(k1_relat_1(A_123),k2_relat_1(A_123))) = A_123
      | ~ v1_relat_1(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8,c_2286])).

tff(c_28,plain,(
    k3_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2760,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2735,c_28])).

tff(c_2772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2760])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.83/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.68  
% 3.83/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.68  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.83/1.68  
% 3.83/1.68  %Foreground sorts:
% 3.83/1.68  
% 3.83/1.68  
% 3.83/1.68  %Background operators:
% 3.83/1.68  
% 3.83/1.68  
% 3.83/1.68  %Foreground operators:
% 3.83/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.83/1.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.83/1.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.83/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.83/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.83/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.83/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.83/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.83/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.83/1.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.68  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.83/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.83/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.83/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.83/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.83/1.68  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.83/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.83/1.68  
% 3.83/1.69  tff(f_60, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.83/1.69  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.83/1.69  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.83/1.69  tff(f_55, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.83/1.69  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.83/1.69  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.83/1.69  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.83/1.69  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.83/1.69  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.83/1.69  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.83/1.69  tff(c_76, plain, (![A_48]: (r1_tarski(A_48, k2_zfmisc_1(k1_relat_1(A_48), k2_relat_1(A_48))) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.83/1.69  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.83/1.69  tff(c_2269, plain, (![A_117]: (k2_xboole_0(A_117, k2_zfmisc_1(k1_relat_1(A_117), k2_relat_1(A_117)))=k2_zfmisc_1(k1_relat_1(A_117), k2_relat_1(A_117)) | ~v1_relat_1(A_117))), inference(resolution, [status(thm)], [c_76, c_2])).
% 3.83/1.69  tff(c_145, plain, (![A_56, B_57, C_58]: (k5_xboole_0(k5_xboole_0(A_56, B_57), C_58)=k5_xboole_0(A_56, k5_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.83/1.69  tff(c_10, plain, (![A_8, B_9]: (k5_xboole_0(k5_xboole_0(A_8, B_9), k2_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.83/1.69  tff(c_162, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k5_xboole_0(B_57, k2_xboole_0(A_56, B_57)))=k3_xboole_0(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_145, c_10])).
% 3.83/1.69  tff(c_2286, plain, (![A_117]: (k5_xboole_0(A_117, k5_xboole_0(k2_zfmisc_1(k1_relat_1(A_117), k2_relat_1(A_117)), k2_zfmisc_1(k1_relat_1(A_117), k2_relat_1(A_117))))=k3_xboole_0(A_117, k2_zfmisc_1(k1_relat_1(A_117), k2_relat_1(A_117))) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_2269, c_162])).
% 3.83/1.69  tff(c_2735, plain, (![A_123]: (k3_xboole_0(A_123, k2_zfmisc_1(k1_relat_1(A_123), k2_relat_1(A_123)))=A_123 | ~v1_relat_1(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8, c_2286])).
% 3.83/1.69  tff(c_28, plain, (k3_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.83/1.69  tff(c_2760, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2735, c_28])).
% 3.83/1.69  tff(c_2772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2760])).
% 3.83/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.69  
% 3.83/1.69  Inference rules
% 3.83/1.69  ----------------------
% 3.83/1.69  #Ref     : 0
% 3.83/1.69  #Sup     : 690
% 3.83/1.69  #Fact    : 0
% 3.83/1.69  #Define  : 0
% 3.83/1.69  #Split   : 0
% 3.83/1.69  #Chain   : 0
% 3.83/1.69  #Close   : 0
% 3.83/1.69  
% 3.83/1.69  Ordering : KBO
% 3.83/1.69  
% 3.83/1.69  Simplification rules
% 3.83/1.69  ----------------------
% 3.83/1.69  #Subsume      : 9
% 3.83/1.69  #Demod        : 576
% 3.83/1.69  #Tautology    : 359
% 3.83/1.69  #SimpNegUnit  : 0
% 3.83/1.69  #BackRed      : 4
% 3.83/1.69  
% 3.83/1.69  #Partial instantiations: 0
% 3.83/1.69  #Strategies tried      : 1
% 3.83/1.69  
% 3.83/1.69  Timing (in seconds)
% 3.83/1.69  ----------------------
% 3.83/1.69  Preprocessing        : 0.29
% 3.83/1.70  Parsing              : 0.16
% 3.83/1.70  CNF conversion       : 0.02
% 3.83/1.70  Main loop            : 0.64
% 3.83/1.70  Inferencing          : 0.20
% 3.83/1.70  Reduction            : 0.30
% 3.83/1.70  Demodulation         : 0.25
% 3.83/1.70  BG Simplification    : 0.03
% 3.83/1.70  Subsumption          : 0.07
% 3.83/1.70  Abstraction          : 0.04
% 3.83/1.70  MUC search           : 0.00
% 3.83/1.70  Cooper               : 0.00
% 3.83/1.70  Total                : 0.96
% 3.83/1.70  Index Insertion      : 0.00
% 3.83/1.70  Index Deletion       : 0.00
% 3.83/1.70  Index Matching       : 0.00
% 3.83/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
