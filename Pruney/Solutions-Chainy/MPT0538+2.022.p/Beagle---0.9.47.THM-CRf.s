%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:25 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  45 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [B_21,A_22] :
      ( v1_relat_1(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ! [A_2] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_30])).

tff(c_35,plain,(
    ! [A_2] : ~ v1_relat_1(A_2) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11,D_12] : v1_relat_1(k2_tarski(k4_tarski(A_9,B_10),k4_tarski(C_11,D_12))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_10])).

tff(c_39,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    ! [A_23,B_24] :
      ( k8_relat_1(A_23,B_24) = B_24
      | ~ r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_43,plain,(
    ! [A_23] :
      ( k8_relat_1(A_23,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_23)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_45,plain,(
    ! [A_23] :
      ( k8_relat_1(A_23,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_43])).

tff(c_47,plain,(
    ! [A_23] : k8_relat_1(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_45])).

tff(c_18,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:22:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.49  
% 2.01/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.50  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.01/1.50  
% 2.01/1.50  %Foreground sorts:
% 2.01/1.50  
% 2.01/1.50  
% 2.01/1.50  %Background operators:
% 2.01/1.50  
% 2.01/1.50  
% 2.01/1.50  %Foreground operators:
% 2.01/1.50  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.01/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.01/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.01/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.01/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.01/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.01/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.50  
% 2.10/1.52  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.10/1.52  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.10/1.52  tff(f_44, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 2.10/1.52  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.10/1.52  tff(f_53, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.10/1.52  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.10/1.52  tff(f_56, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 2.10/1.52  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.52  tff(c_30, plain, (![B_21, A_22]: (v1_relat_1(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_22)) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.10/1.52  tff(c_34, plain, (![A_2]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_2))), inference(resolution, [status(thm)], [c_4, c_30])).
% 2.10/1.52  tff(c_35, plain, (![A_2]: (~v1_relat_1(A_2))), inference(splitLeft, [status(thm)], [c_34])).
% 2.10/1.52  tff(c_10, plain, (![A_9, B_10, C_11, D_12]: (v1_relat_1(k2_tarski(k4_tarski(A_9, B_10), k4_tarski(C_11, D_12))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.52  tff(c_38, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_10])).
% 2.10/1.52  tff(c_39, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_34])).
% 2.10/1.52  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.52  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.52  tff(c_40, plain, (![A_23, B_24]: (k8_relat_1(A_23, B_24)=B_24 | ~r1_tarski(k2_relat_1(B_24), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.52  tff(c_43, plain, (![A_23]: (k8_relat_1(A_23, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_23) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_40])).
% 2.10/1.52  tff(c_45, plain, (![A_23]: (k8_relat_1(A_23, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_43])).
% 2.10/1.52  tff(c_47, plain, (![A_23]: (k8_relat_1(A_23, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_39, c_45])).
% 2.10/1.52  tff(c_18, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.52  tff(c_50, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_18])).
% 2.10/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.52  
% 2.10/1.52  Inference rules
% 2.10/1.52  ----------------------
% 2.10/1.52  #Ref     : 0
% 2.10/1.52  #Sup     : 6
% 2.10/1.52  #Fact    : 0
% 2.10/1.52  #Define  : 0
% 2.10/1.52  #Split   : 1
% 2.10/1.52  #Chain   : 0
% 2.10/1.52  #Close   : 0
% 2.10/1.52  
% 2.10/1.52  Ordering : KBO
% 2.10/1.52  
% 2.10/1.52  Simplification rules
% 2.10/1.52  ----------------------
% 2.10/1.52  #Subsume      : 1
% 2.10/1.52  #Demod        : 3
% 2.10/1.52  #Tautology    : 4
% 2.10/1.52  #SimpNegUnit  : 2
% 2.10/1.52  #BackRed      : 2
% 2.10/1.52  
% 2.10/1.52  #Partial instantiations: 0
% 2.10/1.52  #Strategies tried      : 1
% 2.10/1.52  
% 2.10/1.52  Timing (in seconds)
% 2.10/1.52  ----------------------
% 2.10/1.52  Preprocessing        : 0.42
% 2.10/1.52  Parsing              : 0.23
% 2.10/1.52  CNF conversion       : 0.03
% 2.10/1.52  Main loop            : 0.16
% 2.10/1.52  Inferencing          : 0.07
% 2.10/1.52  Reduction            : 0.04
% 2.10/1.52  Demodulation         : 0.03
% 2.10/1.52  BG Simplification    : 0.01
% 2.10/1.52  Subsumption          : 0.02
% 2.10/1.52  Abstraction          : 0.01
% 2.10/1.52  MUC search           : 0.00
% 2.10/1.52  Cooper               : 0.00
% 2.10/1.52  Total                : 0.63
% 2.10/1.52  Index Insertion      : 0.00
% 2.10/1.52  Index Deletion       : 0.00
% 2.10/1.52  Index Matching       : 0.00
% 2.10/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
