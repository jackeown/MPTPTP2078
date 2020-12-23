%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:28 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_64,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_1'(A_32),A_32)
      | v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    ! [A_29,B_30] : ~ r2_hidden(A_29,k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    ! [A_2] : ~ r2_hidden(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_56])).

tff(c_69,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64,c_59])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_82,plain,(
    ! [A_38,B_39] :
      ( k8_relat_1(A_38,B_39) = B_39
      | ~ r1_tarski(k2_relat_1(B_39),A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_85,plain,(
    ! [A_38] :
      ( k8_relat_1(A_38,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_38)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_82])).

tff(c_87,plain,(
    ! [A_38] : k8_relat_1(A_38,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2,c_85])).

tff(c_24,plain,(
    k8_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.11  
% 1.59/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.11  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.59/1.11  
% 1.59/1.11  %Foreground sorts:
% 1.59/1.11  
% 1.59/1.11  
% 1.59/1.11  %Background operators:
% 1.59/1.11  
% 1.59/1.11  
% 1.59/1.11  %Foreground operators:
% 1.59/1.11  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.59/1.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.59/1.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.59/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.59/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.59/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.59/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.59/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.59/1.11  
% 1.59/1.12  tff(f_46, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.59/1.12  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.59/1.12  tff(f_36, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.59/1.12  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.59/1.12  tff(f_55, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.59/1.12  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.59/1.12  tff(f_58, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.59/1.12  tff(c_64, plain, (![A_32]: (r2_hidden('#skF_1'(A_32), A_32) | v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.59/1.12  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.59/1.12  tff(c_56, plain, (![A_29, B_30]: (~r2_hidden(A_29, k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.59/1.12  tff(c_59, plain, (![A_2]: (~r2_hidden(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_56])).
% 1.59/1.12  tff(c_69, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_59])).
% 1.59/1.12  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.12  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.59/1.12  tff(c_82, plain, (![A_38, B_39]: (k8_relat_1(A_38, B_39)=B_39 | ~r1_tarski(k2_relat_1(B_39), A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.59/1.12  tff(c_85, plain, (![A_38]: (k8_relat_1(A_38, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_38) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_82])).
% 1.59/1.12  tff(c_87, plain, (![A_38]: (k8_relat_1(A_38, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_69, c_2, c_85])).
% 1.59/1.12  tff(c_24, plain, (k8_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.59/1.12  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_24])).
% 1.59/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.12  
% 1.59/1.12  Inference rules
% 1.59/1.12  ----------------------
% 1.59/1.12  #Ref     : 0
% 1.59/1.12  #Sup     : 16
% 1.59/1.12  #Fact    : 0
% 1.59/1.12  #Define  : 0
% 1.59/1.12  #Split   : 0
% 1.59/1.12  #Chain   : 0
% 1.59/1.12  #Close   : 0
% 1.59/1.12  
% 1.59/1.12  Ordering : KBO
% 1.59/1.12  
% 1.59/1.12  Simplification rules
% 1.59/1.12  ----------------------
% 1.59/1.12  #Subsume      : 1
% 1.59/1.12  #Demod        : 3
% 1.59/1.12  #Tautology    : 12
% 1.59/1.12  #SimpNegUnit  : 0
% 1.59/1.12  #BackRed      : 1
% 1.59/1.12  
% 1.59/1.12  #Partial instantiations: 0
% 1.59/1.12  #Strategies tried      : 1
% 1.59/1.12  
% 1.59/1.12  Timing (in seconds)
% 1.59/1.12  ----------------------
% 1.71/1.12  Preprocessing        : 0.26
% 1.71/1.12  Parsing              : 0.15
% 1.71/1.12  CNF conversion       : 0.02
% 1.71/1.12  Main loop            : 0.10
% 1.71/1.12  Inferencing          : 0.04
% 1.71/1.13  Reduction            : 0.03
% 1.71/1.13  Demodulation         : 0.02
% 1.71/1.13  BG Simplification    : 0.01
% 1.71/1.13  Subsumption          : 0.01
% 1.71/1.13  Abstraction          : 0.00
% 1.71/1.13  MUC search           : 0.00
% 1.71/1.13  Cooper               : 0.00
% 1.71/1.13  Total                : 0.38
% 1.71/1.13  Index Insertion      : 0.00
% 1.71/1.13  Index Deletion       : 0.00
% 1.71/1.13  Index Matching       : 0.00
% 1.71/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
