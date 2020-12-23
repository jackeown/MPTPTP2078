%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:40 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   43 (  43 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_65,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_58,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_24,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_1'(A_32),A_32)
      | v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden(A_57,B_58)
      | ~ r1_xboole_0(k1_tarski(A_57),B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_67,plain,(
    ! [A_59] : ~ r2_hidden(A_59,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_72,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [A_50] : k7_relat_1(k1_xboole_0,A_50) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_92,plain,(
    ! [B_68,A_69] :
      ( k2_relat_1(k7_relat_1(B_68,A_69)) = k9_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_101,plain,(
    ! [A_50] :
      ( k9_relat_1(k1_xboole_0,A_50) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_92])).

tff(c_105,plain,(
    ! [A_50] : k9_relat_1(k1_xboole_0,A_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_30,c_101])).

tff(c_34,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.12  
% 1.71/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.12  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.71/1.12  
% 1.71/1.12  %Foreground sorts:
% 1.71/1.12  
% 1.71/1.12  
% 1.71/1.12  %Background operators:
% 1.71/1.12  
% 1.71/1.12  
% 1.71/1.12  %Foreground operators:
% 1.71/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.12  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.71/1.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.71/1.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.71/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.71/1.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.71/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.71/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.71/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.71/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.71/1.12  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.71/1.12  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.71/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.71/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.71/1.12  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.71/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.71/1.12  
% 1.71/1.13  tff(f_56, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.71/1.13  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.71/1.13  tff(f_46, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.71/1.13  tff(f_65, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.71/1.13  tff(f_58, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.71/1.13  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.71/1.13  tff(f_68, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.71/1.13  tff(c_24, plain, (![A_32]: (r2_hidden('#skF_1'(A_32), A_32) | v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.71/1.13  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.71/1.13  tff(c_61, plain, (![A_57, B_58]: (~r2_hidden(A_57, B_58) | ~r1_xboole_0(k1_tarski(A_57), B_58))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.71/1.13  tff(c_67, plain, (![A_59]: (~r2_hidden(A_59, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_61])).
% 1.71/1.13  tff(c_72, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_67])).
% 1.71/1.13  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.71/1.13  tff(c_26, plain, (![A_50]: (k7_relat_1(k1_xboole_0, A_50)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.13  tff(c_92, plain, (![B_68, A_69]: (k2_relat_1(k7_relat_1(B_68, A_69))=k9_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.71/1.13  tff(c_101, plain, (![A_50]: (k9_relat_1(k1_xboole_0, A_50)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_92])).
% 1.71/1.13  tff(c_105, plain, (![A_50]: (k9_relat_1(k1_xboole_0, A_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_30, c_101])).
% 1.71/1.13  tff(c_34, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.71/1.13  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_34])).
% 1.71/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.13  
% 1.71/1.13  Inference rules
% 1.71/1.13  ----------------------
% 1.71/1.13  #Ref     : 0
% 1.71/1.13  #Sup     : 17
% 1.71/1.13  #Fact    : 0
% 1.71/1.13  #Define  : 0
% 1.71/1.13  #Split   : 0
% 1.71/1.13  #Chain   : 0
% 1.71/1.13  #Close   : 0
% 1.71/1.13  
% 1.71/1.13  Ordering : KBO
% 1.71/1.13  
% 1.71/1.13  Simplification rules
% 1.71/1.13  ----------------------
% 1.71/1.13  #Subsume      : 0
% 1.71/1.13  #Demod        : 3
% 1.71/1.13  #Tautology    : 14
% 1.71/1.13  #SimpNegUnit  : 0
% 1.71/1.13  #BackRed      : 1
% 1.71/1.13  
% 1.71/1.13  #Partial instantiations: 0
% 1.71/1.13  #Strategies tried      : 1
% 1.71/1.13  
% 1.71/1.13  Timing (in seconds)
% 1.71/1.13  ----------------------
% 1.71/1.13  Preprocessing        : 0.29
% 1.71/1.13  Parsing              : 0.15
% 1.71/1.13  CNF conversion       : 0.02
% 1.71/1.13  Main loop            : 0.09
% 1.71/1.13  Inferencing          : 0.04
% 1.71/1.13  Reduction            : 0.03
% 1.71/1.13  Demodulation         : 0.02
% 1.71/1.13  BG Simplification    : 0.01
% 1.71/1.13  Subsumption          : 0.01
% 1.71/1.13  Abstraction          : 0.01
% 1.71/1.13  MUC search           : 0.00
% 1.71/1.13  Cooper               : 0.00
% 1.71/1.13  Total                : 0.41
% 1.71/1.13  Index Insertion      : 0.00
% 1.71/1.13  Index Deletion       : 0.00
% 1.71/1.13  Index Matching       : 0.00
% 1.71/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
