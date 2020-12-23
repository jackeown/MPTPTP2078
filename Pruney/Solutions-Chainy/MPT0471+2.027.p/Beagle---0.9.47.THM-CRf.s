%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:24 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  36 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_63,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_30,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_79,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_1'(A_37),A_37)
      | v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    ! [A_34,B_35] : ~ r2_hidden(A_34,k2_zfmisc_1(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_71])).

tff(c_84,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_79,c_74])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_85])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_143,plain,(
    ! [A_49] :
      ( k2_xboole_0(k1_relat_1(A_49),k2_relat_1(A_49)) = k3_relat_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_152,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_143])).

tff(c_159,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_89,c_28,c_152])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:35:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.26  
% 1.92/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.26  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.92/1.26  
% 1.92/1.26  %Foreground sorts:
% 1.92/1.26  
% 1.92/1.26  
% 1.92/1.26  %Background operators:
% 1.92/1.26  
% 1.92/1.26  
% 1.92/1.26  %Foreground operators:
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.92/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.92/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.26  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.92/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.92/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.92/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.92/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.26  
% 1.92/1.27  tff(f_63, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_relat_1)).
% 1.92/1.27  tff(f_54, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.92/1.27  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.92/1.27  tff(f_44, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.92/1.27  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.92/1.27  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.92/1.27  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.92/1.27  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.92/1.27  tff(c_30, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.92/1.27  tff(c_79, plain, (![A_37]: (r2_hidden('#skF_1'(A_37), A_37) | v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.92/1.27  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.27  tff(c_71, plain, (![A_34, B_35]: (~r2_hidden(A_34, k2_zfmisc_1(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.92/1.27  tff(c_74, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_71])).
% 1.92/1.27  tff(c_84, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_79, c_74])).
% 1.92/1.27  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.27  tff(c_85, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.27  tff(c_89, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_85])).
% 1.92/1.27  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.27  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.27  tff(c_143, plain, (![A_49]: (k2_xboole_0(k1_relat_1(A_49), k2_relat_1(A_49))=k3_relat_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.92/1.27  tff(c_152, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_143])).
% 1.92/1.27  tff(c_159, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_84, c_89, c_28, c_152])).
% 1.92/1.27  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_159])).
% 1.92/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.27  
% 1.92/1.27  Inference rules
% 1.92/1.27  ----------------------
% 1.92/1.27  #Ref     : 0
% 1.92/1.27  #Sup     : 31
% 1.92/1.27  #Fact    : 0
% 1.92/1.27  #Define  : 0
% 1.92/1.27  #Split   : 0
% 1.92/1.27  #Chain   : 0
% 1.92/1.27  #Close   : 0
% 1.92/1.27  
% 1.92/1.27  Ordering : KBO
% 1.92/1.27  
% 1.92/1.27  Simplification rules
% 1.92/1.27  ----------------------
% 1.92/1.27  #Subsume      : 1
% 1.92/1.27  #Demod        : 8
% 1.92/1.27  #Tautology    : 24
% 1.92/1.27  #SimpNegUnit  : 1
% 1.92/1.27  #BackRed      : 0
% 1.92/1.27  
% 1.92/1.27  #Partial instantiations: 0
% 1.92/1.27  #Strategies tried      : 1
% 1.92/1.27  
% 1.92/1.27  Timing (in seconds)
% 1.92/1.27  ----------------------
% 1.92/1.27  Preprocessing        : 0.28
% 2.01/1.27  Parsing              : 0.16
% 2.01/1.27  CNF conversion       : 0.02
% 2.01/1.27  Main loop            : 0.12
% 2.01/1.27  Inferencing          : 0.05
% 2.01/1.27  Reduction            : 0.04
% 2.01/1.27  Demodulation         : 0.03
% 2.01/1.27  BG Simplification    : 0.01
% 2.01/1.27  Subsumption          : 0.02
% 2.01/1.27  Abstraction          : 0.01
% 2.01/1.27  MUC search           : 0.00
% 2.01/1.27  Cooper               : 0.00
% 2.01/1.27  Total                : 0.43
% 2.01/1.27  Index Insertion      : 0.00
% 2.01/1.27  Index Deletion       : 0.00
% 2.01/1.27  Index Matching       : 0.00
% 2.01/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
