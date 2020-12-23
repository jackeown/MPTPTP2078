%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:24 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   43 (  44 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  37 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(f_59,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_28,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_83,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_1'(A_35),A_35)
      | v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    ! [A_32,B_33] : ~ r2_hidden(A_32,k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_78,plain,(
    ! [A_5] : ~ r2_hidden(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_75])).

tff(c_88,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_83,c_78])).

tff(c_4,plain,(
    ! [A_2] : k5_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_90,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k4_xboole_0(B_40,A_39)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k2_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_90])).

tff(c_102,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_99])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_123,plain,(
    ! [A_44] :
      ( k2_xboole_0(k1_relat_1(A_44),k2_relat_1(A_44)) = k3_relat_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_132,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_123])).

tff(c_139,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_102,c_26,c_132])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.22  %$ r2_hidden > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.88/1.22  
% 1.88/1.22  %Foreground sorts:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Background operators:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Foreground operators:
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.88/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.88/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.22  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.88/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.88/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.88/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.88/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.22  
% 1.97/1.23  tff(f_59, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 1.97/1.23  tff(f_50, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.97/1.23  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.97/1.23  tff(f_40, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.97/1.23  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.97/1.23  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.97/1.23  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.97/1.23  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.97/1.23  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.97/1.23  tff(c_28, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.97/1.23  tff(c_83, plain, (![A_35]: (r2_hidden('#skF_1'(A_35), A_35) | v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.23  tff(c_10, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.23  tff(c_75, plain, (![A_32, B_33]: (~r2_hidden(A_32, k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.97/1.23  tff(c_78, plain, (![A_5]: (~r2_hidden(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_75])).
% 1.97/1.23  tff(c_88, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_83, c_78])).
% 1.97/1.23  tff(c_4, plain, (![A_2]: (k5_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.23  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.23  tff(c_90, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k4_xboole_0(B_40, A_39))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.23  tff(c_99, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k2_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_90])).
% 1.97/1.23  tff(c_102, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_99])).
% 1.97/1.23  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.97/1.23  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.97/1.23  tff(c_123, plain, (![A_44]: (k2_xboole_0(k1_relat_1(A_44), k2_relat_1(A_44))=k3_relat_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.97/1.23  tff(c_132, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_123])).
% 1.97/1.23  tff(c_139, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_88, c_102, c_26, c_132])).
% 1.97/1.23  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_139])).
% 1.97/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.23  
% 1.97/1.23  Inference rules
% 1.97/1.23  ----------------------
% 1.97/1.23  #Ref     : 0
% 1.97/1.23  #Sup     : 28
% 1.97/1.23  #Fact    : 0
% 1.97/1.23  #Define  : 0
% 1.97/1.23  #Split   : 0
% 1.97/1.23  #Chain   : 0
% 1.97/1.23  #Close   : 0
% 1.97/1.23  
% 1.97/1.23  Ordering : KBO
% 1.97/1.23  
% 1.97/1.23  Simplification rules
% 1.97/1.23  ----------------------
% 1.97/1.23  #Subsume      : 1
% 1.97/1.23  #Demod        : 4
% 1.97/1.23  #Tautology    : 22
% 1.97/1.23  #SimpNegUnit  : 1
% 1.97/1.23  #BackRed      : 0
% 1.97/1.23  
% 1.97/1.23  #Partial instantiations: 0
% 1.97/1.23  #Strategies tried      : 1
% 1.97/1.23  
% 1.97/1.23  Timing (in seconds)
% 1.97/1.23  ----------------------
% 1.97/1.23  Preprocessing        : 0.30
% 1.97/1.23  Parsing              : 0.17
% 1.97/1.23  CNF conversion       : 0.02
% 1.97/1.23  Main loop            : 0.12
% 1.97/1.23  Inferencing          : 0.05
% 1.97/1.23  Reduction            : 0.04
% 1.97/1.23  Demodulation         : 0.03
% 1.97/1.23  BG Simplification    : 0.01
% 1.97/1.23  Subsumption          : 0.02
% 1.97/1.23  Abstraction          : 0.01
% 1.97/1.23  MUC search           : 0.00
% 1.97/1.23  Cooper               : 0.00
% 1.97/1.23  Total                : 0.45
% 1.97/1.23  Index Insertion      : 0.00
% 1.97/1.23  Index Deletion       : 0.00
% 1.97/1.23  Index Matching       : 0.00
% 1.97/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
