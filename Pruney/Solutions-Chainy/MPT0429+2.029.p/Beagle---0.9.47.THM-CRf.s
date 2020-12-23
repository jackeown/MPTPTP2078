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
% DateTime   : Thu Dec  3 09:58:09 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   41 (  56 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   42 (  66 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_44,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(c_87,plain,(
    ! [A_30,B_31] :
      ( r2_hidden(A_30,B_31)
      | v1_xboole_0(B_31)
      | ~ m1_subset_1(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    ! [A_25,B_26] : ~ r2_hidden(A_25,k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_70])).

tff(c_96,plain,(
    ! [A_30] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_30,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_87,c_73])).

tff(c_98,plain,(
    ! [A_30] : ~ m1_subset_1(A_30,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_140,plain,(
    ! [B_45,A_46] :
      ( m1_subset_1(k1_tarski(B_45),k1_zfmisc_1(A_46))
      | k1_xboole_0 = A_46
      | ~ m1_subset_1(B_45,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_145,plain,
    ( k1_zfmisc_1('#skF_1') = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_140,c_28])).

tff(c_152,plain,(
    k1_zfmisc_1('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_145])).

tff(c_162,plain,(
    m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_20])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_162])).

tff(c_170,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_206,plain,(
    ! [B_57,A_58] :
      ( m1_subset_1(k1_tarski(B_57),k1_zfmisc_1(A_58))
      | k1_xboole_0 = A_58
      | ~ m1_subset_1(B_57,A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_211,plain,
    ( k1_zfmisc_1('#skF_1') = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_206,c_28])).

tff(c_218,plain,(
    k1_zfmisc_1('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_211])).

tff(c_18,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_231,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_18])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:09:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.21  
% 2.00/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.22  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 2.00/1.22  
% 2.00/1.22  %Foreground sorts:
% 2.00/1.22  
% 2.00/1.22  
% 2.00/1.22  %Background operators:
% 2.00/1.22  
% 2.00/1.22  
% 2.00/1.22  %Foreground operators:
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.00/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.22  
% 2.00/1.23  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.00/1.23  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.00/1.23  tff(f_40, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.00/1.23  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.00/1.23  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.00/1.23  tff(f_68, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 2.00/1.23  tff(f_44, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.00/1.23  tff(c_87, plain, (![A_30, B_31]: (r2_hidden(A_30, B_31) | v1_xboole_0(B_31) | ~m1_subset_1(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.00/1.23  tff(c_10, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.23  tff(c_70, plain, (![A_25, B_26]: (~r2_hidden(A_25, k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.00/1.23  tff(c_73, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_70])).
% 2.00/1.23  tff(c_96, plain, (![A_30]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_30, k1_xboole_0))), inference(resolution, [status(thm)], [c_87, c_73])).
% 2.00/1.23  tff(c_98, plain, (![A_30]: (~m1_subset_1(A_30, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_96])).
% 2.00/1.23  tff(c_20, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.00/1.23  tff(c_140, plain, (![B_45, A_46]: (m1_subset_1(k1_tarski(B_45), k1_zfmisc_1(A_46)) | k1_xboole_0=A_46 | ~m1_subset_1(B_45, A_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.00/1.23  tff(c_28, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.00/1.23  tff(c_145, plain, (k1_zfmisc_1('#skF_1')=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_140, c_28])).
% 2.00/1.23  tff(c_152, plain, (k1_zfmisc_1('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_145])).
% 2.00/1.23  tff(c_162, plain, (m1_subset_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_20])).
% 2.00/1.23  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_162])).
% 2.00/1.23  tff(c_170, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_96])).
% 2.00/1.23  tff(c_206, plain, (![B_57, A_58]: (m1_subset_1(k1_tarski(B_57), k1_zfmisc_1(A_58)) | k1_xboole_0=A_58 | ~m1_subset_1(B_57, A_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.00/1.23  tff(c_211, plain, (k1_zfmisc_1('#skF_1')=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_206, c_28])).
% 2.00/1.23  tff(c_218, plain, (k1_zfmisc_1('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_211])).
% 2.00/1.23  tff(c_18, plain, (![A_11]: (~v1_xboole_0(k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.00/1.23  tff(c_231, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_218, c_18])).
% 2.00/1.23  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_231])).
% 2.00/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  Inference rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Ref     : 0
% 2.00/1.23  #Sup     : 53
% 2.00/1.23  #Fact    : 0
% 2.00/1.23  #Define  : 0
% 2.00/1.23  #Split   : 1
% 2.00/1.23  #Chain   : 0
% 2.00/1.23  #Close   : 0
% 2.00/1.23  
% 2.00/1.23  Ordering : KBO
% 2.00/1.23  
% 2.00/1.23  Simplification rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Subsume      : 8
% 2.00/1.23  #Demod        : 13
% 2.00/1.23  #Tautology    : 25
% 2.00/1.23  #SimpNegUnit  : 3
% 2.00/1.23  #BackRed      : 2
% 2.00/1.23  
% 2.00/1.23  #Partial instantiations: 0
% 2.00/1.23  #Strategies tried      : 1
% 2.00/1.23  
% 2.00/1.23  Timing (in seconds)
% 2.00/1.23  ----------------------
% 2.00/1.23  Preprocessing        : 0.30
% 2.00/1.23  Parsing              : 0.16
% 2.00/1.23  CNF conversion       : 0.02
% 2.00/1.23  Main loop            : 0.16
% 2.00/1.23  Inferencing          : 0.06
% 2.00/1.23  Reduction            : 0.05
% 2.00/1.23  Demodulation         : 0.04
% 2.00/1.23  BG Simplification    : 0.01
% 2.00/1.23  Subsumption          : 0.02
% 2.00/1.23  Abstraction          : 0.01
% 2.00/1.23  MUC search           : 0.00
% 2.00/1.23  Cooper               : 0.00
% 2.00/1.23  Total                : 0.49
% 2.00/1.23  Index Insertion      : 0.00
% 2.00/1.23  Index Deletion       : 0.00
% 2.00/1.23  Index Matching       : 0.00
% 2.00/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
