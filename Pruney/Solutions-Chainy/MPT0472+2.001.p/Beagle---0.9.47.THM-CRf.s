%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:25 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  81 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ( k1_relat_1(A) = k1_xboole_0
            | k2_relat_1(A) = k1_xboole_0 )
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_64,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_104,plain,(
    ! [A_23] :
      ( r1_tarski(A_23,k2_zfmisc_1(k1_relat_1(A_23),k2_relat_1(A_23)))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_109,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_1')))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_104])).

tff(c_112,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_18,c_109])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_81,plain,(
    ! [B_20,A_21] :
      ( B_20 = A_21
      | ~ r1_tarski(B_20,A_21)
      | ~ r1_tarski(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_81])).

tff(c_115,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_112,c_90])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_115])).

tff(c_122,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_128,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(k2_relat_1(A_24))
      | ~ v1_relat_1(A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_131,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_128])).

tff(c_133,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2,c_131])).

tff(c_54,plain,(
    ! [B_14,A_15] :
      ( ~ v1_xboole_0(B_14)
      | B_14 = A_15
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_57,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_2,c_54])).

tff(c_136,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_133,c_57])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:33:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.20  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.81/1.20  
% 1.81/1.20  %Foreground sorts:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Background operators:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Foreground operators:
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.81/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.20  
% 1.88/1.21  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.88/1.21  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.88/1.21  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.88/1.21  tff(f_60, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 1.88/1.21  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.88/1.21  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.88/1.21  tff(f_56, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 1.88/1.21  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.88/1.21  tff(c_24, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.88/1.21  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.88/1.21  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.88/1.21  tff(c_18, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.21  tff(c_26, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.88/1.21  tff(c_64, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_26])).
% 1.88/1.21  tff(c_104, plain, (![A_23]: (r1_tarski(A_23, k2_zfmisc_1(k1_relat_1(A_23), k2_relat_1(A_23))) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.88/1.21  tff(c_109, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_1'))) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_64, c_104])).
% 1.88/1.21  tff(c_112, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_18, c_109])).
% 1.88/1.21  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.88/1.21  tff(c_81, plain, (![B_20, A_21]: (B_20=A_21 | ~r1_tarski(B_20, A_21) | ~r1_tarski(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.21  tff(c_90, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_81])).
% 1.88/1.21  tff(c_115, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_112, c_90])).
% 1.88/1.21  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_115])).
% 1.88/1.21  tff(c_122, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 1.88/1.21  tff(c_128, plain, (![A_24]: (~v1_xboole_0(k2_relat_1(A_24)) | ~v1_relat_1(A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.21  tff(c_131, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_122, c_128])).
% 1.88/1.21  tff(c_133, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2, c_131])).
% 1.88/1.21  tff(c_54, plain, (![B_14, A_15]: (~v1_xboole_0(B_14) | B_14=A_15 | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.21  tff(c_57, plain, (![A_15]: (k1_xboole_0=A_15 | ~v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_2, c_54])).
% 1.88/1.21  tff(c_136, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_133, c_57])).
% 1.88/1.21  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_136])).
% 1.88/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  Inference rules
% 1.88/1.21  ----------------------
% 1.88/1.21  #Ref     : 0
% 1.88/1.21  #Sup     : 25
% 1.88/1.21  #Fact    : 0
% 1.88/1.21  #Define  : 0
% 1.88/1.21  #Split   : 1
% 1.88/1.21  #Chain   : 0
% 1.88/1.21  #Close   : 0
% 1.88/1.21  
% 1.88/1.21  Ordering : KBO
% 1.88/1.21  
% 1.88/1.21  Simplification rules
% 1.88/1.21  ----------------------
% 1.88/1.21  #Subsume      : 0
% 1.88/1.21  #Demod        : 6
% 1.88/1.21  #Tautology    : 17
% 1.88/1.21  #SimpNegUnit  : 2
% 1.88/1.21  #BackRed      : 0
% 1.88/1.21  
% 1.88/1.21  #Partial instantiations: 0
% 1.88/1.21  #Strategies tried      : 1
% 1.88/1.21  
% 1.88/1.21  Timing (in seconds)
% 1.88/1.21  ----------------------
% 1.88/1.22  Preprocessing        : 0.30
% 1.88/1.22  Parsing              : 0.16
% 1.88/1.22  CNF conversion       : 0.02
% 1.88/1.22  Main loop            : 0.12
% 1.88/1.22  Inferencing          : 0.04
% 1.88/1.22  Reduction            : 0.04
% 1.88/1.22  Demodulation         : 0.03
% 1.88/1.22  BG Simplification    : 0.01
% 1.88/1.22  Subsumption          : 0.02
% 1.88/1.22  Abstraction          : 0.00
% 1.88/1.22  MUC search           : 0.00
% 1.88/1.22  Cooper               : 0.00
% 1.88/1.22  Total                : 0.45
% 1.88/1.22  Index Insertion      : 0.00
% 1.88/1.22  Index Deletion       : 0.00
% 1.88/1.22  Index Matching       : 0.00
% 1.88/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
