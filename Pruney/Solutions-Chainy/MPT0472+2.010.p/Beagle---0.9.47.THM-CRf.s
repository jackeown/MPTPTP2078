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
% DateTime   : Thu Dec  3 09:59:26 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   32 (  44 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  68 expanded)
%              Number of equality atoms :   17 (  40 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ( k1_relat_1(A) = k1_xboole_0
            | k2_relat_1(A) = k1_xboole_0 )
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_56,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_1')))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_56])).

tff(c_61,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8,c_59])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_68,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_64])).

tff(c_69,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_86,plain,(
    ! [A_13] :
      ( r1_tarski(A_13,k2_zfmisc_1(k1_relat_1(A_13),k2_relat_1(A_13)))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_86])).

tff(c_91,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6,c_89])).

tff(c_94,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.07  
% 1.49/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.07  %$ r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.49/1.07  
% 1.49/1.07  %Foreground sorts:
% 1.49/1.07  
% 1.49/1.07  
% 1.49/1.07  %Background operators:
% 1.49/1.07  
% 1.49/1.07  
% 1.49/1.07  %Foreground operators:
% 1.49/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.49/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.49/1.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.49/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.49/1.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.49/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.49/1.07  
% 1.49/1.08  tff(f_48, negated_conjecture, ~(![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.49/1.08  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.49/1.08  tff(f_39, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 1.49/1.08  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.49/1.08  tff(c_12, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.49/1.08  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.49/1.08  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.49/1.08  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.49/1.08  tff(c_14, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.49/1.08  tff(c_40, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14])).
% 1.49/1.08  tff(c_56, plain, (![A_10]: (r1_tarski(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.49/1.08  tff(c_59, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_1'))) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_56])).
% 1.49/1.08  tff(c_61, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8, c_59])).
% 1.49/1.08  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.49/1.08  tff(c_64, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_61, c_2])).
% 1.49/1.08  tff(c_68, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_64])).
% 1.49/1.08  tff(c_69, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_14])).
% 1.49/1.08  tff(c_86, plain, (![A_13]: (r1_tarski(A_13, k2_zfmisc_1(k1_relat_1(A_13), k2_relat_1(A_13))) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.49/1.08  tff(c_89, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_69, c_86])).
% 1.49/1.08  tff(c_91, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_6, c_89])).
% 1.49/1.08  tff(c_94, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_91, c_2])).
% 1.49/1.08  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_94])).
% 1.49/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.08  
% 1.49/1.08  Inference rules
% 1.49/1.08  ----------------------
% 1.49/1.08  #Ref     : 0
% 1.49/1.08  #Sup     : 18
% 1.49/1.08  #Fact    : 0
% 1.49/1.08  #Define  : 0
% 1.49/1.08  #Split   : 1
% 1.49/1.08  #Chain   : 0
% 1.49/1.08  #Close   : 0
% 1.49/1.08  
% 1.49/1.08  Ordering : KBO
% 1.49/1.08  
% 1.49/1.08  Simplification rules
% 1.49/1.08  ----------------------
% 1.49/1.08  #Subsume      : 0
% 1.49/1.08  #Demod        : 4
% 1.49/1.08  #Tautology    : 14
% 1.49/1.08  #SimpNegUnit  : 2
% 1.49/1.08  #BackRed      : 0
% 1.49/1.08  
% 1.49/1.08  #Partial instantiations: 0
% 1.49/1.08  #Strategies tried      : 1
% 1.49/1.08  
% 1.49/1.08  Timing (in seconds)
% 1.49/1.08  ----------------------
% 1.63/1.08  Preprocessing        : 0.25
% 1.63/1.08  Parsing              : 0.13
% 1.63/1.08  CNF conversion       : 0.01
% 1.63/1.08  Main loop            : 0.09
% 1.63/1.08  Inferencing          : 0.03
% 1.63/1.08  Reduction            : 0.03
% 1.63/1.08  Demodulation         : 0.02
% 1.63/1.08  BG Simplification    : 0.01
% 1.63/1.08  Subsumption          : 0.01
% 1.63/1.08  Abstraction          : 0.00
% 1.63/1.08  MUC search           : 0.00
% 1.63/1.08  Cooper               : 0.00
% 1.63/1.08  Total                : 0.36
% 1.63/1.08  Index Insertion      : 0.00
% 1.63/1.08  Index Deletion       : 0.00
% 1.63/1.08  Index Matching       : 0.00
% 1.63/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
