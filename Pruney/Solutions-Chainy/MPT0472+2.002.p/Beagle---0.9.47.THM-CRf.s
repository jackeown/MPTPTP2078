%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:25 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 ( 102 expanded)
%              Number of equality atoms :   17 (  42 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ( k1_relat_1(A) = k1_xboole_0
            | k2_relat_1(A) = k1_xboole_0 )
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_31,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(k1_relat_1(A_14))
      | ~ v1_relat_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_31])).

tff(c_36,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6,c_34])).

tff(c_37,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | r2_hidden(k4_tarski('#skF_2'(A_15),'#skF_3'(A_15)),A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(A_16)
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_37,c_2])).

tff(c_45,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_42])).

tff(c_51,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_45])).

tff(c_53,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_51])).

tff(c_54,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_66,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(k2_relat_1(A_19))
      | ~ v1_relat_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_69,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_66])).

tff(c_71,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6,c_69])).

tff(c_72,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | r2_hidden(k4_tarski('#skF_2'(A_20),'#skF_3'(A_20)),A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_77,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(A_21)
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_80,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_77])).

tff(c_86,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_80])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 1.67/1.13  
% 1.67/1.13  %Foreground sorts:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Background operators:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Foreground operators:
% 1.67/1.13  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.67/1.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.67/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.67/1.13  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.13  
% 1.67/1.14  tff(f_65, negated_conjecture, ~(![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.67/1.14  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.67/1.14  tff(f_40, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 1.67/1.14  tff(f_56, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 1.67/1.14  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.67/1.14  tff(f_48, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 1.67/1.14  tff(c_14, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.67/1.14  tff(c_18, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.67/1.14  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.67/1.14  tff(c_16, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.67/1.14  tff(c_20, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_16])).
% 1.67/1.14  tff(c_31, plain, (![A_14]: (~v1_xboole_0(k1_relat_1(A_14)) | ~v1_relat_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.14  tff(c_34, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20, c_31])).
% 1.67/1.14  tff(c_36, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6, c_34])).
% 1.67/1.14  tff(c_37, plain, (![A_15]: (k1_xboole_0=A_15 | r2_hidden(k4_tarski('#skF_2'(A_15), '#skF_3'(A_15)), A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.14  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.14  tff(c_42, plain, (![A_16]: (~v1_xboole_0(A_16) | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_37, c_2])).
% 1.67/1.14  tff(c_45, plain, (k1_xboole_0='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_42])).
% 1.67/1.14  tff(c_51, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_45])).
% 1.67/1.14  tff(c_53, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_51])).
% 1.67/1.14  tff(c_54, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_16])).
% 1.67/1.14  tff(c_66, plain, (![A_19]: (~v1_xboole_0(k2_relat_1(A_19)) | ~v1_relat_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.14  tff(c_69, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_54, c_66])).
% 1.67/1.14  tff(c_71, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6, c_69])).
% 1.67/1.14  tff(c_72, plain, (![A_20]: (k1_xboole_0=A_20 | r2_hidden(k4_tarski('#skF_2'(A_20), '#skF_3'(A_20)), A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.14  tff(c_77, plain, (![A_21]: (~v1_xboole_0(A_21) | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(resolution, [status(thm)], [c_72, c_2])).
% 1.67/1.14  tff(c_80, plain, (k1_xboole_0='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_71, c_77])).
% 1.67/1.14  tff(c_86, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_80])).
% 1.67/1.14  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_86])).
% 1.67/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  Inference rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Ref     : 0
% 1.67/1.14  #Sup     : 14
% 1.67/1.14  #Fact    : 0
% 1.67/1.14  #Define  : 0
% 1.67/1.14  #Split   : 1
% 1.67/1.14  #Chain   : 0
% 1.67/1.14  #Close   : 0
% 1.67/1.14  
% 1.67/1.14  Ordering : KBO
% 1.67/1.14  
% 1.67/1.14  Simplification rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Subsume      : 0
% 1.67/1.14  #Demod        : 6
% 1.67/1.15  #Tautology    : 6
% 1.67/1.15  #SimpNegUnit  : 2
% 1.67/1.15  #BackRed      : 0
% 1.67/1.15  
% 1.67/1.15  #Partial instantiations: 0
% 1.67/1.15  #Strategies tried      : 1
% 1.67/1.15  
% 1.67/1.15  Timing (in seconds)
% 1.67/1.15  ----------------------
% 1.67/1.15  Preprocessing        : 0.27
% 1.67/1.15  Parsing              : 0.15
% 1.67/1.15  CNF conversion       : 0.02
% 1.67/1.15  Main loop            : 0.11
% 1.67/1.15  Inferencing          : 0.04
% 1.67/1.15  Reduction            : 0.03
% 1.67/1.15  Demodulation         : 0.02
% 1.67/1.15  BG Simplification    : 0.01
% 1.67/1.15  Subsumption          : 0.01
% 1.73/1.15  Abstraction          : 0.00
% 1.73/1.15  MUC search           : 0.00
% 1.73/1.15  Cooper               : 0.00
% 1.73/1.15  Total                : 0.40
% 1.73/1.15  Index Insertion      : 0.00
% 1.73/1.15  Index Deletion       : 0.00
% 1.73/1.15  Index Matching       : 0.00
% 1.73/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
