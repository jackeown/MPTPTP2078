%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:30 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   25 (  63 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 ( 142 expanded)
%              Number of equality atoms :   42 ( 140 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_zfmisc_1(A,A,A) = k3_zfmisc_1(B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

tff(c_16,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [A_16,B_17,C_18] :
      ( k3_zfmisc_1(A_16,B_17,C_18) != k1_xboole_0
      | k1_xboole_0 = C_18
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,
    ( k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_68])).

tff(c_87,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_92,plain,(
    ! [A_24,C_21,D_22,F_20,B_19,E_23] :
      ( F_20 = C_21
      | k3_zfmisc_1(A_24,B_19,C_21) = k1_xboole_0
      | k3_zfmisc_1(D_22,E_23,F_20) != k3_zfmisc_1(A_24,B_19,C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_95,plain,(
    ! [C_21,A_24,B_19] :
      ( C_21 = '#skF_2'
      | k3_zfmisc_1(A_24,B_19,C_21) = k1_xboole_0
      | k3_zfmisc_1(A_24,B_19,C_21) != k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_92])).

tff(c_124,plain,
    ( '#skF_2' = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_95])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_16,c_124])).

tff(c_128,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k3_zfmisc_1(A_1,B_2,C_3) != k1_xboole_0
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_2])).

tff(c_127,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_232,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_136,c_136,c_127])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_16,c_16,c_232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:31:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.24  
% 1.93/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.24  %$ k3_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.93/1.24  
% 1.93/1.24  %Foreground sorts:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Background operators:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Foreground operators:
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.24  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.24  
% 1.93/1.25  tff(f_52, negated_conjecture, ~(![A, B]: ((k3_zfmisc_1(A, A, A) = k3_zfmisc_1(B, B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_mcart_1)).
% 1.93/1.25  tff(f_37, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 1.93/1.25  tff(f_47, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_mcart_1)).
% 1.93/1.25  tff(c_16, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.25  tff(c_18, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.25  tff(c_68, plain, (![A_16, B_17, C_18]: (k3_zfmisc_1(A_16, B_17, C_18)!=k1_xboole_0 | k1_xboole_0=C_18 | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.25  tff(c_71, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_18, c_68])).
% 1.93/1.25  tff(c_87, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_71])).
% 1.93/1.25  tff(c_92, plain, (![A_24, C_21, D_22, F_20, B_19, E_23]: (F_20=C_21 | k3_zfmisc_1(A_24, B_19, C_21)=k1_xboole_0 | k3_zfmisc_1(D_22, E_23, F_20)!=k3_zfmisc_1(A_24, B_19, C_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.25  tff(c_95, plain, (![C_21, A_24, B_19]: (C_21='#skF_2' | k3_zfmisc_1(A_24, B_19, C_21)=k1_xboole_0 | k3_zfmisc_1(A_24, B_19, C_21)!=k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_92])).
% 1.93/1.25  tff(c_124, plain, ('#skF_2'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_95])).
% 1.93/1.25  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_16, c_124])).
% 1.93/1.25  tff(c_128, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_71])).
% 1.93/1.25  tff(c_2, plain, (![A_1, B_2, C_3]: (k3_zfmisc_1(A_1, B_2, C_3)!=k1_xboole_0 | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.25  tff(c_136, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_128, c_2])).
% 1.93/1.25  tff(c_127, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_71])).
% 1.93/1.25  tff(c_232, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_136, c_136, c_127])).
% 1.93/1.25  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_16, c_16, c_232])).
% 1.93/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.25  
% 1.93/1.25  Inference rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Ref     : 3
% 1.93/1.25  #Sup     : 53
% 1.93/1.25  #Fact    : 0
% 1.93/1.25  #Define  : 0
% 1.93/1.25  #Split   : 1
% 1.93/1.25  #Chain   : 0
% 1.93/1.25  #Close   : 0
% 1.93/1.25  
% 1.93/1.25  Ordering : KBO
% 1.93/1.25  
% 1.93/1.25  Simplification rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Subsume      : 0
% 1.93/1.25  #Demod        : 26
% 1.93/1.25  #Tautology    : 52
% 1.93/1.25  #SimpNegUnit  : 3
% 1.93/1.25  #BackRed      : 6
% 1.93/1.25  
% 1.93/1.25  #Partial instantiations: 0
% 1.93/1.25  #Strategies tried      : 1
% 1.93/1.25  
% 1.93/1.25  Timing (in seconds)
% 1.93/1.25  ----------------------
% 1.93/1.25  Preprocessing        : 0.29
% 1.93/1.25  Parsing              : 0.15
% 1.93/1.25  CNF conversion       : 0.02
% 1.93/1.25  Main loop            : 0.15
% 1.93/1.25  Inferencing          : 0.05
% 1.93/1.25  Reduction            : 0.04
% 1.93/1.25  Demodulation         : 0.03
% 1.93/1.25  BG Simplification    : 0.01
% 1.93/1.25  Subsumption          : 0.04
% 1.93/1.25  Abstraction          : 0.01
% 1.93/1.25  MUC search           : 0.00
% 1.93/1.25  Cooper               : 0.00
% 1.93/1.25  Total                : 0.46
% 1.93/1.25  Index Insertion      : 0.00
% 1.93/1.25  Index Deletion       : 0.00
% 1.93/1.25  Index Matching       : 0.00
% 1.93/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
