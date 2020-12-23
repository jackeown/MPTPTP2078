%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:30 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 120 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 318 expanded)
%              Number of equality atoms :   60 ( 315 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_zfmisc_1(A,A,A) = k3_zfmisc_1(B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(c_16,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    ! [A_24,C_21,D_22,F_20,B_19,E_23] :
      ( F_20 = C_21
      | k1_xboole_0 = C_21
      | k1_xboole_0 = B_19
      | k1_xboole_0 = A_24
      | k3_zfmisc_1(D_22,E_23,F_20) != k3_zfmisc_1(A_24,B_19,C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_95,plain,(
    ! [C_21,B_19,A_24] :
      ( C_21 = '#skF_2'
      | k1_xboole_0 = C_21
      | k1_xboole_0 = B_19
      | k1_xboole_0 = A_24
      | k3_zfmisc_1(A_24,B_19,C_21) != k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_92])).

tff(c_122,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_95])).

tff(c_123,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_122])).

tff(c_139,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_6,plain,(
    ! [A_1,C_3] : k3_zfmisc_1(A_1,k1_xboole_0,C_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_144,plain,(
    ! [A_1,C_3] : k3_zfmisc_1(A_1,'#skF_1',C_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_139,c_6])).

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

tff(c_142,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_87])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_142])).

tff(c_238,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_237,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_238,c_237])).

tff(c_258,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k3_zfmisc_1(A_1,B_2,C_3) != k1_xboole_0
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_266,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_2])).

tff(c_257,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_322,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_266,c_266,c_257])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_16,c_16,c_322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:37:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.29  
% 2.05/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.29  %$ k3_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.05/1.29  
% 2.05/1.29  %Foreground sorts:
% 2.05/1.29  
% 2.05/1.29  
% 2.05/1.29  %Background operators:
% 2.05/1.29  
% 2.05/1.29  
% 2.05/1.29  %Foreground operators:
% 2.05/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.29  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.05/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.29  
% 2.05/1.30  tff(f_56, negated_conjecture, ~(![A, B]: ((k3_zfmisc_1(A, A, A) = k3_zfmisc_1(B, B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_mcart_1)).
% 2.05/1.30  tff(f_51, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_mcart_1)).
% 2.05/1.30  tff(f_37, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 2.05/1.30  tff(c_16, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.05/1.30  tff(c_18, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.05/1.30  tff(c_92, plain, (![A_24, C_21, D_22, F_20, B_19, E_23]: (F_20=C_21 | k1_xboole_0=C_21 | k1_xboole_0=B_19 | k1_xboole_0=A_24 | k3_zfmisc_1(D_22, E_23, F_20)!=k3_zfmisc_1(A_24, B_19, C_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.30  tff(c_95, plain, (![C_21, B_19, A_24]: (C_21='#skF_2' | k1_xboole_0=C_21 | k1_xboole_0=B_19 | k1_xboole_0=A_24 | k3_zfmisc_1(A_24, B_19, C_21)!=k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_92])).
% 2.05/1.30  tff(c_122, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_95])).
% 2.05/1.30  tff(c_123, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_16, c_122])).
% 2.05/1.30  tff(c_139, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_123])).
% 2.05/1.30  tff(c_6, plain, (![A_1, C_3]: (k3_zfmisc_1(A_1, k1_xboole_0, C_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.30  tff(c_144, plain, (![A_1, C_3]: (k3_zfmisc_1(A_1, '#skF_1', C_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_139, c_6])).
% 2.05/1.30  tff(c_68, plain, (![A_16, B_17, C_18]: (k3_zfmisc_1(A_16, B_17, C_18)!=k1_xboole_0 | k1_xboole_0=C_18 | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.30  tff(c_71, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_18, c_68])).
% 2.05/1.30  tff(c_87, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_71])).
% 2.05/1.30  tff(c_142, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_87])).
% 2.05/1.30  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_142])).
% 2.05/1.30  tff(c_238, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_123])).
% 2.05/1.30  tff(c_237, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_123])).
% 2.05/1.30  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_238, c_237])).
% 2.05/1.30  tff(c_258, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_71])).
% 2.05/1.30  tff(c_2, plain, (![A_1, B_2, C_3]: (k3_zfmisc_1(A_1, B_2, C_3)!=k1_xboole_0 | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.30  tff(c_266, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_258, c_2])).
% 2.05/1.30  tff(c_257, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_71])).
% 2.05/1.30  tff(c_322, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_266, c_266, c_266, c_257])).
% 2.05/1.30  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_16, c_16, c_322])).
% 2.05/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.30  
% 2.05/1.30  Inference rules
% 2.05/1.30  ----------------------
% 2.05/1.30  #Ref     : 4
% 2.05/1.30  #Sup     : 73
% 2.05/1.30  #Fact    : 0
% 2.05/1.30  #Define  : 0
% 2.05/1.30  #Split   : 3
% 2.05/1.30  #Chain   : 0
% 2.05/1.30  #Close   : 0
% 2.05/1.30  
% 2.05/1.30  Ordering : KBO
% 2.05/1.30  
% 2.05/1.30  Simplification rules
% 2.05/1.30  ----------------------
% 2.05/1.30  #Subsume      : 11
% 2.05/1.30  #Demod        : 61
% 2.05/1.30  #Tautology    : 56
% 2.05/1.30  #SimpNegUnit  : 5
% 2.05/1.30  #BackRed      : 23
% 2.05/1.30  
% 2.05/1.30  #Partial instantiations: 0
% 2.05/1.30  #Strategies tried      : 1
% 2.05/1.30  
% 2.05/1.30  Timing (in seconds)
% 2.05/1.30  ----------------------
% 2.05/1.30  Preprocessing        : 0.27
% 2.05/1.30  Parsing              : 0.15
% 2.05/1.30  CNF conversion       : 0.02
% 2.05/1.30  Main loop            : 0.20
% 2.05/1.30  Inferencing          : 0.06
% 2.05/1.30  Reduction            : 0.05
% 2.05/1.30  Demodulation         : 0.03
% 2.05/1.30  BG Simplification    : 0.01
% 2.05/1.30  Subsumption          : 0.06
% 2.05/1.30  Abstraction          : 0.01
% 2.05/1.30  MUC search           : 0.00
% 2.05/1.30  Cooper               : 0.00
% 2.05/1.30  Total                : 0.50
% 2.05/1.30  Index Insertion      : 0.00
% 2.05/1.30  Index Deletion       : 0.00
% 2.05/1.30  Index Matching       : 0.00
% 2.05/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
