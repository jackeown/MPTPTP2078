%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:52 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 120 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :   73 ( 377 expanded)
%              Number of equality atoms :   70 ( 374 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_58,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | D = k1_xboole_0
        | ( A = E
          & B = F
          & C = G
          & D = H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(c_20,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_210,plain,(
    ! [A_50,F_46,D_45,E_52,G_47,C_49,H_51,B_48] :
      ( E_52 = A_50
      | k1_xboole_0 = D_45
      | k1_xboole_0 = C_49
      | k1_xboole_0 = B_48
      | k1_xboole_0 = A_50
      | k4_zfmisc_1(E_52,F_46,G_47,H_51) != k4_zfmisc_1(A_50,B_48,C_49,D_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_216,plain,(
    ! [E_52,F_46,G_47,H_51] :
      ( E_52 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k4_zfmisc_1(E_52,F_46,G_47,H_51) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_210])).

tff(c_284,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_10,plain,(
    ! [B_2,C_3,D_4] : k4_zfmisc_1(k1_xboole_0,B_2,C_3,D_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_291,plain,(
    ! [B_2,C_3,D_4] : k4_zfmisc_1('#skF_2',B_2,C_3,D_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_284,c_10])).

tff(c_299,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_22])).

tff(c_103,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( k4_zfmisc_1(A_25,B_26,C_27,D_28) != k1_xboole_0
      | k1_xboole_0 = D_28
      | k1_xboole_0 = C_27
      | k1_xboole_0 = B_26
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_106,plain,
    ( k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_103])).

tff(c_127,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_289,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_127])).

tff(c_382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_289])).

tff(c_384,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_383,plain,(
    ! [E_52,F_46,G_47,H_51] :
      ( k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | E_52 = '#skF_2'
      | k4_zfmisc_1(E_52,F_46,G_47,H_51) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_385,plain,(
    ! [E_52,F_46,G_47,H_51] :
      ( E_52 = '#skF_2'
      | k4_zfmisc_1(E_52,F_46,G_47,H_51) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_384,c_384,c_384,c_383])).

tff(c_388,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_385])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_388])).

tff(c_392,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( k4_zfmisc_1(A_1,B_2,C_3,D_4) != k1_xboole_0
      | k1_xboole_0 = D_4
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_400,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_2])).

tff(c_391,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_461,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_400,c_400,c_400,c_391])).

tff(c_462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_20,c_20,c_461])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.35  
% 2.40/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.36  %$ k4_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.40/1.36  
% 2.40/1.36  %Foreground sorts:
% 2.40/1.36  
% 2.40/1.36  
% 2.40/1.36  %Background operators:
% 2.40/1.36  
% 2.40/1.36  
% 2.40/1.36  %Foreground operators:
% 2.40/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.36  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.40/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.36  
% 2.67/1.37  tff(f_63, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_mcart_1)).
% 2.67/1.37  tff(f_58, axiom, (![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_mcart_1)).
% 2.67/1.37  tff(f_40, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 2.67/1.37  tff(c_20, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.67/1.37  tff(c_22, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.67/1.37  tff(c_210, plain, (![A_50, F_46, D_45, E_52, G_47, C_49, H_51, B_48]: (E_52=A_50 | k1_xboole_0=D_45 | k1_xboole_0=C_49 | k1_xboole_0=B_48 | k1_xboole_0=A_50 | k4_zfmisc_1(E_52, F_46, G_47, H_51)!=k4_zfmisc_1(A_50, B_48, C_49, D_45))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.67/1.37  tff(c_216, plain, (![E_52, F_46, G_47, H_51]: (E_52='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k4_zfmisc_1(E_52, F_46, G_47, H_51)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_210])).
% 2.67/1.37  tff(c_284, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_216])).
% 2.67/1.37  tff(c_10, plain, (![B_2, C_3, D_4]: (k4_zfmisc_1(k1_xboole_0, B_2, C_3, D_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.37  tff(c_291, plain, (![B_2, C_3, D_4]: (k4_zfmisc_1('#skF_2', B_2, C_3, D_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_284, c_10])).
% 2.67/1.37  tff(c_299, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_291, c_22])).
% 2.67/1.37  tff(c_103, plain, (![A_25, B_26, C_27, D_28]: (k4_zfmisc_1(A_25, B_26, C_27, D_28)!=k1_xboole_0 | k1_xboole_0=D_28 | k1_xboole_0=C_27 | k1_xboole_0=B_26 | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.37  tff(c_106, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_22, c_103])).
% 2.67/1.37  tff(c_127, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_106])).
% 2.67/1.37  tff(c_289, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_284, c_127])).
% 2.67/1.37  tff(c_382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_299, c_289])).
% 2.67/1.37  tff(c_384, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_216])).
% 2.67/1.37  tff(c_383, plain, (![E_52, F_46, G_47, H_51]: (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | E_52='#skF_2' | k4_zfmisc_1(E_52, F_46, G_47, H_51)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(splitRight, [status(thm)], [c_216])).
% 2.67/1.37  tff(c_385, plain, (![E_52, F_46, G_47, H_51]: (E_52='#skF_2' | k4_zfmisc_1(E_52, F_46, G_47, H_51)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_384, c_384, c_384, c_383])).
% 2.67/1.37  tff(c_388, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_385])).
% 2.67/1.37  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_388])).
% 2.67/1.37  tff(c_392, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_106])).
% 2.67/1.37  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k4_zfmisc_1(A_1, B_2, C_3, D_4)!=k1_xboole_0 | k1_xboole_0=D_4 | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.37  tff(c_400, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_392, c_2])).
% 2.67/1.37  tff(c_391, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_106])).
% 2.67/1.37  tff(c_461, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_400, c_400, c_400, c_400, c_391])).
% 2.67/1.37  tff(c_462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_20, c_20, c_20, c_461])).
% 2.67/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.37  
% 2.67/1.37  Inference rules
% 2.67/1.37  ----------------------
% 2.67/1.37  #Ref     : 6
% 2.67/1.37  #Sup     : 110
% 2.67/1.37  #Fact    : 0
% 2.67/1.37  #Define  : 0
% 2.67/1.37  #Split   : 2
% 2.67/1.37  #Chain   : 0
% 2.67/1.37  #Close   : 0
% 2.67/1.37  
% 2.67/1.37  Ordering : KBO
% 2.67/1.37  
% 2.67/1.37  Simplification rules
% 2.67/1.37  ----------------------
% 2.67/1.37  #Subsume      : 21
% 2.67/1.37  #Demod        : 61
% 2.67/1.37  #Tautology    : 84
% 2.67/1.37  #SimpNegUnit  : 3
% 2.67/1.37  #BackRed      : 19
% 2.67/1.37  
% 2.67/1.37  #Partial instantiations: 0
% 2.67/1.37  #Strategies tried      : 1
% 2.67/1.37  
% 2.67/1.37  Timing (in seconds)
% 2.67/1.37  ----------------------
% 2.67/1.37  Preprocessing        : 0.27
% 2.67/1.37  Parsing              : 0.15
% 2.67/1.37  CNF conversion       : 0.02
% 2.67/1.37  Main loop            : 0.28
% 2.67/1.37  Inferencing          : 0.08
% 2.67/1.37  Reduction            : 0.06
% 2.67/1.37  Demodulation         : 0.04
% 2.67/1.37  BG Simplification    : 0.02
% 2.67/1.37  Subsumption          : 0.12
% 2.67/1.37  Abstraction          : 0.01
% 2.67/1.37  MUC search           : 0.00
% 2.67/1.37  Cooper               : 0.00
% 2.67/1.37  Total                : 0.58
% 2.67/1.37  Index Insertion      : 0.00
% 2.67/1.37  Index Deletion       : 0.00
% 2.67/1.37  Index Matching       : 0.00
% 2.67/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
