%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:52 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   27 (  78 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 ( 206 expanded)
%              Number of equality atoms :   53 ( 204 expanded)
%              Maximal formula depth    :   14 (   5 average)
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

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_52,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
     => ( k4_zfmisc_1(A,B,C,D) = k1_xboole_0
        | ( A = E
          & B = F
          & C = G
          & D = H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

tff(c_20,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

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

tff(c_132,plain,(
    ! [D_29,G_31,C_33,H_35,F_30,B_32,E_36,A_34] :
      ( F_30 = B_32
      | k4_zfmisc_1(A_34,B_32,C_33,D_29) = k1_xboole_0
      | k4_zfmisc_1(E_36,F_30,G_31,H_35) != k4_zfmisc_1(A_34,B_32,C_33,D_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_138,plain,(
    ! [F_30,E_36,G_31,H_35] :
      ( F_30 = '#skF_2'
      | k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k1_xboole_0
      | k4_zfmisc_1(E_36,F_30,G_31,H_35) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_132])).

tff(c_163,plain,(
    ! [F_30,E_36,G_31,H_35] :
      ( F_30 = '#skF_2'
      | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0
      | k4_zfmisc_1(E_36,F_30,G_31,H_35) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_138])).

tff(c_164,plain,(
    ! [F_30,E_36,G_31,H_35] :
      ( F_30 = '#skF_2'
      | k4_zfmisc_1(E_36,F_30,G_31,H_35) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_163])).

tff(c_171,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_164])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_171])).

tff(c_175,plain,(
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

tff(c_183,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_2])).

tff(c_174,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_280,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_183,c_183,c_183,c_174])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_20,c_20,c_280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:15:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.18  
% 1.60/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.18  %$ k4_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.88/1.18  
% 1.88/1.18  %Foreground sorts:
% 1.88/1.18  
% 1.88/1.18  
% 1.88/1.18  %Background operators:
% 1.88/1.18  
% 1.88/1.18  
% 1.88/1.18  %Foreground operators:
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.18  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 1.88/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.18  
% 1.88/1.19  tff(f_57, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_mcart_1)).
% 1.88/1.19  tff(f_40, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 1.88/1.19  tff(f_52, axiom, (![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => ((k4_zfmisc_1(A, B, C, D) = k1_xboole_0) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_mcart_1)).
% 1.88/1.19  tff(c_20, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.19  tff(c_22, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.19  tff(c_103, plain, (![A_25, B_26, C_27, D_28]: (k4_zfmisc_1(A_25, B_26, C_27, D_28)!=k1_xboole_0 | k1_xboole_0=D_28 | k1_xboole_0=C_27 | k1_xboole_0=B_26 | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.88/1.19  tff(c_106, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_22, c_103])).
% 1.88/1.19  tff(c_127, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_106])).
% 1.88/1.19  tff(c_132, plain, (![D_29, G_31, C_33, H_35, F_30, B_32, E_36, A_34]: (F_30=B_32 | k4_zfmisc_1(A_34, B_32, C_33, D_29)=k1_xboole_0 | k4_zfmisc_1(E_36, F_30, G_31, H_35)!=k4_zfmisc_1(A_34, B_32, C_33, D_29))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.19  tff(c_138, plain, (![F_30, E_36, G_31, H_35]: (F_30='#skF_2' | k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k1_xboole_0 | k4_zfmisc_1(E_36, F_30, G_31, H_35)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_132])).
% 1.88/1.19  tff(c_163, plain, (![F_30, E_36, G_31, H_35]: (F_30='#skF_2' | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0 | k4_zfmisc_1(E_36, F_30, G_31, H_35)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_138])).
% 1.88/1.19  tff(c_164, plain, (![F_30, E_36, G_31, H_35]: (F_30='#skF_2' | k4_zfmisc_1(E_36, F_30, G_31, H_35)!=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_127, c_163])).
% 1.88/1.19  tff(c_171, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_164])).
% 1.88/1.19  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_171])).
% 1.88/1.19  tff(c_175, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_106])).
% 1.88/1.19  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k4_zfmisc_1(A_1, B_2, C_3, D_4)!=k1_xboole_0 | k1_xboole_0=D_4 | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.88/1.19  tff(c_183, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_175, c_2])).
% 1.88/1.19  tff(c_174, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_106])).
% 1.88/1.19  tff(c_280, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_183, c_183, c_183, c_183, c_174])).
% 1.88/1.19  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_20, c_20, c_20, c_280])).
% 1.88/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  Inference rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Ref     : 3
% 1.88/1.19  #Sup     : 64
% 1.88/1.19  #Fact    : 0
% 1.88/1.19  #Define  : 0
% 1.88/1.19  #Split   : 1
% 1.88/1.19  #Chain   : 0
% 1.88/1.19  #Close   : 0
% 1.88/1.19  
% 1.88/1.19  Ordering : KBO
% 1.88/1.19  
% 1.88/1.19  Simplification rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Subsume      : 0
% 1.88/1.19  #Demod        : 31
% 1.88/1.19  #Tautology    : 63
% 1.88/1.19  #SimpNegUnit  : 3
% 1.88/1.19  #BackRed      : 7
% 1.88/1.19  
% 1.88/1.19  #Partial instantiations: 0
% 1.88/1.19  #Strategies tried      : 1
% 1.88/1.19  
% 1.88/1.19  Timing (in seconds)
% 1.88/1.19  ----------------------
% 1.88/1.19  Preprocessing        : 0.27
% 1.88/1.19  Parsing              : 0.14
% 1.88/1.19  CNF conversion       : 0.02
% 1.88/1.19  Main loop            : 0.16
% 1.88/1.19  Inferencing          : 0.05
% 1.88/1.19  Reduction            : 0.05
% 1.88/1.19  Demodulation         : 0.03
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.04
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.45
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
