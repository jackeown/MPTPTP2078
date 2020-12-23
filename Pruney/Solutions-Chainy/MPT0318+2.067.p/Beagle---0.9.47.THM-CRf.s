%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:10 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  74 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,k3_xboole_0(A_52,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    ! [A_8,C_54] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_54,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_78,plain,(
    ! [C_54] : ~ r2_hidden(C_54,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_75])).

tff(c_38,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_92,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_121,plain,(
    ! [C_71,B_72,D_73] :
      ( r2_hidden(k4_tarski(C_71,B_72),k2_zfmisc_1(k1_tarski(C_71),D_73))
      | ~ r2_hidden(B_72,D_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_131,plain,(
    ! [B_72] :
      ( r2_hidden(k4_tarski('#skF_4',B_72),k1_xboole_0)
      | ~ r2_hidden(B_72,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_121])).

tff(c_136,plain,(
    ! [B_74] : ~ r2_hidden(B_74,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_131])).

tff(c_140,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_140])).

tff(c_145,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_224,plain,(
    ! [A_102,D_103,C_104] :
      ( r2_hidden(k4_tarski(A_102,D_103),k2_zfmisc_1(C_104,k1_tarski(D_103)))
      | ~ r2_hidden(A_102,C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_237,plain,(
    ! [A_102] :
      ( r2_hidden(k4_tarski(A_102,'#skF_4'),k1_xboole_0)
      | ~ r2_hidden(A_102,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_224])).

tff(c_243,plain,(
    ! [A_105] : ~ r2_hidden(A_105,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_237])).

tff(c_247,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_243])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:23:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.69  
% 2.49/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.70  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.49/1.70  
% 2.49/1.70  %Foreground sorts:
% 2.49/1.70  
% 2.49/1.70  
% 2.49/1.70  %Background operators:
% 2.49/1.70  
% 2.49/1.70  
% 2.49/1.70  %Foreground operators:
% 2.49/1.70  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.49/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.70  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.49/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.49/1.70  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.70  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.70  
% 2.67/1.71  tff(f_87, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.67/1.71  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.67/1.71  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.67/1.71  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.67/1.71  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.67/1.71  tff(f_71, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.67/1.71  tff(f_77, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.67/1.71  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.67/1.71  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.67/1.71  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.67/1.71  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.67/1.71  tff(c_68, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, k3_xboole_0(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.67/1.71  tff(c_75, plain, (![A_8, C_54]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_68])).
% 2.67/1.71  tff(c_78, plain, (![C_54]: (~r2_hidden(C_54, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_75])).
% 2.67/1.71  tff(c_38, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.67/1.71  tff(c_92, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 2.67/1.71  tff(c_121, plain, (![C_71, B_72, D_73]: (r2_hidden(k4_tarski(C_71, B_72), k2_zfmisc_1(k1_tarski(C_71), D_73)) | ~r2_hidden(B_72, D_73))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.67/1.71  tff(c_131, plain, (![B_72]: (r2_hidden(k4_tarski('#skF_4', B_72), k1_xboole_0) | ~r2_hidden(B_72, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_121])).
% 2.67/1.71  tff(c_136, plain, (![B_74]: (~r2_hidden(B_74, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_78, c_131])).
% 2.67/1.71  tff(c_140, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_136])).
% 2.67/1.71  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_140])).
% 2.67/1.71  tff(c_145, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.67/1.71  tff(c_224, plain, (![A_102, D_103, C_104]: (r2_hidden(k4_tarski(A_102, D_103), k2_zfmisc_1(C_104, k1_tarski(D_103))) | ~r2_hidden(A_102, C_104))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.67/1.71  tff(c_237, plain, (![A_102]: (r2_hidden(k4_tarski(A_102, '#skF_4'), k1_xboole_0) | ~r2_hidden(A_102, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_224])).
% 2.67/1.71  tff(c_243, plain, (![A_105]: (~r2_hidden(A_105, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_78, c_237])).
% 2.67/1.71  tff(c_247, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_243])).
% 2.67/1.71  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_247])).
% 2.67/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.71  
% 2.67/1.71  Inference rules
% 2.67/1.71  ----------------------
% 2.67/1.71  #Ref     : 0
% 2.67/1.71  #Sup     : 43
% 2.67/1.71  #Fact    : 0
% 2.67/1.71  #Define  : 0
% 2.67/1.71  #Split   : 2
% 2.67/1.71  #Chain   : 0
% 2.67/1.71  #Close   : 0
% 2.67/1.71  
% 2.67/1.71  Ordering : KBO
% 2.67/1.71  
% 2.67/1.71  Simplification rules
% 2.67/1.71  ----------------------
% 2.67/1.71  #Subsume      : 4
% 2.67/1.71  #Demod        : 4
% 2.67/1.71  #Tautology    : 28
% 2.67/1.72  #SimpNegUnit  : 6
% 2.67/1.72  #BackRed      : 0
% 2.67/1.72  
% 2.67/1.72  #Partial instantiations: 0
% 2.67/1.72  #Strategies tried      : 1
% 2.67/1.72  
% 2.67/1.72  Timing (in seconds)
% 2.67/1.72  ----------------------
% 2.67/1.72  Preprocessing        : 0.52
% 2.67/1.72  Parsing              : 0.26
% 2.67/1.72  CNF conversion       : 0.04
% 2.67/1.72  Main loop            : 0.28
% 2.67/1.72  Inferencing          : 0.11
% 2.67/1.72  Reduction            : 0.08
% 2.67/1.72  Demodulation         : 0.05
% 2.67/1.72  BG Simplification    : 0.02
% 2.67/1.72  Subsumption          : 0.04
% 2.67/1.72  Abstraction          : 0.01
% 2.67/1.72  MUC search           : 0.00
% 2.67/1.72  Cooper               : 0.00
% 2.67/1.72  Total                : 0.84
% 2.67/1.72  Index Insertion      : 0.00
% 2.67/1.72  Index Deletion       : 0.00
% 2.67/1.72  Index Matching       : 0.00
% 2.67/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
