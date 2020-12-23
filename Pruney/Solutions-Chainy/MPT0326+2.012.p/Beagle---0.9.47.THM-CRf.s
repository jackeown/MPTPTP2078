%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:29 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   47 (  99 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 ( 189 expanded)
%              Number of equality atoms :   23 (  59 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_20,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3'))
    | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_83,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_14,plain,(
    ! [A_4,C_6,B_5,D_7] :
      ( r1_tarski(A_4,C_6)
      | k2_zfmisc_1(A_4,B_5) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_4,B_5),k2_zfmisc_1(C_6,D_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_87,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_14])).

tff(c_88,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( k1_xboole_0 = B_3
      | k1_xboole_0 = A_2
      | k2_zfmisc_1(A_2,B_3) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_110,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_6])).

tff(c_112,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_120,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_2])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_120])).

tff(c_123,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_158,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_4])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_16])).

tff(c_172,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_182,plain,(
    ! [B_29,D_30,A_31,C_32] :
      ( r1_tarski(B_29,D_30)
      | k2_zfmisc_1(A_31,B_29) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_31,B_29),k2_zfmisc_1(C_32,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_185,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_182])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_16,c_185])).

tff(c_202,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_206,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_202,c_14])).

tff(c_209,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_206])).

tff(c_231,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_6])).

tff(c_233,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_240,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_4])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_16])).

tff(c_249,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_258,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_2])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.57  
% 2.35/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.57  %$ r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.35/1.57  
% 2.35/1.57  %Foreground sorts:
% 2.35/1.57  
% 2.35/1.57  
% 2.35/1.57  %Background operators:
% 2.35/1.57  
% 2.35/1.57  
% 2.35/1.57  %Foreground operators:
% 2.35/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.57  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.57  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.57  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.57  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.57  
% 2.35/1.59  tff(f_53, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.35/1.59  tff(f_42, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.35/1.59  tff(f_34, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.35/1.59  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.35/1.59  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.35/1.59  tff(c_20, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.35/1.59  tff(c_16, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.35/1.59  tff(c_18, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.35/1.59  tff(c_83, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_18])).
% 2.35/1.59  tff(c_14, plain, (![A_4, C_6, B_5, D_7]: (r1_tarski(A_4, C_6) | k2_zfmisc_1(A_4, B_5)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_4, B_5), k2_zfmisc_1(C_6, D_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.35/1.59  tff(c_87, plain, (r1_tarski('#skF_1', '#skF_3') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_83, c_14])).
% 2.35/1.59  tff(c_88, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_87])).
% 2.35/1.59  tff(c_6, plain, (![B_3, A_2]: (k1_xboole_0=B_3 | k1_xboole_0=A_2 | k2_zfmisc_1(A_2, B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.35/1.59  tff(c_110, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_88, c_6])).
% 2.35/1.59  tff(c_112, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_110])).
% 2.35/1.59  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.35/1.59  tff(c_120, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_2])).
% 2.35/1.59  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_120])).
% 2.35/1.59  tff(c_123, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_110])).
% 2.35/1.59  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.35/1.59  tff(c_158, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_4])).
% 2.35/1.59  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_16])).
% 2.35/1.59  tff(c_172, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_87])).
% 2.35/1.59  tff(c_182, plain, (![B_29, D_30, A_31, C_32]: (r1_tarski(B_29, D_30) | k2_zfmisc_1(A_31, B_29)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_31, B_29), k2_zfmisc_1(C_32, D_30)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.35/1.59  tff(c_185, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_83, c_182])).
% 2.35/1.59  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_16, c_185])).
% 2.35/1.59  tff(c_202, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_18])).
% 2.35/1.59  tff(c_206, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_202, c_14])).
% 2.35/1.59  tff(c_209, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_206])).
% 2.35/1.59  tff(c_231, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_209, c_6])).
% 2.35/1.59  tff(c_233, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_231])).
% 2.35/1.59  tff(c_240, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_4])).
% 2.35/1.59  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_240, c_16])).
% 2.35/1.59  tff(c_249, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_231])).
% 2.35/1.59  tff(c_258, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_2])).
% 2.35/1.59  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_258])).
% 2.35/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.59  
% 2.35/1.59  Inference rules
% 2.35/1.59  ----------------------
% 2.35/1.59  #Ref     : 0
% 2.35/1.59  #Sup     : 47
% 2.35/1.59  #Fact    : 0
% 2.35/1.59  #Define  : 0
% 2.35/1.59  #Split   : 4
% 2.35/1.59  #Chain   : 0
% 2.35/1.59  #Close   : 0
% 2.35/1.59  
% 2.35/1.59  Ordering : KBO
% 2.35/1.59  
% 2.35/1.59  Simplification rules
% 2.35/1.59  ----------------------
% 2.35/1.59  #Subsume      : 1
% 2.35/1.59  #Demod        : 94
% 2.35/1.59  #Tautology    : 33
% 2.35/1.59  #SimpNegUnit  : 4
% 2.35/1.59  #BackRed      : 38
% 2.35/1.59  
% 2.35/1.59  #Partial instantiations: 0
% 2.35/1.59  #Strategies tried      : 1
% 2.35/1.59  
% 2.35/1.59  Timing (in seconds)
% 2.35/1.59  ----------------------
% 2.35/1.60  Preprocessing        : 0.42
% 2.35/1.60  Parsing              : 0.23
% 2.35/1.60  CNF conversion       : 0.03
% 2.35/1.60  Main loop            : 0.30
% 2.35/1.60  Inferencing          : 0.10
% 2.35/1.60  Reduction            : 0.10
% 2.35/1.60  Demodulation         : 0.07
% 2.35/1.60  BG Simplification    : 0.02
% 2.35/1.60  Subsumption          : 0.06
% 2.35/1.60  Abstraction          : 0.01
% 2.35/1.60  MUC search           : 0.00
% 2.35/1.60  Cooper               : 0.00
% 2.35/1.60  Total                : 0.77
% 2.35/1.60  Index Insertion      : 0.00
% 2.35/1.60  Index Deletion       : 0.00
% 2.35/1.60  Index Matching       : 0.00
% 2.35/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
