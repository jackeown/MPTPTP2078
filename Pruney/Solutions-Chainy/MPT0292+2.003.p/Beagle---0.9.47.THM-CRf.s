%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:35 EST 2020

% Result     : Theorem 5.69s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :   46 (  47 expanded)
%              Number of leaves         :   29 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  52 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_129,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_143,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(c_84,plain,(
    ! [A_46] : r1_tarski(k1_tarski(A_46),k1_zfmisc_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_34,plain,(
    ! [C_25] : r2_hidden(C_25,k1_tarski(C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_408,plain,(
    ! [C_105,B_106,A_107] :
      ( r2_hidden(C_105,B_106)
      | ~ r2_hidden(C_105,A_107)
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_421,plain,(
    ! [C_108,B_109] :
      ( r2_hidden(C_108,B_109)
      | ~ r1_tarski(k1_tarski(C_108),B_109) ) ),
    inference(resolution,[status(thm)],[c_34,c_408])).

tff(c_442,plain,(
    ! [A_46] : r2_hidden(A_46,k1_zfmisc_1(A_46)) ),
    inference(resolution,[status(thm)],[c_84,c_421])).

tff(c_397,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_6'(A_103,B_104),A_103)
      | r1_tarski(k3_tarski(A_103),B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_46,plain,(
    ! [C_31,A_27] :
      ( r1_tarski(C_31,A_27)
      | ~ r2_hidden(C_31,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4840,plain,(
    ! [A_357,B_358] :
      ( r1_tarski('#skF_6'(k1_zfmisc_1(A_357),B_358),A_357)
      | r1_tarski(k3_tarski(k1_zfmisc_1(A_357)),B_358) ) ),
    inference(resolution,[status(thm)],[c_397,c_46])).

tff(c_88,plain,(
    ! [A_49,B_50] :
      ( ~ r1_tarski('#skF_6'(A_49,B_50),B_50)
      | r1_tarski(k3_tarski(A_49),B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4881,plain,(
    ! [A_359] : r1_tarski(k3_tarski(k1_zfmisc_1(A_359)),A_359) ),
    inference(resolution,[status(thm)],[c_4840,c_88])).

tff(c_86,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,k3_tarski(B_48))
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_311,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(B_94,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_330,plain,(
    ! [B_48,A_47] :
      ( k3_tarski(B_48) = A_47
      | ~ r1_tarski(k3_tarski(B_48),A_47)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_86,c_311])).

tff(c_4888,plain,(
    ! [A_359] :
      ( k3_tarski(k1_zfmisc_1(A_359)) = A_359
      | ~ r2_hidden(A_359,k1_zfmisc_1(A_359)) ) ),
    inference(resolution,[status(thm)],[c_4881,c_330])).

tff(c_4907,plain,(
    ! [A_359] : k3_tarski(k1_zfmisc_1(A_359)) = A_359 ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_4888])).

tff(c_92,plain,(
    k3_tarski(k1_zfmisc_1('#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4946,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4907,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.69/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.06  
% 5.69/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.06  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 5.69/2.06  
% 5.69/2.06  %Foreground sorts:
% 5.69/2.06  
% 5.69/2.06  
% 5.69/2.06  %Background operators:
% 5.69/2.06  
% 5.69/2.06  
% 5.69/2.06  %Foreground operators:
% 5.69/2.06  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.69/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.69/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.69/2.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.69/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.69/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.69/2.06  tff('#skF_7', type, '#skF_7': $i).
% 5.69/2.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.69/2.06  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.69/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.69/2.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.69/2.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.69/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.69/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.69/2.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.69/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.69/2.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.69/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.69/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.69/2.06  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.69/2.06  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.69/2.06  
% 5.76/2.07  tff(f_129, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 5.76/2.07  tff(f_79, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.76/2.07  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.76/2.07  tff(f_140, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 5.76/2.07  tff(f_88, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.76/2.07  tff(f_133, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 5.76/2.07  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.76/2.07  tff(f_143, negated_conjecture, ~(![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 5.76/2.07  tff(c_84, plain, (![A_46]: (r1_tarski(k1_tarski(A_46), k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.76/2.07  tff(c_34, plain, (![C_25]: (r2_hidden(C_25, k1_tarski(C_25)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.76/2.07  tff(c_408, plain, (![C_105, B_106, A_107]: (r2_hidden(C_105, B_106) | ~r2_hidden(C_105, A_107) | ~r1_tarski(A_107, B_106))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.76/2.07  tff(c_421, plain, (![C_108, B_109]: (r2_hidden(C_108, B_109) | ~r1_tarski(k1_tarski(C_108), B_109))), inference(resolution, [status(thm)], [c_34, c_408])).
% 5.76/2.07  tff(c_442, plain, (![A_46]: (r2_hidden(A_46, k1_zfmisc_1(A_46)))), inference(resolution, [status(thm)], [c_84, c_421])).
% 5.76/2.07  tff(c_397, plain, (![A_103, B_104]: (r2_hidden('#skF_6'(A_103, B_104), A_103) | r1_tarski(k3_tarski(A_103), B_104))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.76/2.07  tff(c_46, plain, (![C_31, A_27]: (r1_tarski(C_31, A_27) | ~r2_hidden(C_31, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.76/2.07  tff(c_4840, plain, (![A_357, B_358]: (r1_tarski('#skF_6'(k1_zfmisc_1(A_357), B_358), A_357) | r1_tarski(k3_tarski(k1_zfmisc_1(A_357)), B_358))), inference(resolution, [status(thm)], [c_397, c_46])).
% 5.76/2.07  tff(c_88, plain, (![A_49, B_50]: (~r1_tarski('#skF_6'(A_49, B_50), B_50) | r1_tarski(k3_tarski(A_49), B_50))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.76/2.07  tff(c_4881, plain, (![A_359]: (r1_tarski(k3_tarski(k1_zfmisc_1(A_359)), A_359))), inference(resolution, [status(thm)], [c_4840, c_88])).
% 5.76/2.07  tff(c_86, plain, (![A_47, B_48]: (r1_tarski(A_47, k3_tarski(B_48)) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.76/2.07  tff(c_311, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(B_94, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.76/2.07  tff(c_330, plain, (![B_48, A_47]: (k3_tarski(B_48)=A_47 | ~r1_tarski(k3_tarski(B_48), A_47) | ~r2_hidden(A_47, B_48))), inference(resolution, [status(thm)], [c_86, c_311])).
% 5.76/2.07  tff(c_4888, plain, (![A_359]: (k3_tarski(k1_zfmisc_1(A_359))=A_359 | ~r2_hidden(A_359, k1_zfmisc_1(A_359)))), inference(resolution, [status(thm)], [c_4881, c_330])).
% 5.76/2.07  tff(c_4907, plain, (![A_359]: (k3_tarski(k1_zfmisc_1(A_359))=A_359)), inference(demodulation, [status(thm), theory('equality')], [c_442, c_4888])).
% 5.76/2.07  tff(c_92, plain, (k3_tarski(k1_zfmisc_1('#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.76/2.07  tff(c_4946, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4907, c_92])).
% 5.76/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.07  
% 5.76/2.07  Inference rules
% 5.76/2.07  ----------------------
% 5.76/2.07  #Ref     : 0
% 5.76/2.07  #Sup     : 1014
% 5.76/2.07  #Fact    : 0
% 5.76/2.07  #Define  : 0
% 5.76/2.07  #Split   : 1
% 5.76/2.07  #Chain   : 0
% 5.76/2.07  #Close   : 0
% 5.76/2.07  
% 5.76/2.07  Ordering : KBO
% 5.76/2.07  
% 5.76/2.07  Simplification rules
% 5.76/2.07  ----------------------
% 5.76/2.07  #Subsume      : 49
% 5.76/2.07  #Demod        : 405
% 5.76/2.07  #Tautology    : 341
% 5.76/2.07  #SimpNegUnit  : 83
% 5.76/2.07  #BackRed      : 21
% 5.76/2.07  
% 5.76/2.07  #Partial instantiations: 0
% 5.76/2.07  #Strategies tried      : 1
% 5.76/2.07  
% 5.76/2.07  Timing (in seconds)
% 5.76/2.07  ----------------------
% 5.76/2.07  Preprocessing        : 0.34
% 5.76/2.07  Parsing              : 0.17
% 5.76/2.07  CNF conversion       : 0.03
% 5.76/2.07  Main loop            : 0.98
% 5.76/2.07  Inferencing          : 0.32
% 5.76/2.07  Reduction            : 0.36
% 5.76/2.07  Demodulation         : 0.27
% 5.76/2.07  BG Simplification    : 0.04
% 5.76/2.07  Subsumption          : 0.19
% 5.76/2.07  Abstraction          : 0.04
% 5.76/2.07  MUC search           : 0.00
% 5.76/2.07  Cooper               : 0.00
% 5.76/2.07  Total                : 1.34
% 5.76/2.07  Index Insertion      : 0.00
% 5.76/2.07  Index Deletion       : 0.00
% 5.76/2.07  Index Matching       : 0.00
% 5.76/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
