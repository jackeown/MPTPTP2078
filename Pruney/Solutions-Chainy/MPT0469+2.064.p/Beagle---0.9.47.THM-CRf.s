%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:00 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   43 (  72 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  88 expanded)
%              Number of equality atoms :   21 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_32,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_753,plain,(
    ! [A_94,B_95] :
      ( r2_hidden(k4_tarski('#skF_6'(A_94,B_95),'#skF_5'(A_94,B_95)),A_94)
      | r2_hidden('#skF_7'(A_94,B_95),B_95)
      | k2_relat_1(A_94) = B_95 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [B_45,A_46] :
      ( ~ r2_hidden(B_45,A_46)
      | k4_xboole_0(A_46,k1_tarski(B_45)) != A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [B_45] : ~ r2_hidden(B_45,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_1109,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_106),B_106)
      | k2_relat_1(k1_xboole_0) = B_106 ) ),
    inference(resolution,[status(thm)],[c_753,c_69])).

tff(c_1270,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1109,c_69])).

tff(c_79,plain,(
    ! [C_56,A_57] :
      ( r2_hidden(k4_tarski(C_56,'#skF_4'(A_57,k1_relat_1(A_57),C_56)),A_57)
      | ~ r2_hidden(C_56,k1_relat_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_91,plain,(
    ! [C_56] : ~ r2_hidden(C_56,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_79,c_69])).

tff(c_1269,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1109,c_91])).

tff(c_1301,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1270,c_1269])).

tff(c_1302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1301])).

tff(c_1303,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1809,plain,(
    ! [A_155,B_156] :
      ( r2_hidden(k4_tarski('#skF_6'(A_155,B_156),'#skF_5'(A_155,B_156)),A_155)
      | r2_hidden('#skF_7'(A_155,B_156),B_156)
      | k2_relat_1(A_155) = B_156 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1328,plain,(
    ! [B_112,A_113] :
      ( ~ r2_hidden(B_112,A_113)
      | k4_xboole_0(A_113,k1_tarski(B_112)) != A_113 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1337,plain,(
    ! [B_112] : ~ r2_hidden(B_112,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1328])).

tff(c_1923,plain,(
    ! [B_157] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_157),B_157)
      | k2_relat_1(k1_xboole_0) = B_157 ) ),
    inference(resolution,[status(thm)],[c_1809,c_1337])).

tff(c_2007,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1923,c_1337])).

tff(c_2032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1303,c_2007])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:11:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.54  
% 3.46/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.54  %$ r2_hidden > k4_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5
% 3.46/1.54  
% 3.46/1.54  %Foreground sorts:
% 3.46/1.54  
% 3.46/1.54  
% 3.46/1.54  %Background operators:
% 3.46/1.54  
% 3.46/1.54  
% 3.46/1.54  %Foreground operators:
% 3.46/1.54  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.46/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.46/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.46/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.46/1.54  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.46/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.46/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.46/1.54  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.46/1.54  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.46/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.46/1.54  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.46/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.46/1.54  
% 3.46/1.55  tff(f_52, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.46/1.55  tff(f_48, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 3.46/1.55  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.46/1.55  tff(f_32, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.46/1.55  tff(f_40, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.46/1.55  tff(c_32, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.55  tff(c_40, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 3.46/1.55  tff(c_753, plain, (![A_94, B_95]: (r2_hidden(k4_tarski('#skF_6'(A_94, B_95), '#skF_5'(A_94, B_95)), A_94) | r2_hidden('#skF_7'(A_94, B_95), B_95) | k2_relat_1(A_94)=B_95)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.46/1.55  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.46/1.55  tff(c_60, plain, (![B_45, A_46]: (~r2_hidden(B_45, A_46) | k4_xboole_0(A_46, k1_tarski(B_45))!=A_46)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.46/1.55  tff(c_69, plain, (![B_45]: (~r2_hidden(B_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_60])).
% 3.46/1.55  tff(c_1109, plain, (![B_106]: (r2_hidden('#skF_7'(k1_xboole_0, B_106), B_106) | k2_relat_1(k1_xboole_0)=B_106)), inference(resolution, [status(thm)], [c_753, c_69])).
% 3.46/1.55  tff(c_1270, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1109, c_69])).
% 3.46/1.55  tff(c_79, plain, (![C_56, A_57]: (r2_hidden(k4_tarski(C_56, '#skF_4'(A_57, k1_relat_1(A_57), C_56)), A_57) | ~r2_hidden(C_56, k1_relat_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.46/1.55  tff(c_91, plain, (![C_56]: (~r2_hidden(C_56, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_79, c_69])).
% 3.46/1.55  tff(c_1269, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_1109, c_91])).
% 3.46/1.55  tff(c_1301, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1270, c_1269])).
% 3.46/1.55  tff(c_1302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1301])).
% 3.46/1.55  tff(c_1303, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.46/1.55  tff(c_1809, plain, (![A_155, B_156]: (r2_hidden(k4_tarski('#skF_6'(A_155, B_156), '#skF_5'(A_155, B_156)), A_155) | r2_hidden('#skF_7'(A_155, B_156), B_156) | k2_relat_1(A_155)=B_156)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.46/1.55  tff(c_1328, plain, (![B_112, A_113]: (~r2_hidden(B_112, A_113) | k4_xboole_0(A_113, k1_tarski(B_112))!=A_113)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.46/1.55  tff(c_1337, plain, (![B_112]: (~r2_hidden(B_112, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1328])).
% 3.46/1.55  tff(c_1923, plain, (![B_157]: (r2_hidden('#skF_7'(k1_xboole_0, B_157), B_157) | k2_relat_1(k1_xboole_0)=B_157)), inference(resolution, [status(thm)], [c_1809, c_1337])).
% 3.46/1.55  tff(c_2007, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1923, c_1337])).
% 3.46/1.55  tff(c_2032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1303, c_2007])).
% 3.46/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.55  
% 3.46/1.55  Inference rules
% 3.46/1.55  ----------------------
% 3.46/1.55  #Ref     : 0
% 3.46/1.55  #Sup     : 386
% 3.46/1.55  #Fact    : 0
% 3.46/1.55  #Define  : 0
% 3.46/1.55  #Split   : 1
% 3.46/1.55  #Chain   : 0
% 3.46/1.55  #Close   : 0
% 3.46/1.55  
% 3.46/1.55  Ordering : KBO
% 3.46/1.55  
% 3.46/1.55  Simplification rules
% 3.46/1.55  ----------------------
% 3.46/1.55  #Subsume      : 124
% 3.46/1.55  #Demod        : 31
% 3.46/1.55  #Tautology    : 22
% 3.46/1.55  #SimpNegUnit  : 4
% 3.46/1.55  #BackRed      : 16
% 3.46/1.55  
% 3.46/1.55  #Partial instantiations: 0
% 3.46/1.55  #Strategies tried      : 1
% 3.46/1.55  
% 3.46/1.55  Timing (in seconds)
% 3.46/1.55  ----------------------
% 3.46/1.56  Preprocessing        : 0.28
% 3.46/1.56  Parsing              : 0.14
% 3.46/1.56  CNF conversion       : 0.03
% 3.46/1.56  Main loop            : 0.51
% 3.46/1.56  Inferencing          : 0.19
% 3.46/1.56  Reduction            : 0.14
% 3.46/1.56  Demodulation         : 0.07
% 3.46/1.56  BG Simplification    : 0.02
% 3.46/1.56  Subsumption          : 0.11
% 3.46/1.56  Abstraction          : 0.03
% 3.46/1.56  MUC search           : 0.00
% 3.46/1.56  Cooper               : 0.00
% 3.46/1.56  Total                : 0.81
% 3.46/1.56  Index Insertion      : 0.00
% 3.46/1.56  Index Deletion       : 0.00
% 3.46/1.56  Index Matching       : 0.00
% 3.46/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
