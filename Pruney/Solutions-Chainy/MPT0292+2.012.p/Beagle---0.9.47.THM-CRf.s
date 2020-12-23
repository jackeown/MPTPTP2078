%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:36 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   45 (  46 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  48 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_69,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(c_154,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_3'(A_78,B_79),A_78)
      | r1_tarski(k3_tarski(A_78),B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [C_37,A_33] :
      ( r1_tarski(C_37,A_33)
      | ~ r2_hidden(C_37,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_191,plain,(
    ! [A_88,B_89] :
      ( r1_tarski('#skF_3'(k1_zfmisc_1(A_88),B_89),A_88)
      | r1_tarski(k3_tarski(k1_zfmisc_1(A_88)),B_89) ) ),
    inference(resolution,[status(thm)],[c_154,c_24])).

tff(c_40,plain,(
    ! [A_40,B_41] :
      ( ~ r1_tarski('#skF_3'(A_40,B_41),B_41)
      | r1_tarski(k3_tarski(A_40),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_203,plain,(
    ! [A_88] : r1_tarski(k3_tarski(k1_zfmisc_1(A_88)),A_88) ),
    inference(resolution,[status(thm)],[c_191,c_40])).

tff(c_38,plain,(
    ! [A_39] : r1_tarski(k1_tarski(A_39),k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ! [A_38] : k3_tarski(k1_tarski(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_84,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k3_tarski(A_59),k3_tarski(B_60))
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_106,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,k3_tarski(B_64))
      | ~ r1_tarski(k1_tarski(A_63),B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_84])).

tff(c_110,plain,(
    ! [A_39] : r1_tarski(A_39,k3_tarski(k1_zfmisc_1(A_39))) ),
    inference(resolution,[status(thm)],[c_38,c_106])).

tff(c_91,plain,(
    ! [A_61,B_62] :
      ( r2_xboole_0(A_61,B_62)
      | B_62 = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ r2_xboole_0(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [B_72,A_73] :
      ( ~ r1_tarski(B_72,A_73)
      | B_72 = A_73
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(resolution,[status(thm)],[c_91,c_8])).

tff(c_149,plain,(
    ! [A_39] :
      ( k3_tarski(k1_zfmisc_1(A_39)) = A_39
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(A_39)),A_39) ) ),
    inference(resolution,[status(thm)],[c_110,c_136])).

tff(c_208,plain,(
    ! [A_39] : k3_tarski(k1_zfmisc_1(A_39)) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_149])).

tff(c_46,plain,(
    k3_tarski(k1_zfmisc_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:33:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.30  
% 1.99/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.30  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.19/1.30  
% 2.19/1.30  %Foreground sorts:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Background operators:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Foreground operators:
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.19/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.30  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.19/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.19/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.30  
% 2.19/1.31  tff(f_69, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.19/1.31  tff(f_58, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.19/1.31  tff(f_62, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 2.19/1.31  tff(f_60, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.19/1.31  tff(f_73, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.19/1.31  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.19/1.31  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.19/1.31  tff(f_76, negated_conjecture, ~(![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.19/1.31  tff(c_154, plain, (![A_78, B_79]: (r2_hidden('#skF_3'(A_78, B_79), A_78) | r1_tarski(k3_tarski(A_78), B_79))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.19/1.31  tff(c_24, plain, (![C_37, A_33]: (r1_tarski(C_37, A_33) | ~r2_hidden(C_37, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.19/1.31  tff(c_191, plain, (![A_88, B_89]: (r1_tarski('#skF_3'(k1_zfmisc_1(A_88), B_89), A_88) | r1_tarski(k3_tarski(k1_zfmisc_1(A_88)), B_89))), inference(resolution, [status(thm)], [c_154, c_24])).
% 2.19/1.31  tff(c_40, plain, (![A_40, B_41]: (~r1_tarski('#skF_3'(A_40, B_41), B_41) | r1_tarski(k3_tarski(A_40), B_41))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.19/1.31  tff(c_203, plain, (![A_88]: (r1_tarski(k3_tarski(k1_zfmisc_1(A_88)), A_88))), inference(resolution, [status(thm)], [c_191, c_40])).
% 2.19/1.31  tff(c_38, plain, (![A_39]: (r1_tarski(k1_tarski(A_39), k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.31  tff(c_36, plain, (![A_38]: (k3_tarski(k1_tarski(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.19/1.31  tff(c_84, plain, (![A_59, B_60]: (r1_tarski(k3_tarski(A_59), k3_tarski(B_60)) | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.19/1.31  tff(c_106, plain, (![A_63, B_64]: (r1_tarski(A_63, k3_tarski(B_64)) | ~r1_tarski(k1_tarski(A_63), B_64))), inference(superposition, [status(thm), theory('equality')], [c_36, c_84])).
% 2.19/1.31  tff(c_110, plain, (![A_39]: (r1_tarski(A_39, k3_tarski(k1_zfmisc_1(A_39))))), inference(resolution, [status(thm)], [c_38, c_106])).
% 2.19/1.31  tff(c_91, plain, (![A_61, B_62]: (r2_xboole_0(A_61, B_62) | B_62=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.31  tff(c_8, plain, (![B_4, A_3]: (~r2_xboole_0(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.31  tff(c_136, plain, (![B_72, A_73]: (~r1_tarski(B_72, A_73) | B_72=A_73 | ~r1_tarski(A_73, B_72))), inference(resolution, [status(thm)], [c_91, c_8])).
% 2.19/1.31  tff(c_149, plain, (![A_39]: (k3_tarski(k1_zfmisc_1(A_39))=A_39 | ~r1_tarski(k3_tarski(k1_zfmisc_1(A_39)), A_39))), inference(resolution, [status(thm)], [c_110, c_136])).
% 2.19/1.31  tff(c_208, plain, (![A_39]: (k3_tarski(k1_zfmisc_1(A_39))=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_149])).
% 2.19/1.31  tff(c_46, plain, (k3_tarski(k1_zfmisc_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.31  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_208, c_46])).
% 2.19/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.31  
% 2.19/1.31  Inference rules
% 2.19/1.31  ----------------------
% 2.19/1.31  #Ref     : 0
% 2.19/1.31  #Sup     : 35
% 2.19/1.31  #Fact    : 0
% 2.19/1.31  #Define  : 0
% 2.19/1.31  #Split   : 0
% 2.19/1.31  #Chain   : 0
% 2.19/1.31  #Close   : 0
% 2.19/1.31  
% 2.19/1.31  Ordering : KBO
% 2.19/1.31  
% 2.19/1.31  Simplification rules
% 2.19/1.31  ----------------------
% 2.19/1.31  #Subsume      : 0
% 2.19/1.31  #Demod        : 12
% 2.19/1.31  #Tautology    : 14
% 2.19/1.31  #SimpNegUnit  : 0
% 2.19/1.31  #BackRed      : 7
% 2.19/1.31  
% 2.19/1.31  #Partial instantiations: 0
% 2.19/1.31  #Strategies tried      : 1
% 2.19/1.31  
% 2.19/1.31  Timing (in seconds)
% 2.19/1.31  ----------------------
% 2.19/1.31  Preprocessing        : 0.34
% 2.19/1.31  Parsing              : 0.17
% 2.19/1.31  CNF conversion       : 0.02
% 2.19/1.31  Main loop            : 0.17
% 2.19/1.31  Inferencing          : 0.06
% 2.19/1.31  Reduction            : 0.05
% 2.19/1.31  Demodulation         : 0.04
% 2.19/1.31  BG Simplification    : 0.02
% 2.19/1.31  Subsumption          : 0.03
% 2.19/1.31  Abstraction          : 0.01
% 2.19/1.31  MUC search           : 0.00
% 2.19/1.31  Cooper               : 0.00
% 2.19/1.31  Total                : 0.54
% 2.19/1.31  Index Insertion      : 0.00
% 2.19/1.31  Index Deletion       : 0.00
% 2.19/1.31  Index Matching       : 0.00
% 2.19/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
