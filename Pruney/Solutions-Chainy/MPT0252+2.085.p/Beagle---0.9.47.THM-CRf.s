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
% DateTime   : Thu Dec  3 09:51:11 EST 2020

% Result     : Theorem 8.80s
% Output     : CNFRefutation 8.80s
% Verified   : 
% Statistics : Number of formulae       :   56 (  76 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  98 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_87,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_66,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_84,plain,(
    ! [A_87,B_88] : k1_enumset1(A_87,A_87,B_88) = k2_tarski(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    ! [B_88,A_87] : r2_hidden(B_88,k2_tarski(A_87,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_18])).

tff(c_64,plain,(
    ! [A_70,B_71] : k3_tarski(k2_tarski(A_70,B_71)) = k2_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_125,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(A_96,k3_tarski(B_97))
      | ~ r2_hidden(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_9457,plain,(
    ! [A_15118,A_15119,B_15120] :
      ( r1_tarski(A_15118,k2_xboole_0(A_15119,B_15120))
      | ~ r2_hidden(A_15118,k2_tarski(A_15119,B_15120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_125])).

tff(c_9480,plain,(
    ! [B_88,A_87] : r1_tarski(B_88,k2_xboole_0(A_87,B_88)) ),
    inference(resolution,[status(thm)],[c_93,c_9457])).

tff(c_68,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_149,plain,(
    ! [A_99,B_100] :
      ( r2_xboole_0(A_99,B_100)
      | B_100 = A_99
      | ~ r1_tarski(A_99,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( ~ r2_xboole_0(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_172,plain,(
    ! [B_106,A_107] :
      ( ~ r1_tarski(B_106,A_107)
      | B_106 = A_107
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(resolution,[status(thm)],[c_149,c_14])).

tff(c_184,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_68,c_172])).

tff(c_334,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_9485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9480,c_334])).

tff(c_9486,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_22,plain,(
    ! [E_16,B_11,C_12] : r2_hidden(E_16,k1_enumset1(E_16,B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_90,plain,(
    ! [A_87,B_88] : r2_hidden(A_87,k2_tarski(A_87,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_22])).

tff(c_62,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(A_68,k3_tarski(B_69))
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_194,plain,(
    ! [C_111,B_112,A_113] :
      ( r2_hidden(C_111,B_112)
      | ~ r2_hidden(C_111,A_113)
      | ~ r1_tarski(A_113,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_286,plain,(
    ! [A_123,B_124,B_125] :
      ( r2_hidden(A_123,B_124)
      | ~ r1_tarski(k2_tarski(A_123,B_125),B_124) ) ),
    inference(resolution,[status(thm)],[c_90,c_194])).

tff(c_16911,plain,(
    ! [A_28686,B_28687,B_28688] :
      ( r2_hidden(A_28686,k3_tarski(B_28687))
      | ~ r2_hidden(k2_tarski(A_28686,B_28688),B_28687) ) ),
    inference(resolution,[status(thm)],[c_62,c_286])).

tff(c_16990,plain,(
    ! [A_28686,B_28688,B_88] : r2_hidden(A_28686,k3_tarski(k2_tarski(k2_tarski(A_28686,B_28688),B_88))) ),
    inference(resolution,[status(thm)],[c_90,c_16911])).

tff(c_17099,plain,(
    ! [A_29136,B_29137,B_29138] : r2_hidden(A_29136,k2_xboole_0(k2_tarski(A_29136,B_29137),B_29138)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16990])).

tff(c_17122,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9486,c_17099])).

tff(c_17135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_17122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.80/3.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.80/3.15  
% 8.80/3.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.80/3.15  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 8.80/3.15  
% 8.80/3.15  %Foreground sorts:
% 8.80/3.15  
% 8.80/3.15  
% 8.80/3.15  %Background operators:
% 8.80/3.15  
% 8.80/3.15  
% 8.80/3.15  %Foreground operators:
% 8.80/3.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.80/3.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.80/3.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.80/3.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.80/3.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.80/3.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.80/3.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.80/3.15  tff('#skF_5', type, '#skF_5': $i).
% 8.80/3.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 8.80/3.15  tff('#skF_6', type, '#skF_6': $i).
% 8.80/3.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.80/3.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.80/3.15  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 8.80/3.15  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.80/3.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.80/3.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.80/3.15  tff('#skF_4', type, '#skF_4': $i).
% 8.80/3.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.80/3.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 8.80/3.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.80/3.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.80/3.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.80/3.15  
% 8.80/3.16  tff(f_92, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 8.80/3.16  tff(f_71, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 8.80/3.16  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 8.80/3.16  tff(f_87, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.80/3.16  tff(f_85, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 8.80/3.16  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 8.80/3.16  tff(f_44, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 8.80/3.16  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.80/3.16  tff(c_66, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.80/3.16  tff(c_84, plain, (![A_87, B_88]: (k1_enumset1(A_87, A_87, B_88)=k2_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.80/3.16  tff(c_18, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.80/3.16  tff(c_93, plain, (![B_88, A_87]: (r2_hidden(B_88, k2_tarski(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_18])).
% 8.80/3.16  tff(c_64, plain, (![A_70, B_71]: (k3_tarski(k2_tarski(A_70, B_71))=k2_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.80/3.16  tff(c_125, plain, (![A_96, B_97]: (r1_tarski(A_96, k3_tarski(B_97)) | ~r2_hidden(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.80/3.16  tff(c_9457, plain, (![A_15118, A_15119, B_15120]: (r1_tarski(A_15118, k2_xboole_0(A_15119, B_15120)) | ~r2_hidden(A_15118, k2_tarski(A_15119, B_15120)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_125])).
% 8.80/3.16  tff(c_9480, plain, (![B_88, A_87]: (r1_tarski(B_88, k2_xboole_0(A_87, B_88)))), inference(resolution, [status(thm)], [c_93, c_9457])).
% 8.80/3.16  tff(c_68, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.80/3.16  tff(c_149, plain, (![A_99, B_100]: (r2_xboole_0(A_99, B_100) | B_100=A_99 | ~r1_tarski(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.80/3.16  tff(c_14, plain, (![B_9, A_8]: (~r2_xboole_0(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.80/3.16  tff(c_172, plain, (![B_106, A_107]: (~r1_tarski(B_106, A_107) | B_106=A_107 | ~r1_tarski(A_107, B_106))), inference(resolution, [status(thm)], [c_149, c_14])).
% 8.80/3.16  tff(c_184, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_68, c_172])).
% 8.80/3.16  tff(c_334, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_184])).
% 8.80/3.16  tff(c_9485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9480, c_334])).
% 8.80/3.16  tff(c_9486, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_184])).
% 8.80/3.16  tff(c_22, plain, (![E_16, B_11, C_12]: (r2_hidden(E_16, k1_enumset1(E_16, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.80/3.16  tff(c_90, plain, (![A_87, B_88]: (r2_hidden(A_87, k2_tarski(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_22])).
% 8.80/3.16  tff(c_62, plain, (![A_68, B_69]: (r1_tarski(A_68, k3_tarski(B_69)) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.80/3.16  tff(c_194, plain, (![C_111, B_112, A_113]: (r2_hidden(C_111, B_112) | ~r2_hidden(C_111, A_113) | ~r1_tarski(A_113, B_112))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.80/3.16  tff(c_286, plain, (![A_123, B_124, B_125]: (r2_hidden(A_123, B_124) | ~r1_tarski(k2_tarski(A_123, B_125), B_124))), inference(resolution, [status(thm)], [c_90, c_194])).
% 8.80/3.16  tff(c_16911, plain, (![A_28686, B_28687, B_28688]: (r2_hidden(A_28686, k3_tarski(B_28687)) | ~r2_hidden(k2_tarski(A_28686, B_28688), B_28687))), inference(resolution, [status(thm)], [c_62, c_286])).
% 8.80/3.16  tff(c_16990, plain, (![A_28686, B_28688, B_88]: (r2_hidden(A_28686, k3_tarski(k2_tarski(k2_tarski(A_28686, B_28688), B_88))))), inference(resolution, [status(thm)], [c_90, c_16911])).
% 8.80/3.16  tff(c_17099, plain, (![A_29136, B_29137, B_29138]: (r2_hidden(A_29136, k2_xboole_0(k2_tarski(A_29136, B_29137), B_29138)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16990])).
% 8.80/3.16  tff(c_17122, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9486, c_17099])).
% 8.80/3.16  tff(c_17135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_17122])).
% 8.80/3.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.80/3.16  
% 8.80/3.16  Inference rules
% 8.80/3.16  ----------------------
% 8.80/3.16  #Ref     : 0
% 8.80/3.16  #Sup     : 2261
% 8.80/3.16  #Fact    : 36
% 8.80/3.16  #Define  : 0
% 8.80/3.16  #Split   : 1
% 8.80/3.16  #Chain   : 0
% 8.80/3.16  #Close   : 0
% 8.80/3.16  
% 8.80/3.16  Ordering : KBO
% 8.80/3.16  
% 8.80/3.16  Simplification rules
% 8.80/3.16  ----------------------
% 8.80/3.16  #Subsume      : 329
% 8.80/3.16  #Demod        : 1097
% 8.80/3.16  #Tautology    : 983
% 8.80/3.16  #SimpNegUnit  : 1
% 8.80/3.16  #BackRed      : 2
% 8.80/3.16  
% 8.80/3.16  #Partial instantiations: 9360
% 8.80/3.16  #Strategies tried      : 1
% 8.80/3.16  
% 8.80/3.16  Timing (in seconds)
% 8.80/3.16  ----------------------
% 8.80/3.17  Preprocessing        : 0.34
% 8.80/3.17  Parsing              : 0.17
% 8.80/3.17  CNF conversion       : 0.03
% 8.80/3.17  Main loop            : 2.01
% 8.80/3.17  Inferencing          : 1.06
% 8.80/3.17  Reduction            : 0.57
% 8.80/3.17  Demodulation         : 0.46
% 8.80/3.17  BG Simplification    : 0.07
% 8.80/3.17  Subsumption          : 0.23
% 8.80/3.17  Abstraction          : 0.09
% 8.80/3.17  MUC search           : 0.00
% 8.80/3.17  Cooper               : 0.00
% 8.80/3.17  Total                : 2.38
% 8.80/3.17  Index Insertion      : 0.00
% 8.80/3.17  Index Deletion       : 0.00
% 8.80/3.17  Index Matching       : 0.00
% 8.80/3.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
