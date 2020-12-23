%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:12 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :   54 (  69 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 (  86 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_78,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_64,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_83,plain,(
    ! [A_83,B_84] : k1_enumset1(A_83,A_83,B_84) = k2_tarski(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_89,plain,(
    ! [B_84,A_83] : r2_hidden(B_84,k2_tarski(A_83,B_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_12])).

tff(c_112,plain,(
    ! [A_90,B_91] : k3_tarski(k2_tarski(A_90,B_91)) = k2_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,k3_tarski(B_60))
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1436,plain,(
    ! [A_287,A_288,B_289] :
      ( r1_tarski(A_287,k2_xboole_0(A_288,B_289))
      | ~ r2_hidden(A_287,k2_tarski(A_288,B_289)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_54])).

tff(c_1452,plain,(
    ! [B_84,A_83] : r1_tarski(B_84,k2_xboole_0(A_83,B_84)) ),
    inference(resolution,[status(thm)],[c_89,c_1436])).

tff(c_66,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_162,plain,(
    ! [A_98,B_99] :
      ( r2_xboole_0(A_98,B_99)
      | B_99 = A_98
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ r2_xboole_0(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_186,plain,(
    ! [B_103,A_104] :
      ( ~ r1_tarski(B_103,A_104)
      | B_103 = A_104
      | ~ r1_tarski(A_104,B_103) ) ),
    inference(resolution,[status(thm)],[c_162,c_8])).

tff(c_191,plain,
    ( k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_186])).

tff(c_274,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_1489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_274])).

tff(c_1490,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_56,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [E_11,A_5,C_7] : r2_hidden(E_11,k1_enumset1(A_5,E_11,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_92,plain,(
    ! [A_83,B_84] : r2_hidden(A_83,k2_tarski(A_83,B_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_14])).

tff(c_177,plain,(
    ! [A_100,C_101,B_102] :
      ( r2_hidden(A_100,C_101)
      | ~ r1_tarski(k2_tarski(A_100,B_102),C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1606,plain,(
    ! [A_315,B_316,B_317] :
      ( r2_hidden(A_315,k3_tarski(B_316))
      | ~ r2_hidden(k2_tarski(A_315,B_317),B_316) ) ),
    inference(resolution,[status(thm)],[c_54,c_177])).

tff(c_1646,plain,(
    ! [A_315,B_317,B_84] : r2_hidden(A_315,k3_tarski(k2_tarski(k2_tarski(A_315,B_317),B_84))) ),
    inference(resolution,[status(thm)],[c_92,c_1606])).

tff(c_1687,plain,(
    ! [A_318,B_319,B_320] : r2_hidden(A_318,k2_xboole_0(k2_tarski(A_318,B_319),B_320)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1646])).

tff(c_1698,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1490,c_1687])).

tff(c_1709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1698])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.72  
% 3.76/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.73  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.76/1.73  
% 3.76/1.73  %Foreground sorts:
% 3.76/1.73  
% 3.76/1.73  
% 3.76/1.73  %Background operators:
% 3.76/1.73  
% 3.76/1.73  
% 3.76/1.73  %Foreground operators:
% 3.76/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.76/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.76/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.76/1.73  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.76/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.76/1.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.76/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.76/1.73  tff('#skF_5', type, '#skF_5': $i).
% 3.76/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.76/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.76/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.76/1.73  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.76/1.73  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.76/1.73  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.76/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.76/1.73  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.76/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.76/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.76/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.76/1.73  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.76/1.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.76/1.73  
% 3.76/1.74  tff(f_89, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 3.76/1.74  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.76/1.74  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.76/1.74  tff(f_78, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.76/1.74  tff(f_76, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.76/1.74  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.76/1.74  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 3.76/1.74  tff(f_84, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.76/1.74  tff(c_64, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.76/1.74  tff(c_83, plain, (![A_83, B_84]: (k1_enumset1(A_83, A_83, B_84)=k2_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.76/1.74  tff(c_12, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.76/1.74  tff(c_89, plain, (![B_84, A_83]: (r2_hidden(B_84, k2_tarski(A_83, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_12])).
% 3.76/1.74  tff(c_112, plain, (![A_90, B_91]: (k3_tarski(k2_tarski(A_90, B_91))=k2_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.76/1.74  tff(c_54, plain, (![A_59, B_60]: (r1_tarski(A_59, k3_tarski(B_60)) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.76/1.74  tff(c_1436, plain, (![A_287, A_288, B_289]: (r1_tarski(A_287, k2_xboole_0(A_288, B_289)) | ~r2_hidden(A_287, k2_tarski(A_288, B_289)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_54])).
% 3.76/1.74  tff(c_1452, plain, (![B_84, A_83]: (r1_tarski(B_84, k2_xboole_0(A_83, B_84)))), inference(resolution, [status(thm)], [c_89, c_1436])).
% 3.76/1.74  tff(c_66, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.76/1.74  tff(c_162, plain, (![A_98, B_99]: (r2_xboole_0(A_98, B_99) | B_99=A_98 | ~r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.76/1.74  tff(c_8, plain, (![B_4, A_3]: (~r2_xboole_0(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.76/1.74  tff(c_186, plain, (![B_103, A_104]: (~r1_tarski(B_103, A_104) | B_103=A_104 | ~r1_tarski(A_104, B_103))), inference(resolution, [status(thm)], [c_162, c_8])).
% 3.76/1.74  tff(c_191, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_186])).
% 3.76/1.74  tff(c_274, plain, (~r1_tarski('#skF_5', k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_191])).
% 3.76/1.74  tff(c_1489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1452, c_274])).
% 3.76/1.74  tff(c_1490, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_191])).
% 3.76/1.74  tff(c_56, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.76/1.74  tff(c_14, plain, (![E_11, A_5, C_7]: (r2_hidden(E_11, k1_enumset1(A_5, E_11, C_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.76/1.74  tff(c_92, plain, (![A_83, B_84]: (r2_hidden(A_83, k2_tarski(A_83, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_14])).
% 3.76/1.74  tff(c_177, plain, (![A_100, C_101, B_102]: (r2_hidden(A_100, C_101) | ~r1_tarski(k2_tarski(A_100, B_102), C_101))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.76/1.74  tff(c_1606, plain, (![A_315, B_316, B_317]: (r2_hidden(A_315, k3_tarski(B_316)) | ~r2_hidden(k2_tarski(A_315, B_317), B_316))), inference(resolution, [status(thm)], [c_54, c_177])).
% 3.76/1.74  tff(c_1646, plain, (![A_315, B_317, B_84]: (r2_hidden(A_315, k3_tarski(k2_tarski(k2_tarski(A_315, B_317), B_84))))), inference(resolution, [status(thm)], [c_92, c_1606])).
% 3.76/1.74  tff(c_1687, plain, (![A_318, B_319, B_320]: (r2_hidden(A_318, k2_xboole_0(k2_tarski(A_318, B_319), B_320)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1646])).
% 3.76/1.74  tff(c_1698, plain, (r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1490, c_1687])).
% 3.76/1.74  tff(c_1709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1698])).
% 3.76/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.74  
% 3.76/1.74  Inference rules
% 3.76/1.74  ----------------------
% 3.76/1.74  #Ref     : 0
% 3.76/1.74  #Sup     : 340
% 3.76/1.74  #Fact    : 0
% 3.76/1.74  #Define  : 0
% 3.76/1.74  #Split   : 1
% 3.76/1.74  #Chain   : 0
% 3.76/1.74  #Close   : 0
% 3.76/1.74  
% 3.76/1.74  Ordering : KBO
% 3.76/1.74  
% 3.76/1.74  Simplification rules
% 3.76/1.74  ----------------------
% 3.76/1.74  #Subsume      : 15
% 3.76/1.74  #Demod        : 111
% 3.76/1.74  #Tautology    : 133
% 3.76/1.74  #SimpNegUnit  : 1
% 3.76/1.74  #BackRed      : 2
% 3.76/1.74  
% 3.76/1.74  #Partial instantiations: 0
% 3.76/1.74  #Strategies tried      : 1
% 3.76/1.74  
% 3.76/1.74  Timing (in seconds)
% 3.76/1.74  ----------------------
% 3.76/1.74  Preprocessing        : 0.34
% 3.76/1.74  Parsing              : 0.18
% 3.76/1.74  CNF conversion       : 0.03
% 3.76/1.74  Main loop            : 0.63
% 3.76/1.74  Inferencing          : 0.24
% 3.76/1.74  Reduction            : 0.21
% 3.76/1.74  Demodulation         : 0.16
% 3.76/1.74  BG Simplification    : 0.03
% 3.76/1.74  Subsumption          : 0.11
% 3.76/1.74  Abstraction          : 0.03
% 3.76/1.74  MUC search           : 0.00
% 3.76/1.74  Cooper               : 0.00
% 3.76/1.74  Total                : 1.00
% 3.76/1.74  Index Insertion      : 0.00
% 3.76/1.74  Index Deletion       : 0.00
% 3.76/1.74  Index Matching       : 0.00
% 3.76/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
