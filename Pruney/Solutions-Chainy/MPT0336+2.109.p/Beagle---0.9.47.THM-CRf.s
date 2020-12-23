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
% DateTime   : Thu Dec  3 09:55:15 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   53 (  80 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 135 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_34,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_49,plain,(
    ! [B_28,A_29] :
      ( r1_xboole_0(B_28,A_29)
      | ~ r1_xboole_0(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_453,plain,(
    ! [A_99,C_100,B_101] :
      ( ~ r1_xboole_0(A_99,C_100)
      | ~ r1_xboole_0(A_99,B_101)
      | r1_xboole_0(A_99,k2_xboole_0(B_101,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_957,plain,(
    ! [B_174,C_175,A_176] :
      ( r1_xboole_0(k2_xboole_0(B_174,C_175),A_176)
      | ~ r1_xboole_0(A_176,C_175)
      | ~ r1_xboole_0(A_176,B_174) ) ),
    inference(resolution,[status(thm)],[c_453,c_2])).

tff(c_32,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_974,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_957,c_32])).

tff(c_982,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_974])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_134,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,k1_tarski(B_56)) = A_55
      | r2_hidden(B_56,A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_54,plain,(
    ! [B_19,A_18] : r1_xboole_0(B_19,k4_xboole_0(A_18,B_19)) ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_152,plain,(
    ! [B_56,A_55] :
      ( r1_xboole_0(k1_tarski(B_56),A_55)
      | r2_hidden(B_56,A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_54])).

tff(c_312,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_xboole_0(A_84,C_85)
      | ~ r1_xboole_0(B_86,C_85)
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1217,plain,(
    ! [A_227,A_228,B_229] :
      ( r1_xboole_0(A_227,A_228)
      | ~ r1_tarski(A_227,k1_tarski(B_229))
      | r2_hidden(B_229,A_228) ) ),
    inference(resolution,[status(thm)],[c_152,c_312])).

tff(c_1221,plain,(
    ! [A_230] :
      ( r1_xboole_0(k3_xboole_0('#skF_2','#skF_3'),A_230)
      | r2_hidden('#skF_5',A_230) ) ),
    inference(resolution,[status(thm)],[c_38,c_1217])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( ~ r1_xboole_0(k3_xboole_0(A_16,B_17),B_17)
      | r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1243,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_1221,c_20])).

tff(c_1246,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1243])).

tff(c_216,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ r1_xboole_0(A_72,B_73)
      | ~ r2_hidden(C_74,B_73)
      | ~ r2_hidden(C_74,A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_252,plain,(
    ! [C_74] :
      ( ~ r2_hidden(C_74,'#skF_3')
      | ~ r2_hidden(C_74,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_216])).

tff(c_1287,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1246,c_252])).

tff(c_1293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1287])).

tff(c_1294,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1243])).

tff(c_1301,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1294,c_2])).

tff(c_1307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_982,c_1301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:43:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.52  
% 3.34/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.34/1.52  
% 3.34/1.52  %Foreground sorts:
% 3.34/1.52  
% 3.34/1.52  
% 3.34/1.52  %Background operators:
% 3.34/1.52  
% 3.34/1.52  
% 3.34/1.52  %Foreground operators:
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.34/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.34/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.34/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.34/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.34/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.34/1.52  
% 3.34/1.54  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.34/1.54  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.34/1.54  tff(f_71, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.34/1.54  tff(f_88, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.34/1.54  tff(f_79, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.34/1.54  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.57/1.54  tff(f_77, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 3.57/1.54  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.57/1.54  tff(c_34, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.57/1.54  tff(c_49, plain, (![B_28, A_29]: (r1_xboole_0(B_28, A_29) | ~r1_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.57/1.54  tff(c_55, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_49])).
% 3.57/1.54  tff(c_453, plain, (![A_99, C_100, B_101]: (~r1_xboole_0(A_99, C_100) | ~r1_xboole_0(A_99, B_101) | r1_xboole_0(A_99, k2_xboole_0(B_101, C_100)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.54  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.57/1.54  tff(c_957, plain, (![B_174, C_175, A_176]: (r1_xboole_0(k2_xboole_0(B_174, C_175), A_176) | ~r1_xboole_0(A_176, C_175) | ~r1_xboole_0(A_176, B_174))), inference(resolution, [status(thm)], [c_453, c_2])).
% 3.57/1.54  tff(c_32, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.57/1.54  tff(c_974, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_957, c_32])).
% 3.57/1.54  tff(c_982, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_974])).
% 3.57/1.54  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.57/1.54  tff(c_38, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.57/1.54  tff(c_134, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k1_tarski(B_56))=A_55 | r2_hidden(B_56, A_55))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.57/1.54  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.57/1.54  tff(c_54, plain, (![B_19, A_18]: (r1_xboole_0(B_19, k4_xboole_0(A_18, B_19)))), inference(resolution, [status(thm)], [c_22, c_49])).
% 3.57/1.54  tff(c_152, plain, (![B_56, A_55]: (r1_xboole_0(k1_tarski(B_56), A_55) | r2_hidden(B_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_134, c_54])).
% 3.57/1.54  tff(c_312, plain, (![A_84, C_85, B_86]: (r1_xboole_0(A_84, C_85) | ~r1_xboole_0(B_86, C_85) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.57/1.54  tff(c_1217, plain, (![A_227, A_228, B_229]: (r1_xboole_0(A_227, A_228) | ~r1_tarski(A_227, k1_tarski(B_229)) | r2_hidden(B_229, A_228))), inference(resolution, [status(thm)], [c_152, c_312])).
% 3.57/1.54  tff(c_1221, plain, (![A_230]: (r1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), A_230) | r2_hidden('#skF_5', A_230))), inference(resolution, [status(thm)], [c_38, c_1217])).
% 3.57/1.54  tff(c_20, plain, (![A_16, B_17]: (~r1_xboole_0(k3_xboole_0(A_16, B_17), B_17) | r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.57/1.54  tff(c_1243, plain, (r1_xboole_0('#skF_2', '#skF_3') | r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_1221, c_20])).
% 3.57/1.54  tff(c_1246, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1243])).
% 3.57/1.54  tff(c_216, plain, (![A_72, B_73, C_74]: (~r1_xboole_0(A_72, B_73) | ~r2_hidden(C_74, B_73) | ~r2_hidden(C_74, A_72))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.57/1.54  tff(c_252, plain, (![C_74]: (~r2_hidden(C_74, '#skF_3') | ~r2_hidden(C_74, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_216])).
% 3.57/1.54  tff(c_1287, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1246, c_252])).
% 3.57/1.54  tff(c_1293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1287])).
% 3.57/1.54  tff(c_1294, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_1243])).
% 3.57/1.54  tff(c_1301, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1294, c_2])).
% 3.57/1.54  tff(c_1307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_982, c_1301])).
% 3.57/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.54  
% 3.57/1.54  Inference rules
% 3.57/1.54  ----------------------
% 3.57/1.54  #Ref     : 0
% 3.57/1.54  #Sup     : 322
% 3.57/1.54  #Fact    : 0
% 3.57/1.54  #Define  : 0
% 3.57/1.54  #Split   : 4
% 3.57/1.54  #Chain   : 0
% 3.57/1.54  #Close   : 0
% 3.57/1.54  
% 3.57/1.54  Ordering : KBO
% 3.57/1.54  
% 3.57/1.54  Simplification rules
% 3.57/1.54  ----------------------
% 3.57/1.54  #Subsume      : 27
% 3.57/1.54  #Demod        : 22
% 3.57/1.54  #Tautology    : 34
% 3.57/1.54  #SimpNegUnit  : 1
% 3.57/1.54  #BackRed      : 0
% 3.57/1.54  
% 3.57/1.54  #Partial instantiations: 0
% 3.57/1.54  #Strategies tried      : 1
% 3.57/1.54  
% 3.57/1.54  Timing (in seconds)
% 3.57/1.54  ----------------------
% 3.57/1.54  Preprocessing        : 0.28
% 3.57/1.54  Parsing              : 0.15
% 3.57/1.54  CNF conversion       : 0.02
% 3.57/1.54  Main loop            : 0.50
% 3.57/1.54  Inferencing          : 0.19
% 3.57/1.54  Reduction            : 0.14
% 3.57/1.54  Demodulation         : 0.10
% 3.57/1.54  BG Simplification    : 0.02
% 3.57/1.54  Subsumption          : 0.11
% 3.57/1.54  Abstraction          : 0.02
% 3.57/1.54  MUC search           : 0.00
% 3.57/1.54  Cooper               : 0.00
% 3.57/1.54  Total                : 0.81
% 3.57/1.54  Index Insertion      : 0.00
% 3.57/1.54  Index Deletion       : 0.00
% 3.57/1.54  Index Matching       : 0.00
% 3.57/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
