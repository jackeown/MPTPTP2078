%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:34 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  99 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 ( 130 expanded)
%              Number of equality atoms :   35 (  91 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_50,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_307,plain,(
    ! [A_100,B_101] : k1_enumset1(A_100,A_100,B_101) = k2_tarski(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    ! [E_17,A_11,B_12] : r2_hidden(E_17,k1_enumset1(A_11,B_12,E_17)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_325,plain,(
    ! [B_102,A_103] : r2_hidden(B_102,k2_tarski(A_103,B_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_28])).

tff(c_328,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_325])).

tff(c_78,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_96,plain,(
    ! [B_38,A_39] : r2_hidden(B_38,k2_tarski(A_39,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_28])).

tff(c_99,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_96])).

tff(c_60,plain,
    ( '#skF_5' != '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_65,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_114,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(k1_tarski(A_47),k1_tarski(B_48))
      | B_48 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_140,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(k1_tarski(A_60),k1_tarski(B_61)) = k1_tarski(A_60)
      | B_61 = A_60 ) ),
    inference(resolution,[status(thm)],[c_114,c_22])).

tff(c_58,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_101,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_152,plain,(
    '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_101])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_152])).

tff(c_161,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_162,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_258,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_161,c_162,c_62])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_277,plain,(
    ! [D_89] :
      ( ~ r2_hidden(D_89,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_89,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_4])).

tff(c_280,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_99,c_277])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_280])).

tff(c_285,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_286,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( '#skF_5' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_360,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_285,c_286,c_64])).

tff(c_371,plain,(
    ! [D_121] :
      ( ~ r2_hidden(D_121,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_121,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_4])).

tff(c_374,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_328,c_371])).

tff(c_378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.29  
% 2.20/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.29  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.20/1.29  
% 2.20/1.29  %Foreground sorts:
% 2.20/1.29  
% 2.20/1.29  
% 2.20/1.29  %Background operators:
% 2.20/1.29  
% 2.20/1.29  
% 2.20/1.29  %Foreground operators:
% 2.20/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.20/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.20/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.20/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.20/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.20/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.20/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.20/1.29  tff('#skF_8', type, '#skF_8': $i).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.20/1.29  
% 2.20/1.30  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.20/1.30  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.20/1.30  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.20/1.30  tff(f_73, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.20/1.30  tff(f_67, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.20/1.30  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.20/1.30  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.20/1.30  tff(c_50, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.20/1.30  tff(c_307, plain, (![A_100, B_101]: (k1_enumset1(A_100, A_100, B_101)=k2_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.20/1.30  tff(c_28, plain, (![E_17, A_11, B_12]: (r2_hidden(E_17, k1_enumset1(A_11, B_12, E_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.20/1.30  tff(c_325, plain, (![B_102, A_103]: (r2_hidden(B_102, k2_tarski(A_103, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_307, c_28])).
% 2.20/1.30  tff(c_328, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_325])).
% 2.20/1.30  tff(c_78, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.20/1.30  tff(c_96, plain, (![B_38, A_39]: (r2_hidden(B_38, k2_tarski(A_39, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_28])).
% 2.20/1.30  tff(c_99, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_96])).
% 2.20/1.30  tff(c_60, plain, ('#skF_5'!='#skF_6' | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.20/1.30  tff(c_65, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_60])).
% 2.20/1.30  tff(c_114, plain, (![A_47, B_48]: (r1_xboole_0(k1_tarski(A_47), k1_tarski(B_48)) | B_48=A_47)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.20/1.30  tff(c_22, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.20/1.30  tff(c_140, plain, (![A_60, B_61]: (k4_xboole_0(k1_tarski(A_60), k1_tarski(B_61))=k1_tarski(A_60) | B_61=A_60)), inference(resolution, [status(thm)], [c_114, c_22])).
% 2.20/1.30  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.20/1.30  tff(c_101, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_58])).
% 2.20/1.30  tff(c_152, plain, ('#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_140, c_101])).
% 2.20/1.30  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_152])).
% 2.20/1.30  tff(c_161, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_58])).
% 2.20/1.30  tff(c_162, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 2.20/1.30  tff(c_62, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.20/1.30  tff(c_258, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_161, c_162, c_62])).
% 2.20/1.30  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.30  tff(c_277, plain, (![D_89]: (~r2_hidden(D_89, k1_tarski('#skF_8')) | ~r2_hidden(D_89, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_258, c_4])).
% 2.20/1.30  tff(c_280, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_99, c_277])).
% 2.20/1.30  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_280])).
% 2.20/1.30  tff(c_285, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_60])).
% 2.20/1.30  tff(c_286, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_60])).
% 2.20/1.30  tff(c_64, plain, ('#skF_5'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.20/1.30  tff(c_360, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_285, c_286, c_64])).
% 2.20/1.30  tff(c_371, plain, (![D_121]: (~r2_hidden(D_121, k1_tarski('#skF_8')) | ~r2_hidden(D_121, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_360, c_4])).
% 2.20/1.30  tff(c_374, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_328, c_371])).
% 2.20/1.30  tff(c_378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_328, c_374])).
% 2.20/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.30  
% 2.20/1.30  Inference rules
% 2.20/1.30  ----------------------
% 2.20/1.30  #Ref     : 0
% 2.20/1.30  #Sup     : 71
% 2.20/1.30  #Fact    : 0
% 2.20/1.30  #Define  : 0
% 2.20/1.30  #Split   : 2
% 2.20/1.30  #Chain   : 0
% 2.20/1.30  #Close   : 0
% 2.20/1.30  
% 2.20/1.30  Ordering : KBO
% 2.20/1.30  
% 2.20/1.30  Simplification rules
% 2.20/1.30  ----------------------
% 2.20/1.30  #Subsume      : 2
% 2.20/1.30  #Demod        : 19
% 2.20/1.30  #Tautology    : 53
% 2.20/1.30  #SimpNegUnit  : 3
% 2.20/1.30  #BackRed      : 0
% 2.20/1.30  
% 2.20/1.30  #Partial instantiations: 0
% 2.20/1.30  #Strategies tried      : 1
% 2.20/1.30  
% 2.20/1.30  Timing (in seconds)
% 2.20/1.30  ----------------------
% 2.20/1.31  Preprocessing        : 0.30
% 2.20/1.31  Parsing              : 0.15
% 2.20/1.31  CNF conversion       : 0.03
% 2.20/1.31  Main loop            : 0.21
% 2.20/1.31  Inferencing          : 0.08
% 2.20/1.31  Reduction            : 0.06
% 2.20/1.31  Demodulation         : 0.04
% 2.20/1.31  BG Simplification    : 0.02
% 2.20/1.31  Subsumption          : 0.04
% 2.20/1.31  Abstraction          : 0.01
% 2.20/1.31  MUC search           : 0.00
% 2.20/1.31  Cooper               : 0.00
% 2.20/1.31  Total                : 0.54
% 2.20/1.31  Index Insertion      : 0.00
% 2.20/1.31  Index Deletion       : 0.00
% 2.20/1.31  Index Matching       : 0.00
% 2.20/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
