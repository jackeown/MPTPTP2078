%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:57 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   64 (  83 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :    5
%              Number of atoms          :   74 ( 116 expanded)
%              Number of equality atoms :   28 (  47 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_66,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_134,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = A_54
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_214,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(k1_tarski(A_74),B_75) = k1_tarski(A_74)
      | r2_hidden(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_48,c_134])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_160,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_220,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_160])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_220])).

tff(c_230,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_236,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_54])).

tff(c_40,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_103,plain,(
    ! [A_43,B_44] : k1_enumset1(A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [E_18,B_13,C_14] : r2_hidden(E_18,k1_enumset1(E_18,B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_121,plain,(
    ! [A_45,B_46] : r2_hidden(A_45,k2_tarski(A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_22])).

tff(c_124,plain,(
    ! [A_19] : r2_hidden(A_19,k1_tarski(A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_121])).

tff(c_229,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_269,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | ~ r2_hidden(C_80,B_79)
      | ~ r2_hidden(C_80,A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_323,plain,(
    ! [C_90,B_91,A_92] :
      ( ~ r2_hidden(C_90,B_91)
      | ~ r2_hidden(C_90,A_92)
      | k4_xboole_0(A_92,B_91) != A_92 ) ),
    inference(resolution,[status(thm)],[c_14,c_269])).

tff(c_351,plain,(
    ! [A_93] :
      ( ~ r2_hidden('#skF_6',A_93)
      | k4_xboole_0(A_93,'#skF_7') != A_93 ) ),
    inference(resolution,[status(thm)],[c_229,c_323])).

tff(c_362,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_124,c_351])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_362])).

tff(c_386,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_449,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_56])).

tff(c_425,plain,(
    ! [A_107,B_108] : k1_enumset1(A_107,A_107,B_108) = k2_tarski(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [E_18,A_12,C_14] : r2_hidden(E_18,k1_enumset1(A_12,E_18,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_443,plain,(
    ! [A_109,B_110] : r2_hidden(A_109,k2_tarski(A_109,B_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_20])).

tff(c_446,plain,(
    ! [A_19] : r2_hidden(A_19,k1_tarski(A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_443])).

tff(c_385,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_525,plain,(
    ! [A_129,B_130,C_131] :
      ( ~ r1_xboole_0(A_129,B_130)
      | ~ r2_hidden(C_131,B_130)
      | ~ r2_hidden(C_131,A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_551,plain,(
    ! [C_134,B_135,A_136] :
      ( ~ r2_hidden(C_134,B_135)
      | ~ r2_hidden(C_134,A_136)
      | k4_xboole_0(A_136,B_135) != A_136 ) ),
    inference(resolution,[status(thm)],[c_14,c_525])).

tff(c_631,plain,(
    ! [A_142] :
      ( ~ r2_hidden('#skF_6',A_142)
      | k4_xboole_0(A_142,'#skF_7') != A_142 ) ),
    inference(resolution,[status(thm)],[c_385,c_551])).

tff(c_639,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_446,c_631])).

tff(c_663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_639])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:27:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.32  
% 2.41/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.33  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.41/1.33  
% 2.41/1.33  %Foreground sorts:
% 2.41/1.33  
% 2.41/1.33  
% 2.41/1.33  %Background operators:
% 2.41/1.33  
% 2.41/1.33  
% 2.41/1.33  %Foreground operators:
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.41/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.41/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.41/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.41/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.41/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.41/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.41/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.41/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.41/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.41/1.33  
% 2.41/1.34  tff(f_85, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 2.41/1.34  tff(f_79, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.41/1.34  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.41/1.34  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.41/1.34  tff(f_70, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.41/1.34  tff(f_66, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.41/1.34  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.41/1.34  tff(c_52, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.41/1.34  tff(c_66, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 2.41/1.34  tff(c_48, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.41/1.34  tff(c_134, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=A_54 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.41/1.34  tff(c_214, plain, (![A_74, B_75]: (k4_xboole_0(k1_tarski(A_74), B_75)=k1_tarski(A_74) | r2_hidden(A_74, B_75))), inference(resolution, [status(thm)], [c_48, c_134])).
% 2.41/1.34  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.41/1.34  tff(c_160, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 2.41/1.34  tff(c_220, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_214, c_160])).
% 2.41/1.34  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_220])).
% 2.41/1.34  tff(c_230, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 2.41/1.34  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.41/1.34  tff(c_236, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_54])).
% 2.41/1.34  tff(c_40, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.41/1.34  tff(c_103, plain, (![A_43, B_44]: (k1_enumset1(A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.41/1.34  tff(c_22, plain, (![E_18, B_13, C_14]: (r2_hidden(E_18, k1_enumset1(E_18, B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.41/1.34  tff(c_121, plain, (![A_45, B_46]: (r2_hidden(A_45, k2_tarski(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_22])).
% 2.41/1.34  tff(c_124, plain, (![A_19]: (r2_hidden(A_19, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_121])).
% 2.41/1.34  tff(c_229, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 2.41/1.34  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.41/1.34  tff(c_269, plain, (![A_78, B_79, C_80]: (~r1_xboole_0(A_78, B_79) | ~r2_hidden(C_80, B_79) | ~r2_hidden(C_80, A_78))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.41/1.34  tff(c_323, plain, (![C_90, B_91, A_92]: (~r2_hidden(C_90, B_91) | ~r2_hidden(C_90, A_92) | k4_xboole_0(A_92, B_91)!=A_92)), inference(resolution, [status(thm)], [c_14, c_269])).
% 2.41/1.34  tff(c_351, plain, (![A_93]: (~r2_hidden('#skF_6', A_93) | k4_xboole_0(A_93, '#skF_7')!=A_93)), inference(resolution, [status(thm)], [c_229, c_323])).
% 2.41/1.34  tff(c_362, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_124, c_351])).
% 2.41/1.34  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_236, c_362])).
% 2.41/1.34  tff(c_386, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 2.41/1.34  tff(c_56, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.41/1.34  tff(c_449, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_56])).
% 2.41/1.34  tff(c_425, plain, (![A_107, B_108]: (k1_enumset1(A_107, A_107, B_108)=k2_tarski(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.41/1.34  tff(c_20, plain, (![E_18, A_12, C_14]: (r2_hidden(E_18, k1_enumset1(A_12, E_18, C_14)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.41/1.34  tff(c_443, plain, (![A_109, B_110]: (r2_hidden(A_109, k2_tarski(A_109, B_110)))), inference(superposition, [status(thm), theory('equality')], [c_425, c_20])).
% 2.41/1.34  tff(c_446, plain, (![A_19]: (r2_hidden(A_19, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_443])).
% 2.41/1.34  tff(c_385, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 2.41/1.34  tff(c_525, plain, (![A_129, B_130, C_131]: (~r1_xboole_0(A_129, B_130) | ~r2_hidden(C_131, B_130) | ~r2_hidden(C_131, A_129))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.41/1.34  tff(c_551, plain, (![C_134, B_135, A_136]: (~r2_hidden(C_134, B_135) | ~r2_hidden(C_134, A_136) | k4_xboole_0(A_136, B_135)!=A_136)), inference(resolution, [status(thm)], [c_14, c_525])).
% 2.41/1.34  tff(c_631, plain, (![A_142]: (~r2_hidden('#skF_6', A_142) | k4_xboole_0(A_142, '#skF_7')!=A_142)), inference(resolution, [status(thm)], [c_385, c_551])).
% 2.41/1.34  tff(c_639, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_446, c_631])).
% 2.41/1.34  tff(c_663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_449, c_639])).
% 2.41/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.34  
% 2.41/1.34  Inference rules
% 2.41/1.34  ----------------------
% 2.41/1.34  #Ref     : 0
% 2.41/1.34  #Sup     : 140
% 2.41/1.34  #Fact    : 0
% 2.41/1.34  #Define  : 0
% 2.41/1.34  #Split   : 2
% 2.41/1.34  #Chain   : 0
% 2.41/1.34  #Close   : 0
% 2.41/1.34  
% 2.41/1.34  Ordering : KBO
% 2.41/1.34  
% 2.41/1.34  Simplification rules
% 2.41/1.34  ----------------------
% 2.41/1.34  #Subsume      : 1
% 2.41/1.34  #Demod        : 24
% 2.41/1.34  #Tautology    : 85
% 2.41/1.34  #SimpNegUnit  : 3
% 2.41/1.34  #BackRed      : 0
% 2.41/1.34  
% 2.41/1.34  #Partial instantiations: 0
% 2.41/1.34  #Strategies tried      : 1
% 2.41/1.34  
% 2.41/1.34  Timing (in seconds)
% 2.41/1.34  ----------------------
% 2.41/1.34  Preprocessing        : 0.31
% 2.41/1.34  Parsing              : 0.16
% 2.41/1.34  CNF conversion       : 0.02
% 2.41/1.34  Main loop            : 0.27
% 2.41/1.34  Inferencing          : 0.10
% 2.41/1.34  Reduction            : 0.08
% 2.41/1.34  Demodulation         : 0.06
% 2.41/1.34  BG Simplification    : 0.02
% 2.41/1.34  Subsumption          : 0.04
% 2.41/1.34  Abstraction          : 0.02
% 2.41/1.34  MUC search           : 0.00
% 2.41/1.34  Cooper               : 0.00
% 2.41/1.34  Total                : 0.61
% 2.41/1.34  Index Insertion      : 0.00
% 2.41/1.34  Index Deletion       : 0.00
% 2.41/1.34  Index Matching       : 0.00
% 2.41/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
