%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:33 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   36 (  51 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  63 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_21,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_25,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_21])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    '#skF_5' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_18])).

tff(c_20,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_27,plain,(
    r1_setfam_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_20])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden('#skF_4'(A_33,B_34,C_35),B_34)
      | ~ r2_hidden(C_35,A_33)
      | ~ r1_setfam_1(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [B_36,C_37,A_38] :
      ( ~ v1_xboole_0(B_36)
      | ~ r2_hidden(C_37,A_38)
      | ~ r1_setfam_1(A_38,B_36) ) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_73,plain,(
    ! [B_39,A_40] :
      ( ~ v1_xboole_0(B_39)
      | ~ r1_setfam_1(A_40,B_39)
      | v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_4,c_63])).

tff(c_79,plain,
    ( ~ v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_27,c_73])).

tff(c_83,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_79])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_6])).

tff(c_86,plain,(
    '#skF_5' = '#skF_2' ),
    inference(resolution,[status(thm)],[c_83,c_26])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.16  
% 1.77/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.16  %$ r2_hidden > r1_tarski > r1_setfam_1 > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2
% 1.77/1.16  
% 1.77/1.16  %Foreground sorts:
% 1.77/1.16  
% 1.77/1.16  
% 1.77/1.16  %Background operators:
% 1.77/1.16  
% 1.77/1.16  
% 1.77/1.16  %Foreground operators:
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.16  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.77/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.77/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.77/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.77/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.77/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.77/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.77/1.16  
% 1.83/1.17  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.83/1.17  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.83/1.17  tff(f_54, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.83/1.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.83/1.17  tff(f_49, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.83/1.17  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.83/1.17  tff(c_21, plain, (![A_18]: (k1_xboole_0=A_18 | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.17  tff(c_25, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_21])).
% 1.83/1.17  tff(c_18, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.83/1.17  tff(c_28, plain, ('#skF_5'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_25, c_18])).
% 1.83/1.17  tff(c_20, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.83/1.17  tff(c_27, plain, (r1_setfam_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25, c_20])).
% 1.83/1.17  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.17  tff(c_58, plain, (![A_33, B_34, C_35]: (r2_hidden('#skF_4'(A_33, B_34, C_35), B_34) | ~r2_hidden(C_35, A_33) | ~r1_setfam_1(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.83/1.17  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.17  tff(c_63, plain, (![B_36, C_37, A_38]: (~v1_xboole_0(B_36) | ~r2_hidden(C_37, A_38) | ~r1_setfam_1(A_38, B_36))), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.83/1.17  tff(c_73, plain, (![B_39, A_40]: (~v1_xboole_0(B_39) | ~r1_setfam_1(A_40, B_39) | v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_4, c_63])).
% 1.83/1.17  tff(c_79, plain, (~v1_xboole_0('#skF_2') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_27, c_73])).
% 1.83/1.17  tff(c_83, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_79])).
% 1.83/1.17  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.17  tff(c_26, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_25, c_6])).
% 1.83/1.17  tff(c_86, plain, ('#skF_5'='#skF_2'), inference(resolution, [status(thm)], [c_83, c_26])).
% 1.83/1.17  tff(c_90, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_86])).
% 1.83/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  Inference rules
% 1.83/1.17  ----------------------
% 1.83/1.17  #Ref     : 0
% 1.83/1.17  #Sup     : 14
% 1.83/1.17  #Fact    : 0
% 1.83/1.17  #Define  : 0
% 1.83/1.17  #Split   : 0
% 1.83/1.17  #Chain   : 0
% 1.83/1.17  #Close   : 0
% 1.83/1.17  
% 1.83/1.17  Ordering : KBO
% 1.83/1.17  
% 1.83/1.17  Simplification rules
% 1.83/1.17  ----------------------
% 1.83/1.17  #Subsume      : 0
% 1.83/1.17  #Demod        : 4
% 1.83/1.17  #Tautology    : 5
% 1.83/1.17  #SimpNegUnit  : 1
% 1.83/1.17  #BackRed      : 3
% 1.83/1.17  
% 1.83/1.17  #Partial instantiations: 0
% 1.83/1.17  #Strategies tried      : 1
% 1.83/1.17  
% 1.83/1.17  Timing (in seconds)
% 1.83/1.17  ----------------------
% 1.83/1.18  Preprocessing        : 0.27
% 1.83/1.18  Parsing              : 0.15
% 1.83/1.18  CNF conversion       : 0.02
% 1.83/1.18  Main loop            : 0.11
% 1.83/1.18  Inferencing          : 0.05
% 1.83/1.18  Reduction            : 0.03
% 1.83/1.18  Demodulation         : 0.02
% 1.83/1.18  BG Simplification    : 0.01
% 1.83/1.18  Subsumption          : 0.02
% 1.83/1.18  Abstraction          : 0.00
% 1.83/1.18  MUC search           : 0.00
% 1.83/1.18  Cooper               : 0.00
% 1.83/1.18  Total                : 0.41
% 1.83/1.18  Index Insertion      : 0.00
% 1.83/1.18  Index Deletion       : 0.00
% 1.83/1.18  Index Matching       : 0.00
% 1.83/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
