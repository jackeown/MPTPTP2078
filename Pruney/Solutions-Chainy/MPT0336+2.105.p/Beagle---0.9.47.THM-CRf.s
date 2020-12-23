%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:14 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   55 (  82 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 145 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_32,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46,plain,(
    ! [B_22,A_23] :
      ( r1_xboole_0(B_22,A_23)
      | ~ r1_xboole_0(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_334,plain,(
    ! [A_80,C_81,B_82] :
      ( ~ r1_xboole_0(A_80,C_81)
      | ~ r1_xboole_0(A_80,B_82)
      | r1_xboole_0(A_80,k2_xboole_0(B_82,C_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_597,plain,(
    ! [B_128,C_129,A_130] :
      ( r1_xboole_0(k2_xboole_0(B_128,C_129),A_130)
      | ~ r1_xboole_0(A_130,C_129)
      | ~ r1_xboole_0(A_130,B_128) ) ),
    inference(resolution,[status(thm)],[c_334,c_2])).

tff(c_30,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_615,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_597,c_30])).

tff(c_623,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_615])).

tff(c_66,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = A_28
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_82,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_66])).

tff(c_36,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(k1_tarski(A_19),B_20)
      | r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_371,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(k1_tarski(A_97),B_98) = k1_tarski(A_97)
      | r2_hidden(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_10,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_tarski(A_8,k4_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_530,plain,(
    ! [A_124,B_125,A_126] :
      ( r1_xboole_0(A_124,B_125)
      | ~ r1_tarski(A_124,k1_tarski(A_126))
      | r2_hidden(A_126,B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_10])).

tff(c_534,plain,(
    ! [B_127] :
      ( r1_xboole_0(k3_xboole_0('#skF_2','#skF_3'),B_127)
      | r2_hidden('#skF_5',B_127) ) ),
    inference(resolution,[status(thm)],[c_36,c_530])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( ~ r1_xboole_0(k3_xboole_0(A_14,B_15),B_15)
      | r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_557,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_534,c_20])).

tff(c_560,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_557])).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_58,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k4_xboole_0(A_26,B_27) != A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_64,plain,(
    ! [B_27,A_26] :
      ( r1_xboole_0(B_27,A_26)
      | k4_xboole_0(A_26,B_27) != A_26 ) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_273,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,B_66)
      | ~ r2_hidden(C_67,A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_498,plain,(
    ! [C_118,A_119,B_120] :
      ( ~ r2_hidden(C_118,A_119)
      | ~ r2_hidden(C_118,B_120)
      | k4_xboole_0(A_119,B_120) != A_119 ) ),
    inference(resolution,[status(thm)],[c_64,c_273])).

tff(c_513,plain,(
    ! [B_120] :
      ( ~ r2_hidden('#skF_5',B_120)
      | k4_xboole_0('#skF_4',B_120) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_34,c_498])).

tff(c_563,plain,(
    k4_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_560,c_513])).

tff(c_584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_563])).

tff(c_585,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_596,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_585,c_2])).

tff(c_652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_623,c_596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.41  
% 2.73/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.73/1.42  
% 2.73/1.42  %Foreground sorts:
% 2.73/1.42  
% 2.73/1.42  
% 2.73/1.42  %Background operators:
% 2.73/1.42  
% 2.73/1.42  
% 2.73/1.42  %Foreground operators:
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.73/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.42  
% 2.73/1.43  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 2.73/1.43  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.73/1.43  tff(f_69, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.73/1.43  tff(f_79, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.73/1.43  tff(f_86, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.73/1.43  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.73/1.43  tff(f_75, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.73/1.43  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.73/1.43  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.73/1.43  tff(c_46, plain, (![B_22, A_23]: (r1_xboole_0(B_22, A_23) | ~r1_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.43  tff(c_49, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_46])).
% 2.73/1.43  tff(c_334, plain, (![A_80, C_81, B_82]: (~r1_xboole_0(A_80, C_81) | ~r1_xboole_0(A_80, B_82) | r1_xboole_0(A_80, k2_xboole_0(B_82, C_81)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.73/1.43  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.43  tff(c_597, plain, (![B_128, C_129, A_130]: (r1_xboole_0(k2_xboole_0(B_128, C_129), A_130) | ~r1_xboole_0(A_130, C_129) | ~r1_xboole_0(A_130, B_128))), inference(resolution, [status(thm)], [c_334, c_2])).
% 2.73/1.43  tff(c_30, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.73/1.43  tff(c_615, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_597, c_30])).
% 2.73/1.43  tff(c_623, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_615])).
% 2.73/1.43  tff(c_66, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=A_28 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.73/1.43  tff(c_82, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_32, c_66])).
% 2.73/1.43  tff(c_36, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.73/1.43  tff(c_28, plain, (![A_19, B_20]: (r1_xboole_0(k1_tarski(A_19), B_20) | r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.73/1.43  tff(c_371, plain, (![A_97, B_98]: (k4_xboole_0(k1_tarski(A_97), B_98)=k1_tarski(A_97) | r2_hidden(A_97, B_98))), inference(resolution, [status(thm)], [c_28, c_66])).
% 2.73/1.43  tff(c_10, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_tarski(A_8, k4_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.43  tff(c_530, plain, (![A_124, B_125, A_126]: (r1_xboole_0(A_124, B_125) | ~r1_tarski(A_124, k1_tarski(A_126)) | r2_hidden(A_126, B_125))), inference(superposition, [status(thm), theory('equality')], [c_371, c_10])).
% 2.73/1.43  tff(c_534, plain, (![B_127]: (r1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), B_127) | r2_hidden('#skF_5', B_127))), inference(resolution, [status(thm)], [c_36, c_530])).
% 2.73/1.43  tff(c_20, plain, (![A_14, B_15]: (~r1_xboole_0(k3_xboole_0(A_14, B_15), B_15) | r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.73/1.43  tff(c_557, plain, (r1_xboole_0('#skF_2', '#skF_3') | r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_534, c_20])).
% 2.73/1.43  tff(c_560, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_557])).
% 2.73/1.43  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.73/1.43  tff(c_58, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k4_xboole_0(A_26, B_27)!=A_26)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.73/1.43  tff(c_64, plain, (![B_27, A_26]: (r1_xboole_0(B_27, A_26) | k4_xboole_0(A_26, B_27)!=A_26)), inference(resolution, [status(thm)], [c_58, c_2])).
% 2.73/1.43  tff(c_273, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, B_66) | ~r2_hidden(C_67, A_65))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.73/1.43  tff(c_498, plain, (![C_118, A_119, B_120]: (~r2_hidden(C_118, A_119) | ~r2_hidden(C_118, B_120) | k4_xboole_0(A_119, B_120)!=A_119)), inference(resolution, [status(thm)], [c_64, c_273])).
% 2.73/1.43  tff(c_513, plain, (![B_120]: (~r2_hidden('#skF_5', B_120) | k4_xboole_0('#skF_4', B_120)!='#skF_4')), inference(resolution, [status(thm)], [c_34, c_498])).
% 2.73/1.43  tff(c_563, plain, (k4_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(resolution, [status(thm)], [c_560, c_513])).
% 2.73/1.43  tff(c_584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_563])).
% 2.73/1.43  tff(c_585, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_557])).
% 2.73/1.43  tff(c_596, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_585, c_2])).
% 2.73/1.43  tff(c_652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_623, c_596])).
% 2.73/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.43  
% 2.73/1.43  Inference rules
% 2.73/1.43  ----------------------
% 2.73/1.43  #Ref     : 0
% 2.73/1.43  #Sup     : 146
% 2.73/1.43  #Fact    : 0
% 2.73/1.43  #Define  : 0
% 2.73/1.43  #Split   : 1
% 2.73/1.43  #Chain   : 0
% 2.73/1.43  #Close   : 0
% 2.73/1.43  
% 2.73/1.43  Ordering : KBO
% 2.73/1.43  
% 2.73/1.43  Simplification rules
% 2.73/1.43  ----------------------
% 2.73/1.43  #Subsume      : 14
% 2.73/1.43  #Demod        : 7
% 2.73/1.43  #Tautology    : 24
% 2.73/1.43  #SimpNegUnit  : 1
% 2.73/1.43  #BackRed      : 0
% 2.73/1.43  
% 2.73/1.43  #Partial instantiations: 0
% 2.73/1.43  #Strategies tried      : 1
% 2.73/1.43  
% 2.73/1.43  Timing (in seconds)
% 2.73/1.43  ----------------------
% 2.73/1.43  Preprocessing        : 0.30
% 2.73/1.43  Parsing              : 0.16
% 2.73/1.43  CNF conversion       : 0.02
% 2.73/1.43  Main loop            : 0.36
% 2.73/1.43  Inferencing          : 0.14
% 2.73/1.43  Reduction            : 0.09
% 2.73/1.43  Demodulation         : 0.06
% 2.73/1.43  BG Simplification    : 0.02
% 2.73/1.43  Subsumption          : 0.08
% 2.73/1.43  Abstraction          : 0.02
% 2.73/1.43  MUC search           : 0.00
% 2.73/1.43  Cooper               : 0.00
% 2.73/1.43  Total                : 0.70
% 2.73/1.44  Index Insertion      : 0.00
% 2.73/1.44  Index Deletion       : 0.00
% 2.73/1.44  Index Matching       : 0.00
% 2.73/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
