%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:41 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   71 (  97 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 144 expanded)
%              Number of equality atoms :   36 (  65 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_53,axiom,(
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

tff(f_76,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_66,plain,
    ( k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6'
    | r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_110,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_68,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_82,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_58,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_319,plain,(
    ! [E_99,C_100,B_101,A_102] :
      ( E_99 = C_100
      | E_99 = B_101
      | E_99 = A_102
      | ~ r2_hidden(E_99,k1_enumset1(A_102,B_101,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_560,plain,(
    ! [E_135,B_136,A_137] :
      ( E_135 = B_136
      | E_135 = A_137
      | E_135 = A_137
      | ~ r2_hidden(E_135,k2_tarski(A_137,B_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_319])).

tff(c_661,plain,(
    ! [E_143,A_144] :
      ( E_143 = A_144
      | E_143 = A_144
      | E_143 = A_144
      | ~ r2_hidden(E_143,k1_tarski(A_144)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_560])).

tff(c_697,plain,(
    ! [A_145,A_146] :
      ( '#skF_3'(A_145,k1_tarski(A_146)) = A_146
      | r1_xboole_0(A_145,k1_tarski(A_146)) ) ),
    inference(resolution,[status(thm)],[c_22,c_661])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_714,plain,(
    ! [A_149,A_150] :
      ( k4_xboole_0(A_149,k1_tarski(A_150)) = A_149
      | '#skF_3'(A_149,k1_tarski(A_150)) = A_150 ) ),
    inference(resolution,[status(thm)],[c_697,c_28])).

tff(c_752,plain,(
    '#skF_3'('#skF_6',k1_tarski('#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_110])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_767,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_24])).

tff(c_771,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_767])).

tff(c_777,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_771,c_28])).

tff(c_782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_777])).

tff(c_783,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_92,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [E_22,A_16,C_18] : r2_hidden(E_22,k1_enumset1(A_16,E_22,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_789,plain,(
    ! [A_155,B_156] : r2_hidden(A_155,k2_tarski(A_155,B_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_36])).

tff(c_792,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_789])).

tff(c_784,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_70,plain,
    ( k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6'
    | k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_826,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_70])).

tff(c_834,plain,(
    ! [D_169,B_170,A_171] :
      ( ~ r2_hidden(D_169,B_170)
      | ~ r2_hidden(D_169,k4_xboole_0(A_171,B_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_851,plain,(
    ! [D_172] :
      ( ~ r2_hidden(D_172,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_172,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_826,c_834])).

tff(c_863,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_792,c_851])).

tff(c_869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_863])).

tff(c_870,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_887,plain,(
    ! [A_186,B_187] : k1_enumset1(A_186,A_186,B_187) = k2_tarski(A_186,B_187) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [E_22,A_16,B_17] : r2_hidden(E_22,k1_enumset1(A_16,B_17,E_22)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_905,plain,(
    ! [B_188,A_189] : r2_hidden(B_188,k2_tarski(A_189,B_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_34])).

tff(c_908,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_905])).

tff(c_871,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_882,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_72])).

tff(c_927,plain,(
    ! [D_199,B_200,A_201] :
      ( ~ r2_hidden(D_199,B_200)
      | ~ r2_hidden(D_199,k4_xboole_0(A_201,B_200)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_942,plain,(
    ! [D_202] :
      ( ~ r2_hidden(D_202,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_202,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_927])).

tff(c_954,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_908,c_942])).

tff(c_960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_954])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:21:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.46  
% 3.11/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.46  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5
% 3.16/1.46  
% 3.16/1.46  %Foreground sorts:
% 3.16/1.46  
% 3.16/1.46  
% 3.16/1.46  %Background operators:
% 3.16/1.46  
% 3.16/1.46  
% 3.16/1.46  %Foreground operators:
% 3.16/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.16/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.46  tff('#skF_7', type, '#skF_7': $i).
% 3.16/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.16/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.16/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.16/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.16/1.46  tff('#skF_9', type, '#skF_9': $i).
% 3.16/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.16/1.46  tff('#skF_8', type, '#skF_8': $i).
% 3.16/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.46  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.16/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.46  
% 3.16/1.47  tff(f_91, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.16/1.47  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.16/1.47  tff(f_76, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.16/1.47  tff(f_78, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.16/1.47  tff(f_74, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.16/1.47  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.16/1.47  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.16/1.47  tff(c_66, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6' | r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.16/1.47  tff(c_110, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_66])).
% 3.16/1.47  tff(c_68, plain, (~r2_hidden('#skF_7', '#skF_6') | r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.16/1.47  tff(c_82, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_68])).
% 3.16/1.47  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.47  tff(c_56, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.47  tff(c_58, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.16/1.47  tff(c_319, plain, (![E_99, C_100, B_101, A_102]: (E_99=C_100 | E_99=B_101 | E_99=A_102 | ~r2_hidden(E_99, k1_enumset1(A_102, B_101, C_100)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.16/1.47  tff(c_560, plain, (![E_135, B_136, A_137]: (E_135=B_136 | E_135=A_137 | E_135=A_137 | ~r2_hidden(E_135, k2_tarski(A_137, B_136)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_319])).
% 3.16/1.47  tff(c_661, plain, (![E_143, A_144]: (E_143=A_144 | E_143=A_144 | E_143=A_144 | ~r2_hidden(E_143, k1_tarski(A_144)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_560])).
% 3.16/1.47  tff(c_697, plain, (![A_145, A_146]: ('#skF_3'(A_145, k1_tarski(A_146))=A_146 | r1_xboole_0(A_145, k1_tarski(A_146)))), inference(resolution, [status(thm)], [c_22, c_661])).
% 3.16/1.47  tff(c_28, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.16/1.47  tff(c_714, plain, (![A_149, A_150]: (k4_xboole_0(A_149, k1_tarski(A_150))=A_149 | '#skF_3'(A_149, k1_tarski(A_150))=A_150)), inference(resolution, [status(thm)], [c_697, c_28])).
% 3.16/1.47  tff(c_752, plain, ('#skF_3'('#skF_6', k1_tarski('#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_714, c_110])).
% 3.16/1.47  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.47  tff(c_767, plain, (r2_hidden('#skF_7', '#skF_6') | r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_752, c_24])).
% 3.16/1.47  tff(c_771, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_82, c_767])).
% 3.16/1.47  tff(c_777, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_771, c_28])).
% 3.16/1.47  tff(c_782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_777])).
% 3.16/1.47  tff(c_783, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_66])).
% 3.16/1.47  tff(c_92, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.16/1.47  tff(c_36, plain, (![E_22, A_16, C_18]: (r2_hidden(E_22, k1_enumset1(A_16, E_22, C_18)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.16/1.47  tff(c_789, plain, (![A_155, B_156]: (r2_hidden(A_155, k2_tarski(A_155, B_156)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_36])).
% 3.16/1.47  tff(c_792, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_789])).
% 3.16/1.47  tff(c_784, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(splitRight, [status(thm)], [c_66])).
% 3.16/1.47  tff(c_70, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6' | k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.16/1.47  tff(c_826, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_784, c_70])).
% 3.16/1.47  tff(c_834, plain, (![D_169, B_170, A_171]: (~r2_hidden(D_169, B_170) | ~r2_hidden(D_169, k4_xboole_0(A_171, B_170)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.47  tff(c_851, plain, (![D_172]: (~r2_hidden(D_172, k1_tarski('#skF_9')) | ~r2_hidden(D_172, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_826, c_834])).
% 3.16/1.47  tff(c_863, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_792, c_851])).
% 3.16/1.47  tff(c_869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_783, c_863])).
% 3.16/1.47  tff(c_870, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_68])).
% 3.16/1.47  tff(c_887, plain, (![A_186, B_187]: (k1_enumset1(A_186, A_186, B_187)=k2_tarski(A_186, B_187))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.16/1.47  tff(c_34, plain, (![E_22, A_16, B_17]: (r2_hidden(E_22, k1_enumset1(A_16, B_17, E_22)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.16/1.47  tff(c_905, plain, (![B_188, A_189]: (r2_hidden(B_188, k2_tarski(A_189, B_188)))), inference(superposition, [status(thm), theory('equality')], [c_887, c_34])).
% 3.16/1.47  tff(c_908, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_905])).
% 3.16/1.47  tff(c_871, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 3.16/1.47  tff(c_72, plain, (~r2_hidden('#skF_7', '#skF_6') | k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.16/1.47  tff(c_882, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_871, c_72])).
% 3.16/1.47  tff(c_927, plain, (![D_199, B_200, A_201]: (~r2_hidden(D_199, B_200) | ~r2_hidden(D_199, k4_xboole_0(A_201, B_200)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.47  tff(c_942, plain, (![D_202]: (~r2_hidden(D_202, k1_tarski('#skF_9')) | ~r2_hidden(D_202, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_882, c_927])).
% 3.16/1.47  tff(c_954, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_908, c_942])).
% 3.16/1.47  tff(c_960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_870, c_954])).
% 3.16/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.47  
% 3.16/1.47  Inference rules
% 3.16/1.47  ----------------------
% 3.16/1.47  #Ref     : 0
% 3.16/1.47  #Sup     : 202
% 3.16/1.47  #Fact    : 0
% 3.16/1.47  #Define  : 0
% 3.16/1.47  #Split   : 2
% 3.16/1.47  #Chain   : 0
% 3.16/1.47  #Close   : 0
% 3.16/1.47  
% 3.16/1.47  Ordering : KBO
% 3.16/1.47  
% 3.16/1.47  Simplification rules
% 3.16/1.47  ----------------------
% 3.16/1.47  #Subsume      : 14
% 3.16/1.47  #Demod        : 18
% 3.16/1.47  #Tautology    : 59
% 3.16/1.47  #SimpNegUnit  : 2
% 3.16/1.47  #BackRed      : 0
% 3.16/1.47  
% 3.16/1.47  #Partial instantiations: 0
% 3.16/1.47  #Strategies tried      : 1
% 3.16/1.47  
% 3.16/1.47  Timing (in seconds)
% 3.16/1.47  ----------------------
% 3.16/1.47  Preprocessing        : 0.32
% 3.16/1.47  Parsing              : 0.16
% 3.16/1.47  CNF conversion       : 0.02
% 3.16/1.47  Main loop            : 0.38
% 3.16/1.47  Inferencing          : 0.14
% 3.16/1.48  Reduction            : 0.10
% 3.16/1.48  Demodulation         : 0.07
% 3.16/1.48  BG Simplification    : 0.03
% 3.16/1.48  Subsumption          : 0.08
% 3.16/1.48  Abstraction          : 0.03
% 3.16/1.48  MUC search           : 0.00
% 3.16/1.48  Cooper               : 0.00
% 3.16/1.48  Total                : 0.73
% 3.16/1.48  Index Insertion      : 0.00
% 3.16/1.48  Index Deletion       : 0.00
% 3.16/1.48  Index Matching       : 0.00
% 3.16/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
