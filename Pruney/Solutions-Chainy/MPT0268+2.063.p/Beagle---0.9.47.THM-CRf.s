%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:42 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   56 (  73 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 (  94 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_95,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(k1_tarski(A_40),B_41)
      | r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_139,plain,(
    ! [B_46,A_47] :
      ( r1_xboole_0(B_46,k1_tarski(A_47))
      | r2_hidden(A_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_95,c_20])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_221,plain,(
    ! [B_62,A_63] :
      ( k4_xboole_0(B_62,k1_tarski(A_63)) = B_62
      | r2_hidden(A_63,B_62) ) ),
    inference(resolution,[status(thm)],[c_139,c_26])).

tff(c_54,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_147,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_240,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_147])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_240])).

tff(c_264,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_48,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,(
    ! [D_29,B_30] : r2_hidden(D_29,k2_tarski(D_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_74,plain,(
    ! [A_21] : r2_hidden(A_21,k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_71])).

tff(c_265,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_58,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_296,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_58])).

tff(c_371,plain,(
    ! [D_66,B_67,A_68] :
      ( ~ r2_hidden(D_66,B_67)
      | ~ r2_hidden(D_66,k4_xboole_0(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_395,plain,(
    ! [D_71] :
      ( ~ r2_hidden(D_71,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_371])).

tff(c_399,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_395])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_399])).

tff(c_404,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_405,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_476,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_60])).

tff(c_540,plain,(
    ! [D_89,B_90,A_91] :
      ( ~ r2_hidden(D_89,B_90)
      | ~ r2_hidden(D_89,k4_xboole_0(A_91,B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_550,plain,(
    ! [D_92] :
      ( ~ r2_hidden(D_92,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_92,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_540])).

tff(c_554,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_550])).

tff(c_558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_554])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:58:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.31  
% 2.13/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.31  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3
% 2.13/1.31  
% 2.13/1.31  %Foreground sorts:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Background operators:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Foreground operators:
% 2.13/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.13/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.13/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.13/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.13/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.31  
% 2.13/1.32  tff(f_71, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.13/1.32  tff(f_65, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.13/1.32  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.13/1.32  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.13/1.32  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.13/1.32  tff(f_56, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.13/1.32  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.13/1.32  tff(c_56, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.13/1.32  tff(c_90, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_56])).
% 2.13/1.32  tff(c_95, plain, (![A_40, B_41]: (r1_xboole_0(k1_tarski(A_40), B_41) | r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.13/1.32  tff(c_20, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.32  tff(c_139, plain, (![B_46, A_47]: (r1_xboole_0(B_46, k1_tarski(A_47)) | r2_hidden(A_47, B_46))), inference(resolution, [status(thm)], [c_95, c_20])).
% 2.13/1.32  tff(c_26, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.32  tff(c_221, plain, (![B_62, A_63]: (k4_xboole_0(B_62, k1_tarski(A_63))=B_62 | r2_hidden(A_63, B_62))), inference(resolution, [status(thm)], [c_139, c_26])).
% 2.13/1.32  tff(c_54, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.13/1.32  tff(c_147, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_54])).
% 2.13/1.32  tff(c_240, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_221, c_147])).
% 2.13/1.32  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_240])).
% 2.13/1.32  tff(c_264, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 2.13/1.32  tff(c_48, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.32  tff(c_71, plain, (![D_29, B_30]: (r2_hidden(D_29, k2_tarski(D_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.13/1.32  tff(c_74, plain, (![A_21]: (r2_hidden(A_21, k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_71])).
% 2.13/1.32  tff(c_265, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_54])).
% 2.13/1.32  tff(c_58, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.13/1.32  tff(c_296, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_265, c_58])).
% 2.13/1.32  tff(c_371, plain, (![D_66, B_67, A_68]: (~r2_hidden(D_66, B_67) | ~r2_hidden(D_66, k4_xboole_0(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.32  tff(c_395, plain, (![D_71]: (~r2_hidden(D_71, k1_tarski('#skF_8')) | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_296, c_371])).
% 2.13/1.32  tff(c_399, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_74, c_395])).
% 2.13/1.32  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_264, c_399])).
% 2.13/1.32  tff(c_404, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_56])).
% 2.13/1.32  tff(c_405, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 2.13/1.32  tff(c_60, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.13/1.32  tff(c_476, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_405, c_60])).
% 2.13/1.32  tff(c_540, plain, (![D_89, B_90, A_91]: (~r2_hidden(D_89, B_90) | ~r2_hidden(D_89, k4_xboole_0(A_91, B_90)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.32  tff(c_550, plain, (![D_92]: (~r2_hidden(D_92, k1_tarski('#skF_8')) | ~r2_hidden(D_92, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_476, c_540])).
% 2.13/1.32  tff(c_554, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_74, c_550])).
% 2.13/1.32  tff(c_558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_404, c_554])).
% 2.13/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.32  
% 2.13/1.32  Inference rules
% 2.13/1.32  ----------------------
% 2.13/1.32  #Ref     : 0
% 2.13/1.32  #Sup     : 126
% 2.13/1.32  #Fact    : 0
% 2.13/1.32  #Define  : 0
% 2.13/1.32  #Split   : 2
% 2.13/1.32  #Chain   : 0
% 2.13/1.32  #Close   : 0
% 2.13/1.32  
% 2.13/1.32  Ordering : KBO
% 2.13/1.32  
% 2.13/1.33  Simplification rules
% 2.13/1.33  ----------------------
% 2.13/1.33  #Subsume      : 8
% 2.13/1.33  #Demod        : 42
% 2.13/1.33  #Tautology    : 74
% 2.13/1.33  #SimpNegUnit  : 1
% 2.13/1.33  #BackRed      : 0
% 2.13/1.33  
% 2.13/1.33  #Partial instantiations: 0
% 2.13/1.33  #Strategies tried      : 1
% 2.13/1.33  
% 2.13/1.33  Timing (in seconds)
% 2.13/1.33  ----------------------
% 2.13/1.33  Preprocessing        : 0.31
% 2.13/1.33  Parsing              : 0.16
% 2.13/1.33  CNF conversion       : 0.02
% 2.13/1.33  Main loop            : 0.25
% 2.13/1.33  Inferencing          : 0.09
% 2.13/1.33  Reduction            : 0.07
% 2.13/1.33  Demodulation         : 0.05
% 2.13/1.33  BG Simplification    : 0.02
% 2.13/1.33  Subsumption          : 0.04
% 2.13/1.33  Abstraction          : 0.02
% 2.13/1.33  MUC search           : 0.00
% 2.13/1.33  Cooper               : 0.00
% 2.13/1.33  Total                : 0.58
% 2.13/1.33  Index Insertion      : 0.00
% 2.13/1.33  Index Deletion       : 0.00
% 2.13/1.33  Index Matching       : 0.00
% 2.13/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
