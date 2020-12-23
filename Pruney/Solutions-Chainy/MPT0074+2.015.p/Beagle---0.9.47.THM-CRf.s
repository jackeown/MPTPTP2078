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
% DateTime   : Thu Dec  3 09:43:28 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   54 (  72 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 103 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_68,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_56,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_476,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76),B_76)
      | r2_hidden('#skF_2'(A_75,B_76),A_75)
      | B_76 = A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ! [A_20] : r1_xboole_0(A_20,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_119,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,k3_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_122,plain,(
    ! [A_13,C_35] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_35,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_119])).

tff(c_124,plain,(
    ! [C_35] : ~ r2_hidden(C_35,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_122])).

tff(c_619,plain,(
    ! [B_89] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_89),B_89)
      | k1_xboole_0 = B_89 ) ),
    inference(resolution,[status(thm)],[c_476,c_124])).

tff(c_34,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_54,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_54])).

tff(c_231,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_xboole_0(A_46,C_47)
      | ~ r1_xboole_0(B_48,C_47)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_262,plain,(
    ! [A_50] :
      ( r1_xboole_0(A_50,'#skF_5')
      | ~ r1_tarski(A_50,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_59,c_231])).

tff(c_22,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_71,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_83,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_92,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_107,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_92])).

tff(c_116,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_107])).

tff(c_14,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_150,plain,(
    ! [C_10] :
      ( ~ r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_10,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_14])).

tff(c_183,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_270,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_262,c_183])).

tff(c_278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_270])).

tff(c_279,plain,(
    ! [C_10] : ~ r2_hidden(C_10,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_629,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_619,c_279])).

tff(c_643,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.37  
% 2.44/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.44/1.37  
% 2.44/1.37  %Foreground sorts:
% 2.44/1.37  
% 2.44/1.37  
% 2.44/1.37  %Background operators:
% 2.44/1.37  
% 2.44/1.37  
% 2.44/1.37  %Foreground operators:
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.44/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.44/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.44/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.44/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.44/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.44/1.37  
% 2.72/1.39  tff(f_77, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.72/1.39  tff(f_36, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.72/1.39  tff(f_68, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.72/1.39  tff(f_56, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.72/1.39  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.72/1.39  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.72/1.39  tff(f_66, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.72/1.39  tff(f_58, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.72/1.39  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.72/1.39  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.72/1.39  tff(c_30, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.39  tff(c_476, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75, B_76), B_76) | r2_hidden('#skF_2'(A_75, B_76), A_75) | B_76=A_75)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.72/1.39  tff(c_28, plain, (![A_20]: (r1_xboole_0(A_20, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.72/1.39  tff(c_20, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.72/1.39  tff(c_119, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.39  tff(c_122, plain, (![A_13, C_35]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_119])).
% 2.72/1.39  tff(c_124, plain, (![C_35]: (~r2_hidden(C_35, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_122])).
% 2.72/1.39  tff(c_619, plain, (![B_89]: (r2_hidden('#skF_1'(k1_xboole_0, B_89), B_89) | k1_xboole_0=B_89)), inference(resolution, [status(thm)], [c_476, c_124])).
% 2.72/1.39  tff(c_34, plain, (r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.39  tff(c_32, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.39  tff(c_54, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.39  tff(c_59, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_54])).
% 2.72/1.39  tff(c_231, plain, (![A_46, C_47, B_48]: (r1_xboole_0(A_46, C_47) | ~r1_xboole_0(B_48, C_47) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.72/1.39  tff(c_262, plain, (![A_50]: (r1_xboole_0(A_50, '#skF_5') | ~r1_tarski(A_50, '#skF_6'))), inference(resolution, [status(thm)], [c_59, c_231])).
% 2.72/1.39  tff(c_22, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.72/1.39  tff(c_36, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.39  tff(c_71, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.72/1.39  tff(c_83, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_71])).
% 2.72/1.39  tff(c_92, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.39  tff(c_107, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_83, c_92])).
% 2.72/1.39  tff(c_116, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_107])).
% 2.72/1.39  tff(c_14, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.39  tff(c_150, plain, (![C_10]: (~r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_10, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_14])).
% 2.72/1.39  tff(c_183, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_150])).
% 2.72/1.39  tff(c_270, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_262, c_183])).
% 2.72/1.39  tff(c_278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_270])).
% 2.72/1.39  tff(c_279, plain, (![C_10]: (~r2_hidden(C_10, '#skF_4'))), inference(splitRight, [status(thm)], [c_150])).
% 2.72/1.39  tff(c_629, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_619, c_279])).
% 2.72/1.39  tff(c_643, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_629])).
% 2.72/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.39  
% 2.72/1.39  Inference rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Ref     : 0
% 2.72/1.39  #Sup     : 150
% 2.72/1.39  #Fact    : 0
% 2.72/1.39  #Define  : 0
% 2.72/1.39  #Split   : 6
% 2.72/1.39  #Chain   : 0
% 2.72/1.39  #Close   : 0
% 2.72/1.39  
% 2.72/1.39  Ordering : KBO
% 2.72/1.39  
% 2.72/1.39  Simplification rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Subsume      : 25
% 2.72/1.39  #Demod        : 26
% 2.72/1.39  #Tautology    : 37
% 2.72/1.39  #SimpNegUnit  : 4
% 2.72/1.39  #BackRed      : 0
% 2.72/1.39  
% 2.72/1.39  #Partial instantiations: 0
% 2.72/1.39  #Strategies tried      : 1
% 2.72/1.39  
% 2.72/1.39  Timing (in seconds)
% 2.72/1.39  ----------------------
% 2.72/1.39  Preprocessing        : 0.29
% 2.72/1.39  Parsing              : 0.15
% 2.72/1.39  CNF conversion       : 0.02
% 2.72/1.39  Main loop            : 0.33
% 2.72/1.39  Inferencing          : 0.13
% 2.72/1.39  Reduction            : 0.09
% 2.72/1.39  Demodulation         : 0.06
% 2.72/1.39  BG Simplification    : 0.02
% 2.72/1.39  Subsumption          : 0.07
% 2.72/1.39  Abstraction          : 0.01
% 2.72/1.39  MUC search           : 0.00
% 2.72/1.39  Cooper               : 0.00
% 2.72/1.39  Total                : 0.65
% 2.72/1.39  Index Insertion      : 0.00
% 2.72/1.39  Index Deletion       : 0.00
% 2.72/1.39  Index Matching       : 0.00
% 2.72/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
