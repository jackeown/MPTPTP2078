%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:42 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   61 (  91 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 147 expanded)
%              Number of equality atoms :   30 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_43,axiom,(
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

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_38,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_76,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_104,plain,(
    ! [D_44,B_45,A_46] :
      ( D_44 = B_45
      | D_44 = A_46
      | ~ r2_hidden(D_44,k2_tarski(A_46,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_128,plain,(
    ! [D_47,A_48] :
      ( D_47 = A_48
      | D_47 = A_48
      | ~ r2_hidden(D_47,k1_tarski(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_104])).

tff(c_153,plain,(
    ! [A_51,A_52] :
      ( '#skF_1'(A_51,k1_tarski(A_52)) = A_52
      | r1_xboole_0(A_51,k1_tarski(A_52)) ) ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_267,plain,(
    ! [A_83,A_84] :
      ( k4_xboole_0(A_83,k1_tarski(A_84)) = A_83
      | '#skF_1'(A_83,k1_tarski(A_84)) = A_84 ) ),
    inference(resolution,[status(thm)],[c_153,c_10])).

tff(c_291,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_76])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_297,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_6])).

tff(c_303,plain,(
    r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_297])).

tff(c_311,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_303,c_10])).

tff(c_316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_311])).

tff(c_317,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_318,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_408,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_42])).

tff(c_54,plain,(
    ! [D_22,B_23] : r2_hidden(D_22,k2_tarski(D_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_57,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_54])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_343,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ r1_xboole_0(A_96,B_97)
      | ~ r2_hidden(C_98,B_97)
      | ~ r2_hidden(C_98,A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_421,plain,(
    ! [C_110,B_111,A_112] :
      ( ~ r2_hidden(C_110,B_111)
      | ~ r2_hidden(C_110,A_112)
      | k4_xboole_0(A_112,B_111) != A_112 ) ),
    inference(resolution,[status(thm)],[c_12,c_343])).

tff(c_466,plain,(
    ! [A_117,A_118] :
      ( ~ r2_hidden(A_117,A_118)
      | k4_xboole_0(A_118,k1_tarski(A_117)) != A_118 ) ),
    inference(resolution,[status(thm)],[c_57,c_421])).

tff(c_469,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_466])).

tff(c_480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_469])).

tff(c_481,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_482,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_516,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_44])).

tff(c_562,plain,(
    ! [A_138,B_139,C_140] :
      ( ~ r1_xboole_0(A_138,B_139)
      | ~ r2_hidden(C_140,B_139)
      | ~ r2_hidden(C_140,A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_671,plain,(
    ! [C_166,B_167,A_168] :
      ( ~ r2_hidden(C_166,B_167)
      | ~ r2_hidden(C_166,A_168)
      | k4_xboole_0(A_168,B_167) != A_168 ) ),
    inference(resolution,[status(thm)],[c_12,c_562])).

tff(c_744,plain,(
    ! [A_174,A_175] :
      ( ~ r2_hidden(A_174,A_175)
      | k4_xboole_0(A_175,k1_tarski(A_174)) != A_175 ) ),
    inference(resolution,[status(thm)],[c_57,c_671])).

tff(c_751,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_744])).

tff(c_756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_751])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.35  
% 2.55/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.35  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.55/1.35  
% 2.55/1.35  %Foreground sorts:
% 2.55/1.35  
% 2.55/1.35  
% 2.55/1.35  %Background operators:
% 2.55/1.35  
% 2.55/1.35  
% 2.55/1.35  %Foreground operators:
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.55/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.55/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.55/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.55/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.55/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.55/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.55/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.55/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.55/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.55/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.55/1.35  
% 2.55/1.37  tff(f_73, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.55/1.37  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.55/1.37  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.55/1.37  tff(f_58, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.55/1.37  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.55/1.37  tff(c_38, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.55/1.37  tff(c_76, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_38])).
% 2.55/1.37  tff(c_40, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.55/1.37  tff(c_64, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 2.55/1.37  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.37  tff(c_32, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.55/1.37  tff(c_104, plain, (![D_44, B_45, A_46]: (D_44=B_45 | D_44=A_46 | ~r2_hidden(D_44, k2_tarski(A_46, B_45)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.37  tff(c_128, plain, (![D_47, A_48]: (D_47=A_48 | D_47=A_48 | ~r2_hidden(D_47, k1_tarski(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_104])).
% 2.55/1.37  tff(c_153, plain, (![A_51, A_52]: ('#skF_1'(A_51, k1_tarski(A_52))=A_52 | r1_xboole_0(A_51, k1_tarski(A_52)))), inference(resolution, [status(thm)], [c_4, c_128])).
% 2.55/1.37  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.55/1.37  tff(c_267, plain, (![A_83, A_84]: (k4_xboole_0(A_83, k1_tarski(A_84))=A_83 | '#skF_1'(A_83, k1_tarski(A_84))=A_84)), inference(resolution, [status(thm)], [c_153, c_10])).
% 2.55/1.37  tff(c_291, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_267, c_76])).
% 2.55/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.37  tff(c_297, plain, (r2_hidden('#skF_5', '#skF_4') | r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_291, c_6])).
% 2.55/1.37  tff(c_303, plain, (r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_297])).
% 2.55/1.37  tff(c_311, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_303, c_10])).
% 2.55/1.37  tff(c_316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_311])).
% 2.55/1.37  tff(c_317, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_38])).
% 2.55/1.37  tff(c_318, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 2.55/1.37  tff(c_42, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.55/1.37  tff(c_408, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_318, c_42])).
% 2.55/1.37  tff(c_54, plain, (![D_22, B_23]: (r2_hidden(D_22, k2_tarski(D_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.37  tff(c_57, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_54])).
% 2.55/1.37  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.55/1.37  tff(c_343, plain, (![A_96, B_97, C_98]: (~r1_xboole_0(A_96, B_97) | ~r2_hidden(C_98, B_97) | ~r2_hidden(C_98, A_96))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.37  tff(c_421, plain, (![C_110, B_111, A_112]: (~r2_hidden(C_110, B_111) | ~r2_hidden(C_110, A_112) | k4_xboole_0(A_112, B_111)!=A_112)), inference(resolution, [status(thm)], [c_12, c_343])).
% 2.55/1.37  tff(c_466, plain, (![A_117, A_118]: (~r2_hidden(A_117, A_118) | k4_xboole_0(A_118, k1_tarski(A_117))!=A_118)), inference(resolution, [status(thm)], [c_57, c_421])).
% 2.55/1.37  tff(c_469, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_408, c_466])).
% 2.55/1.37  tff(c_480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_317, c_469])).
% 2.55/1.37  tff(c_481, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_40])).
% 2.55/1.37  tff(c_482, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 2.55/1.37  tff(c_44, plain, (~r2_hidden('#skF_5', '#skF_4') | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.55/1.37  tff(c_516, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_482, c_44])).
% 2.55/1.37  tff(c_562, plain, (![A_138, B_139, C_140]: (~r1_xboole_0(A_138, B_139) | ~r2_hidden(C_140, B_139) | ~r2_hidden(C_140, A_138))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.37  tff(c_671, plain, (![C_166, B_167, A_168]: (~r2_hidden(C_166, B_167) | ~r2_hidden(C_166, A_168) | k4_xboole_0(A_168, B_167)!=A_168)), inference(resolution, [status(thm)], [c_12, c_562])).
% 2.55/1.37  tff(c_744, plain, (![A_174, A_175]: (~r2_hidden(A_174, A_175) | k4_xboole_0(A_175, k1_tarski(A_174))!=A_175)), inference(resolution, [status(thm)], [c_57, c_671])).
% 2.55/1.37  tff(c_751, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_516, c_744])).
% 2.55/1.37  tff(c_756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_481, c_751])).
% 2.55/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.37  
% 2.55/1.37  Inference rules
% 2.55/1.37  ----------------------
% 2.55/1.37  #Ref     : 0
% 2.55/1.37  #Sup     : 161
% 2.55/1.37  #Fact    : 0
% 2.55/1.37  #Define  : 0
% 2.55/1.37  #Split   : 2
% 2.55/1.37  #Chain   : 0
% 2.55/1.37  #Close   : 0
% 2.55/1.37  
% 2.55/1.37  Ordering : KBO
% 2.55/1.37  
% 2.55/1.37  Simplification rules
% 2.55/1.37  ----------------------
% 2.55/1.37  #Subsume      : 9
% 2.55/1.37  #Demod        : 19
% 2.55/1.37  #Tautology    : 58
% 2.55/1.37  #SimpNegUnit  : 2
% 2.55/1.37  #BackRed      : 0
% 2.55/1.37  
% 2.55/1.37  #Partial instantiations: 0
% 2.55/1.37  #Strategies tried      : 1
% 2.55/1.37  
% 2.55/1.37  Timing (in seconds)
% 2.55/1.37  ----------------------
% 2.55/1.37  Preprocessing        : 0.29
% 2.55/1.37  Parsing              : 0.15
% 2.55/1.37  CNF conversion       : 0.02
% 2.55/1.37  Main loop            : 0.31
% 2.55/1.37  Inferencing          : 0.12
% 2.55/1.37  Reduction            : 0.08
% 2.55/1.37  Demodulation         : 0.06
% 2.55/1.37  BG Simplification    : 0.02
% 2.55/1.37  Subsumption          : 0.06
% 2.55/1.37  Abstraction          : 0.02
% 2.55/1.37  MUC search           : 0.00
% 2.55/1.37  Cooper               : 0.00
% 2.55/1.37  Total                : 0.63
% 2.55/1.37  Index Insertion      : 0.00
% 2.55/1.37  Index Deletion       : 0.00
% 2.55/1.37  Index Matching       : 0.00
% 2.55/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
