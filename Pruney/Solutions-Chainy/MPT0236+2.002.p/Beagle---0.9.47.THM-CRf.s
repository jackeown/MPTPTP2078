%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:44 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 137 expanded)
%              Number of leaves         :   16 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :   67 ( 289 expanded)
%              Number of equality atoms :   23 ( 125 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > #nlpp > k3_tarski > k1_tarski > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(c_32,plain,(
    k3_tarski(k1_tarski('#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_4'(A_6,B_7),A_6)
      | r2_hidden('#skF_5'(A_6,B_7),B_7)
      | k3_tarski(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_353,plain,(
    ! [A_77,B_78,D_79] :
      ( r2_hidden('#skF_4'(A_77,B_78),A_77)
      | ~ r2_hidden(D_79,A_77)
      | ~ r2_hidden('#skF_5'(A_77,B_78),D_79)
      | k3_tarski(A_77) = B_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_381,plain,(
    ! [B_80,A_81] :
      ( ~ r2_hidden(B_80,A_81)
      | r2_hidden('#skF_4'(A_81,B_80),A_81)
      | k3_tarski(A_81) = B_80 ) ),
    inference(resolution,[status(thm)],[c_28,c_353])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_400,plain,(
    ! [A_82,B_83] :
      ( '#skF_4'(k1_tarski(A_82),B_83) = A_82
      | ~ r2_hidden(B_83,k1_tarski(A_82))
      | k3_tarski(k1_tarski(A_82)) = B_83 ) ),
    inference(resolution,[status(thm)],[c_381,c_2])).

tff(c_440,plain,(
    ! [C_84] :
      ( '#skF_4'(k1_tarski(C_84),C_84) = C_84
      | k3_tarski(k1_tarski(C_84)) = C_84 ) ),
    inference(resolution,[status(thm)],[c_4,c_400])).

tff(c_501,plain,(
    '#skF_4'(k1_tarski('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_32])).

tff(c_30,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7),'#skF_4'(A_6,B_7))
      | r2_hidden('#skF_5'(A_6,B_7),B_7)
      | k3_tarski(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_511,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_30])).

tff(c_521,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_511])).

tff(c_525,plain,(
    r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_521])).

tff(c_620,plain,(
    ! [A_89,B_90,D_91] :
      ( r2_hidden('#skF_3'(A_89,B_90),'#skF_4'(A_89,B_90))
      | ~ r2_hidden(D_91,A_89)
      | ~ r2_hidden('#skF_5'(A_89,B_90),D_91)
      | k3_tarski(A_89) = B_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_624,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_4'(k1_tarski('#skF_7'),'#skF_7'))
    | ~ r2_hidden('#skF_7',k1_tarski('#skF_7'))
    | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_525,c_620])).

tff(c_650,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_501,c_624])).

tff(c_651,plain,(
    r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_650])).

tff(c_20,plain,(
    ! [A_6,B_7,D_20] :
      ( ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | ~ r2_hidden(D_20,A_6)
      | ~ r2_hidden('#skF_5'(A_6,B_7),D_20)
      | k3_tarski(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_662,plain,(
    ! [D_20] :
      ( ~ r2_hidden(D_20,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),D_20)
      | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_651,c_20])).

tff(c_679,plain,(
    ! [D_92] :
      ( ~ r2_hidden(D_92,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),D_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_662])).

tff(c_685,plain,(
    ~ r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_525,c_679])).

tff(c_716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_685])).

tff(c_717,plain,(
    r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_521])).

tff(c_26,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | r2_hidden('#skF_5'(A_6,B_7),B_7)
      | k3_tarski(A_6) = B_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_725,plain,
    ( r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_717,c_26])).

tff(c_736,plain,(
    r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_725])).

tff(c_718,plain,(
    ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_521])).

tff(c_755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.41  
% 2.71/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.41  %$ r2_hidden > #nlpp > k3_tarski > k1_tarski > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.71/1.41  
% 2.71/1.41  %Foreground sorts:
% 2.71/1.41  
% 2.71/1.41  
% 2.71/1.41  %Background operators:
% 2.71/1.41  
% 2.71/1.41  
% 2.71/1.41  %Foreground operators:
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.41  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.71/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.71/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.71/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.71/1.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.71/1.41  
% 2.71/1.42  tff(f_45, negated_conjecture, ~(![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.71/1.42  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.71/1.42  tff(f_42, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.71/1.42  tff(c_32, plain, (k3_tarski(k1_tarski('#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.71/1.42  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.42  tff(c_28, plain, (![A_6, B_7]: (r2_hidden('#skF_4'(A_6, B_7), A_6) | r2_hidden('#skF_5'(A_6, B_7), B_7) | k3_tarski(A_6)=B_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.42  tff(c_353, plain, (![A_77, B_78, D_79]: (r2_hidden('#skF_4'(A_77, B_78), A_77) | ~r2_hidden(D_79, A_77) | ~r2_hidden('#skF_5'(A_77, B_78), D_79) | k3_tarski(A_77)=B_78)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.42  tff(c_381, plain, (![B_80, A_81]: (~r2_hidden(B_80, A_81) | r2_hidden('#skF_4'(A_81, B_80), A_81) | k3_tarski(A_81)=B_80)), inference(resolution, [status(thm)], [c_28, c_353])).
% 2.71/1.42  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.42  tff(c_400, plain, (![A_82, B_83]: ('#skF_4'(k1_tarski(A_82), B_83)=A_82 | ~r2_hidden(B_83, k1_tarski(A_82)) | k3_tarski(k1_tarski(A_82))=B_83)), inference(resolution, [status(thm)], [c_381, c_2])).
% 2.71/1.42  tff(c_440, plain, (![C_84]: ('#skF_4'(k1_tarski(C_84), C_84)=C_84 | k3_tarski(k1_tarski(C_84))=C_84)), inference(resolution, [status(thm)], [c_4, c_400])).
% 2.71/1.42  tff(c_501, plain, ('#skF_4'(k1_tarski('#skF_7'), '#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_440, c_32])).
% 2.71/1.42  tff(c_30, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7), '#skF_4'(A_6, B_7)) | r2_hidden('#skF_5'(A_6, B_7), B_7) | k3_tarski(A_6)=B_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.42  tff(c_511, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | k3_tarski(k1_tarski('#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_501, c_30])).
% 2.71/1.42  tff(c_521, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_32, c_511])).
% 2.71/1.42  tff(c_525, plain, (r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_521])).
% 2.71/1.42  tff(c_620, plain, (![A_89, B_90, D_91]: (r2_hidden('#skF_3'(A_89, B_90), '#skF_4'(A_89, B_90)) | ~r2_hidden(D_91, A_89) | ~r2_hidden('#skF_5'(A_89, B_90), D_91) | k3_tarski(A_89)=B_90)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.42  tff(c_624, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_7'), '#skF_7'), '#skF_4'(k1_tarski('#skF_7'), '#skF_7')) | ~r2_hidden('#skF_7', k1_tarski('#skF_7')) | k3_tarski(k1_tarski('#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_525, c_620])).
% 2.71/1.42  tff(c_650, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | k3_tarski(k1_tarski('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_501, c_624])).
% 2.71/1.42  tff(c_651, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_32, c_650])).
% 2.71/1.42  tff(c_20, plain, (![A_6, B_7, D_20]: (~r2_hidden('#skF_3'(A_6, B_7), B_7) | ~r2_hidden(D_20, A_6) | ~r2_hidden('#skF_5'(A_6, B_7), D_20) | k3_tarski(A_6)=B_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.42  tff(c_662, plain, (![D_20]: (~r2_hidden(D_20, k1_tarski('#skF_7')) | ~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), D_20) | k3_tarski(k1_tarski('#skF_7'))='#skF_7')), inference(resolution, [status(thm)], [c_651, c_20])).
% 2.71/1.42  tff(c_679, plain, (![D_92]: (~r2_hidden(D_92, k1_tarski('#skF_7')) | ~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), D_92))), inference(negUnitSimplification, [status(thm)], [c_32, c_662])).
% 2.71/1.42  tff(c_685, plain, (~r2_hidden('#skF_7', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_525, c_679])).
% 2.71/1.42  tff(c_716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_685])).
% 2.71/1.42  tff(c_717, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_521])).
% 2.71/1.42  tff(c_26, plain, (![A_6, B_7]: (~r2_hidden('#skF_3'(A_6, B_7), B_7) | r2_hidden('#skF_5'(A_6, B_7), B_7) | k3_tarski(A_6)=B_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.71/1.42  tff(c_725, plain, (r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | k3_tarski(k1_tarski('#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_717, c_26])).
% 2.71/1.42  tff(c_736, plain, (r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_32, c_725])).
% 2.71/1.42  tff(c_718, plain, (~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_521])).
% 2.71/1.42  tff(c_755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_736, c_718])).
% 2.71/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.42  
% 2.71/1.42  Inference rules
% 2.71/1.42  ----------------------
% 2.71/1.42  #Ref     : 0
% 2.71/1.42  #Sup     : 176
% 2.71/1.42  #Fact    : 0
% 2.71/1.42  #Define  : 0
% 2.71/1.42  #Split   : 1
% 2.71/1.42  #Chain   : 0
% 2.71/1.42  #Close   : 0
% 2.71/1.42  
% 2.71/1.42  Ordering : KBO
% 2.71/1.42  
% 2.71/1.42  Simplification rules
% 2.71/1.42  ----------------------
% 2.71/1.42  #Subsume      : 4
% 2.71/1.42  #Demod        : 24
% 2.71/1.42  #Tautology    : 27
% 2.71/1.42  #SimpNegUnit  : 12
% 2.71/1.42  #BackRed      : 0
% 2.71/1.42  
% 2.71/1.42  #Partial instantiations: 0
% 2.71/1.42  #Strategies tried      : 1
% 2.71/1.42  
% 2.71/1.42  Timing (in seconds)
% 2.71/1.42  ----------------------
% 2.71/1.43  Preprocessing        : 0.27
% 2.71/1.43  Parsing              : 0.14
% 2.71/1.43  CNF conversion       : 0.02
% 2.71/1.43  Main loop            : 0.39
% 2.71/1.43  Inferencing          : 0.15
% 2.71/1.43  Reduction            : 0.09
% 2.71/1.43  Demodulation         : 0.06
% 2.71/1.43  BG Simplification    : 0.02
% 2.71/1.43  Subsumption          : 0.10
% 2.71/1.43  Abstraction          : 0.03
% 2.71/1.43  MUC search           : 0.00
% 2.71/1.43  Cooper               : 0.00
% 2.71/1.43  Total                : 0.70
% 2.71/1.43  Index Insertion      : 0.00
% 2.71/1.43  Index Deletion       : 0.00
% 2.71/1.43  Index Matching       : 0.00
% 2.71/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
