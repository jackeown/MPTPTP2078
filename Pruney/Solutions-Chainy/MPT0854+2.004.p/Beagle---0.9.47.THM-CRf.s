%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:51 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   44 (  62 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   45 (  94 expanded)
%              Number of equality atoms :   16 (  29 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( r2_hidden(k1_mcart_1(A),B)
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_30,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_7'),'#skF_9')
    | ~ r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_51,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    r2_hidden('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_58,plain,(
    ! [A_60,B_61,D_62] :
      ( k4_tarski('#skF_5'(A_60,B_61,k2_zfmisc_1(A_60,B_61),D_62),'#skF_6'(A_60,B_61,k2_zfmisc_1(A_60,B_61),D_62)) = D_62
      | ~ r2_hidden(D_62,k2_zfmisc_1(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_35,B_36] : k2_mcart_1(k4_tarski(A_35,B_36)) = B_36 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    ! [A_63,B_64,D_65] :
      ( '#skF_6'(A_63,B_64,k2_zfmisc_1(A_63,B_64),D_65) = k2_mcart_1(D_65)
      | ~ r2_hidden(D_65,k2_zfmisc_1(A_63,B_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_28])).

tff(c_107,plain,(
    '#skF_6'('#skF_8','#skF_9',k2_zfmisc_1('#skF_8','#skF_9'),'#skF_7') = k2_mcart_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_76])).

tff(c_4,plain,(
    ! [A_1,B_2,D_28] :
      ( k4_tarski('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),'#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28)) = D_28
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_111,plain,
    ( k4_tarski('#skF_5'('#skF_8','#skF_9',k2_zfmisc_1('#skF_8','#skF_9'),'#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | ~ r2_hidden('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_4])).

tff(c_118,plain,(
    k4_tarski('#skF_5'('#skF_8','#skF_9',k2_zfmisc_1('#skF_8','#skF_9'),'#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_111])).

tff(c_26,plain,(
    ! [A_35,B_36] : k1_mcart_1(k4_tarski(A_35,B_36)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_136,plain,(
    '#skF_5'('#skF_8','#skF_9',k2_zfmisc_1('#skF_8','#skF_9'),'#skF_7') = k1_mcart_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_26])).

tff(c_8,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_1)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,
    ( r2_hidden(k1_mcart_1('#skF_7'),'#skF_8')
    | ~ r2_hidden('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_8])).

tff(c_154,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_148])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_154])).

tff(c_157,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_7'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_165,plain,(
    ! [A_90,B_91,D_92] :
      ( k4_tarski('#skF_5'(A_90,B_91,k2_zfmisc_1(A_90,B_91),D_92),'#skF_6'(A_90,B_91,k2_zfmisc_1(A_90,B_91),D_92)) = D_92
      | ~ r2_hidden(D_92,k2_zfmisc_1(A_90,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_183,plain,(
    ! [A_93,B_94,D_95] :
      ( '#skF_6'(A_93,B_94,k2_zfmisc_1(A_93,B_94),D_95) = k2_mcart_1(D_95)
      | ~ r2_hidden(D_95,k2_zfmisc_1(A_93,B_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_28])).

tff(c_214,plain,(
    '#skF_6'('#skF_8','#skF_9',k2_zfmisc_1('#skF_8','#skF_9'),'#skF_7') = k2_mcart_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_183])).

tff(c_6,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),B_2)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_221,plain,
    ( r2_hidden(k2_mcart_1('#skF_7'),'#skF_9')
    | ~ r2_hidden('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_6])).

tff(c_227,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_221])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 19:42:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.21  
% 1.97/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.21  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 1.97/1.21  
% 1.97/1.21  %Foreground sorts:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Background operators:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Foreground operators:
% 1.97/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.97/1.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.97/1.21  tff('#skF_7', type, '#skF_7': $i).
% 1.97/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.97/1.21  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 1.97/1.21  tff('#skF_9', type, '#skF_9': $i).
% 1.97/1.21  tff('#skF_8', type, '#skF_8': $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.21  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.97/1.21  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 1.97/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.21  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.97/1.21  
% 1.97/1.22  tff(f_48, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.97/1.22  tff(f_37, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 1.97/1.22  tff(f_41, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.97/1.22  tff(c_30, plain, (~r2_hidden(k2_mcart_1('#skF_7'), '#skF_9') | ~r2_hidden(k1_mcart_1('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.22  tff(c_51, plain, (~r2_hidden(k1_mcart_1('#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_30])).
% 1.97/1.22  tff(c_32, plain, (r2_hidden('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.22  tff(c_58, plain, (![A_60, B_61, D_62]: (k4_tarski('#skF_5'(A_60, B_61, k2_zfmisc_1(A_60, B_61), D_62), '#skF_6'(A_60, B_61, k2_zfmisc_1(A_60, B_61), D_62))=D_62 | ~r2_hidden(D_62, k2_zfmisc_1(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.22  tff(c_28, plain, (![A_35, B_36]: (k2_mcart_1(k4_tarski(A_35, B_36))=B_36)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.22  tff(c_76, plain, (![A_63, B_64, D_65]: ('#skF_6'(A_63, B_64, k2_zfmisc_1(A_63, B_64), D_65)=k2_mcart_1(D_65) | ~r2_hidden(D_65, k2_zfmisc_1(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_28])).
% 1.97/1.22  tff(c_107, plain, ('#skF_6'('#skF_8', '#skF_9', k2_zfmisc_1('#skF_8', '#skF_9'), '#skF_7')=k2_mcart_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_76])).
% 1.97/1.22  tff(c_4, plain, (![A_1, B_2, D_28]: (k4_tarski('#skF_5'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), '#skF_6'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28))=D_28 | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.22  tff(c_111, plain, (k4_tarski('#skF_5'('#skF_8', '#skF_9', k2_zfmisc_1('#skF_8', '#skF_9'), '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | ~r2_hidden('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_4])).
% 1.97/1.22  tff(c_118, plain, (k4_tarski('#skF_5'('#skF_8', '#skF_9', k2_zfmisc_1('#skF_8', '#skF_9'), '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_111])).
% 1.97/1.22  tff(c_26, plain, (![A_35, B_36]: (k1_mcart_1(k4_tarski(A_35, B_36))=A_35)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.22  tff(c_136, plain, ('#skF_5'('#skF_8', '#skF_9', k2_zfmisc_1('#skF_8', '#skF_9'), '#skF_7')=k1_mcart_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_118, c_26])).
% 1.97/1.22  tff(c_8, plain, (![A_1, B_2, D_28]: (r2_hidden('#skF_5'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), A_1) | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.22  tff(c_148, plain, (r2_hidden(k1_mcart_1('#skF_7'), '#skF_8') | ~r2_hidden('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_8])).
% 1.97/1.22  tff(c_154, plain, (r2_hidden(k1_mcart_1('#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_148])).
% 1.97/1.22  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_154])).
% 1.97/1.22  tff(c_157, plain, (~r2_hidden(k2_mcart_1('#skF_7'), '#skF_9')), inference(splitRight, [status(thm)], [c_30])).
% 1.97/1.22  tff(c_165, plain, (![A_90, B_91, D_92]: (k4_tarski('#skF_5'(A_90, B_91, k2_zfmisc_1(A_90, B_91), D_92), '#skF_6'(A_90, B_91, k2_zfmisc_1(A_90, B_91), D_92))=D_92 | ~r2_hidden(D_92, k2_zfmisc_1(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.22  tff(c_183, plain, (![A_93, B_94, D_95]: ('#skF_6'(A_93, B_94, k2_zfmisc_1(A_93, B_94), D_95)=k2_mcart_1(D_95) | ~r2_hidden(D_95, k2_zfmisc_1(A_93, B_94)))), inference(superposition, [status(thm), theory('equality')], [c_165, c_28])).
% 1.97/1.22  tff(c_214, plain, ('#skF_6'('#skF_8', '#skF_9', k2_zfmisc_1('#skF_8', '#skF_9'), '#skF_7')=k2_mcart_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_183])).
% 1.97/1.22  tff(c_6, plain, (![A_1, B_2, D_28]: (r2_hidden('#skF_6'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), B_2) | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.22  tff(c_221, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_9') | ~r2_hidden('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_214, c_6])).
% 1.97/1.22  tff(c_227, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_221])).
% 1.97/1.22  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_227])).
% 1.97/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  Inference rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Ref     : 0
% 1.97/1.22  #Sup     : 49
% 1.97/1.22  #Fact    : 0
% 1.97/1.22  #Define  : 0
% 1.97/1.22  #Split   : 1
% 1.97/1.22  #Chain   : 0
% 1.97/1.22  #Close   : 0
% 1.97/1.22  
% 1.97/1.22  Ordering : KBO
% 1.97/1.22  
% 1.97/1.22  Simplification rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Subsume      : 0
% 1.97/1.22  #Demod        : 10
% 1.97/1.22  #Tautology    : 15
% 1.97/1.22  #SimpNegUnit  : 2
% 1.97/1.22  #BackRed      : 1
% 1.97/1.22  
% 1.97/1.22  #Partial instantiations: 0
% 1.97/1.22  #Strategies tried      : 1
% 1.97/1.22  
% 1.97/1.22  Timing (in seconds)
% 1.97/1.22  ----------------------
% 1.97/1.23  Preprocessing        : 0.27
% 1.97/1.23  Parsing              : 0.14
% 1.97/1.23  CNF conversion       : 0.03
% 1.97/1.23  Main loop            : 0.20
% 1.97/1.23  Inferencing          : 0.08
% 1.97/1.23  Reduction            : 0.05
% 1.97/1.23  Demodulation         : 0.04
% 1.97/1.23  BG Simplification    : 0.02
% 1.97/1.23  Subsumption          : 0.03
% 1.97/1.23  Abstraction          : 0.01
% 1.97/1.23  MUC search           : 0.00
% 1.97/1.23  Cooper               : 0.00
% 1.97/1.23  Total                : 0.50
% 1.97/1.23  Index Insertion      : 0.00
% 1.97/1.23  Index Deletion       : 0.00
% 1.97/1.23  Index Matching       : 0.00
% 1.97/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
