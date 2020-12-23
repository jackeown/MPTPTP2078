%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:00 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   50 (  78 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 ( 136 expanded)
%              Number of equality atoms :   23 (  59 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

tff(c_44,plain,
    ( k2_mcart_1('#skF_7') != '#skF_10'
    | ~ r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_65,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    r2_hidden('#skF_7',k2_zfmisc_1('#skF_8',k2_tarski('#skF_9','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_75,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden(k1_mcart_1(A_55),B_56)
      | ~ r2_hidden(A_55,k2_zfmisc_1(B_56,C_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_75])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_77])).

tff(c_83,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( k2_mcart_1('#skF_7') != '#skF_9'
    | ~ r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_84,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_84])).

tff(c_87,plain,(
    k2_mcart_1('#skF_7') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_82,plain,(
    k2_mcart_1('#skF_7') != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_113,plain,(
    ! [A_66,C_67,B_68] :
      ( r2_hidden(k2_mcart_1(A_66),C_67)
      | ~ r2_hidden(A_66,k2_zfmisc_1(B_68,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_116,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),k2_tarski('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_42,c_113])).

tff(c_38,plain,(
    ! [A_47,B_48] : k1_mcart_1(k4_tarski(A_47,B_48)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_118,plain,(
    ! [E_73,F_74,A_75,B_76] :
      ( r2_hidden(k4_tarski(E_73,F_74),k2_zfmisc_1(A_75,B_76))
      | ~ r2_hidden(F_74,B_76)
      | ~ r2_hidden(E_73,A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [A_43,C_45,B_44,D_46] :
      ( k1_mcart_1(A_43) = C_45
      | k1_mcart_1(A_43) = B_44
      | ~ r2_hidden(A_43,k2_zfmisc_1(k2_tarski(B_44,C_45),D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_122,plain,(
    ! [F_74,E_73,C_45,B_44,B_76] :
      ( k1_mcart_1(k4_tarski(E_73,F_74)) = C_45
      | k1_mcart_1(k4_tarski(E_73,F_74)) = B_44
      | ~ r2_hidden(F_74,B_76)
      | ~ r2_hidden(E_73,k2_tarski(B_44,C_45)) ) ),
    inference(resolution,[status(thm)],[c_118,c_36])).

tff(c_128,plain,(
    ! [F_74,E_73,C_45,B_44,B_76] :
      ( E_73 = C_45
      | E_73 = B_44
      | ~ r2_hidden(F_74,B_76)
      | ~ r2_hidden(E_73,k2_tarski(B_44,C_45)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_122])).

tff(c_133,plain,(
    ! [F_74,B_76] : ~ r2_hidden(F_74,B_76) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_116])).

tff(c_156,plain,(
    ! [E_80,C_81,B_82] :
      ( E_80 = C_81
      | E_80 = B_82
      | ~ r2_hidden(E_80,k2_tarski(B_82,C_81)) ) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_163,plain,
    ( k2_mcart_1('#skF_7') = '#skF_10'
    | k2_mcart_1('#skF_7') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_116,c_156])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_82,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:27:36 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.22  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 1.98/1.22  
% 1.98/1.22  %Foreground sorts:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Background operators:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Foreground operators:
% 1.98/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.98/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.98/1.22  tff('#skF_7', type, '#skF_7': $i).
% 1.98/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.22  tff('#skF_10', type, '#skF_10': $i).
% 1.98/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.98/1.22  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 1.98/1.22  tff('#skF_9', type, '#skF_9': $i).
% 1.98/1.22  tff('#skF_8', type, '#skF_8': $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.22  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.98/1.22  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 1.98/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.22  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.98/1.22  
% 1.98/1.23  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_mcart_1)).
% 1.98/1.23  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.98/1.23  tff(f_59, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.98/1.23  tff(f_41, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 1.98/1.23  tff(f_55, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_mcart_1)).
% 1.98/1.23  tff(c_44, plain, (k2_mcart_1('#skF_7')!='#skF_10' | ~r2_hidden(k1_mcart_1('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.23  tff(c_65, plain, (~r2_hidden(k1_mcart_1('#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_44])).
% 1.98/1.23  tff(c_42, plain, (r2_hidden('#skF_7', k2_zfmisc_1('#skF_8', k2_tarski('#skF_9', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.23  tff(c_75, plain, (![A_55, B_56, C_57]: (r2_hidden(k1_mcart_1(A_55), B_56) | ~r2_hidden(A_55, k2_zfmisc_1(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.23  tff(c_77, plain, (r2_hidden(k1_mcart_1('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_42, c_75])).
% 1.98/1.23  tff(c_81, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_77])).
% 1.98/1.23  tff(c_83, plain, (r2_hidden(k1_mcart_1('#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_44])).
% 1.98/1.23  tff(c_46, plain, (k2_mcart_1('#skF_7')!='#skF_9' | ~r2_hidden(k1_mcart_1('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.23  tff(c_84, plain, (~r2_hidden(k1_mcart_1('#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_46])).
% 1.98/1.23  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_84])).
% 1.98/1.23  tff(c_87, plain, (k2_mcart_1('#skF_7')!='#skF_9'), inference(splitRight, [status(thm)], [c_46])).
% 1.98/1.23  tff(c_82, plain, (k2_mcart_1('#skF_7')!='#skF_10'), inference(splitRight, [status(thm)], [c_44])).
% 1.98/1.23  tff(c_113, plain, (![A_66, C_67, B_68]: (r2_hidden(k2_mcart_1(A_66), C_67) | ~r2_hidden(A_66, k2_zfmisc_1(B_68, C_67)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.23  tff(c_116, plain, (r2_hidden(k2_mcart_1('#skF_7'), k2_tarski('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_42, c_113])).
% 1.98/1.23  tff(c_38, plain, (![A_47, B_48]: (k1_mcart_1(k4_tarski(A_47, B_48))=A_47)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.98/1.23  tff(c_118, plain, (![E_73, F_74, A_75, B_76]: (r2_hidden(k4_tarski(E_73, F_74), k2_zfmisc_1(A_75, B_76)) | ~r2_hidden(F_74, B_76) | ~r2_hidden(E_73, A_75))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.23  tff(c_36, plain, (![A_43, C_45, B_44, D_46]: (k1_mcart_1(A_43)=C_45 | k1_mcart_1(A_43)=B_44 | ~r2_hidden(A_43, k2_zfmisc_1(k2_tarski(B_44, C_45), D_46)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.98/1.23  tff(c_122, plain, (![F_74, E_73, C_45, B_44, B_76]: (k1_mcart_1(k4_tarski(E_73, F_74))=C_45 | k1_mcart_1(k4_tarski(E_73, F_74))=B_44 | ~r2_hidden(F_74, B_76) | ~r2_hidden(E_73, k2_tarski(B_44, C_45)))), inference(resolution, [status(thm)], [c_118, c_36])).
% 1.98/1.23  tff(c_128, plain, (![F_74, E_73, C_45, B_44, B_76]: (E_73=C_45 | E_73=B_44 | ~r2_hidden(F_74, B_76) | ~r2_hidden(E_73, k2_tarski(B_44, C_45)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_122])).
% 1.98/1.23  tff(c_133, plain, (![F_74, B_76]: (~r2_hidden(F_74, B_76))), inference(splitLeft, [status(thm)], [c_128])).
% 1.98/1.23  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_116])).
% 1.98/1.23  tff(c_156, plain, (![E_80, C_81, B_82]: (E_80=C_81 | E_80=B_82 | ~r2_hidden(E_80, k2_tarski(B_82, C_81)))), inference(splitRight, [status(thm)], [c_128])).
% 1.98/1.23  tff(c_163, plain, (k2_mcart_1('#skF_7')='#skF_10' | k2_mcart_1('#skF_7')='#skF_9'), inference(resolution, [status(thm)], [c_116, c_156])).
% 1.98/1.23  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_82, c_163])).
% 1.98/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  Inference rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Ref     : 0
% 1.98/1.23  #Sup     : 21
% 1.98/1.23  #Fact    : 0
% 1.98/1.23  #Define  : 0
% 1.98/1.23  #Split   : 3
% 1.98/1.23  #Chain   : 0
% 1.98/1.23  #Close   : 0
% 1.98/1.23  
% 1.98/1.23  Ordering : KBO
% 1.98/1.23  
% 1.98/1.23  Simplification rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Subsume      : 6
% 1.98/1.23  #Demod        : 7
% 1.98/1.23  #Tautology    : 14
% 1.98/1.23  #SimpNegUnit  : 8
% 1.98/1.23  #BackRed      : 3
% 1.98/1.23  
% 1.98/1.23  #Partial instantiations: 0
% 1.98/1.23  #Strategies tried      : 1
% 1.98/1.23  
% 1.98/1.23  Timing (in seconds)
% 1.98/1.23  ----------------------
% 1.98/1.23  Preprocessing        : 0.33
% 1.98/1.23  Parsing              : 0.17
% 1.98/1.23  CNF conversion       : 0.03
% 1.98/1.23  Main loop            : 0.15
% 1.98/1.23  Inferencing          : 0.05
% 1.98/1.23  Reduction            : 0.05
% 1.98/1.23  Demodulation         : 0.03
% 1.98/1.23  BG Simplification    : 0.02
% 1.98/1.23  Subsumption          : 0.02
% 1.98/1.23  Abstraction          : 0.01
% 1.98/1.24  MUC search           : 0.00
% 1.98/1.24  Cooper               : 0.00
% 1.98/1.24  Total                : 0.50
% 1.98/1.24  Index Insertion      : 0.00
% 1.98/1.24  Index Deletion       : 0.00
% 1.98/1.24  Index Matching       : 0.00
% 1.98/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
