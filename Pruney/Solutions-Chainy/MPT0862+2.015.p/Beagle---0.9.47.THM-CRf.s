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
% DateTime   : Thu Dec  3 10:09:06 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   58 (  96 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 155 expanded)
%              Number of equality atoms :   33 (  83 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(c_50,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_60,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_138,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden(k1_mcart_1(A_46),B_47)
      | ~ r2_hidden(A_46,k2_zfmisc_1(B_47,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_141,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_138])).

tff(c_104,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(k1_tarski(A_44),k1_tarski(B_45)) = k1_tarski(A_44)
      | B_45 = A_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( ~ r2_hidden(B_19,A_18)
      | k4_xboole_0(A_18,k1_tarski(B_19)) != A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_142,plain,(
    ! [B_49,A_50] :
      ( ~ r2_hidden(B_49,k1_tarski(A_50))
      | B_49 = A_50 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_32])).

tff(c_145,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_141,c_142])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_145])).

tff(c_154,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_155,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_155])).

tff(c_162,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_153,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_262,plain,(
    ! [A_75,C_76,B_77] :
      ( r2_hidden(k2_mcart_1(A_75),C_76)
      | ~ r2_hidden(A_75,k2_zfmisc_1(B_77,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_265,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_46,c_262])).

tff(c_337,plain,(
    ! [C_105,A_106,B_107] :
      ( k4_xboole_0(C_105,k2_tarski(A_106,B_107)) = C_105
      | r2_hidden(B_107,C_105)
      | r2_hidden(A_106,C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_289,plain,(
    ! [B_87,C_88,A_89] :
      ( ~ r2_hidden(B_87,C_88)
      | k4_xboole_0(k2_tarski(A_89,B_87),C_88) != k2_tarski(A_89,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_296,plain,(
    ! [A_7,C_88] :
      ( ~ r2_hidden(A_7,C_88)
      | k4_xboole_0(k1_tarski(A_7),C_88) != k2_tarski(A_7,A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_289])).

tff(c_298,plain,(
    ! [A_7,C_88] :
      ( ~ r2_hidden(A_7,C_88)
      | k4_xboole_0(k1_tarski(A_7),C_88) != k1_tarski(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_296])).

tff(c_378,plain,(
    ! [A_110,A_111,B_112] :
      ( ~ r2_hidden(A_110,k2_tarski(A_111,B_112))
      | r2_hidden(B_112,k1_tarski(A_110))
      | r2_hidden(A_111,k1_tarski(A_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_298])).

tff(c_391,plain,
    ( r2_hidden('#skF_6',k1_tarski(k2_mcart_1('#skF_3')))
    | r2_hidden('#skF_5',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_265,c_378])).

tff(c_392,plain,(
    r2_hidden('#skF_5',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_213,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(k1_tarski(A_68),k1_tarski(B_69)) = k1_tarski(A_68)
      | B_69 = A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_242,plain,(
    ! [B_69,A_68] :
      ( ~ r2_hidden(B_69,k1_tarski(A_68))
      | B_69 = A_68 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_32])).

tff(c_405,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_392,c_242])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_405])).

tff(c_415,plain,(
    r2_hidden('#skF_6',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_484,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_415,c_242])).

tff(c_493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:16:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.34  
% 2.45/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.34  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.45/1.34  
% 2.45/1.34  %Foreground sorts:
% 2.45/1.34  
% 2.45/1.34  
% 2.45/1.34  %Background operators:
% 2.45/1.34  
% 2.45/1.34  
% 2.45/1.34  %Foreground operators:
% 2.45/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.45/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.45/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.45/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.45/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.45/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.45/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.45/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.45/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.34  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.45/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.34  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.45/1.34  
% 2.45/1.36  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_mcart_1)).
% 2.45/1.36  tff(f_75, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.45/1.36  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.45/1.36  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.45/1.36  tff(f_51, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 2.45/1.36  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.45/1.36  tff(f_69, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.45/1.36  tff(c_50, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.45/1.36  tff(c_60, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_50])).
% 2.45/1.36  tff(c_46, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.45/1.36  tff(c_138, plain, (![A_46, B_47, C_48]: (r2_hidden(k1_mcart_1(A_46), B_47) | ~r2_hidden(A_46, k2_zfmisc_1(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.45/1.36  tff(c_141, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_138])).
% 2.45/1.36  tff(c_104, plain, (![A_44, B_45]: (k4_xboole_0(k1_tarski(A_44), k1_tarski(B_45))=k1_tarski(A_44) | B_45=A_44)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.45/1.36  tff(c_32, plain, (![B_19, A_18]: (~r2_hidden(B_19, A_18) | k4_xboole_0(A_18, k1_tarski(B_19))!=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.45/1.36  tff(c_142, plain, (![B_49, A_50]: (~r2_hidden(B_49, k1_tarski(A_50)) | B_49=A_50)), inference(superposition, [status(thm), theory('equality')], [c_104, c_32])).
% 2.45/1.36  tff(c_145, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_141, c_142])).
% 2.45/1.36  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_145])).
% 2.45/1.36  tff(c_154, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 2.45/1.36  tff(c_48, plain, (k2_mcart_1('#skF_3')!='#skF_6' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.45/1.36  tff(c_155, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_48])).
% 2.45/1.36  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_155])).
% 2.45/1.36  tff(c_162, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 2.45/1.36  tff(c_153, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_50])).
% 2.45/1.36  tff(c_262, plain, (![A_75, C_76, B_77]: (r2_hidden(k2_mcart_1(A_75), C_76) | ~r2_hidden(A_75, k2_zfmisc_1(B_77, C_76)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.45/1.36  tff(c_265, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_262])).
% 2.45/1.36  tff(c_337, plain, (![C_105, A_106, B_107]: (k4_xboole_0(C_105, k2_tarski(A_106, B_107))=C_105 | r2_hidden(B_107, C_105) | r2_hidden(A_106, C_105))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.45/1.36  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.36  tff(c_289, plain, (![B_87, C_88, A_89]: (~r2_hidden(B_87, C_88) | k4_xboole_0(k2_tarski(A_89, B_87), C_88)!=k2_tarski(A_89, B_87))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.45/1.36  tff(c_296, plain, (![A_7, C_88]: (~r2_hidden(A_7, C_88) | k4_xboole_0(k1_tarski(A_7), C_88)!=k2_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_289])).
% 2.45/1.36  tff(c_298, plain, (![A_7, C_88]: (~r2_hidden(A_7, C_88) | k4_xboole_0(k1_tarski(A_7), C_88)!=k1_tarski(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_296])).
% 2.45/1.36  tff(c_378, plain, (![A_110, A_111, B_112]: (~r2_hidden(A_110, k2_tarski(A_111, B_112)) | r2_hidden(B_112, k1_tarski(A_110)) | r2_hidden(A_111, k1_tarski(A_110)))), inference(superposition, [status(thm), theory('equality')], [c_337, c_298])).
% 2.45/1.36  tff(c_391, plain, (r2_hidden('#skF_6', k1_tarski(k2_mcart_1('#skF_3'))) | r2_hidden('#skF_5', k1_tarski(k2_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_265, c_378])).
% 2.45/1.36  tff(c_392, plain, (r2_hidden('#skF_5', k1_tarski(k2_mcart_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_391])).
% 2.45/1.36  tff(c_213, plain, (![A_68, B_69]: (k4_xboole_0(k1_tarski(A_68), k1_tarski(B_69))=k1_tarski(A_68) | B_69=A_68)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.45/1.36  tff(c_242, plain, (![B_69, A_68]: (~r2_hidden(B_69, k1_tarski(A_68)) | B_69=A_68)), inference(superposition, [status(thm), theory('equality')], [c_213, c_32])).
% 2.45/1.36  tff(c_405, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_392, c_242])).
% 2.45/1.36  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_153, c_405])).
% 2.45/1.36  tff(c_415, plain, (r2_hidden('#skF_6', k1_tarski(k2_mcart_1('#skF_3')))), inference(splitRight, [status(thm)], [c_391])).
% 2.45/1.36  tff(c_484, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_415, c_242])).
% 2.45/1.36  tff(c_493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_484])).
% 2.45/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.36  
% 2.45/1.36  Inference rules
% 2.45/1.36  ----------------------
% 2.45/1.36  #Ref     : 0
% 2.45/1.36  #Sup     : 102
% 2.45/1.36  #Fact    : 0
% 2.45/1.36  #Define  : 0
% 2.45/1.36  #Split   : 3
% 2.45/1.36  #Chain   : 0
% 2.45/1.36  #Close   : 0
% 2.45/1.36  
% 2.45/1.36  Ordering : KBO
% 2.45/1.36  
% 2.45/1.36  Simplification rules
% 2.45/1.36  ----------------------
% 2.45/1.36  #Subsume      : 7
% 2.45/1.36  #Demod        : 12
% 2.45/1.36  #Tautology    : 59
% 2.45/1.36  #SimpNegUnit  : 3
% 2.45/1.36  #BackRed      : 0
% 2.45/1.36  
% 2.45/1.36  #Partial instantiations: 0
% 2.45/1.36  #Strategies tried      : 1
% 2.45/1.36  
% 2.45/1.36  Timing (in seconds)
% 2.45/1.36  ----------------------
% 2.45/1.36  Preprocessing        : 0.33
% 2.45/1.36  Parsing              : 0.17
% 2.45/1.36  CNF conversion       : 0.02
% 2.45/1.36  Main loop            : 0.27
% 2.58/1.36  Inferencing          : 0.10
% 2.58/1.36  Reduction            : 0.08
% 2.58/1.36  Demodulation         : 0.05
% 2.58/1.36  BG Simplification    : 0.02
% 2.58/1.36  Subsumption          : 0.05
% 2.58/1.36  Abstraction          : 0.02
% 2.58/1.37  MUC search           : 0.00
% 2.58/1.37  Cooper               : 0.00
% 2.58/1.37  Total                : 0.63
% 2.58/1.37  Index Insertion      : 0.00
% 2.58/1.37  Index Deletion       : 0.00
% 2.58/1.37  Index Matching       : 0.00
% 2.58/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
