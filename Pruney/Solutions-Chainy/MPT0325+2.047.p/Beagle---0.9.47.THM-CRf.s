%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:27 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 185 expanded)
%              Number of leaves         :   18 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 412 expanded)
%              Number of equality atoms :   15 (  46 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_106,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( r2_hidden(k4_tarski(A_45,B_46),k2_zfmisc_1(C_47,D_48))
      | ~ r2_hidden(B_46,D_48)
      | ~ r2_hidden(A_45,C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_176,plain,(
    ! [B_62,A_59,C_61,B_58,D_60] :
      ( r2_hidden(k4_tarski(A_59,B_58),B_62)
      | ~ r1_tarski(k2_zfmisc_1(C_61,D_60),B_62)
      | ~ r2_hidden(B_58,D_60)
      | ~ r2_hidden(A_59,C_61) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_227,plain,(
    ! [A_68,B_69] :
      ( r2_hidden(k4_tarski(A_68,B_69),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_69,'#skF_3')
      | ~ r2_hidden(A_68,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_176])).

tff(c_14,plain,(
    ! [A_7,C_9,B_8,D_10] :
      ( r2_hidden(A_7,C_9)
      | ~ r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_242,plain,(
    ! [A_68,B_69] :
      ( r2_hidden(A_68,'#skF_4')
      | ~ r2_hidden(B_69,'#skF_3')
      | ~ r2_hidden(A_68,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_227,c_14])).

tff(c_246,plain,(
    ! [B_70] : ~ r2_hidden(B_70,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_257,plain,(
    ! [B_71] : r1_tarski('#skF_3',B_71) ),
    inference(resolution,[status(thm)],[c_6,c_246])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_262,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_257,c_8])).

tff(c_18,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_272,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_262,c_18])).

tff(c_24,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_274,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_24])).

tff(c_340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_274])).

tff(c_342,plain,(
    ! [A_74] :
      ( r2_hidden(A_74,'#skF_4')
      | ~ r2_hidden(A_74,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_384,plain,(
    ! [B_77] :
      ( r2_hidden('#skF_1'('#skF_2',B_77),'#skF_4')
      | r1_tarski('#skF_2',B_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_342])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_394,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_384,c_4])).

tff(c_401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_394])).

tff(c_402,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_459,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( r2_hidden(k4_tarski(A_107,B_108),k2_zfmisc_1(C_109,D_110))
      | ~ r2_hidden(B_108,D_110)
      | ~ r2_hidden(A_107,C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_530,plain,(
    ! [A_124,B_122,D_121,C_120,B_123] :
      ( r2_hidden(k4_tarski(A_124,B_122),B_123)
      | ~ r1_tarski(k2_zfmisc_1(C_120,D_121),B_123)
      | ~ r2_hidden(B_122,D_121)
      | ~ r2_hidden(A_124,C_120) ) ),
    inference(resolution,[status(thm)],[c_459,c_2])).

tff(c_581,plain,(
    ! [A_130,B_131] :
      ( r2_hidden(k4_tarski(A_130,B_131),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_131,'#skF_3')
      | ~ r2_hidden(A_130,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_530])).

tff(c_12,plain,(
    ! [B_8,D_10,A_7,C_9] :
      ( r2_hidden(B_8,D_10)
      | ~ r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_597,plain,(
    ! [B_131,A_130] :
      ( r2_hidden(B_131,'#skF_5')
      | ~ r2_hidden(B_131,'#skF_3')
      | ~ r2_hidden(A_130,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_581,c_12])).

tff(c_664,plain,(
    ! [A_138] : ~ r2_hidden(A_138,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_597])).

tff(c_677,plain,(
    ! [B_139] : r1_tarski('#skF_2',B_139) ),
    inference(resolution,[status(thm)],[c_6,c_664])).

tff(c_682,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_677,c_8])).

tff(c_20,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_694,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_2',B_12) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_682,c_20])).

tff(c_695,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_24])).

tff(c_760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_695])).

tff(c_762,plain,(
    ! [B_142] :
      ( r2_hidden(B_142,'#skF_5')
      | ~ r2_hidden(B_142,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_804,plain,(
    ! [A_147] :
      ( r1_tarski(A_147,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_147,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_762,c_4])).

tff(c_812,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_804])).

tff(c_817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_402,c_402,c_812])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.37  
% 2.75/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.37  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.75/1.37  
% 2.75/1.37  %Foreground sorts:
% 2.75/1.37  
% 2.75/1.37  
% 2.75/1.37  %Background operators:
% 2.75/1.37  
% 2.75/1.37  
% 2.75/1.37  %Foreground operators:
% 2.75/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.75/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.37  
% 2.75/1.39  tff(f_57, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.75/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.75/1.39  tff(f_42, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.75/1.39  tff(f_36, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.75/1.39  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.75/1.39  tff(c_22, plain, (~r1_tarski('#skF_3', '#skF_5') | ~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.75/1.39  tff(c_50, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_22])).
% 2.75/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.39  tff(c_26, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.75/1.39  tff(c_106, plain, (![A_45, B_46, C_47, D_48]: (r2_hidden(k4_tarski(A_45, B_46), k2_zfmisc_1(C_47, D_48)) | ~r2_hidden(B_46, D_48) | ~r2_hidden(A_45, C_47))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.75/1.39  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.39  tff(c_176, plain, (![B_62, A_59, C_61, B_58, D_60]: (r2_hidden(k4_tarski(A_59, B_58), B_62) | ~r1_tarski(k2_zfmisc_1(C_61, D_60), B_62) | ~r2_hidden(B_58, D_60) | ~r2_hidden(A_59, C_61))), inference(resolution, [status(thm)], [c_106, c_2])).
% 2.75/1.39  tff(c_227, plain, (![A_68, B_69]: (r2_hidden(k4_tarski(A_68, B_69), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_69, '#skF_3') | ~r2_hidden(A_68, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_176])).
% 2.75/1.39  tff(c_14, plain, (![A_7, C_9, B_8, D_10]: (r2_hidden(A_7, C_9) | ~r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.75/1.39  tff(c_242, plain, (![A_68, B_69]: (r2_hidden(A_68, '#skF_4') | ~r2_hidden(B_69, '#skF_3') | ~r2_hidden(A_68, '#skF_2'))), inference(resolution, [status(thm)], [c_227, c_14])).
% 2.75/1.39  tff(c_246, plain, (![B_70]: (~r2_hidden(B_70, '#skF_3'))), inference(splitLeft, [status(thm)], [c_242])).
% 2.75/1.39  tff(c_257, plain, (![B_71]: (r1_tarski('#skF_3', B_71))), inference(resolution, [status(thm)], [c_6, c_246])).
% 2.75/1.39  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.75/1.39  tff(c_262, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_257, c_8])).
% 2.75/1.39  tff(c_18, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.75/1.39  tff(c_272, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_262, c_18])).
% 2.75/1.39  tff(c_24, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.75/1.39  tff(c_274, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_262, c_24])).
% 2.75/1.39  tff(c_340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_272, c_274])).
% 2.75/1.39  tff(c_342, plain, (![A_74]: (r2_hidden(A_74, '#skF_4') | ~r2_hidden(A_74, '#skF_2'))), inference(splitRight, [status(thm)], [c_242])).
% 2.75/1.39  tff(c_384, plain, (![B_77]: (r2_hidden('#skF_1'('#skF_2', B_77), '#skF_4') | r1_tarski('#skF_2', B_77))), inference(resolution, [status(thm)], [c_6, c_342])).
% 2.75/1.39  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.39  tff(c_394, plain, (r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_384, c_4])).
% 2.75/1.39  tff(c_401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_394])).
% 2.75/1.39  tff(c_402, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_22])).
% 2.75/1.39  tff(c_459, plain, (![A_107, B_108, C_109, D_110]: (r2_hidden(k4_tarski(A_107, B_108), k2_zfmisc_1(C_109, D_110)) | ~r2_hidden(B_108, D_110) | ~r2_hidden(A_107, C_109))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.75/1.39  tff(c_530, plain, (![A_124, B_122, D_121, C_120, B_123]: (r2_hidden(k4_tarski(A_124, B_122), B_123) | ~r1_tarski(k2_zfmisc_1(C_120, D_121), B_123) | ~r2_hidden(B_122, D_121) | ~r2_hidden(A_124, C_120))), inference(resolution, [status(thm)], [c_459, c_2])).
% 2.75/1.39  tff(c_581, plain, (![A_130, B_131]: (r2_hidden(k4_tarski(A_130, B_131), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_131, '#skF_3') | ~r2_hidden(A_130, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_530])).
% 2.75/1.39  tff(c_12, plain, (![B_8, D_10, A_7, C_9]: (r2_hidden(B_8, D_10) | ~r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.75/1.39  tff(c_597, plain, (![B_131, A_130]: (r2_hidden(B_131, '#skF_5') | ~r2_hidden(B_131, '#skF_3') | ~r2_hidden(A_130, '#skF_2'))), inference(resolution, [status(thm)], [c_581, c_12])).
% 2.75/1.39  tff(c_664, plain, (![A_138]: (~r2_hidden(A_138, '#skF_2'))), inference(splitLeft, [status(thm)], [c_597])).
% 2.75/1.39  tff(c_677, plain, (![B_139]: (r1_tarski('#skF_2', B_139))), inference(resolution, [status(thm)], [c_6, c_664])).
% 2.75/1.39  tff(c_682, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_677, c_8])).
% 2.75/1.39  tff(c_20, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.75/1.39  tff(c_694, plain, (![B_12]: (k2_zfmisc_1('#skF_2', B_12)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_682, c_682, c_20])).
% 2.75/1.39  tff(c_695, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_682, c_24])).
% 2.75/1.39  tff(c_760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_694, c_695])).
% 2.75/1.39  tff(c_762, plain, (![B_142]: (r2_hidden(B_142, '#skF_5') | ~r2_hidden(B_142, '#skF_3'))), inference(splitRight, [status(thm)], [c_597])).
% 2.75/1.39  tff(c_804, plain, (![A_147]: (r1_tarski(A_147, '#skF_5') | ~r2_hidden('#skF_1'(A_147, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_762, c_4])).
% 2.75/1.39  tff(c_812, plain, (r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_804])).
% 2.75/1.39  tff(c_817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_402, c_402, c_812])).
% 2.75/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.39  
% 2.75/1.39  Inference rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Ref     : 0
% 2.75/1.39  #Sup     : 174
% 2.75/1.39  #Fact    : 0
% 2.75/1.39  #Define  : 0
% 2.75/1.39  #Split   : 7
% 2.75/1.39  #Chain   : 0
% 2.75/1.39  #Close   : 0
% 2.75/1.39  
% 2.75/1.39  Ordering : KBO
% 2.75/1.39  
% 2.75/1.39  Simplification rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Subsume      : 58
% 2.75/1.39  #Demod        : 86
% 2.75/1.39  #Tautology    : 58
% 2.75/1.39  #SimpNegUnit  : 18
% 2.75/1.39  #BackRed      : 35
% 2.75/1.39  
% 2.75/1.39  #Partial instantiations: 0
% 2.75/1.39  #Strategies tried      : 1
% 2.75/1.39  
% 2.75/1.39  Timing (in seconds)
% 2.75/1.39  ----------------------
% 2.75/1.39  Preprocessing        : 0.27
% 2.75/1.39  Parsing              : 0.15
% 2.75/1.39  CNF conversion       : 0.02
% 2.75/1.39  Main loop            : 0.36
% 2.75/1.39  Inferencing          : 0.14
% 2.75/1.39  Reduction            : 0.09
% 2.75/1.39  Demodulation         : 0.06
% 2.75/1.39  BG Simplification    : 0.02
% 2.75/1.39  Subsumption          : 0.09
% 2.75/1.39  Abstraction          : 0.02
% 2.75/1.39  MUC search           : 0.00
% 2.75/1.39  Cooper               : 0.00
% 2.75/1.39  Total                : 0.67
% 2.75/1.39  Index Insertion      : 0.00
% 2.75/1.39  Index Deletion       : 0.00
% 2.75/1.39  Index Matching       : 0.00
% 2.75/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
