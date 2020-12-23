%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:48 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 100 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 203 expanded)
%              Number of equality atoms :   15 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_22,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( r2_hidden(k4_tarski(A_39,B_40),k2_zfmisc_1(C_41,D_42))
      | ~ r2_hidden(B_40,D_42)
      | ~ r2_hidden(A_39,C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k2_zfmisc_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_66,plain,(
    ! [B_31,D_32,A_33,C_34] :
      ( r2_hidden(B_31,D_32)
      | ~ r2_hidden(k4_tarski(A_33,B_31),k2_zfmisc_1(C_34,D_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_69,plain,(
    ! [B_31,A_33] :
      ( r2_hidden(B_31,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_33,B_31),k2_zfmisc_1('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_66])).

tff(c_92,plain,(
    ! [B_40,A_39] :
      ( r2_hidden(B_40,'#skF_4')
      | ~ r2_hidden(B_40,'#skF_3')
      | ~ r2_hidden(A_39,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_69])).

tff(c_99,plain,(
    ! [A_43] : ~ r2_hidden(A_43,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_111,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_111])).

tff(c_119,plain,(
    ! [B_44] :
      ( r2_hidden(B_44,'#skF_4')
      | ~ r2_hidden(B_44,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_150,plain,(
    ! [B_46] :
      ( r2_hidden('#skF_1'('#skF_3',B_46),'#skF_4')
      | r1_tarski('#skF_3',B_46) ) ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_158,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_150,c_4])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_160,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_10])).

tff(c_163,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_160])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62,plain,(
    ! [A_27,C_28,B_29,D_30] :
      ( r2_hidden(A_27,C_28)
      | ~ r2_hidden(k4_tarski(A_27,B_29),k2_zfmisc_1(C_28,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    ! [A_27,B_29] :
      ( r2_hidden(A_27,'#skF_3')
      | ~ r2_hidden(k4_tarski(A_27,B_29),k2_zfmisc_1('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_62])).

tff(c_93,plain,(
    ! [A_39,B_40] :
      ( r2_hidden(A_39,'#skF_3')
      | ~ r2_hidden(B_40,'#skF_3')
      | ~ r2_hidden(A_39,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_65])).

tff(c_180,plain,(
    ! [B_50] : ~ r2_hidden(B_50,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_200,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_180])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_200])).

tff(c_210,plain,(
    ! [A_51] :
      ( r2_hidden(A_51,'#skF_3')
      | ~ r2_hidden(A_51,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_223,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,'#skF_3')
      | ~ r2_hidden('#skF_1'(A_52,'#skF_3'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_210,c_4])).

tff(c_231,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_223])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_163,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.22  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.91/1.22  
% 1.91/1.22  %Foreground sorts:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Background operators:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Foreground operators:
% 1.91/1.22  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.91/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.22  
% 1.91/1.23  tff(f_61, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 1.91/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.91/1.23  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.91/1.23  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.91/1.23  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.91/1.23  tff(c_22, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.91/1.23  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.23  tff(c_24, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.91/1.23  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.91/1.23  tff(c_72, plain, (![A_39, B_40, C_41, D_42]: (r2_hidden(k4_tarski(A_39, B_40), k2_zfmisc_1(C_41, D_42)) | ~r2_hidden(B_40, D_42) | ~r2_hidden(A_39, C_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.23  tff(c_28, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k2_zfmisc_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.91/1.23  tff(c_66, plain, (![B_31, D_32, A_33, C_34]: (r2_hidden(B_31, D_32) | ~r2_hidden(k4_tarski(A_33, B_31), k2_zfmisc_1(C_34, D_32)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.23  tff(c_69, plain, (![B_31, A_33]: (r2_hidden(B_31, '#skF_4') | ~r2_hidden(k4_tarski(A_33, B_31), k2_zfmisc_1('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_66])).
% 1.91/1.23  tff(c_92, plain, (![B_40, A_39]: (r2_hidden(B_40, '#skF_4') | ~r2_hidden(B_40, '#skF_3') | ~r2_hidden(A_39, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_69])).
% 1.91/1.23  tff(c_99, plain, (![A_43]: (~r2_hidden(A_43, '#skF_4'))), inference(splitLeft, [status(thm)], [c_92])).
% 1.91/1.23  tff(c_111, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_99])).
% 1.91/1.23  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_111])).
% 1.91/1.23  tff(c_119, plain, (![B_44]: (r2_hidden(B_44, '#skF_4') | ~r2_hidden(B_44, '#skF_3'))), inference(splitRight, [status(thm)], [c_92])).
% 1.91/1.23  tff(c_150, plain, (![B_46]: (r2_hidden('#skF_1'('#skF_3', B_46), '#skF_4') | r1_tarski('#skF_3', B_46))), inference(resolution, [status(thm)], [c_6, c_119])).
% 1.91/1.23  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.23  tff(c_158, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_150, c_4])).
% 1.91/1.23  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.23  tff(c_160, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_158, c_10])).
% 1.91/1.23  tff(c_163, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_22, c_160])).
% 1.91/1.23  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.91/1.23  tff(c_62, plain, (![A_27, C_28, B_29, D_30]: (r2_hidden(A_27, C_28) | ~r2_hidden(k4_tarski(A_27, B_29), k2_zfmisc_1(C_28, D_30)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.23  tff(c_65, plain, (![A_27, B_29]: (r2_hidden(A_27, '#skF_3') | ~r2_hidden(k4_tarski(A_27, B_29), k2_zfmisc_1('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_62])).
% 1.91/1.23  tff(c_93, plain, (![A_39, B_40]: (r2_hidden(A_39, '#skF_3') | ~r2_hidden(B_40, '#skF_3') | ~r2_hidden(A_39, '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_65])).
% 1.91/1.23  tff(c_180, plain, (![B_50]: (~r2_hidden(B_50, '#skF_3'))), inference(splitLeft, [status(thm)], [c_93])).
% 1.91/1.23  tff(c_200, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_180])).
% 1.91/1.23  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_200])).
% 1.91/1.23  tff(c_210, plain, (![A_51]: (r2_hidden(A_51, '#skF_3') | ~r2_hidden(A_51, '#skF_4'))), inference(splitRight, [status(thm)], [c_93])).
% 1.91/1.23  tff(c_223, plain, (![A_52]: (r1_tarski(A_52, '#skF_3') | ~r2_hidden('#skF_1'(A_52, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_210, c_4])).
% 1.91/1.23  tff(c_231, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_223])).
% 1.91/1.23  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_163, c_231])).
% 1.91/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.23  
% 1.91/1.23  Inference rules
% 1.91/1.23  ----------------------
% 1.91/1.23  #Ref     : 0
% 1.91/1.23  #Sup     : 40
% 1.91/1.23  #Fact    : 0
% 1.91/1.23  #Define  : 0
% 1.91/1.23  #Split   : 2
% 1.91/1.23  #Chain   : 0
% 1.91/1.23  #Close   : 0
% 1.91/1.23  
% 1.91/1.23  Ordering : KBO
% 1.91/1.23  
% 1.91/1.23  Simplification rules
% 1.91/1.23  ----------------------
% 1.91/1.23  #Subsume      : 2
% 1.91/1.23  #Demod        : 5
% 1.91/1.23  #Tautology    : 11
% 1.91/1.23  #SimpNegUnit  : 7
% 1.91/1.23  #BackRed      : 2
% 1.91/1.23  
% 1.91/1.23  #Partial instantiations: 0
% 1.91/1.23  #Strategies tried      : 1
% 1.91/1.23  
% 1.91/1.23  Timing (in seconds)
% 1.91/1.23  ----------------------
% 2.01/1.23  Preprocessing        : 0.28
% 2.01/1.23  Parsing              : 0.14
% 2.01/1.23  CNF conversion       : 0.02
% 2.01/1.23  Main loop            : 0.19
% 2.01/1.23  Inferencing          : 0.07
% 2.01/1.23  Reduction            : 0.05
% 2.01/1.23  Demodulation         : 0.03
% 2.01/1.23  BG Simplification    : 0.01
% 2.01/1.24  Subsumption          : 0.05
% 2.02/1.24  Abstraction          : 0.01
% 2.02/1.24  MUC search           : 0.00
% 2.02/1.24  Cooper               : 0.00
% 2.02/1.24  Total                : 0.49
% 2.02/1.24  Index Insertion      : 0.00
% 2.02/1.24  Index Deletion       : 0.00
% 2.02/1.24  Index Matching       : 0.00
% 2.02/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
