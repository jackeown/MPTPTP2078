%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:52 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   50 (  99 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 212 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
            | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
          & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

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

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_16,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_3','#skF_5'))
    | r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_60,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( r2_hidden(k4_tarski(A_37,B_38),k2_zfmisc_1(C_39,D_40))
      | ~ r2_hidden(B_38,D_40)
      | ~ r2_hidden(A_37,C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_41,B_42,C_44,B_45,D_43] :
      ( r2_hidden(k4_tarski(A_41,B_42),B_45)
      | ~ r1_tarski(k2_zfmisc_1(C_44,D_43),B_45)
      | ~ r2_hidden(B_42,D_43)
      | ~ r2_hidden(A_41,C_44) ) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_80,plain,(
    ! [A_46,B_47] :
      ( r2_hidden(k4_tarski(A_46,B_47),k2_zfmisc_1('#skF_5','#skF_3'))
      | ~ r2_hidden(B_47,'#skF_3')
      | ~ r2_hidden(A_46,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_72])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9,D_11] :
      ( r2_hidden(A_8,C_10)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_90,plain,(
    ! [A_46,B_47] :
      ( r2_hidden(A_46,'#skF_5')
      | ~ r2_hidden(B_47,'#skF_3')
      | ~ r2_hidden(A_46,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_80,c_14])).

tff(c_93,plain,(
    ! [B_48] : ~ r2_hidden(B_48,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_109,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_109])).

tff(c_122,plain,(
    ! [A_50] :
      ( r2_hidden(A_50,'#skF_5')
      | ~ r2_hidden(A_50,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_51,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_122,c_4])).

tff(c_139,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_16,c_139])).

tff(c_145,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_148,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( r2_hidden(k4_tarski(A_56,B_57),k2_zfmisc_1(C_58,D_59))
      | ~ r2_hidden(B_57,D_59)
      | ~ r2_hidden(A_56,C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_207,plain,(
    ! [B_78,D_79,A_80,C_77,B_76] :
      ( r2_hidden(k4_tarski(A_80,B_76),B_78)
      | ~ r1_tarski(k2_zfmisc_1(C_77,D_79),B_78)
      | ~ r2_hidden(B_76,D_79)
      | ~ r2_hidden(A_80,C_77) ) ),
    inference(resolution,[status(thm)],[c_148,c_2])).

tff(c_219,plain,(
    ! [A_81,B_82] :
      ( r2_hidden(k4_tarski(A_81,B_82),k2_zfmisc_1('#skF_3','#skF_5'))
      | ~ r2_hidden(B_82,'#skF_4')
      | ~ r2_hidden(A_81,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_145,c_207])).

tff(c_12,plain,(
    ! [B_9,D_11,A_8,C_10] :
      ( r2_hidden(B_9,D_11)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_228,plain,(
    ! [B_82,A_81] :
      ( r2_hidden(B_82,'#skF_5')
      | ~ r2_hidden(B_82,'#skF_4')
      | ~ r2_hidden(A_81,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_219,c_12])).

tff(c_232,plain,(
    ! [A_83] : ~ r2_hidden(A_83,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_252,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_232])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_252])).

tff(c_262,plain,(
    ! [B_84] :
      ( r2_hidden(B_84,'#skF_5')
      | ~ r2_hidden(B_84,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_271,plain,(
    ! [A_85] :
      ( r1_tarski(A_85,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_85,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_262,c_4])).

tff(c_279,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_271])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_16,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:30:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.31  
% 2.01/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.31  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.01/1.31  
% 2.01/1.31  %Foreground sorts:
% 2.01/1.31  
% 2.01/1.31  
% 2.01/1.31  %Background operators:
% 2.01/1.31  
% 2.01/1.31  
% 2.01/1.31  %Foreground operators:
% 2.01/1.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.01/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.01/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.01/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.31  
% 2.25/1.32  tff(f_58, negated_conjecture, ~(![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 2.25/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.25/1.32  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.25/1.32  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.25/1.32  tff(c_16, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.25/1.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.25/1.32  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.25/1.32  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.25/1.32  tff(c_18, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_5')) | r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.25/1.32  tff(c_42, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_18])).
% 2.25/1.32  tff(c_60, plain, (![A_37, B_38, C_39, D_40]: (r2_hidden(k4_tarski(A_37, B_38), k2_zfmisc_1(C_39, D_40)) | ~r2_hidden(B_38, D_40) | ~r2_hidden(A_37, C_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.25/1.32  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.25/1.32  tff(c_72, plain, (![A_41, B_42, C_44, B_45, D_43]: (r2_hidden(k4_tarski(A_41, B_42), B_45) | ~r1_tarski(k2_zfmisc_1(C_44, D_43), B_45) | ~r2_hidden(B_42, D_43) | ~r2_hidden(A_41, C_44))), inference(resolution, [status(thm)], [c_60, c_2])).
% 2.25/1.32  tff(c_80, plain, (![A_46, B_47]: (r2_hidden(k4_tarski(A_46, B_47), k2_zfmisc_1('#skF_5', '#skF_3')) | ~r2_hidden(B_47, '#skF_3') | ~r2_hidden(A_46, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_72])).
% 2.25/1.32  tff(c_14, plain, (![A_8, C_10, B_9, D_11]: (r2_hidden(A_8, C_10) | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.25/1.32  tff(c_90, plain, (![A_46, B_47]: (r2_hidden(A_46, '#skF_5') | ~r2_hidden(B_47, '#skF_3') | ~r2_hidden(A_46, '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_14])).
% 2.25/1.32  tff(c_93, plain, (![B_48]: (~r2_hidden(B_48, '#skF_3'))), inference(splitLeft, [status(thm)], [c_90])).
% 2.25/1.32  tff(c_109, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_93])).
% 2.25/1.32  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_109])).
% 2.25/1.32  tff(c_122, plain, (![A_50]: (r2_hidden(A_50, '#skF_5') | ~r2_hidden(A_50, '#skF_4'))), inference(splitRight, [status(thm)], [c_90])).
% 2.25/1.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.25/1.32  tff(c_131, plain, (![A_51]: (r1_tarski(A_51, '#skF_5') | ~r2_hidden('#skF_1'(A_51, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_122, c_4])).
% 2.25/1.32  tff(c_139, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_131])).
% 2.25/1.32  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_16, c_139])).
% 2.25/1.32  tff(c_145, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_18])).
% 2.25/1.32  tff(c_148, plain, (![A_56, B_57, C_58, D_59]: (r2_hidden(k4_tarski(A_56, B_57), k2_zfmisc_1(C_58, D_59)) | ~r2_hidden(B_57, D_59) | ~r2_hidden(A_56, C_58))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.25/1.32  tff(c_207, plain, (![B_78, D_79, A_80, C_77, B_76]: (r2_hidden(k4_tarski(A_80, B_76), B_78) | ~r1_tarski(k2_zfmisc_1(C_77, D_79), B_78) | ~r2_hidden(B_76, D_79) | ~r2_hidden(A_80, C_77))), inference(resolution, [status(thm)], [c_148, c_2])).
% 2.25/1.32  tff(c_219, plain, (![A_81, B_82]: (r2_hidden(k4_tarski(A_81, B_82), k2_zfmisc_1('#skF_3', '#skF_5')) | ~r2_hidden(B_82, '#skF_4') | ~r2_hidden(A_81, '#skF_3'))), inference(resolution, [status(thm)], [c_145, c_207])).
% 2.25/1.32  tff(c_12, plain, (![B_9, D_11, A_8, C_10]: (r2_hidden(B_9, D_11) | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.25/1.32  tff(c_228, plain, (![B_82, A_81]: (r2_hidden(B_82, '#skF_5') | ~r2_hidden(B_82, '#skF_4') | ~r2_hidden(A_81, '#skF_3'))), inference(resolution, [status(thm)], [c_219, c_12])).
% 2.25/1.32  tff(c_232, plain, (![A_83]: (~r2_hidden(A_83, '#skF_3'))), inference(splitLeft, [status(thm)], [c_228])).
% 2.25/1.32  tff(c_252, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_232])).
% 2.25/1.32  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_252])).
% 2.25/1.32  tff(c_262, plain, (![B_84]: (r2_hidden(B_84, '#skF_5') | ~r2_hidden(B_84, '#skF_4'))), inference(splitRight, [status(thm)], [c_228])).
% 2.25/1.32  tff(c_271, plain, (![A_85]: (r1_tarski(A_85, '#skF_5') | ~r2_hidden('#skF_1'(A_85, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_262, c_4])).
% 2.25/1.32  tff(c_279, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_271])).
% 2.25/1.32  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_16, c_279])).
% 2.25/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.32  
% 2.25/1.32  Inference rules
% 2.25/1.32  ----------------------
% 2.25/1.32  #Ref     : 0
% 2.25/1.32  #Sup     : 55
% 2.25/1.32  #Fact    : 0
% 2.25/1.32  #Define  : 0
% 2.25/1.32  #Split   : 3
% 2.25/1.32  #Chain   : 0
% 2.25/1.32  #Close   : 0
% 2.25/1.32  
% 2.25/1.32  Ordering : KBO
% 2.25/1.32  
% 2.25/1.32  Simplification rules
% 2.25/1.32  ----------------------
% 2.25/1.32  #Subsume      : 7
% 2.25/1.32  #Demod        : 0
% 2.25/1.32  #Tautology    : 8
% 2.25/1.32  #SimpNegUnit  : 4
% 2.25/1.32  #BackRed      : 0
% 2.25/1.32  
% 2.25/1.32  #Partial instantiations: 0
% 2.25/1.32  #Strategies tried      : 1
% 2.25/1.32  
% 2.25/1.32  Timing (in seconds)
% 2.25/1.32  ----------------------
% 2.25/1.33  Preprocessing        : 0.29
% 2.25/1.33  Parsing              : 0.16
% 2.25/1.33  CNF conversion       : 0.02
% 2.25/1.33  Main loop            : 0.23
% 2.25/1.33  Inferencing          : 0.10
% 2.25/1.33  Reduction            : 0.05
% 2.25/1.33  Demodulation         : 0.03
% 2.25/1.33  BG Simplification    : 0.01
% 2.25/1.33  Subsumption          : 0.06
% 2.25/1.33  Abstraction          : 0.01
% 2.25/1.33  MUC search           : 0.00
% 2.25/1.33  Cooper               : 0.00
% 2.25/1.33  Total                : 0.56
% 2.25/1.33  Index Insertion      : 0.00
% 2.25/1.33  Index Deletion       : 0.00
% 2.25/1.33  Index Matching       : 0.00
% 2.25/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
