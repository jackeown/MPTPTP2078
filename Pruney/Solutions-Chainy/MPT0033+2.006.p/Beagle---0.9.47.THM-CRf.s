%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:38 EST 2020

% Result     : Theorem 6.49s
% Output     : CNFRefutation 6.49s
% Verified   : 
% Statistics : Number of formulae       :   47 (  83 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 181 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_1'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_31,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_1'(A_18,B_19),A_18)
      | r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_115,plain,(
    ! [A_40,B_41,B_42] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_40,B_41),B_42),A_40)
      | r1_tarski(k3_xboole_0(A_40,B_41),B_42) ) ),
    inference(resolution,[status(thm)],[c_31,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,(
    ! [A_40,B_41] : r1_tarski(k3_xboole_0(A_40,B_41),A_40) ),
    inference(resolution,[status(thm)],[c_115,c_4])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_49,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_32,B_33,B_34] :
      ( r2_hidden('#skF_1'(A_32,B_33),B_34)
      | ~ r1_tarski(A_32,B_34)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_292,plain,(
    ! [A_73,B_74,B_75,B_76] :
      ( r2_hidden('#skF_1'(A_73,B_74),B_75)
      | ~ r1_tarski(B_76,B_75)
      | ~ r1_tarski(A_73,B_76)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_318,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_1'(A_80,B_81),'#skF_5')
      | ~ r1_tarski(A_80,'#skF_4')
      | r1_tarski(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_28,c_292])).

tff(c_327,plain,(
    ! [A_82] :
      ( ~ r1_tarski(A_82,'#skF_4')
      | r1_tarski(A_82,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_318,c_4])).

tff(c_91,plain,(
    ! [A_32,B_33,B_2,B_34] :
      ( r2_hidden('#skF_1'(A_32,B_33),B_2)
      | ~ r1_tarski(B_34,B_2)
      | ~ r1_tarski(A_32,B_34)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_409,plain,(
    ! [A_91,B_92,A_93] :
      ( r2_hidden('#skF_1'(A_91,B_92),'#skF_5')
      | ~ r1_tarski(A_91,A_93)
      | r1_tarski(A_91,B_92)
      | ~ r1_tarski(A_93,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_327,c_91])).

tff(c_653,plain,(
    ! [A_134,B_135,B_136] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_134,B_135),B_136),'#skF_5')
      | r1_tarski(k3_xboole_0(A_134,B_135),B_136)
      | ~ r1_tarski(A_134,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_131,c_409])).

tff(c_664,plain,(
    ! [A_134,B_135] :
      ( r1_tarski(k3_xboole_0(A_134,B_135),'#skF_5')
      | ~ r1_tarski(A_134,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_653,c_4])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    ! [A_35,B_36,B_37] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_35,B_36),B_37),B_36)
      | r1_tarski(k3_xboole_0(A_35,B_36),B_37) ) ),
    inference(resolution,[status(thm)],[c_31,c_10])).

tff(c_111,plain,(
    ! [A_35,B_36] : r1_tarski(k3_xboole_0(A_35,B_36),B_36) ),
    inference(resolution,[status(thm)],[c_95,c_4])).

tff(c_52,plain,(
    ! [A_1,B_2,B_24] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_24)
      | ~ r1_tarski(A_1,B_24)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_53,plain,(
    ! [D_26,A_27,B_28] :
      ( r2_hidden(D_26,k3_xboole_0(A_27,B_28))
      | ~ r2_hidden(D_26,B_28)
      | ~ r2_hidden(D_26,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1985,plain,(
    ! [A_255,A_256,B_257] :
      ( r1_tarski(A_255,k3_xboole_0(A_256,B_257))
      | ~ r2_hidden('#skF_1'(A_255,k3_xboole_0(A_256,B_257)),B_257)
      | ~ r2_hidden('#skF_1'(A_255,k3_xboole_0(A_256,B_257)),A_256) ) ),
    inference(resolution,[status(thm)],[c_53,c_4])).

tff(c_3765,plain,(
    ! [A_326,A_327,B_328] :
      ( ~ r2_hidden('#skF_1'(A_326,k3_xboole_0(A_327,B_328)),A_327)
      | ~ r1_tarski(A_326,B_328)
      | r1_tarski(A_326,k3_xboole_0(A_327,B_328)) ) ),
    inference(resolution,[status(thm)],[c_52,c_1985])).

tff(c_3926,plain,(
    ! [A_331,B_332,B_333] :
      ( ~ r1_tarski(A_331,B_332)
      | ~ r1_tarski(A_331,B_333)
      | r1_tarski(A_331,k3_xboole_0(B_333,B_332)) ) ),
    inference(resolution,[status(thm)],[c_52,c_3765])).

tff(c_26,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3984,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),'#skF_6')
    | ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_3926,c_26])).

tff(c_4016,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_3984])).

tff(c_4022,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_664,c_4016])).

tff(c_4036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_4022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.49/2.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.49/2.32  
% 6.49/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.49/2.32  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.49/2.32  
% 6.49/2.32  %Foreground sorts:
% 6.49/2.32  
% 6.49/2.32  
% 6.49/2.32  %Background operators:
% 6.49/2.32  
% 6.49/2.32  
% 6.49/2.32  %Foreground operators:
% 6.49/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.49/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.49/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.49/2.32  tff('#skF_5', type, '#skF_5': $i).
% 6.49/2.32  tff('#skF_6', type, '#skF_6': $i).
% 6.49/2.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.49/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.49/2.32  tff('#skF_4', type, '#skF_4': $i).
% 6.49/2.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.49/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.49/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.49/2.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.49/2.32  
% 6.49/2.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.49/2.33  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.49/2.33  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_xboole_1)).
% 6.49/2.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.49/2.33  tff(c_42, plain, (![A_20, B_21]: (~r2_hidden('#skF_1'(A_20, B_21), B_21) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.49/2.33  tff(c_47, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_42])).
% 6.49/2.33  tff(c_31, plain, (![A_18, B_19]: (r2_hidden('#skF_1'(A_18, B_19), A_18) | r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.49/2.33  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.49/2.33  tff(c_115, plain, (![A_40, B_41, B_42]: (r2_hidden('#skF_1'(k3_xboole_0(A_40, B_41), B_42), A_40) | r1_tarski(k3_xboole_0(A_40, B_41), B_42))), inference(resolution, [status(thm)], [c_31, c_12])).
% 6.49/2.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.49/2.33  tff(c_131, plain, (![A_40, B_41]: (r1_tarski(k3_xboole_0(A_40, B_41), A_40))), inference(resolution, [status(thm)], [c_115, c_4])).
% 6.49/2.33  tff(c_28, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.49/2.33  tff(c_49, plain, (![C_23, B_24, A_25]: (r2_hidden(C_23, B_24) | ~r2_hidden(C_23, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.49/2.33  tff(c_76, plain, (![A_32, B_33, B_34]: (r2_hidden('#skF_1'(A_32, B_33), B_34) | ~r1_tarski(A_32, B_34) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_6, c_49])).
% 6.49/2.33  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.49/2.33  tff(c_292, plain, (![A_73, B_74, B_75, B_76]: (r2_hidden('#skF_1'(A_73, B_74), B_75) | ~r1_tarski(B_76, B_75) | ~r1_tarski(A_73, B_76) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_76, c_2])).
% 6.49/2.33  tff(c_318, plain, (![A_80, B_81]: (r2_hidden('#skF_1'(A_80, B_81), '#skF_5') | ~r1_tarski(A_80, '#skF_4') | r1_tarski(A_80, B_81))), inference(resolution, [status(thm)], [c_28, c_292])).
% 6.49/2.33  tff(c_327, plain, (![A_82]: (~r1_tarski(A_82, '#skF_4') | r1_tarski(A_82, '#skF_5'))), inference(resolution, [status(thm)], [c_318, c_4])).
% 6.49/2.33  tff(c_91, plain, (![A_32, B_33, B_2, B_34]: (r2_hidden('#skF_1'(A_32, B_33), B_2) | ~r1_tarski(B_34, B_2) | ~r1_tarski(A_32, B_34) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_76, c_2])).
% 6.49/2.33  tff(c_409, plain, (![A_91, B_92, A_93]: (r2_hidden('#skF_1'(A_91, B_92), '#skF_5') | ~r1_tarski(A_91, A_93) | r1_tarski(A_91, B_92) | ~r1_tarski(A_93, '#skF_4'))), inference(resolution, [status(thm)], [c_327, c_91])).
% 6.49/2.33  tff(c_653, plain, (![A_134, B_135, B_136]: (r2_hidden('#skF_1'(k3_xboole_0(A_134, B_135), B_136), '#skF_5') | r1_tarski(k3_xboole_0(A_134, B_135), B_136) | ~r1_tarski(A_134, '#skF_4'))), inference(resolution, [status(thm)], [c_131, c_409])).
% 6.49/2.33  tff(c_664, plain, (![A_134, B_135]: (r1_tarski(k3_xboole_0(A_134, B_135), '#skF_5') | ~r1_tarski(A_134, '#skF_4'))), inference(resolution, [status(thm)], [c_653, c_4])).
% 6.49/2.33  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.49/2.33  tff(c_95, plain, (![A_35, B_36, B_37]: (r2_hidden('#skF_1'(k3_xboole_0(A_35, B_36), B_37), B_36) | r1_tarski(k3_xboole_0(A_35, B_36), B_37))), inference(resolution, [status(thm)], [c_31, c_10])).
% 6.49/2.33  tff(c_111, plain, (![A_35, B_36]: (r1_tarski(k3_xboole_0(A_35, B_36), B_36))), inference(resolution, [status(thm)], [c_95, c_4])).
% 6.49/2.33  tff(c_52, plain, (![A_1, B_2, B_24]: (r2_hidden('#skF_1'(A_1, B_2), B_24) | ~r1_tarski(A_1, B_24) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_49])).
% 6.49/2.33  tff(c_53, plain, (![D_26, A_27, B_28]: (r2_hidden(D_26, k3_xboole_0(A_27, B_28)) | ~r2_hidden(D_26, B_28) | ~r2_hidden(D_26, A_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.49/2.33  tff(c_1985, plain, (![A_255, A_256, B_257]: (r1_tarski(A_255, k3_xboole_0(A_256, B_257)) | ~r2_hidden('#skF_1'(A_255, k3_xboole_0(A_256, B_257)), B_257) | ~r2_hidden('#skF_1'(A_255, k3_xboole_0(A_256, B_257)), A_256))), inference(resolution, [status(thm)], [c_53, c_4])).
% 6.49/2.33  tff(c_3765, plain, (![A_326, A_327, B_328]: (~r2_hidden('#skF_1'(A_326, k3_xboole_0(A_327, B_328)), A_327) | ~r1_tarski(A_326, B_328) | r1_tarski(A_326, k3_xboole_0(A_327, B_328)))), inference(resolution, [status(thm)], [c_52, c_1985])).
% 6.49/2.33  tff(c_3926, plain, (![A_331, B_332, B_333]: (~r1_tarski(A_331, B_332) | ~r1_tarski(A_331, B_333) | r1_tarski(A_331, k3_xboole_0(B_333, B_332)))), inference(resolution, [status(thm)], [c_52, c_3765])).
% 6.49/2.33  tff(c_26, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.49/2.33  tff(c_3984, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), '#skF_6') | ~r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_3926, c_26])).
% 6.49/2.33  tff(c_4016, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_3984])).
% 6.49/2.33  tff(c_4022, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_664, c_4016])).
% 6.49/2.33  tff(c_4036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_4022])).
% 6.49/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.49/2.33  
% 6.49/2.33  Inference rules
% 6.49/2.33  ----------------------
% 6.49/2.33  #Ref     : 0
% 6.49/2.33  #Sup     : 1058
% 6.49/2.33  #Fact    : 0
% 6.49/2.33  #Define  : 0
% 6.49/2.33  #Split   : 1
% 6.49/2.33  #Chain   : 0
% 6.49/2.33  #Close   : 0
% 6.49/2.33  
% 6.49/2.33  Ordering : KBO
% 6.49/2.33  
% 6.49/2.33  Simplification rules
% 6.49/2.33  ----------------------
% 6.49/2.33  #Subsume      : 345
% 6.49/2.33  #Demod        : 129
% 6.49/2.33  #Tautology    : 64
% 6.49/2.33  #SimpNegUnit  : 0
% 6.49/2.33  #BackRed      : 0
% 6.49/2.33  
% 6.49/2.33  #Partial instantiations: 0
% 6.49/2.33  #Strategies tried      : 1
% 6.49/2.33  
% 6.49/2.33  Timing (in seconds)
% 6.49/2.33  ----------------------
% 6.49/2.33  Preprocessing        : 0.29
% 6.49/2.33  Parsing              : 0.15
% 6.49/2.33  CNF conversion       : 0.02
% 6.49/2.33  Main loop            : 1.23
% 6.49/2.33  Inferencing          : 0.36
% 6.49/2.33  Reduction            : 0.27
% 6.49/2.33  Demodulation         : 0.18
% 6.49/2.33  BG Simplification    : 0.04
% 6.49/2.33  Subsumption          : 0.49
% 6.49/2.33  Abstraction          : 0.06
% 6.49/2.34  MUC search           : 0.00
% 6.49/2.34  Cooper               : 0.00
% 6.49/2.34  Total                : 1.55
% 6.49/2.34  Index Insertion      : 0.00
% 6.49/2.34  Index Deletion       : 0.00
% 6.49/2.34  Index Matching       : 0.00
% 6.49/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
