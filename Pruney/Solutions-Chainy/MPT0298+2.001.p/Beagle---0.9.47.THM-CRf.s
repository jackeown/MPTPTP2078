%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:38 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 110 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   70 ( 201 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_12,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_19,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_16,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_21,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_26,plain,(
    ! [A_9,C_10,B_11,D_12] :
      ( r2_hidden(A_9,C_10)
      | ~ r2_hidden(k4_tarski(A_9,B_11),k2_zfmisc_1(C_10,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_21,c_26])).

tff(c_33,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_29])).

tff(c_35,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_18,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_37,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_36])).

tff(c_38,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_34,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4))
      | ~ r2_hidden(B_2,D_4)
      | ~ r2_hidden(A_1,C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_14,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4'))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_54,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_14])).

tff(c_57,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_54])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_57])).

tff(c_63,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_10,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_66,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64])).

tff(c_67,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_70,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_71,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_79,plain,(
    ! [B_25,D_26,A_27,C_28] :
      ( r2_hidden(B_25,D_26)
      | ~ r2_hidden(k4_tarski(A_27,B_25),k2_zfmisc_1(C_28,D_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_71,c_79])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_82])).

tff(c_88,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_90,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_18])).

tff(c_87,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_109,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_14])).

tff(c_112,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_109])).

tff(c_116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_87,c_112])).

tff(c_118,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_120,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_62])).

tff(c_117,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_127,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52))
      | ~ r2_hidden(B_50,D_52)
      | ~ r2_hidden(A_49,C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_126,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_118,c_8])).

tff(c_130,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_126])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_117,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 1.62/1.14  
% 1.62/1.14  %Foreground sorts:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Background operators:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Foreground operators:
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.62/1.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.62/1.14  tff('#skF_7', type, '#skF_7': $i).
% 1.62/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.62/1.14  tff('#skF_6', type, '#skF_6': $i).
% 1.62/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.14  tff('#skF_8', type, '#skF_8': $i).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.62/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.14  
% 1.76/1.16  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 1.76/1.16  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.76/1.16  tff(c_12, plain, (r2_hidden('#skF_1', '#skF_3') | ~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.76/1.16  tff(c_19, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_12])).
% 1.76/1.16  tff(c_16, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.76/1.16  tff(c_21, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_16])).
% 1.76/1.16  tff(c_26, plain, (![A_9, C_10, B_11, D_12]: (r2_hidden(A_9, C_10) | ~r2_hidden(k4_tarski(A_9, B_11), k2_zfmisc_1(C_10, D_12)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.76/1.16  tff(c_29, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_21, c_26])).
% 1.76/1.16  tff(c_33, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19, c_29])).
% 1.76/1.16  tff(c_35, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_16])).
% 1.76/1.16  tff(c_18, plain, (r2_hidden('#skF_1', '#skF_3') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.76/1.16  tff(c_36, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_18])).
% 1.76/1.16  tff(c_37, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_36])).
% 1.76/1.16  tff(c_38, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 1.76/1.16  tff(c_34, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_16])).
% 1.76/1.16  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)) | ~r2_hidden(B_2, D_4) | ~r2_hidden(A_1, C_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.76/1.16  tff(c_39, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_18])).
% 1.76/1.16  tff(c_14, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4')) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.76/1.16  tff(c_54, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_39, c_14])).
% 1.76/1.16  tff(c_57, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_2, c_54])).
% 1.76/1.16  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_57])).
% 1.76/1.16  tff(c_63, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_12])).
% 1.76/1.16  tff(c_10, plain, (r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.76/1.16  tff(c_64, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_10])).
% 1.76/1.16  tff(c_66, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_64])).
% 1.76/1.16  tff(c_67, plain, (~r2_hidden('#skF_6', '#skF_8') | r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_10])).
% 1.76/1.16  tff(c_70, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_67])).
% 1.76/1.16  tff(c_71, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_16])).
% 1.76/1.16  tff(c_79, plain, (![B_25, D_26, A_27, C_28]: (r2_hidden(B_25, D_26) | ~r2_hidden(k4_tarski(A_27, B_25), k2_zfmisc_1(C_28, D_26)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.76/1.16  tff(c_82, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_71, c_79])).
% 1.76/1.16  tff(c_86, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_82])).
% 1.76/1.16  tff(c_88, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_16])).
% 1.76/1.16  tff(c_90, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_88, c_18])).
% 1.76/1.16  tff(c_87, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_16])).
% 1.76/1.16  tff(c_109, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_88, c_14])).
% 1.76/1.16  tff(c_112, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_2, c_109])).
% 1.76/1.16  tff(c_116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_87, c_112])).
% 1.76/1.16  tff(c_118, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_67])).
% 1.76/1.16  tff(c_62, plain, (~r2_hidden('#skF_6', '#skF_8') | r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_12])).
% 1.76/1.16  tff(c_120, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_62])).
% 1.76/1.16  tff(c_117, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_67])).
% 1.76/1.16  tff(c_127, plain, (![A_49, B_50, C_51, D_52]: (r2_hidden(k4_tarski(A_49, B_50), k2_zfmisc_1(C_51, D_52)) | ~r2_hidden(B_50, D_52) | ~r2_hidden(A_49, C_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.76/1.16  tff(c_8, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.76/1.16  tff(c_126, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_118, c_8])).
% 1.76/1.16  tff(c_130, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_127, c_126])).
% 1.76/1.16  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_117, c_130])).
% 1.76/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.16  
% 1.76/1.16  Inference rules
% 1.76/1.16  ----------------------
% 1.76/1.16  #Ref     : 0
% 1.76/1.16  #Sup     : 15
% 1.76/1.16  #Fact    : 0
% 1.76/1.16  #Define  : 0
% 1.76/1.16  #Split   : 6
% 1.76/1.16  #Chain   : 0
% 1.76/1.16  #Close   : 0
% 1.76/1.16  
% 1.76/1.16  Ordering : KBO
% 1.76/1.16  
% 1.76/1.16  Simplification rules
% 1.76/1.16  ----------------------
% 1.76/1.16  #Subsume      : 7
% 1.76/1.16  #Demod        : 17
% 1.76/1.16  #Tautology    : 9
% 1.76/1.16  #SimpNegUnit  : 6
% 1.76/1.16  #BackRed      : 0
% 1.76/1.16  
% 1.76/1.16  #Partial instantiations: 0
% 1.76/1.16  #Strategies tried      : 1
% 1.76/1.16  
% 1.76/1.16  Timing (in seconds)
% 1.76/1.16  ----------------------
% 1.76/1.16  Preprocessing        : 0.24
% 1.76/1.16  Parsing              : 0.13
% 1.76/1.16  CNF conversion       : 0.02
% 1.76/1.16  Main loop            : 0.15
% 1.76/1.16  Inferencing          : 0.06
% 1.76/1.16  Reduction            : 0.04
% 1.76/1.16  Demodulation         : 0.02
% 1.76/1.16  BG Simplification    : 0.01
% 1.76/1.16  Subsumption          : 0.03
% 1.76/1.16  Abstraction          : 0.01
% 1.76/1.16  MUC search           : 0.00
% 1.76/1.16  Cooper               : 0.00
% 1.76/1.16  Total                : 0.43
% 1.76/1.16  Index Insertion      : 0.00
% 1.76/1.16  Index Deletion       : 0.00
% 1.76/1.16  Index Matching       : 0.00
% 1.76/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
