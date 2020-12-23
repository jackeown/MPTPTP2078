%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:58 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 139 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 258 expanded)
%              Number of equality atoms :   17 (  93 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_55,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_57,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_26,plain,(
    ! [A_11,C_13,B_12,D_14] :
      ( r2_hidden(A_11,C_13)
      | ~ r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(C_13,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_61,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_57,c_26])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_69,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_65])).

tff(c_71,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_36])).

tff(c_22,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( r2_hidden(k4_tarski(A_11,B_12),k2_zfmisc_1(C_13,D_14))
      | ~ r2_hidden(B_12,D_14)
      | ~ r2_hidden(A_11,C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_34,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_130,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_34])).

tff(c_131,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_130])).

tff(c_134,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_131])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_78,c_134])).

tff(c_140,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_139,plain,
    ( ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_145,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_148,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_38])).

tff(c_149,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_156,plain,(
    ! [B_45,D_46,A_47,C_48] :
      ( r2_hidden(B_45,D_46)
      | ~ r2_hidden(k4_tarski(A_47,B_45),k2_zfmisc_1(C_48,D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_159,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_149,c_156])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_159])).

tff(c_165,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_173,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_36])).

tff(c_174,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_173])).

tff(c_164,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_228,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_164,c_34])).

tff(c_229,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_228])).

tff(c_232,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_229])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_174,c_232])).

tff(c_238,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_30,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_244,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_238,c_30])).

tff(c_237,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_28,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_273,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_238,c_237,c_28])).

tff(c_276,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_273])).

tff(c_280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_244,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.23  
% 1.91/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.23  %$ r2_hidden > k2_enumset1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 1.91/1.23  
% 1.91/1.23  %Foreground sorts:
% 1.91/1.23  
% 1.91/1.23  
% 1.91/1.23  %Background operators:
% 1.91/1.23  
% 1.91/1.23  
% 1.91/1.23  %Foreground operators:
% 1.91/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.91/1.23  tff('#skF_7', type, '#skF_7': $i).
% 1.91/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.23  tff('#skF_10', type, '#skF_10': $i).
% 1.91/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.91/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.23  tff('#skF_9', type, '#skF_9': $i).
% 1.91/1.23  tff('#skF_8', type, '#skF_8': $i).
% 1.91/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.23  
% 1.91/1.24  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.91/1.24  tff(f_53, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 1.91/1.24  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 1.91/1.24  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.24  tff(c_32, plain, ('#skF_5'='#skF_3' | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.24  tff(c_55, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_32])).
% 1.91/1.24  tff(c_38, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.24  tff(c_57, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_38])).
% 1.91/1.24  tff(c_26, plain, (![A_11, C_13, B_12, D_14]: (r2_hidden(A_11, C_13) | ~r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(C_13, D_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.24  tff(c_61, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_57, c_26])).
% 1.91/1.24  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.24  tff(c_65, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_61, c_2])).
% 1.91/1.24  tff(c_69, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_65])).
% 1.91/1.24  tff(c_71, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_38])).
% 1.91/1.24  tff(c_36, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.24  tff(c_78, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_71, c_36])).
% 1.91/1.24  tff(c_22, plain, (![A_11, B_12, C_13, D_14]: (r2_hidden(k4_tarski(A_11, B_12), k2_zfmisc_1(C_13, D_14)) | ~r2_hidden(B_12, D_14) | ~r2_hidden(A_11, C_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.24  tff(c_70, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 1.91/1.24  tff(c_34, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.24  tff(c_130, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_34])).
% 1.91/1.24  tff(c_131, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_71, c_130])).
% 1.91/1.24  tff(c_134, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_131])).
% 1.91/1.24  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_78, c_134])).
% 1.91/1.24  tff(c_140, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_32])).
% 1.91/1.24  tff(c_139, plain, (~r2_hidden('#skF_8', '#skF_10') | '#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 1.91/1.24  tff(c_145, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_139])).
% 1.91/1.24  tff(c_148, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_38])).
% 1.91/1.24  tff(c_149, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_148])).
% 1.91/1.24  tff(c_156, plain, (![B_45, D_46, A_47, C_48]: (r2_hidden(B_45, D_46) | ~r2_hidden(k4_tarski(A_47, B_45), k2_zfmisc_1(C_48, D_46)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.24  tff(c_159, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_149, c_156])).
% 1.91/1.24  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_159])).
% 1.91/1.24  tff(c_165, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_148])).
% 1.91/1.24  tff(c_173, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_36])).
% 1.91/1.24  tff(c_174, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_165, c_173])).
% 1.91/1.24  tff(c_164, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_148])).
% 1.91/1.25  tff(c_228, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_164, c_34])).
% 1.91/1.25  tff(c_229, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_165, c_228])).
% 1.91/1.25  tff(c_232, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_229])).
% 1.91/1.25  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_174, c_232])).
% 1.91/1.25  tff(c_238, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_139])).
% 1.91/1.25  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.25  tff(c_244, plain, (r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_238, c_30])).
% 1.91/1.25  tff(c_237, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_139])).
% 1.91/1.25  tff(c_28, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.25  tff(c_273, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_238, c_237, c_28])).
% 1.91/1.25  tff(c_276, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_273])).
% 1.91/1.25  tff(c_280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_244, c_276])).
% 1.91/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.25  
% 1.91/1.25  Inference rules
% 1.91/1.25  ----------------------
% 1.91/1.25  #Ref     : 0
% 1.91/1.25  #Sup     : 42
% 1.91/1.25  #Fact    : 0
% 1.91/1.25  #Define  : 0
% 1.91/1.25  #Split   : 5
% 1.91/1.25  #Chain   : 0
% 1.91/1.25  #Close   : 0
% 1.91/1.25  
% 1.91/1.25  Ordering : KBO
% 1.91/1.25  
% 1.91/1.25  Simplification rules
% 1.91/1.25  ----------------------
% 1.91/1.25  #Subsume      : 8
% 1.91/1.25  #Demod        : 31
% 1.91/1.25  #Tautology    : 31
% 1.91/1.25  #SimpNegUnit  : 6
% 1.91/1.25  #BackRed      : 0
% 1.91/1.25  
% 1.91/1.25  #Partial instantiations: 0
% 1.91/1.25  #Strategies tried      : 1
% 1.91/1.25  
% 1.91/1.25  Timing (in seconds)
% 1.91/1.25  ----------------------
% 1.91/1.25  Preprocessing        : 0.29
% 1.91/1.25  Parsing              : 0.15
% 1.91/1.25  CNF conversion       : 0.02
% 1.91/1.25  Main loop            : 0.20
% 1.91/1.25  Inferencing          : 0.08
% 1.91/1.25  Reduction            : 0.06
% 1.91/1.25  Demodulation         : 0.04
% 1.91/1.25  BG Simplification    : 0.01
% 1.91/1.25  Subsumption          : 0.04
% 1.91/1.25  Abstraction          : 0.01
% 1.91/1.25  MUC search           : 0.00
% 1.91/1.25  Cooper               : 0.00
% 1.91/1.25  Total                : 0.52
% 1.91/1.25  Index Insertion      : 0.00
% 1.91/1.25  Index Deletion       : 0.00
% 1.91/1.25  Index Matching       : 0.00
% 1.91/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
