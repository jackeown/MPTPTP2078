%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:25 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 102 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 202 expanded)
%              Number of equality atoms :   22 (  96 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(A,B)
        & r2_hidden(C,k2_xboole_0(A,B))
        & ~ ( r2_hidden(C,A)
            & ~ r2_hidden(C,B) )
        & ~ ( r2_hidden(C,B)
            & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,
    ( r1_xboole_0('#skF_4','#skF_4')
    | k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_41,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_42,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_40])).

tff(c_30,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_43,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_30])).

tff(c_36,plain,
    ( r1_xboole_0('#skF_4','#skF_4')
    | ~ r1_xboole_0('#skF_5','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_36])).

tff(c_28,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_53,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | A_10 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_28])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [C_25,B_26,A_27] :
      ( ~ r2_hidden(C_25,B_26)
      | ~ r2_hidden(C_25,A_27)
      | ~ r2_hidden(C_25,k2_xboole_0(A_27,B_26))
      | ~ r1_xboole_0(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    ! [D_28,A_29,B_30] :
      ( ~ r2_hidden(D_28,A_29)
      | ~ r1_xboole_0(A_29,B_30)
      | ~ r2_hidden(D_28,B_30) ) ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_119,plain,(
    ! [A_37,B_38] :
      ( ~ r1_xboole_0(A_37,B_38)
      | ~ r2_hidden('#skF_3'(A_37),B_38)
      | A_37 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_53,c_85])).

tff(c_134,plain,(
    ! [A_39] :
      ( ~ r1_xboole_0(A_39,A_39)
      | A_39 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_53,c_119])).

tff(c_137,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_134])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_137])).

tff(c_146,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_180,plain,(
    ! [C_53,B_54,A_55] :
      ( ~ r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r2_hidden(C_53,k2_xboole_0(A_55,B_54))
      | ~ r1_xboole_0(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_203,plain,(
    ! [D_59,B_60,A_61] :
      ( ~ r2_hidden(D_59,B_60)
      | ~ r1_xboole_0(A_61,B_60)
      | ~ r2_hidden(D_59,A_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_180])).

tff(c_223,plain,(
    ! [A_65,A_66] :
      ( ~ r1_xboole_0(A_65,A_66)
      | ~ r2_hidden('#skF_3'(A_66),A_65)
      | k1_xboole_0 = A_66 ) ),
    inference(resolution,[status(thm)],[c_28,c_203])).

tff(c_238,plain,(
    ! [A_67] :
      ( ~ r1_xboole_0(A_67,A_67)
      | k1_xboole_0 = A_67 ) ),
    inference(resolution,[status(thm)],[c_28,c_223])).

tff(c_241,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_146,c_238])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_241])).

tff(c_251,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_250,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_257,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_250])).

tff(c_252,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_30])).

tff(c_266,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_252])).

tff(c_38,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_xboole_0('#skF_5','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_257,c_257,c_251,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.29  
% 1.96/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.29  %$ r2_hidden > r1_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.96/1.29  
% 1.96/1.29  %Foreground sorts:
% 1.96/1.29  
% 1.96/1.29  
% 1.96/1.29  %Background operators:
% 1.96/1.29  
% 1.96/1.29  
% 1.96/1.29  %Foreground operators:
% 1.96/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.96/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.29  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.96/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.29  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.29  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.96/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.29  
% 1.96/1.30  tff(f_74, negated_conjecture, ~(![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.96/1.30  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.96/1.30  tff(f_59, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.96/1.30  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.96/1.30  tff(f_51, axiom, (![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_0)).
% 1.96/1.30  tff(c_34, plain, (k1_xboole_0!='#skF_4' | k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.96/1.30  tff(c_40, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_34])).
% 1.96/1.30  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_4') | k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.96/1.30  tff(c_41, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_32])).
% 1.96/1.30  tff(c_42, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_40])).
% 1.96/1.30  tff(c_30, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.96/1.30  tff(c_43, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_30])).
% 1.96/1.30  tff(c_36, plain, (r1_xboole_0('#skF_4', '#skF_4') | ~r1_xboole_0('#skF_5', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.96/1.30  tff(c_52, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_43, c_36])).
% 1.96/1.30  tff(c_28, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.96/1.30  tff(c_53, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | A_10='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_28])).
% 1.96/1.30  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.96/1.30  tff(c_71, plain, (![C_25, B_26, A_27]: (~r2_hidden(C_25, B_26) | ~r2_hidden(C_25, A_27) | ~r2_hidden(C_25, k2_xboole_0(A_27, B_26)) | ~r1_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.30  tff(c_85, plain, (![D_28, A_29, B_30]: (~r2_hidden(D_28, A_29) | ~r1_xboole_0(A_29, B_30) | ~r2_hidden(D_28, B_30))), inference(resolution, [status(thm)], [c_4, c_71])).
% 1.96/1.30  tff(c_119, plain, (![A_37, B_38]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden('#skF_3'(A_37), B_38) | A_37='#skF_5')), inference(resolution, [status(thm)], [c_53, c_85])).
% 1.96/1.30  tff(c_134, plain, (![A_39]: (~r1_xboole_0(A_39, A_39) | A_39='#skF_5')), inference(resolution, [status(thm)], [c_53, c_119])).
% 1.96/1.30  tff(c_137, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_52, c_134])).
% 1.96/1.30  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_137])).
% 1.96/1.30  tff(c_146, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 1.96/1.30  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.96/1.30  tff(c_180, plain, (![C_53, B_54, A_55]: (~r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r2_hidden(C_53, k2_xboole_0(A_55, B_54)) | ~r1_xboole_0(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.30  tff(c_203, plain, (![D_59, B_60, A_61]: (~r2_hidden(D_59, B_60) | ~r1_xboole_0(A_61, B_60) | ~r2_hidden(D_59, A_61))), inference(resolution, [status(thm)], [c_6, c_180])).
% 1.96/1.30  tff(c_223, plain, (![A_65, A_66]: (~r1_xboole_0(A_65, A_66) | ~r2_hidden('#skF_3'(A_66), A_65) | k1_xboole_0=A_66)), inference(resolution, [status(thm)], [c_28, c_203])).
% 1.96/1.30  tff(c_238, plain, (![A_67]: (~r1_xboole_0(A_67, A_67) | k1_xboole_0=A_67)), inference(resolution, [status(thm)], [c_28, c_223])).
% 1.96/1.30  tff(c_241, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_146, c_238])).
% 1.96/1.30  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_241])).
% 1.96/1.30  tff(c_251, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_34])).
% 1.96/1.30  tff(c_250, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_34])).
% 1.96/1.30  tff(c_257, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_251, c_250])).
% 1.96/1.30  tff(c_252, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_30])).
% 1.96/1.30  tff(c_266, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_252])).
% 1.96/1.30  tff(c_38, plain, (k1_xboole_0!='#skF_4' | ~r1_xboole_0('#skF_5', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.96/1.30  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_266, c_257, c_257, c_251, c_38])).
% 1.96/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.30  
% 1.96/1.30  Inference rules
% 1.96/1.30  ----------------------
% 1.96/1.30  #Ref     : 0
% 1.96/1.30  #Sup     : 50
% 1.96/1.30  #Fact    : 0
% 1.96/1.30  #Define  : 0
% 1.96/1.30  #Split   : 2
% 1.96/1.30  #Chain   : 0
% 1.96/1.30  #Close   : 0
% 1.96/1.30  
% 1.96/1.30  Ordering : KBO
% 1.96/1.30  
% 1.96/1.30  Simplification rules
% 1.96/1.30  ----------------------
% 1.96/1.30  #Subsume      : 4
% 1.96/1.30  #Demod        : 14
% 1.96/1.30  #Tautology    : 19
% 1.96/1.30  #SimpNegUnit  : 2
% 1.96/1.30  #BackRed      : 4
% 1.96/1.30  
% 1.96/1.30  #Partial instantiations: 0
% 1.96/1.30  #Strategies tried      : 1
% 1.96/1.30  
% 1.96/1.30  Timing (in seconds)
% 1.96/1.30  ----------------------
% 1.96/1.30  Preprocessing        : 0.31
% 1.96/1.30  Parsing              : 0.16
% 1.96/1.30  CNF conversion       : 0.02
% 1.96/1.30  Main loop            : 0.19
% 1.96/1.30  Inferencing          : 0.07
% 1.96/1.31  Reduction            : 0.05
% 1.96/1.31  Demodulation         : 0.04
% 1.96/1.31  BG Simplification    : 0.02
% 1.96/1.31  Subsumption          : 0.04
% 1.96/1.31  Abstraction          : 0.01
% 1.96/1.31  MUC search           : 0.00
% 1.96/1.31  Cooper               : 0.00
% 1.96/1.31  Total                : 0.53
% 1.96/1.31  Index Insertion      : 0.00
% 1.96/1.31  Index Deletion       : 0.00
% 1.96/1.31  Index Matching       : 0.00
% 1.96/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
