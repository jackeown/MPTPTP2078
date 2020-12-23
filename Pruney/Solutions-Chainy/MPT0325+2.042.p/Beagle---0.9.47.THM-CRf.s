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
% DateTime   : Thu Dec  3 09:54:26 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 185 expanded)
%              Number of leaves         :   18 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 418 expanded)
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

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_51,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_113,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( r2_hidden(k4_tarski(A_44,B_45),k2_zfmisc_1(C_46,D_47))
      | ~ r2_hidden(B_45,D_47)
      | ~ r2_hidden(A_44,C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_177,plain,(
    ! [D_63,B_66,A_67,C_64,B_65] :
      ( r2_hidden(k4_tarski(A_67,B_65),B_66)
      | ~ r1_tarski(k2_zfmisc_1(C_64,D_63),B_66)
      | ~ r2_hidden(B_65,D_63)
      | ~ r2_hidden(A_67,C_64) ) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_223,plain,(
    ! [A_70,B_71] :
      ( r2_hidden(k4_tarski(A_70,B_71),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_71,'#skF_3')
      | ~ r2_hidden(A_70,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_177])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_239,plain,(
    ! [A_70,B_71] :
      ( r2_hidden(A_70,'#skF_4')
      | ~ r2_hidden(B_71,'#skF_3')
      | ~ r2_hidden(A_70,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_223,c_12])).

tff(c_344,plain,(
    ! [B_81] : ~ r2_hidden(B_81,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_356,plain,(
    ! [B_82] : r1_tarski('#skF_3',B_82) ),
    inference(resolution,[status(thm)],[c_6,c_344])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( ~ r1_tarski(A_12,k2_zfmisc_1(A_12,B_13))
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_369,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_356,c_22])).

tff(c_16,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_384,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_369,c_16])).

tff(c_26,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_386,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_26])).

tff(c_433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_386])).

tff(c_435,plain,(
    ! [A_88] :
      ( r2_hidden(A_88,'#skF_4')
      | ~ r2_hidden(A_88,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_472,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_1'('#skF_2',B_93),'#skF_4')
      | r1_tarski('#skF_2',B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_435])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_482,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_472,c_4])).

tff(c_489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_51,c_482])).

tff(c_490,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_553,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( r2_hidden(k4_tarski(A_123,B_124),k2_zfmisc_1(C_125,D_126))
      | ~ r2_hidden(B_124,D_126)
      | ~ r2_hidden(A_123,C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_730,plain,(
    ! [B_155,C_152,A_154,B_156,D_153] :
      ( r2_hidden(k4_tarski(A_154,B_155),B_156)
      | ~ r1_tarski(k2_zfmisc_1(C_152,D_153),B_156)
      | ~ r2_hidden(B_155,D_153)
      | ~ r2_hidden(A_154,C_152) ) ),
    inference(resolution,[status(thm)],[c_553,c_2])).

tff(c_746,plain,(
    ! [A_157,B_158] :
      ( r2_hidden(k4_tarski(A_157,B_158),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_158,'#skF_3')
      | ~ r2_hidden(A_157,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_730])).

tff(c_10,plain,(
    ! [B_7,D_9,A_6,C_8] :
      ( r2_hidden(B_7,D_9)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_755,plain,(
    ! [B_158,A_157] :
      ( r2_hidden(B_158,'#skF_5')
      | ~ r2_hidden(B_158,'#skF_3')
      | ~ r2_hidden(A_157,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_746,c_10])).

tff(c_759,plain,(
    ! [A_159] : ~ r2_hidden(A_159,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_755])).

tff(c_771,plain,(
    ! [B_160] : r1_tarski('#skF_2',B_160) ),
    inference(resolution,[status(thm)],[c_6,c_759])).

tff(c_789,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_771,c_22])).

tff(c_18,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_800,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_2',B_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_789,c_18])).

tff(c_801,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_26])).

tff(c_874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_801])).

tff(c_876,plain,(
    ! [B_167] :
      ( r2_hidden(B_167,'#skF_5')
      | ~ r2_hidden(B_167,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_755])).

tff(c_912,plain,(
    ! [A_170] :
      ( r1_tarski(A_170,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_170,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_876,c_4])).

tff(c_920,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_912])).

tff(c_925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_490,c_490,c_920])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.94  
% 3.52/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.94  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.52/1.94  
% 3.52/1.94  %Foreground sorts:
% 3.52/1.94  
% 3.52/1.94  
% 3.52/1.94  %Background operators:
% 3.52/1.94  
% 3.52/1.94  
% 3.52/1.94  %Foreground operators:
% 3.52/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.94  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.52/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.94  tff('#skF_5', type, '#skF_5': $i).
% 3.52/1.94  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.94  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.94  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.52/1.94  
% 3.60/1.97  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 3.60/1.97  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.60/1.97  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.60/1.97  tff(f_50, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 3.60/1.97  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.60/1.97  tff(c_24, plain, (~r1_tarski('#skF_3', '#skF_5') | ~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.60/1.97  tff(c_51, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 3.60/1.97  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.60/1.97  tff(c_28, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.60/1.97  tff(c_113, plain, (![A_44, B_45, C_46, D_47]: (r2_hidden(k4_tarski(A_44, B_45), k2_zfmisc_1(C_46, D_47)) | ~r2_hidden(B_45, D_47) | ~r2_hidden(A_44, C_46))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.60/1.97  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.60/1.97  tff(c_177, plain, (![D_63, B_66, A_67, C_64, B_65]: (r2_hidden(k4_tarski(A_67, B_65), B_66) | ~r1_tarski(k2_zfmisc_1(C_64, D_63), B_66) | ~r2_hidden(B_65, D_63) | ~r2_hidden(A_67, C_64))), inference(resolution, [status(thm)], [c_113, c_2])).
% 3.60/1.97  tff(c_223, plain, (![A_70, B_71]: (r2_hidden(k4_tarski(A_70, B_71), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_71, '#skF_3') | ~r2_hidden(A_70, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_177])).
% 3.60/1.97  tff(c_12, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.60/1.97  tff(c_239, plain, (![A_70, B_71]: (r2_hidden(A_70, '#skF_4') | ~r2_hidden(B_71, '#skF_3') | ~r2_hidden(A_70, '#skF_2'))), inference(resolution, [status(thm)], [c_223, c_12])).
% 3.60/1.97  tff(c_344, plain, (![B_81]: (~r2_hidden(B_81, '#skF_3'))), inference(splitLeft, [status(thm)], [c_239])).
% 3.60/1.97  tff(c_356, plain, (![B_82]: (r1_tarski('#skF_3', B_82))), inference(resolution, [status(thm)], [c_6, c_344])).
% 3.60/1.97  tff(c_22, plain, (![A_12, B_13]: (~r1_tarski(A_12, k2_zfmisc_1(A_12, B_13)) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.60/1.97  tff(c_369, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_356, c_22])).
% 3.60/1.97  tff(c_16, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.60/1.97  tff(c_384, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_369, c_369, c_16])).
% 3.60/1.97  tff(c_26, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.60/1.97  tff(c_386, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_369, c_26])).
% 3.60/1.97  tff(c_433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_384, c_386])).
% 3.60/1.97  tff(c_435, plain, (![A_88]: (r2_hidden(A_88, '#skF_4') | ~r2_hidden(A_88, '#skF_2'))), inference(splitRight, [status(thm)], [c_239])).
% 3.60/1.97  tff(c_472, plain, (![B_93]: (r2_hidden('#skF_1'('#skF_2', B_93), '#skF_4') | r1_tarski('#skF_2', B_93))), inference(resolution, [status(thm)], [c_6, c_435])).
% 3.60/1.97  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.60/1.97  tff(c_482, plain, (r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_472, c_4])).
% 3.60/1.97  tff(c_489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_51, c_482])).
% 3.60/1.97  tff(c_490, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_24])).
% 3.60/1.97  tff(c_553, plain, (![A_123, B_124, C_125, D_126]: (r2_hidden(k4_tarski(A_123, B_124), k2_zfmisc_1(C_125, D_126)) | ~r2_hidden(B_124, D_126) | ~r2_hidden(A_123, C_125))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.60/1.97  tff(c_730, plain, (![B_155, C_152, A_154, B_156, D_153]: (r2_hidden(k4_tarski(A_154, B_155), B_156) | ~r1_tarski(k2_zfmisc_1(C_152, D_153), B_156) | ~r2_hidden(B_155, D_153) | ~r2_hidden(A_154, C_152))), inference(resolution, [status(thm)], [c_553, c_2])).
% 3.60/1.97  tff(c_746, plain, (![A_157, B_158]: (r2_hidden(k4_tarski(A_157, B_158), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_158, '#skF_3') | ~r2_hidden(A_157, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_730])).
% 3.60/1.97  tff(c_10, plain, (![B_7, D_9, A_6, C_8]: (r2_hidden(B_7, D_9) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.60/1.97  tff(c_755, plain, (![B_158, A_157]: (r2_hidden(B_158, '#skF_5') | ~r2_hidden(B_158, '#skF_3') | ~r2_hidden(A_157, '#skF_2'))), inference(resolution, [status(thm)], [c_746, c_10])).
% 3.60/1.97  tff(c_759, plain, (![A_159]: (~r2_hidden(A_159, '#skF_2'))), inference(splitLeft, [status(thm)], [c_755])).
% 3.60/1.97  tff(c_771, plain, (![B_160]: (r1_tarski('#skF_2', B_160))), inference(resolution, [status(thm)], [c_6, c_759])).
% 3.60/1.97  tff(c_789, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_771, c_22])).
% 3.60/1.97  tff(c_18, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.60/1.97  tff(c_800, plain, (![B_11]: (k2_zfmisc_1('#skF_2', B_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_789, c_789, c_18])).
% 3.60/1.97  tff(c_801, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_789, c_26])).
% 3.60/1.97  tff(c_874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_800, c_801])).
% 3.60/1.97  tff(c_876, plain, (![B_167]: (r2_hidden(B_167, '#skF_5') | ~r2_hidden(B_167, '#skF_3'))), inference(splitRight, [status(thm)], [c_755])).
% 3.60/1.97  tff(c_912, plain, (![A_170]: (r1_tarski(A_170, '#skF_5') | ~r2_hidden('#skF_1'(A_170, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_876, c_4])).
% 3.60/1.97  tff(c_920, plain, (r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_912])).
% 3.60/1.97  tff(c_925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_490, c_490, c_920])).
% 3.60/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.97  
% 3.60/1.97  Inference rules
% 3.60/1.97  ----------------------
% 3.60/1.97  #Ref     : 0
% 3.60/1.97  #Sup     : 190
% 3.60/1.97  #Fact    : 0
% 3.60/1.97  #Define  : 0
% 3.60/1.97  #Split   : 8
% 3.60/1.97  #Chain   : 0
% 3.60/1.97  #Close   : 0
% 3.60/1.97  
% 3.60/1.97  Ordering : KBO
% 3.60/1.97  
% 3.60/1.97  Simplification rules
% 3.60/1.97  ----------------------
% 3.60/1.97  #Subsume      : 63
% 3.60/1.97  #Demod        : 95
% 3.60/1.97  #Tautology    : 67
% 3.60/1.97  #SimpNegUnit  : 16
% 3.60/1.97  #BackRed      : 41
% 3.60/1.97  
% 3.60/1.97  #Partial instantiations: 0
% 3.60/1.97  #Strategies tried      : 1
% 3.60/1.97  
% 3.60/1.97  Timing (in seconds)
% 3.60/1.97  ----------------------
% 3.60/1.97  Preprocessing        : 0.43
% 3.60/1.97  Parsing              : 0.23
% 3.60/1.97  CNF conversion       : 0.03
% 3.60/1.97  Main loop            : 0.63
% 3.60/1.97  Inferencing          : 0.24
% 3.60/1.97  Reduction            : 0.16
% 3.60/1.97  Demodulation         : 0.10
% 3.60/1.97  BG Simplification    : 0.04
% 3.60/1.97  Subsumption          : 0.16
% 3.60/1.97  Abstraction          : 0.02
% 3.60/1.97  MUC search           : 0.00
% 3.60/1.97  Cooper               : 0.00
% 3.60/1.97  Total                : 1.12
% 3.60/1.97  Index Insertion      : 0.00
% 3.60/1.97  Index Deletion       : 0.00
% 3.60/1.97  Index Matching       : 0.00
% 3.60/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
