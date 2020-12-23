%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:51 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 184 expanded)
%              Number of leaves         :   14 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 378 expanded)
%              Number of equality atoms :   10 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,A) = k2_zfmisc_1(B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_20,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( r2_hidden(k4_tarski(A_37,B_38),k2_zfmisc_1(C_39,D_40))
      | ~ r2_hidden(B_38,D_40)
      | ~ r2_hidden(A_37,C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k2_zfmisc_1('#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,(
    ! [B_26,D_27,A_28,C_29] :
      ( r2_hidden(B_26,D_27)
      | ~ r2_hidden(k4_tarski(A_28,B_26),k2_zfmisc_1(C_29,D_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_55,plain,(
    ! [B_26,A_28] :
      ( r2_hidden(B_26,'#skF_2')
      | ~ r2_hidden(k4_tarski(A_28,B_26),k2_zfmisc_1('#skF_3','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_52])).

tff(c_87,plain,(
    ! [B_38,A_37] :
      ( r2_hidden(B_38,'#skF_2')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(A_37,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_67,c_55])).

tff(c_92,plain,(
    ! [A_37] : ~ r2_hidden(A_37,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_104,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(k4_tarski(A_42,B_43),k2_zfmisc_1('#skF_3','#skF_3'))
      | ~ r2_hidden(B_43,'#skF_2')
      | ~ r2_hidden(A_42,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_67])).

tff(c_16,plain,(
    ! [B_9,D_11,A_8,C_10] :
      ( r2_hidden(B_9,D_11)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_113,plain,(
    ! [B_43,A_42] :
      ( r2_hidden(B_43,'#skF_3')
      | ~ r2_hidden(B_43,'#skF_2')
      | ~ r2_hidden(A_42,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_104,c_16])).

tff(c_123,plain,(
    ! [B_43,A_42] :
      ( ~ r2_hidden(B_43,'#skF_2')
      | ~ r2_hidden(A_42,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_113])).

tff(c_148,plain,(
    ! [A_46] : ~ r2_hidden(A_46,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_159,plain,(
    ! [B_47] : r1_tarski('#skF_2',B_47) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_93,plain,(
    ! [A_41] : ~ r2_hidden(A_41,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_128,plain,(
    ! [B_44] : r1_tarski('#skF_3',B_44) ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_131,plain,(
    ! [B_44] :
      ( B_44 = '#skF_3'
      | ~ r1_tarski(B_44,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_128,c_8])).

tff(c_163,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_159,c_131])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_163])).

tff(c_173,plain,(
    ! [B_48] : ~ r2_hidden(B_48,'#skF_2') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_184,plain,(
    ! [B_49] : r1_tarski('#skF_2',B_49) ),
    inference(resolution,[status(thm)],[c_6,c_173])).

tff(c_188,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_184,c_131])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_188])).

tff(c_196,plain,(
    ! [B_50] :
      ( r2_hidden(B_50,'#skF_2')
      | ~ r2_hidden(B_50,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_225,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,'#skF_2')
      | ~ r2_hidden('#skF_1'(A_53,'#skF_2'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_196,c_4])).

tff(c_235,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_225])).

tff(c_237,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_8])).

tff(c_240,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_237])).

tff(c_205,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(k4_tarski(A_51,B_52),k2_zfmisc_1('#skF_3','#skF_3'))
      | ~ r2_hidden(B_52,'#skF_2')
      | ~ r2_hidden(A_51,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_67])).

tff(c_222,plain,(
    ! [B_52,A_51] :
      ( r2_hidden(B_52,'#skF_3')
      | ~ r2_hidden(B_52,'#skF_2')
      | ~ r2_hidden(A_51,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_205,c_16])).

tff(c_258,plain,(
    ! [A_56] : ~ r2_hidden(A_56,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_268,plain,(
    ! [B_2] : r1_tarski('#skF_2',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_258])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_240])).

tff(c_292,plain,(
    ! [B_60] :
      ( r2_hidden(B_60,'#skF_3')
      | ~ r2_hidden(B_60,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_307,plain,(
    ! [B_61] :
      ( r2_hidden('#skF_1'('#skF_2',B_61),'#skF_3')
      | r1_tarski('#skF_2',B_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_292])).

tff(c_317,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_307,c_4])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_240,c_317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:48:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.26  
% 2.02/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.26  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.02/1.26  
% 2.02/1.26  %Foreground sorts:
% 2.02/1.26  
% 2.02/1.26  
% 2.02/1.26  %Background operators:
% 2.02/1.26  
% 2.02/1.26  
% 2.02/1.26  %Foreground operators:
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.26  
% 2.02/1.28  tff(f_49, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, A) = k2_zfmisc_1(B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_zfmisc_1)).
% 2.02/1.28  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.02/1.28  tff(f_44, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.02/1.28  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.02/1.28  tff(c_20, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.02/1.28  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.28  tff(c_67, plain, (![A_37, B_38, C_39, D_40]: (r2_hidden(k4_tarski(A_37, B_38), k2_zfmisc_1(C_39, D_40)) | ~r2_hidden(B_38, D_40) | ~r2_hidden(A_37, C_39))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.28  tff(c_22, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k2_zfmisc_1('#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.02/1.28  tff(c_52, plain, (![B_26, D_27, A_28, C_29]: (r2_hidden(B_26, D_27) | ~r2_hidden(k4_tarski(A_28, B_26), k2_zfmisc_1(C_29, D_27)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.28  tff(c_55, plain, (![B_26, A_28]: (r2_hidden(B_26, '#skF_2') | ~r2_hidden(k4_tarski(A_28, B_26), k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_22, c_52])).
% 2.02/1.28  tff(c_87, plain, (![B_38, A_37]: (r2_hidden(B_38, '#skF_2') | ~r2_hidden(B_38, '#skF_3') | ~r2_hidden(A_37, '#skF_3'))), inference(resolution, [status(thm)], [c_67, c_55])).
% 2.02/1.28  tff(c_92, plain, (![A_37]: (~r2_hidden(A_37, '#skF_3'))), inference(splitLeft, [status(thm)], [c_87])).
% 2.02/1.28  tff(c_104, plain, (![A_42, B_43]: (r2_hidden(k4_tarski(A_42, B_43), k2_zfmisc_1('#skF_3', '#skF_3')) | ~r2_hidden(B_43, '#skF_2') | ~r2_hidden(A_42, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_67])).
% 2.02/1.28  tff(c_16, plain, (![B_9, D_11, A_8, C_10]: (r2_hidden(B_9, D_11) | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.28  tff(c_113, plain, (![B_43, A_42]: (r2_hidden(B_43, '#skF_3') | ~r2_hidden(B_43, '#skF_2') | ~r2_hidden(A_42, '#skF_2'))), inference(resolution, [status(thm)], [c_104, c_16])).
% 2.02/1.28  tff(c_123, plain, (![B_43, A_42]: (~r2_hidden(B_43, '#skF_2') | ~r2_hidden(A_42, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_92, c_113])).
% 2.02/1.28  tff(c_148, plain, (![A_46]: (~r2_hidden(A_46, '#skF_2'))), inference(splitLeft, [status(thm)], [c_123])).
% 2.02/1.28  tff(c_159, plain, (![B_47]: (r1_tarski('#skF_2', B_47))), inference(resolution, [status(thm)], [c_6, c_148])).
% 2.02/1.28  tff(c_93, plain, (![A_41]: (~r2_hidden(A_41, '#skF_3'))), inference(splitLeft, [status(thm)], [c_87])).
% 2.02/1.28  tff(c_128, plain, (![B_44]: (r1_tarski('#skF_3', B_44))), inference(resolution, [status(thm)], [c_6, c_93])).
% 2.02/1.28  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.02/1.28  tff(c_131, plain, (![B_44]: (B_44='#skF_3' | ~r1_tarski(B_44, '#skF_3'))), inference(resolution, [status(thm)], [c_128, c_8])).
% 2.02/1.28  tff(c_163, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_159, c_131])).
% 2.02/1.28  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_163])).
% 2.02/1.28  tff(c_173, plain, (![B_48]: (~r2_hidden(B_48, '#skF_2'))), inference(splitRight, [status(thm)], [c_123])).
% 2.02/1.28  tff(c_184, plain, (![B_49]: (r1_tarski('#skF_2', B_49))), inference(resolution, [status(thm)], [c_6, c_173])).
% 2.02/1.28  tff(c_188, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_184, c_131])).
% 2.02/1.28  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_188])).
% 2.02/1.28  tff(c_196, plain, (![B_50]: (r2_hidden(B_50, '#skF_2') | ~r2_hidden(B_50, '#skF_3'))), inference(splitRight, [status(thm)], [c_87])).
% 2.02/1.28  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.28  tff(c_225, plain, (![A_53]: (r1_tarski(A_53, '#skF_2') | ~r2_hidden('#skF_1'(A_53, '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_196, c_4])).
% 2.02/1.28  tff(c_235, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_225])).
% 2.02/1.28  tff(c_237, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_235, c_8])).
% 2.02/1.28  tff(c_240, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_20, c_237])).
% 2.02/1.28  tff(c_205, plain, (![A_51, B_52]: (r2_hidden(k4_tarski(A_51, B_52), k2_zfmisc_1('#skF_3', '#skF_3')) | ~r2_hidden(B_52, '#skF_2') | ~r2_hidden(A_51, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_67])).
% 2.02/1.28  tff(c_222, plain, (![B_52, A_51]: (r2_hidden(B_52, '#skF_3') | ~r2_hidden(B_52, '#skF_2') | ~r2_hidden(A_51, '#skF_2'))), inference(resolution, [status(thm)], [c_205, c_16])).
% 2.02/1.28  tff(c_258, plain, (![A_56]: (~r2_hidden(A_56, '#skF_2'))), inference(splitLeft, [status(thm)], [c_222])).
% 2.02/1.28  tff(c_268, plain, (![B_2]: (r1_tarski('#skF_2', B_2))), inference(resolution, [status(thm)], [c_6, c_258])).
% 2.02/1.28  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_240])).
% 2.02/1.28  tff(c_292, plain, (![B_60]: (r2_hidden(B_60, '#skF_3') | ~r2_hidden(B_60, '#skF_2'))), inference(splitRight, [status(thm)], [c_222])).
% 2.02/1.28  tff(c_307, plain, (![B_61]: (r2_hidden('#skF_1'('#skF_2', B_61), '#skF_3') | r1_tarski('#skF_2', B_61))), inference(resolution, [status(thm)], [c_6, c_292])).
% 2.02/1.28  tff(c_317, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_307, c_4])).
% 2.02/1.28  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_240, c_317])).
% 2.02/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.28  
% 2.02/1.28  Inference rules
% 2.02/1.28  ----------------------
% 2.02/1.28  #Ref     : 0
% 2.02/1.28  #Sup     : 57
% 2.02/1.28  #Fact    : 0
% 2.02/1.28  #Define  : 0
% 2.02/1.28  #Split   : 3
% 2.02/1.28  #Chain   : 0
% 2.02/1.28  #Close   : 0
% 2.02/1.28  
% 2.02/1.28  Ordering : KBO
% 2.02/1.28  
% 2.02/1.28  Simplification rules
% 2.02/1.28  ----------------------
% 2.02/1.28  #Subsume      : 9
% 2.02/1.28  #Demod        : 6
% 2.02/1.28  #Tautology    : 16
% 2.02/1.28  #SimpNegUnit  : 13
% 2.02/1.28  #BackRed      : 9
% 2.02/1.28  
% 2.02/1.28  #Partial instantiations: 0
% 2.02/1.28  #Strategies tried      : 1
% 2.02/1.28  
% 2.02/1.28  Timing (in seconds)
% 2.02/1.28  ----------------------
% 2.02/1.28  Preprocessing        : 0.29
% 2.02/1.28  Parsing              : 0.15
% 2.02/1.28  CNF conversion       : 0.02
% 2.02/1.28  Main loop            : 0.21
% 2.02/1.28  Inferencing          : 0.08
% 2.02/1.28  Reduction            : 0.05
% 2.02/1.28  Demodulation         : 0.03
% 2.02/1.28  BG Simplification    : 0.02
% 2.02/1.28  Subsumption          : 0.05
% 2.02/1.28  Abstraction          : 0.01
% 2.02/1.28  MUC search           : 0.00
% 2.02/1.28  Cooper               : 0.00
% 2.02/1.28  Total                : 0.53
% 2.02/1.28  Index Insertion      : 0.00
% 2.02/1.28  Index Deletion       : 0.00
% 2.02/1.28  Index Matching       : 0.00
% 2.02/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
