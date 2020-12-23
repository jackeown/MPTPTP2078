%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:47 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 132 expanded)
%              Number of leaves         :   26 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 249 expanded)
%              Number of equality atoms :   17 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_60,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_231,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( r2_hidden(k4_tarski(A_92,B_93),k2_zfmisc_1(C_94,D_95))
      | ~ r2_hidden(B_93,D_95)
      | ~ r2_hidden(A_92,C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_66,plain,(
    k2_zfmisc_1('#skF_9','#skF_8') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_194,plain,(
    ! [B_81,D_82,A_83,C_84] :
      ( r2_hidden(B_81,D_82)
      | ~ r2_hidden(k4_tarski(A_83,B_81),k2_zfmisc_1(C_84,D_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_197,plain,(
    ! [B_81,A_83] :
      ( r2_hidden(B_81,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_83,B_81),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_194])).

tff(c_257,plain,(
    ! [B_93,A_92] :
      ( r2_hidden(B_93,'#skF_8')
      | ~ r2_hidden(B_93,'#skF_9')
      | ~ r2_hidden(A_92,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_231,c_197])).

tff(c_266,plain,(
    ! [A_96] : ~ r2_hidden(A_96,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_272,plain,(
    ! [B_97] : r1_tarski('#skF_8',B_97) ),
    inference(resolution,[status(thm)],[c_6,c_266])).

tff(c_123,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_1'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_111,plain,(
    ! [C_58,B_59] : ~ r2_hidden(C_58,k4_xboole_0(B_59,k1_tarski(C_58))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_114,plain,(
    ! [C_58] : ~ r2_hidden(C_58,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_111])).

tff(c_129,plain,(
    ! [B_65] : r1_tarski(k1_xboole_0,B_65) ),
    inference(resolution,[status(thm)],[c_123,c_114])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_132,plain,(
    ! [B_65] :
      ( k1_xboole_0 = B_65
      | ~ r1_tarski(B_65,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_129,c_8])).

tff(c_276,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_272,c_132])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_276])).

tff(c_304,plain,(
    ! [B_100] :
      ( r2_hidden(B_100,'#skF_8')
      | ~ r2_hidden(B_100,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_310,plain,(
    ! [B_101] :
      ( r2_hidden('#skF_1'('#skF_9',B_101),'#skF_8')
      | r1_tarski('#skF_9',B_101) ) ),
    inference(resolution,[status(thm)],[c_6,c_304])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_318,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_310,c_4])).

tff(c_320,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_318,c_8])).

tff(c_323,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_320])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_183,plain,(
    ! [A_77,C_78,B_79,D_80] :
      ( r2_hidden(A_77,C_78)
      | ~ r2_hidden(k4_tarski(A_77,B_79),k2_zfmisc_1(C_78,D_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_186,plain,(
    ! [A_77,B_79] :
      ( r2_hidden(A_77,'#skF_9')
      | ~ r2_hidden(k4_tarski(A_77,B_79),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_183])).

tff(c_258,plain,(
    ! [A_92,B_93] :
      ( r2_hidden(A_92,'#skF_9')
      | ~ r2_hidden(B_93,'#skF_9')
      | ~ r2_hidden(A_92,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_231,c_186])).

tff(c_359,plain,(
    ! [B_105] : ~ r2_hidden(B_105,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_372,plain,(
    ! [B_106] : r1_tarski('#skF_9',B_106) ),
    inference(resolution,[status(thm)],[c_6,c_359])).

tff(c_376,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_372,c_132])).

tff(c_382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_376])).

tff(c_384,plain,(
    ! [A_107] :
      ( r2_hidden(A_107,'#skF_9')
      | ~ r2_hidden(A_107,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_397,plain,(
    ! [A_108] :
      ( r1_tarski(A_108,'#skF_9')
      | ~ r2_hidden('#skF_1'(A_108,'#skF_9'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_384,c_4])).

tff(c_405,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_397])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_323,c_405])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.35  % Computer   : n019.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 12:02:52 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.19/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.29  
% 2.05/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.30  %$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 2.05/1.30  
% 2.05/1.30  %Foreground sorts:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Background operators:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Foreground operators:
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.05/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.05/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.05/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.05/1.30  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.05/1.30  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.05/1.30  tff('#skF_9', type, '#skF_9': $i).
% 2.05/1.30  tff('#skF_8', type, '#skF_8': $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.05/1.30  
% 2.05/1.31  tff(f_82, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.05/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.05/1.31  tff(f_60, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.05/1.31  tff(f_40, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.05/1.31  tff(f_73, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.05/1.31  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.05/1.31  tff(c_60, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.05/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.31  tff(c_64, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.05/1.31  tff(c_231, plain, (![A_92, B_93, C_94, D_95]: (r2_hidden(k4_tarski(A_92, B_93), k2_zfmisc_1(C_94, D_95)) | ~r2_hidden(B_93, D_95) | ~r2_hidden(A_92, C_94))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.05/1.31  tff(c_66, plain, (k2_zfmisc_1('#skF_9', '#skF_8')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.05/1.31  tff(c_194, plain, (![B_81, D_82, A_83, C_84]: (r2_hidden(B_81, D_82) | ~r2_hidden(k4_tarski(A_83, B_81), k2_zfmisc_1(C_84, D_82)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.05/1.31  tff(c_197, plain, (![B_81, A_83]: (r2_hidden(B_81, '#skF_8') | ~r2_hidden(k4_tarski(A_83, B_81), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_66, c_194])).
% 2.05/1.31  tff(c_257, plain, (![B_93, A_92]: (r2_hidden(B_93, '#skF_8') | ~r2_hidden(B_93, '#skF_9') | ~r2_hidden(A_92, '#skF_8'))), inference(resolution, [status(thm)], [c_231, c_197])).
% 2.05/1.31  tff(c_266, plain, (![A_96]: (~r2_hidden(A_96, '#skF_8'))), inference(splitLeft, [status(thm)], [c_257])).
% 2.05/1.31  tff(c_272, plain, (![B_97]: (r1_tarski('#skF_8', B_97))), inference(resolution, [status(thm)], [c_6, c_266])).
% 2.05/1.31  tff(c_123, plain, (![A_63, B_64]: (r2_hidden('#skF_1'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.31  tff(c_14, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.05/1.31  tff(c_111, plain, (![C_58, B_59]: (~r2_hidden(C_58, k4_xboole_0(B_59, k1_tarski(C_58))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.05/1.31  tff(c_114, plain, (![C_58]: (~r2_hidden(C_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_111])).
% 2.05/1.31  tff(c_129, plain, (![B_65]: (r1_tarski(k1_xboole_0, B_65))), inference(resolution, [status(thm)], [c_123, c_114])).
% 2.05/1.31  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.05/1.31  tff(c_132, plain, (![B_65]: (k1_xboole_0=B_65 | ~r1_tarski(B_65, k1_xboole_0))), inference(resolution, [status(thm)], [c_129, c_8])).
% 2.05/1.31  tff(c_276, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_272, c_132])).
% 2.05/1.31  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_276])).
% 2.05/1.31  tff(c_304, plain, (![B_100]: (r2_hidden(B_100, '#skF_8') | ~r2_hidden(B_100, '#skF_9'))), inference(splitRight, [status(thm)], [c_257])).
% 2.05/1.31  tff(c_310, plain, (![B_101]: (r2_hidden('#skF_1'('#skF_9', B_101), '#skF_8') | r1_tarski('#skF_9', B_101))), inference(resolution, [status(thm)], [c_6, c_304])).
% 2.05/1.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.31  tff(c_318, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_310, c_4])).
% 2.05/1.31  tff(c_320, plain, ('#skF_9'='#skF_8' | ~r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_318, c_8])).
% 2.05/1.31  tff(c_323, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_60, c_320])).
% 2.05/1.31  tff(c_62, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.05/1.31  tff(c_183, plain, (![A_77, C_78, B_79, D_80]: (r2_hidden(A_77, C_78) | ~r2_hidden(k4_tarski(A_77, B_79), k2_zfmisc_1(C_78, D_80)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.05/1.31  tff(c_186, plain, (![A_77, B_79]: (r2_hidden(A_77, '#skF_9') | ~r2_hidden(k4_tarski(A_77, B_79), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_66, c_183])).
% 2.05/1.31  tff(c_258, plain, (![A_92, B_93]: (r2_hidden(A_92, '#skF_9') | ~r2_hidden(B_93, '#skF_9') | ~r2_hidden(A_92, '#skF_8'))), inference(resolution, [status(thm)], [c_231, c_186])).
% 2.05/1.31  tff(c_359, plain, (![B_105]: (~r2_hidden(B_105, '#skF_9'))), inference(splitLeft, [status(thm)], [c_258])).
% 2.05/1.31  tff(c_372, plain, (![B_106]: (r1_tarski('#skF_9', B_106))), inference(resolution, [status(thm)], [c_6, c_359])).
% 2.05/1.31  tff(c_376, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_372, c_132])).
% 2.05/1.31  tff(c_382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_376])).
% 2.05/1.31  tff(c_384, plain, (![A_107]: (r2_hidden(A_107, '#skF_9') | ~r2_hidden(A_107, '#skF_8'))), inference(splitRight, [status(thm)], [c_258])).
% 2.05/1.31  tff(c_397, plain, (![A_108]: (r1_tarski(A_108, '#skF_9') | ~r2_hidden('#skF_1'(A_108, '#skF_9'), '#skF_8'))), inference(resolution, [status(thm)], [c_384, c_4])).
% 2.05/1.31  tff(c_405, plain, (r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_6, c_397])).
% 2.05/1.31  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_323, c_323, c_405])).
% 2.05/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.31  
% 2.05/1.31  Inference rules
% 2.05/1.31  ----------------------
% 2.05/1.31  #Ref     : 0
% 2.05/1.31  #Sup     : 72
% 2.05/1.31  #Fact    : 0
% 2.05/1.31  #Define  : 0
% 2.05/1.31  #Split   : 2
% 2.05/1.31  #Chain   : 0
% 2.05/1.31  #Close   : 0
% 2.05/1.31  
% 2.05/1.31  Ordering : KBO
% 2.05/1.31  
% 2.05/1.31  Simplification rules
% 2.05/1.31  ----------------------
% 2.05/1.31  #Subsume      : 15
% 2.05/1.31  #Demod        : 10
% 2.05/1.31  #Tautology    : 29
% 2.05/1.31  #SimpNegUnit  : 14
% 2.05/1.31  #BackRed      : 2
% 2.05/1.31  
% 2.05/1.31  #Partial instantiations: 0
% 2.05/1.31  #Strategies tried      : 1
% 2.05/1.31  
% 2.05/1.31  Timing (in seconds)
% 2.05/1.31  ----------------------
% 2.05/1.31  Preprocessing        : 0.31
% 2.05/1.31  Parsing              : 0.15
% 2.05/1.31  CNF conversion       : 0.03
% 2.05/1.31  Main loop            : 0.21
% 2.05/1.31  Inferencing          : 0.07
% 2.05/1.31  Reduction            : 0.06
% 2.05/1.31  Demodulation         : 0.04
% 2.05/1.31  BG Simplification    : 0.02
% 2.05/1.31  Subsumption          : 0.05
% 2.05/1.31  Abstraction          : 0.01
% 2.05/1.31  MUC search           : 0.00
% 2.05/1.31  Cooper               : 0.00
% 2.05/1.31  Total                : 0.55
% 2.05/1.31  Index Insertion      : 0.00
% 2.05/1.31  Index Deletion       : 0.00
% 2.05/1.31  Index Matching       : 0.00
% 2.05/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
