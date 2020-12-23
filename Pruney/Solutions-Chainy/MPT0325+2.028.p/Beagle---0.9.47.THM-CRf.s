%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:24 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 203 expanded)
%              Number of leaves         :   19 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 448 expanded)
%              Number of equality atoms :   18 (  52 expanded)
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

tff(f_61,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_28,plain,
    ( ~ r1_tarski('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_135,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( r2_hidden(k4_tarski(A_50,B_51),k2_zfmisc_1(C_52,D_53))
      | ~ r2_hidden(B_51,D_53)
      | ~ r2_hidden(A_50,C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_274,plain,(
    ! [B_73,B_74,C_72,D_75,A_71] :
      ( r2_hidden(k4_tarski(A_71,B_73),B_74)
      | ~ r1_tarski(k2_zfmisc_1(C_72,D_75),B_74)
      | ~ r2_hidden(B_73,D_75)
      | ~ r2_hidden(A_71,C_72) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_290,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(k4_tarski(A_76,B_77),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_77,'#skF_3')
      | ~ r2_hidden(A_76,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_274])).

tff(c_20,plain,(
    ! [A_9,C_11,B_10,D_12] :
      ( r2_hidden(A_9,C_11)
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(C_11,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_299,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(A_76,'#skF_4')
      | ~ r2_hidden(B_77,'#skF_3')
      | ~ r2_hidden(A_76,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_290,c_20])).

tff(c_303,plain,(
    ! [B_78] : ~ r2_hidden(B_78,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_314,plain,(
    ! [B_79] : r1_tarski('#skF_3',B_79) ),
    inference(resolution,[status(thm)],[c_6,c_303])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59,plain,(
    ! [B_19,A_20] :
      ( B_19 = A_20
      | ~ r1_tarski(B_19,A_20)
      | ~ r1_tarski(A_20,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_59])).

tff(c_326,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_314,c_71])).

tff(c_24,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_333,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_326,c_24])).

tff(c_30,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_334,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_30])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_334])).

tff(c_406,plain,(
    ! [A_86] :
      ( r2_hidden(A_86,'#skF_4')
      | ~ r2_hidden(A_86,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_417,plain,(
    ! [B_87] :
      ( r2_hidden('#skF_1'('#skF_2',B_87),'#skF_4')
      | r1_tarski('#skF_2',B_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_406])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_423,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_417,c_4])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_58,c_423])).

tff(c_429,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_511,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( r2_hidden(k4_tarski(A_119,B_120),k2_zfmisc_1(C_121,D_122))
      | ~ r2_hidden(B_120,D_122)
      | ~ r2_hidden(A_119,C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_591,plain,(
    ! [C_136,A_133,B_132,D_134,B_135] :
      ( r2_hidden(k4_tarski(A_133,B_132),B_135)
      | ~ r1_tarski(k2_zfmisc_1(C_136,D_134),B_135)
      | ~ r2_hidden(B_132,D_134)
      | ~ r2_hidden(A_133,C_136) ) ),
    inference(resolution,[status(thm)],[c_511,c_2])).

tff(c_646,plain,(
    ! [A_147,B_148] :
      ( r2_hidden(k4_tarski(A_147,B_148),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_148,'#skF_3')
      | ~ r2_hidden(A_147,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_591])).

tff(c_18,plain,(
    ! [B_10,D_12,A_9,C_11] :
      ( r2_hidden(B_10,D_12)
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(C_11,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_662,plain,(
    ! [B_148,A_147] :
      ( r2_hidden(B_148,'#skF_5')
      | ~ r2_hidden(B_148,'#skF_3')
      | ~ r2_hidden(A_147,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_646,c_18])).

tff(c_729,plain,(
    ! [A_155] : ~ r2_hidden(A_155,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_662])).

tff(c_742,plain,(
    ! [B_156] : r1_tarski('#skF_2',B_156) ),
    inference(resolution,[status(thm)],[c_6,c_729])).

tff(c_431,plain,(
    ! [B_88,A_89] :
      ( B_88 = A_89
      | ~ r1_tarski(B_88,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_446,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_431])).

tff(c_749,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_742,c_446])).

tff(c_26,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_760,plain,(
    ! [B_14] : k2_zfmisc_1('#skF_2',B_14) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_749,c_26])).

tff(c_762,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_30])).

tff(c_827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_762])).

tff(c_829,plain,(
    ! [B_159] :
      ( r2_hidden(B_159,'#skF_5')
      | ~ r2_hidden(B_159,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_857,plain,(
    ! [A_164] :
      ( r1_tarski(A_164,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_164,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_829,c_4])).

tff(c_865,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_857])).

tff(c_870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_429,c_429,c_865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.39  
% 2.66/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.39  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.66/1.39  
% 2.66/1.39  %Foreground sorts:
% 2.66/1.39  
% 2.66/1.39  
% 2.66/1.39  %Background operators:
% 2.66/1.39  
% 2.66/1.39  
% 2.66/1.39  %Foreground operators:
% 2.66/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.66/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.66/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.66/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.39  
% 2.66/1.40  tff(f_61, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.66/1.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.66/1.40  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.66/1.40  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.66/1.40  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.66/1.40  tff(f_52, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.66/1.40  tff(c_28, plain, (~r1_tarski('#skF_3', '#skF_5') | ~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.40  tff(c_58, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_28])).
% 2.66/1.40  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.40  tff(c_32, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.40  tff(c_135, plain, (![A_50, B_51, C_52, D_53]: (r2_hidden(k4_tarski(A_50, B_51), k2_zfmisc_1(C_52, D_53)) | ~r2_hidden(B_51, D_53) | ~r2_hidden(A_50, C_52))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.40  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.40  tff(c_274, plain, (![B_73, B_74, C_72, D_75, A_71]: (r2_hidden(k4_tarski(A_71, B_73), B_74) | ~r1_tarski(k2_zfmisc_1(C_72, D_75), B_74) | ~r2_hidden(B_73, D_75) | ~r2_hidden(A_71, C_72))), inference(resolution, [status(thm)], [c_135, c_2])).
% 2.66/1.41  tff(c_290, plain, (![A_76, B_77]: (r2_hidden(k4_tarski(A_76, B_77), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_77, '#skF_3') | ~r2_hidden(A_76, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_274])).
% 2.66/1.41  tff(c_20, plain, (![A_9, C_11, B_10, D_12]: (r2_hidden(A_9, C_11) | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(C_11, D_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.41  tff(c_299, plain, (![A_76, B_77]: (r2_hidden(A_76, '#skF_4') | ~r2_hidden(B_77, '#skF_3') | ~r2_hidden(A_76, '#skF_2'))), inference(resolution, [status(thm)], [c_290, c_20])).
% 2.66/1.41  tff(c_303, plain, (![B_78]: (~r2_hidden(B_78, '#skF_3'))), inference(splitLeft, [status(thm)], [c_299])).
% 2.66/1.41  tff(c_314, plain, (![B_79]: (r1_tarski('#skF_3', B_79))), inference(resolution, [status(thm)], [c_6, c_303])).
% 2.66/1.41  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.66/1.41  tff(c_59, plain, (![B_19, A_20]: (B_19=A_20 | ~r1_tarski(B_19, A_20) | ~r1_tarski(A_20, B_19))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.66/1.41  tff(c_71, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_59])).
% 2.66/1.41  tff(c_326, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_314, c_71])).
% 2.66/1.41  tff(c_24, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.66/1.41  tff(c_333, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_326, c_24])).
% 2.66/1.41  tff(c_30, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.41  tff(c_334, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_30])).
% 2.66/1.41  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_333, c_334])).
% 2.66/1.41  tff(c_406, plain, (![A_86]: (r2_hidden(A_86, '#skF_4') | ~r2_hidden(A_86, '#skF_2'))), inference(splitRight, [status(thm)], [c_299])).
% 2.66/1.41  tff(c_417, plain, (![B_87]: (r2_hidden('#skF_1'('#skF_2', B_87), '#skF_4') | r1_tarski('#skF_2', B_87))), inference(resolution, [status(thm)], [c_6, c_406])).
% 2.66/1.41  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.41  tff(c_423, plain, (r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_417, c_4])).
% 2.66/1.41  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_58, c_423])).
% 2.66/1.41  tff(c_429, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_28])).
% 2.66/1.41  tff(c_511, plain, (![A_119, B_120, C_121, D_122]: (r2_hidden(k4_tarski(A_119, B_120), k2_zfmisc_1(C_121, D_122)) | ~r2_hidden(B_120, D_122) | ~r2_hidden(A_119, C_121))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.41  tff(c_591, plain, (![C_136, A_133, B_132, D_134, B_135]: (r2_hidden(k4_tarski(A_133, B_132), B_135) | ~r1_tarski(k2_zfmisc_1(C_136, D_134), B_135) | ~r2_hidden(B_132, D_134) | ~r2_hidden(A_133, C_136))), inference(resolution, [status(thm)], [c_511, c_2])).
% 2.66/1.41  tff(c_646, plain, (![A_147, B_148]: (r2_hidden(k4_tarski(A_147, B_148), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_148, '#skF_3') | ~r2_hidden(A_147, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_591])).
% 2.66/1.41  tff(c_18, plain, (![B_10, D_12, A_9, C_11]: (r2_hidden(B_10, D_12) | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(C_11, D_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.41  tff(c_662, plain, (![B_148, A_147]: (r2_hidden(B_148, '#skF_5') | ~r2_hidden(B_148, '#skF_3') | ~r2_hidden(A_147, '#skF_2'))), inference(resolution, [status(thm)], [c_646, c_18])).
% 2.66/1.41  tff(c_729, plain, (![A_155]: (~r2_hidden(A_155, '#skF_2'))), inference(splitLeft, [status(thm)], [c_662])).
% 2.66/1.41  tff(c_742, plain, (![B_156]: (r1_tarski('#skF_2', B_156))), inference(resolution, [status(thm)], [c_6, c_729])).
% 2.66/1.41  tff(c_431, plain, (![B_88, A_89]: (B_88=A_89 | ~r1_tarski(B_88, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.66/1.41  tff(c_446, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_431])).
% 2.66/1.41  tff(c_749, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_742, c_446])).
% 2.66/1.41  tff(c_26, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.66/1.41  tff(c_760, plain, (![B_14]: (k2_zfmisc_1('#skF_2', B_14)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_749, c_749, c_26])).
% 2.66/1.41  tff(c_762, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_749, c_30])).
% 2.66/1.41  tff(c_827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_760, c_762])).
% 2.66/1.41  tff(c_829, plain, (![B_159]: (r2_hidden(B_159, '#skF_5') | ~r2_hidden(B_159, '#skF_3'))), inference(splitRight, [status(thm)], [c_662])).
% 2.66/1.41  tff(c_857, plain, (![A_164]: (r1_tarski(A_164, '#skF_5') | ~r2_hidden('#skF_1'(A_164, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_829, c_4])).
% 2.66/1.41  tff(c_865, plain, (r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_857])).
% 2.66/1.41  tff(c_870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_429, c_429, c_865])).
% 2.66/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.41  
% 2.66/1.41  Inference rules
% 2.66/1.41  ----------------------
% 2.66/1.41  #Ref     : 0
% 2.66/1.41  #Sup     : 180
% 2.66/1.41  #Fact    : 0
% 2.66/1.41  #Define  : 0
% 2.66/1.41  #Split   : 10
% 2.66/1.41  #Chain   : 0
% 2.66/1.41  #Close   : 0
% 2.66/1.41  
% 2.66/1.41  Ordering : KBO
% 2.66/1.41  
% 2.66/1.41  Simplification rules
% 2.66/1.41  ----------------------
% 2.66/1.41  #Subsume      : 54
% 2.66/1.41  #Demod        : 100
% 2.66/1.41  #Tautology    : 69
% 2.66/1.41  #SimpNegUnit  : 16
% 2.66/1.41  #BackRed      : 37
% 2.66/1.41  
% 2.66/1.41  #Partial instantiations: 0
% 2.66/1.41  #Strategies tried      : 1
% 2.66/1.41  
% 2.66/1.41  Timing (in seconds)
% 2.66/1.41  ----------------------
% 2.66/1.41  Preprocessing        : 0.27
% 2.66/1.41  Parsing              : 0.15
% 2.66/1.41  CNF conversion       : 0.02
% 2.66/1.41  Main loop            : 0.35
% 2.66/1.41  Inferencing          : 0.13
% 2.66/1.41  Reduction            : 0.09
% 2.66/1.41  Demodulation         : 0.06
% 2.66/1.41  BG Simplification    : 0.02
% 2.66/1.41  Subsumption          : 0.08
% 2.66/1.41  Abstraction          : 0.01
% 2.66/1.41  MUC search           : 0.00
% 2.66/1.41  Cooper               : 0.00
% 2.66/1.41  Total                : 0.66
% 2.66/1.41  Index Insertion      : 0.00
% 2.66/1.41  Index Deletion       : 0.00
% 2.66/1.41  Index Matching       : 0.00
% 2.66/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
