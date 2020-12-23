%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:09 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   52 (  83 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 134 expanded)
%              Number of equality atoms :   12 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_3 > #skF_2 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_50,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_118,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_135,plain,(
    ! [A_55] : r1_tarski(A_55,A_55) ),
    inference(resolution,[status(thm)],[c_118,c_8])).

tff(c_58,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_307,plain,(
    ! [C_82,D_83,A_84] :
      ( r2_hidden(C_82,D_83)
      | ~ r2_hidden(D_83,A_84)
      | ~ r2_hidden(C_82,k1_setfam_1(A_84))
      | k1_xboole_0 = A_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_325,plain,(
    ! [C_82] :
      ( r2_hidden(C_82,'#skF_9')
      | ~ r2_hidden(C_82,k1_setfam_1('#skF_10'))
      | k1_xboole_0 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_60,c_307])).

tff(c_326,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_30,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = A_44
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_86,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(resolution,[status(thm)],[c_30,c_78])).

tff(c_165,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_175,plain,(
    ! [B_69] :
      ( r2_hidden('#skF_9',B_69)
      | ~ r1_tarski('#skF_10',B_69) ) ),
    inference(resolution,[status(thm)],[c_60,c_165])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( ~ r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,k4_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_243,plain,(
    ! [B_74,A_75] :
      ( ~ r2_hidden('#skF_9',B_74)
      | ~ r1_tarski('#skF_10',k4_xboole_0(A_75,B_74)) ) ),
    inference(resolution,[status(thm)],[c_175,c_14])).

tff(c_249,plain,(
    ! [A_16] :
      ( ~ r2_hidden('#skF_9',k1_xboole_0)
      | ~ r1_tarski('#skF_10',A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_243])).

tff(c_251,plain,(
    ~ r2_hidden('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_328,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_251])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_328])).

tff(c_342,plain,(
    ! [C_85] :
      ( r2_hidden(C_85,'#skF_9')
      | ~ r2_hidden(C_85,k1_setfam_1('#skF_10')) ) ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_1424,plain,(
    ! [B_148] :
      ( r2_hidden('#skF_2'(k1_setfam_1('#skF_10'),B_148),'#skF_9')
      | r1_tarski(k1_setfam_1('#skF_10'),B_148) ) ),
    inference(resolution,[status(thm)],[c_10,c_342])).

tff(c_1432,plain,(
    r1_tarski(k1_setfam_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_1424,c_8])).

tff(c_1443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_58,c_1432])).

tff(c_1446,plain,(
    ! [A_149] : ~ r1_tarski('#skF_10',A_149) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_1456,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_135,c_1446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:25:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.61  
% 3.47/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.61  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_3 > #skF_2 > #skF_7
% 3.47/1.61  
% 3.47/1.61  %Foreground sorts:
% 3.47/1.61  
% 3.47/1.61  
% 3.47/1.61  %Background operators:
% 3.47/1.61  
% 3.47/1.61  
% 3.47/1.61  %Foreground operators:
% 3.47/1.61  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.47/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.47/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.47/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.47/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.61  tff('#skF_10', type, '#skF_10': $i).
% 3.47/1.61  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.47/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.47/1.61  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.47/1.61  tff('#skF_9', type, '#skF_9': $i).
% 3.47/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.47/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.47/1.61  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.47/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.47/1.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.47/1.61  
% 3.47/1.62  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.47/1.62  tff(f_78, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 3.47/1.62  tff(f_73, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 3.47/1.62  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.47/1.62  tff(f_54, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.47/1.62  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.47/1.62  tff(c_118, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.62  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.62  tff(c_135, plain, (![A_55]: (r1_tarski(A_55, A_55))), inference(resolution, [status(thm)], [c_118, c_8])).
% 3.47/1.62  tff(c_58, plain, (~r1_tarski(k1_setfam_1('#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.47/1.62  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.62  tff(c_60, plain, (r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.47/1.62  tff(c_307, plain, (![C_82, D_83, A_84]: (r2_hidden(C_82, D_83) | ~r2_hidden(D_83, A_84) | ~r2_hidden(C_82, k1_setfam_1(A_84)) | k1_xboole_0=A_84)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.47/1.62  tff(c_325, plain, (![C_82]: (r2_hidden(C_82, '#skF_9') | ~r2_hidden(C_82, k1_setfam_1('#skF_10')) | k1_xboole_0='#skF_10')), inference(resolution, [status(thm)], [c_60, c_307])).
% 3.47/1.62  tff(c_326, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_325])).
% 3.47/1.62  tff(c_30, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.47/1.62  tff(c_78, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=A_44 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.47/1.62  tff(c_86, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(resolution, [status(thm)], [c_30, c_78])).
% 3.47/1.62  tff(c_165, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.62  tff(c_175, plain, (![B_69]: (r2_hidden('#skF_9', B_69) | ~r1_tarski('#skF_10', B_69))), inference(resolution, [status(thm)], [c_60, c_165])).
% 3.47/1.62  tff(c_14, plain, (![D_15, B_11, A_10]: (~r2_hidden(D_15, B_11) | ~r2_hidden(D_15, k4_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.47/1.62  tff(c_243, plain, (![B_74, A_75]: (~r2_hidden('#skF_9', B_74) | ~r1_tarski('#skF_10', k4_xboole_0(A_75, B_74)))), inference(resolution, [status(thm)], [c_175, c_14])).
% 3.47/1.62  tff(c_249, plain, (![A_16]: (~r2_hidden('#skF_9', k1_xboole_0) | ~r1_tarski('#skF_10', A_16))), inference(superposition, [status(thm), theory('equality')], [c_86, c_243])).
% 3.47/1.62  tff(c_251, plain, (~r2_hidden('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_249])).
% 3.47/1.62  tff(c_328, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_251])).
% 3.47/1.62  tff(c_339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_328])).
% 3.47/1.62  tff(c_342, plain, (![C_85]: (r2_hidden(C_85, '#skF_9') | ~r2_hidden(C_85, k1_setfam_1('#skF_10')))), inference(splitRight, [status(thm)], [c_325])).
% 3.47/1.62  tff(c_1424, plain, (![B_148]: (r2_hidden('#skF_2'(k1_setfam_1('#skF_10'), B_148), '#skF_9') | r1_tarski(k1_setfam_1('#skF_10'), B_148))), inference(resolution, [status(thm)], [c_10, c_342])).
% 3.47/1.62  tff(c_1432, plain, (r1_tarski(k1_setfam_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_1424, c_8])).
% 3.47/1.62  tff(c_1443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_58, c_1432])).
% 3.47/1.62  tff(c_1446, plain, (![A_149]: (~r1_tarski('#skF_10', A_149))), inference(splitRight, [status(thm)], [c_249])).
% 3.47/1.62  tff(c_1456, plain, $false, inference(resolution, [status(thm)], [c_135, c_1446])).
% 3.47/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.62  
% 3.47/1.62  Inference rules
% 3.47/1.62  ----------------------
% 3.47/1.62  #Ref     : 0
% 3.47/1.62  #Sup     : 302
% 3.47/1.62  #Fact    : 0
% 3.47/1.62  #Define  : 0
% 3.47/1.62  #Split   : 9
% 3.47/1.62  #Chain   : 0
% 3.47/1.62  #Close   : 0
% 3.47/1.62  
% 3.47/1.62  Ordering : KBO
% 3.47/1.62  
% 3.47/1.62  Simplification rules
% 3.47/1.62  ----------------------
% 3.47/1.62  #Subsume      : 87
% 3.47/1.62  #Demod        : 128
% 3.47/1.62  #Tautology    : 85
% 3.47/1.62  #SimpNegUnit  : 20
% 3.47/1.62  #BackRed      : 41
% 3.47/1.62  
% 3.47/1.62  #Partial instantiations: 0
% 3.47/1.62  #Strategies tried      : 1
% 3.47/1.62  
% 3.47/1.62  Timing (in seconds)
% 3.47/1.62  ----------------------
% 3.47/1.63  Preprocessing        : 0.31
% 3.47/1.63  Parsing              : 0.16
% 3.47/1.63  CNF conversion       : 0.03
% 3.47/1.63  Main loop            : 0.54
% 3.47/1.63  Inferencing          : 0.19
% 3.47/1.63  Reduction            : 0.15
% 3.47/1.63  Demodulation         : 0.10
% 3.47/1.63  BG Simplification    : 0.03
% 3.47/1.63  Subsumption          : 0.14
% 3.47/1.63  Abstraction          : 0.02
% 3.47/1.63  MUC search           : 0.00
% 3.47/1.63  Cooper               : 0.00
% 3.47/1.63  Total                : 0.89
% 3.47/1.63  Index Insertion      : 0.00
% 3.47/1.63  Index Deletion       : 0.00
% 3.47/1.63  Index Matching       : 0.00
% 3.47/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
