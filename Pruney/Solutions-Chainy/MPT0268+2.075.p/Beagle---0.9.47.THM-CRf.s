%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:44 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   51 (  66 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  97 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_30,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_45,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k1_tarski(A_13),B_14) = k1_tarski(A_13)
      | r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_xboole_0(k4_xboole_0(A_8,B_9),B_9) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_152,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,B_47)
      | ~ r2_hidden(C_48,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_162,plain,(
    ! [C_49,B_50,A_51] :
      ( ~ r2_hidden(C_49,B_50)
      | ~ r2_hidden(C_49,k4_xboole_0(A_51,B_50)) ) ),
    inference(resolution,[status(thm)],[c_10,c_152])).

tff(c_276,plain,(
    ! [A_71,A_72,B_73] :
      ( ~ r2_hidden('#skF_1'(A_71,k4_xboole_0(A_72,B_73)),B_73)
      | r1_xboole_0(A_71,k4_xboole_0(A_72,B_73)) ) ),
    inference(resolution,[status(thm)],[c_4,c_162])).

tff(c_294,plain,(
    ! [A_74,A_75] : r1_xboole_0(A_74,k4_xboole_0(A_75,A_74)) ),
    inference(resolution,[status(thm)],[c_6,c_276])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_309,plain,(
    ! [A_76,A_77] : k4_xboole_0(A_76,k4_xboole_0(A_77,A_76)) = A_76 ),
    inference(resolution,[status(thm)],[c_294,c_12])).

tff(c_510,plain,(
    ! [B_93,A_94] :
      ( k4_xboole_0(B_93,k1_tarski(A_94)) = B_93
      | r2_hidden(A_94,B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_309])).

tff(c_28,plain,
    ( k4_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_2'
    | r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_565,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_58])).

tff(c_593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_565])).

tff(c_594,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_595,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_32,plain,
    ( k4_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_2'
    | k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_673,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_32])).

tff(c_24,plain,(
    ! [C_17,B_16] : ~ r2_hidden(C_17,k4_xboole_0(B_16,k1_tarski(C_17))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_680,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_24])).

tff(c_689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_680])).

tff(c_690,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_691,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_715,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_34])).

tff(c_719,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_24])).

tff(c_727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:49:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.33  
% 2.30/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.33  %$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.30/1.33  
% 2.30/1.33  %Foreground sorts:
% 2.30/1.33  
% 2.30/1.33  
% 2.30/1.33  %Background operators:
% 2.30/1.33  
% 2.30/1.33  
% 2.30/1.33  %Foreground operators:
% 2.30/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.30/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.30/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.30/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.30/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.30/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.30/1.33  
% 2.30/1.34  tff(f_71, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.30/1.34  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.30/1.34  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.30/1.34  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.30/1.34  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.30/1.34  tff(f_65, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.30/1.34  tff(c_30, plain, (~r2_hidden('#skF_3', '#skF_2') | r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.30/1.34  tff(c_45, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 2.30/1.34  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(k1_tarski(A_13), B_14)=k1_tarski(A_13) | r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.30/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.30/1.34  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.30/1.34  tff(c_10, plain, (![A_8, B_9]: (r1_xboole_0(k4_xboole_0(A_8, B_9), B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.30/1.34  tff(c_152, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, B_47) | ~r2_hidden(C_48, A_46))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.30/1.34  tff(c_162, plain, (![C_49, B_50, A_51]: (~r2_hidden(C_49, B_50) | ~r2_hidden(C_49, k4_xboole_0(A_51, B_50)))), inference(resolution, [status(thm)], [c_10, c_152])).
% 2.30/1.34  tff(c_276, plain, (![A_71, A_72, B_73]: (~r2_hidden('#skF_1'(A_71, k4_xboole_0(A_72, B_73)), B_73) | r1_xboole_0(A_71, k4_xboole_0(A_72, B_73)))), inference(resolution, [status(thm)], [c_4, c_162])).
% 2.30/1.34  tff(c_294, plain, (![A_74, A_75]: (r1_xboole_0(A_74, k4_xboole_0(A_75, A_74)))), inference(resolution, [status(thm)], [c_6, c_276])).
% 2.30/1.34  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.30/1.34  tff(c_309, plain, (![A_76, A_77]: (k4_xboole_0(A_76, k4_xboole_0(A_77, A_76))=A_76)), inference(resolution, [status(thm)], [c_294, c_12])).
% 2.30/1.34  tff(c_510, plain, (![B_93, A_94]: (k4_xboole_0(B_93, k1_tarski(A_94))=B_93 | r2_hidden(A_94, B_93))), inference(superposition, [status(thm), theory('equality')], [c_20, c_309])).
% 2.30/1.34  tff(c_28, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_2' | r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.30/1.34  tff(c_58, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_28])).
% 2.30/1.34  tff(c_565, plain, (r2_hidden('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_510, c_58])).
% 2.30/1.34  tff(c_593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_565])).
% 2.30/1.34  tff(c_594, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 2.30/1.34  tff(c_595, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 2.30/1.34  tff(c_32, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_2' | k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.30/1.34  tff(c_673, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_595, c_32])).
% 2.30/1.34  tff(c_24, plain, (![C_17, B_16]: (~r2_hidden(C_17, k4_xboole_0(B_16, k1_tarski(C_17))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.30/1.34  tff(c_680, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_673, c_24])).
% 2.30/1.34  tff(c_689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_594, c_680])).
% 2.30/1.34  tff(c_690, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 2.30/1.34  tff(c_691, plain, (r2_hidden('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 2.30/1.34  tff(c_34, plain, (~r2_hidden('#skF_3', '#skF_2') | k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.30/1.34  tff(c_715, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_691, c_34])).
% 2.30/1.34  tff(c_719, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_715, c_24])).
% 2.30/1.34  tff(c_727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_690, c_719])).
% 2.30/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.34  
% 2.30/1.34  Inference rules
% 2.30/1.34  ----------------------
% 2.30/1.34  #Ref     : 0
% 2.30/1.34  #Sup     : 168
% 2.30/1.34  #Fact    : 0
% 2.30/1.34  #Define  : 0
% 2.30/1.34  #Split   : 2
% 2.30/1.34  #Chain   : 0
% 2.30/1.34  #Close   : 0
% 2.30/1.34  
% 2.30/1.34  Ordering : KBO
% 2.30/1.34  
% 2.30/1.34  Simplification rules
% 2.30/1.34  ----------------------
% 2.30/1.34  #Subsume      : 27
% 2.30/1.34  #Demod        : 38
% 2.30/1.34  #Tautology    : 61
% 2.30/1.34  #SimpNegUnit  : 4
% 2.30/1.34  #BackRed      : 0
% 2.30/1.34  
% 2.30/1.34  #Partial instantiations: 0
% 2.30/1.34  #Strategies tried      : 1
% 2.30/1.34  
% 2.30/1.34  Timing (in seconds)
% 2.30/1.34  ----------------------
% 2.30/1.35  Preprocessing        : 0.29
% 2.30/1.35  Parsing              : 0.16
% 2.30/1.35  CNF conversion       : 0.02
% 2.30/1.35  Main loop            : 0.29
% 2.30/1.35  Inferencing          : 0.11
% 2.30/1.35  Reduction            : 0.07
% 2.30/1.35  Demodulation         : 0.05
% 2.30/1.35  BG Simplification    : 0.02
% 2.30/1.35  Subsumption          : 0.06
% 2.30/1.35  Abstraction          : 0.02
% 2.30/1.35  MUC search           : 0.00
% 2.30/1.35  Cooper               : 0.00
% 2.30/1.35  Total                : 0.61
% 2.30/1.35  Index Insertion      : 0.00
% 2.30/1.35  Index Deletion       : 0.00
% 2.30/1.35  Index Matching       : 0.00
% 2.30/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
