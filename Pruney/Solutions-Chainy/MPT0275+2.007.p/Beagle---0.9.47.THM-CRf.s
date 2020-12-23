%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:17 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 126 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :    6
%              Number of atoms          :   87 ( 224 expanded)
%              Number of equality atoms :   22 (  63 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_52,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_162,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_60,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_373,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_433,plain,(
    ! [A_77,C_78,B_79] :
      ( r2_hidden(A_77,C_78)
      | ~ r1_tarski(k2_tarski(A_77,B_79),C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_862,plain,(
    ! [A_120,B_121,B_122] :
      ( r2_hidden(A_120,B_121)
      | k4_xboole_0(k2_tarski(A_120,B_122),B_121) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_433])).

tff(c_869,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_862])).

tff(c_885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_869])).

tff(c_886,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_887,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_910,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_887,c_58])).

tff(c_1667,plain,(
    ! [A_189,B_190,C_191] :
      ( r1_tarski(k2_tarski(A_189,B_190),C_191)
      | ~ r2_hidden(B_190,C_191)
      | ~ r2_hidden(A_189,C_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = k1_xboole_0
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7121,plain,(
    ! [A_418,B_419,C_420] :
      ( k4_xboole_0(k2_tarski(A_418,B_419),C_420) = k1_xboole_0
      | ~ r2_hidden(B_419,C_420)
      | ~ r2_hidden(A_418,C_420) ) ),
    inference(resolution,[status(thm)],[c_1667,c_20])).

tff(c_56,plain,
    ( k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0
    | k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_981,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_887,c_56])).

tff(c_7211,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7121,c_981])).

tff(c_7326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_910,c_7211])).

tff(c_7328,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_7327,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_7370,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_7327])).

tff(c_7367,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_7607,plain,(
    ! [B_449,C_450,A_451] :
      ( r2_hidden(B_449,C_450)
      | ~ r1_tarski(k2_tarski(A_451,B_449),C_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8148,plain,(
    ! [B_492,B_493,A_494] :
      ( r2_hidden(B_492,B_493)
      | k4_xboole_0(k2_tarski(A_494,B_492),B_493) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_7607])).

tff(c_8159,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_7367,c_8148])).

tff(c_8171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7370,c_8159])).

tff(c_8173,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_7327])).

tff(c_54,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8184,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7328,c_8173,c_54])).

tff(c_8172,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_7327])).

tff(c_9173,plain,(
    ! [A_582,B_583,C_584] :
      ( r1_tarski(k2_tarski(A_582,B_583),C_584)
      | ~ r2_hidden(B_583,C_584)
      | ~ r2_hidden(A_582,C_584) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_13955,plain,(
    ! [A_762,B_763,C_764] :
      ( k4_xboole_0(k2_tarski(A_762,B_763),C_764) = k1_xboole_0
      | ~ r2_hidden(B_763,C_764)
      | ~ r2_hidden(A_762,C_764) ) ),
    inference(resolution,[status(thm)],[c_9173,c_20])).

tff(c_50,plain,
    ( k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8381,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7328,c_8173,c_50])).

tff(c_14039,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13955,c_8381])).

tff(c_14157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8184,c_8172,c_14039])).

tff(c_14159,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_14162,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_14164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14159,c_14162])).

tff(c_14165,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_14158,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_14945,plain,(
    ! [A_837,B_838,C_839] :
      ( r1_tarski(k2_tarski(A_837,B_838),C_839)
      | ~ r2_hidden(B_838,C_839)
      | ~ r2_hidden(A_837,C_839) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20196,plain,(
    ! [A_1061,B_1062,C_1063] :
      ( k4_xboole_0(k2_tarski(A_1061,B_1062),C_1063) = k1_xboole_0
      | ~ r2_hidden(B_1062,C_1063)
      | ~ r2_hidden(A_1061,C_1063) ) ),
    inference(resolution,[status(thm)],[c_14945,c_20])).

tff(c_14373,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_14159,c_56])).

tff(c_20286,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_20196,c_14373])).

tff(c_20398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14165,c_14158,c_20286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n005.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 14:59:02 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.11/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.91/2.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.90  
% 7.91/2.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.90  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 7.91/2.90  
% 7.91/2.90  %Foreground sorts:
% 7.91/2.90  
% 7.91/2.90  
% 7.91/2.90  %Background operators:
% 7.91/2.90  
% 7.91/2.90  
% 7.91/2.90  %Foreground operators:
% 7.91/2.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.91/2.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.91/2.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.91/2.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.91/2.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.91/2.90  tff('#skF_7', type, '#skF_7': $i).
% 7.91/2.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.91/2.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.91/2.90  tff('#skF_5', type, '#skF_5': $i).
% 7.91/2.90  tff('#skF_6', type, '#skF_6': $i).
% 7.91/2.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.91/2.90  tff('#skF_3', type, '#skF_3': $i).
% 7.91/2.90  tff('#skF_8', type, '#skF_8': $i).
% 7.91/2.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.91/2.90  tff('#skF_4', type, '#skF_4': $i).
% 7.91/2.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.91/2.90  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.91/2.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.91/2.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.91/2.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.91/2.90  
% 7.91/2.91  tff(f_112, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 7.91/2.91  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 7.91/2.91  tff(f_95, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 7.91/2.91  tff(c_52, plain, (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.91/2.91  tff(c_162, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_52])).
% 7.91/2.91  tff(c_60, plain, (r2_hidden('#skF_3', '#skF_5') | k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.91/2.91  tff(c_373, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 7.91/2.91  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | k4_xboole_0(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.91/2.91  tff(c_433, plain, (![A_77, C_78, B_79]: (r2_hidden(A_77, C_78) | ~r1_tarski(k2_tarski(A_77, B_79), C_78))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.91/2.91  tff(c_862, plain, (![A_120, B_121, B_122]: (r2_hidden(A_120, B_121) | k4_xboole_0(k2_tarski(A_120, B_122), B_121)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_433])).
% 7.91/2.91  tff(c_869, plain, (r2_hidden('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_373, c_862])).
% 7.91/2.91  tff(c_885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_869])).
% 7.91/2.91  tff(c_886, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 7.91/2.91  tff(c_887, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 7.91/2.91  tff(c_58, plain, (r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.91/2.91  tff(c_910, plain, (r2_hidden('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_887, c_58])).
% 7.91/2.91  tff(c_1667, plain, (![A_189, B_190, C_191]: (r1_tarski(k2_tarski(A_189, B_190), C_191) | ~r2_hidden(B_190, C_191) | ~r2_hidden(A_189, C_191))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.91/2.91  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=k1_xboole_0 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.91/2.91  tff(c_7121, plain, (![A_418, B_419, C_420]: (k4_xboole_0(k2_tarski(A_418, B_419), C_420)=k1_xboole_0 | ~r2_hidden(B_419, C_420) | ~r2_hidden(A_418, C_420))), inference(resolution, [status(thm)], [c_1667, c_20])).
% 7.91/2.91  tff(c_56, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0 | k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.91/2.91  tff(c_981, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_887, c_56])).
% 7.91/2.91  tff(c_7211, plain, (~r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7121, c_981])).
% 7.91/2.91  tff(c_7326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_886, c_910, c_7211])).
% 7.91/2.91  tff(c_7328, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_52])).
% 7.91/2.91  tff(c_7327, plain, (~r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 7.91/2.91  tff(c_7370, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_7327])).
% 7.91/2.91  tff(c_7367, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 7.91/2.91  tff(c_7607, plain, (![B_449, C_450, A_451]: (r2_hidden(B_449, C_450) | ~r1_tarski(k2_tarski(A_451, B_449), C_450))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.91/2.91  tff(c_8148, plain, (![B_492, B_493, A_494]: (r2_hidden(B_492, B_493) | k4_xboole_0(k2_tarski(A_494, B_492), B_493)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_7607])).
% 7.91/2.91  tff(c_8159, plain, (r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_7367, c_8148])).
% 7.91/2.91  tff(c_8171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7370, c_8159])).
% 7.91/2.91  tff(c_8173, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_7327])).
% 7.91/2.91  tff(c_54, plain, (r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.91/2.91  tff(c_8184, plain, (r2_hidden('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7328, c_8173, c_54])).
% 7.91/2.91  tff(c_8172, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_7327])).
% 7.91/2.91  tff(c_9173, plain, (![A_582, B_583, C_584]: (r1_tarski(k2_tarski(A_582, B_583), C_584) | ~r2_hidden(B_583, C_584) | ~r2_hidden(A_582, C_584))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.91/2.91  tff(c_13955, plain, (![A_762, B_763, C_764]: (k4_xboole_0(k2_tarski(A_762, B_763), C_764)=k1_xboole_0 | ~r2_hidden(B_763, C_764) | ~r2_hidden(A_762, C_764))), inference(resolution, [status(thm)], [c_9173, c_20])).
% 7.91/2.91  tff(c_50, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.91/2.91  tff(c_8381, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7328, c_8173, c_50])).
% 7.91/2.91  tff(c_14039, plain, (~r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13955, c_8381])).
% 7.91/2.91  tff(c_14157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8184, c_8172, c_14039])).
% 7.91/2.91  tff(c_14159, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 7.91/2.91  tff(c_14162, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 7.91/2.91  tff(c_14164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14159, c_14162])).
% 7.91/2.91  tff(c_14165, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 7.91/2.91  tff(c_14158, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 7.91/2.91  tff(c_14945, plain, (![A_837, B_838, C_839]: (r1_tarski(k2_tarski(A_837, B_838), C_839) | ~r2_hidden(B_838, C_839) | ~r2_hidden(A_837, C_839))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.91/2.91  tff(c_20196, plain, (![A_1061, B_1062, C_1063]: (k4_xboole_0(k2_tarski(A_1061, B_1062), C_1063)=k1_xboole_0 | ~r2_hidden(B_1062, C_1063) | ~r2_hidden(A_1061, C_1063))), inference(resolution, [status(thm)], [c_14945, c_20])).
% 7.91/2.91  tff(c_14373, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_14159, c_56])).
% 7.91/2.91  tff(c_20286, plain, (~r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_20196, c_14373])).
% 7.91/2.91  tff(c_20398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14165, c_14158, c_20286])).
% 7.91/2.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.91  
% 7.91/2.91  Inference rules
% 7.91/2.91  ----------------------
% 7.91/2.91  #Ref     : 0
% 7.91/2.91  #Sup     : 4636
% 7.91/2.91  #Fact    : 0
% 7.91/2.91  #Define  : 0
% 7.91/2.91  #Split   : 8
% 7.91/2.91  #Chain   : 0
% 7.91/2.91  #Close   : 0
% 7.91/2.91  
% 7.91/2.91  Ordering : KBO
% 7.91/2.91  
% 7.91/2.91  Simplification rules
% 7.91/2.91  ----------------------
% 7.91/2.91  #Subsume      : 545
% 7.91/2.91  #Demod        : 3256
% 7.91/2.91  #Tautology    : 2809
% 7.91/2.91  #SimpNegUnit  : 116
% 7.91/2.91  #BackRed      : 23
% 7.91/2.91  
% 7.91/2.91  #Partial instantiations: 0
% 7.91/2.91  #Strategies tried      : 1
% 7.91/2.91  
% 7.91/2.91  Timing (in seconds)
% 7.91/2.91  ----------------------
% 7.91/2.91  Preprocessing        : 0.33
% 7.91/2.91  Parsing              : 0.18
% 7.91/2.91  CNF conversion       : 0.02
% 7.91/2.91  Main loop            : 1.95
% 7.91/2.91  Inferencing          : 0.59
% 7.91/2.91  Reduction            : 0.85
% 7.91/2.92  Demodulation         : 0.69
% 7.91/2.92  BG Simplification    : 0.06
% 7.91/2.92  Subsumption          : 0.33
% 7.91/2.92  Abstraction          : 0.07
% 7.91/2.92  MUC search           : 0.00
% 7.91/2.92  Cooper               : 0.00
% 7.91/2.92  Total                : 2.31
% 7.91/2.92  Index Insertion      : 0.00
% 7.91/2.92  Index Deletion       : 0.00
% 7.91/2.92  Index Matching       : 0.00
% 7.91/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
