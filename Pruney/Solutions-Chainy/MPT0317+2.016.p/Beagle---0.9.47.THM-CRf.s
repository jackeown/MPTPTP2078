%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:02 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 129 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :    6
%              Number of atoms          :   85 ( 223 expanded)
%              Number of equality atoms :   25 (  82 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_24,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_73,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_123,plain,(
    ! [A_35,C_36,B_37,D_38] :
      ( r2_hidden(A_35,C_36)
      | ~ r2_hidden(k4_tarski(A_35,B_37),k2_zfmisc_1(C_36,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_126,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_73,c_123])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_126])).

tff(c_132,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_146,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_32])).

tff(c_54,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,k1_tarski(B_22)) = A_21
      | r2_hidden(B_22,A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [B_12] : k4_xboole_0(k1_tarski(B_12),k1_tarski(B_12)) != k1_tarski(B_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_70,plain,(
    ! [B_22] : r2_hidden(B_22,k1_tarski(B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_14])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10))
      | ~ r2_hidden(B_8,D_10)
      | ~ r2_hidden(A_7,C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_131,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_198,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_28])).

tff(c_199,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_198])).

tff(c_202,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_199])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_70,c_202])).

tff(c_208,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_207,plain,
    ( '#skF_6' != '#skF_8'
    | '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_209,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_278,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_294,plain,(
    ! [B_77,D_78,A_79,C_80] :
      ( r2_hidden(B_77,D_78)
      | ~ r2_hidden(k4_tarski(A_79,B_77),k2_zfmisc_1(C_80,D_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_298,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_278,c_294])).

tff(c_244,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(k1_tarski(A_66),k1_tarski(B_67)) = k1_tarski(A_66)
      | B_67 = A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( ~ r2_hidden(B_14,A_13)
      | k4_xboole_0(A_13,k1_tarski(B_14)) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_266,plain,(
    ! [B_67,A_66] :
      ( ~ r2_hidden(B_67,k1_tarski(A_66))
      | B_67 = A_66 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_18])).

tff(c_301,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_298,c_266])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_301])).

tff(c_307,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_322,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_32])).

tff(c_223,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,k1_tarski(B_62)) = A_61
      | r2_hidden(B_62,A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_235,plain,(
    ! [B_62] : r2_hidden(B_62,k1_tarski(B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_14])).

tff(c_306,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_341,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_28])).

tff(c_342,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_341])).

tff(c_345,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_342])).

tff(c_349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_235,c_345])).

tff(c_351,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_26,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_371,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_351,c_26])).

tff(c_372,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(A_99,k1_tarski(B_100)) = A_99
      | r2_hidden(B_100,A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_384,plain,(
    ! [B_100] : r2_hidden(B_100,k1_tarski(B_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_14])).

tff(c_350,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_22,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_450,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_351,c_350,c_22])).

tff(c_453,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_450])).

tff(c_457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_384,c_453])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.25  
% 2.09/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.25  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.09/1.25  
% 2.09/1.25  %Foreground sorts:
% 2.09/1.25  
% 2.09/1.25  
% 2.09/1.25  %Background operators:
% 2.09/1.25  
% 2.09/1.25  
% 2.09/1.25  %Foreground operators:
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.09/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.09/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.25  tff('#skF_8', type, '#skF_8': $i).
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.25  
% 2.09/1.26  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.09/1.26  tff(f_37, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.09/1.26  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.09/1.26  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.09/1.26  tff(c_24, plain, ('#skF_2'='#skF_4' | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.26  tff(c_42, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_24])).
% 2.09/1.26  tff(c_30, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.26  tff(c_73, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_30])).
% 2.09/1.26  tff(c_123, plain, (![A_35, C_36, B_37, D_38]: (r2_hidden(A_35, C_36) | ~r2_hidden(k4_tarski(A_35, B_37), k2_zfmisc_1(C_36, D_38)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.26  tff(c_126, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_73, c_123])).
% 2.09/1.26  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_126])).
% 2.09/1.26  tff(c_132, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_30])).
% 2.09/1.26  tff(c_32, plain, (r2_hidden('#skF_1', '#skF_3') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.26  tff(c_146, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_132, c_32])).
% 2.09/1.26  tff(c_54, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k1_tarski(B_22))=A_21 | r2_hidden(B_22, A_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.26  tff(c_14, plain, (![B_12]: (k4_xboole_0(k1_tarski(B_12), k1_tarski(B_12))!=k1_tarski(B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.09/1.26  tff(c_70, plain, (![B_22]: (r2_hidden(B_22, k1_tarski(B_22)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_14])).
% 2.09/1.26  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)) | ~r2_hidden(B_8, D_10) | ~r2_hidden(A_7, C_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.26  tff(c_131, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.09/1.26  tff(c_28, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.26  tff(c_198, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_28])).
% 2.09/1.26  tff(c_199, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_132, c_198])).
% 2.09/1.26  tff(c_202, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_199])).
% 2.09/1.26  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_70, c_202])).
% 2.09/1.26  tff(c_208, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_24])).
% 2.09/1.26  tff(c_207, plain, ('#skF_6'!='#skF_8' | '#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 2.09/1.26  tff(c_209, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_207])).
% 2.09/1.26  tff(c_278, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_30])).
% 2.09/1.26  tff(c_294, plain, (![B_77, D_78, A_79, C_80]: (r2_hidden(B_77, D_78) | ~r2_hidden(k4_tarski(A_79, B_77), k2_zfmisc_1(C_80, D_78)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.26  tff(c_298, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_278, c_294])).
% 2.09/1.26  tff(c_244, plain, (![A_66, B_67]: (k4_xboole_0(k1_tarski(A_66), k1_tarski(B_67))=k1_tarski(A_66) | B_67=A_66)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.09/1.26  tff(c_18, plain, (![B_14, A_13]: (~r2_hidden(B_14, A_13) | k4_xboole_0(A_13, k1_tarski(B_14))!=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.26  tff(c_266, plain, (![B_67, A_66]: (~r2_hidden(B_67, k1_tarski(A_66)) | B_67=A_66)), inference(superposition, [status(thm), theory('equality')], [c_244, c_18])).
% 2.09/1.26  tff(c_301, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_298, c_266])).
% 2.09/1.26  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_301])).
% 2.09/1.26  tff(c_307, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_30])).
% 2.09/1.26  tff(c_322, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_307, c_32])).
% 2.09/1.26  tff(c_223, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k1_tarski(B_62))=A_61 | r2_hidden(B_62, A_61))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.26  tff(c_235, plain, (![B_62]: (r2_hidden(B_62, k1_tarski(B_62)))), inference(superposition, [status(thm), theory('equality')], [c_223, c_14])).
% 2.09/1.26  tff(c_306, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.09/1.26  tff(c_341, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_28])).
% 2.09/1.26  tff(c_342, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_307, c_341])).
% 2.09/1.26  tff(c_345, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_342])).
% 2.09/1.26  tff(c_349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_322, c_235, c_345])).
% 2.09/1.26  tff(c_351, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_207])).
% 2.09/1.26  tff(c_26, plain, (r2_hidden('#skF_1', '#skF_3') | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.26  tff(c_371, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_351, c_26])).
% 2.09/1.26  tff(c_372, plain, (![A_99, B_100]: (k4_xboole_0(A_99, k1_tarski(B_100))=A_99 | r2_hidden(B_100, A_99))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.26  tff(c_384, plain, (![B_100]: (r2_hidden(B_100, k1_tarski(B_100)))), inference(superposition, [status(thm), theory('equality')], [c_372, c_14])).
% 2.09/1.26  tff(c_350, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_207])).
% 2.09/1.26  tff(c_22, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.26  tff(c_450, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_351, c_350, c_22])).
% 2.09/1.26  tff(c_453, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_450])).
% 2.09/1.26  tff(c_457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_371, c_384, c_453])).
% 2.09/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.26  
% 2.09/1.26  Inference rules
% 2.09/1.26  ----------------------
% 2.09/1.26  #Ref     : 0
% 2.09/1.26  #Sup     : 82
% 2.09/1.26  #Fact    : 0
% 2.09/1.26  #Define  : 0
% 2.09/1.26  #Split   : 5
% 2.09/1.26  #Chain   : 0
% 2.09/1.26  #Close   : 0
% 2.09/1.26  
% 2.09/1.26  Ordering : KBO
% 2.09/1.26  
% 2.09/1.26  Simplification rules
% 2.09/1.26  ----------------------
% 2.09/1.26  #Subsume      : 5
% 2.09/1.26  #Demod        : 23
% 2.09/1.26  #Tautology    : 68
% 2.09/1.26  #SimpNegUnit  : 6
% 2.09/1.26  #BackRed      : 0
% 2.09/1.26  
% 2.09/1.26  #Partial instantiations: 0
% 2.09/1.26  #Strategies tried      : 1
% 2.09/1.26  
% 2.09/1.26  Timing (in seconds)
% 2.09/1.26  ----------------------
% 2.09/1.27  Preprocessing        : 0.28
% 2.09/1.27  Parsing              : 0.15
% 2.09/1.27  CNF conversion       : 0.02
% 2.09/1.27  Main loop            : 0.21
% 2.09/1.27  Inferencing          : 0.09
% 2.09/1.27  Reduction            : 0.06
% 2.09/1.27  Demodulation         : 0.04
% 2.09/1.27  BG Simplification    : 0.01
% 2.09/1.27  Subsumption          : 0.03
% 2.09/1.27  Abstraction          : 0.01
% 2.09/1.27  MUC search           : 0.00
% 2.09/1.27  Cooper               : 0.00
% 2.09/1.27  Total                : 0.53
% 2.09/1.27  Index Insertion      : 0.00
% 2.09/1.27  Index Deletion       : 0.00
% 2.09/1.27  Index Matching       : 0.00
% 2.09/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
