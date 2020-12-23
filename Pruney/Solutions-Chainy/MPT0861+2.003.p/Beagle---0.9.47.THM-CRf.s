%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:01 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 113 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 215 expanded)
%              Number of equality atoms :   22 (  69 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(c_58,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_70,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_134,plain,(
    ! [A_57,C_58,B_59] :
      ( r2_hidden(k2_mcart_1(A_57),C_58)
      | ~ r2_hidden(A_57,k2_zfmisc_1(B_59,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_137,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_54,c_134])).

tff(c_142,plain,(
    ! [A_63,B_64,C_65] :
      ( r2_hidden(A_63,k4_xboole_0(B_64,k1_tarski(C_65)))
      | C_65 = A_63
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_157,plain,(
    ! [A_66,C_67,B_68] :
      ( ~ r2_hidden(A_66,k1_tarski(C_67))
      | C_67 = A_66
      | ~ r2_hidden(A_66,B_68) ) ),
    inference(resolution,[status(thm)],[c_142,c_4])).

tff(c_159,plain,(
    ! [B_68] :
      ( k2_mcart_1('#skF_3') = '#skF_6'
      | ~ r2_hidden(k2_mcart_1('#skF_3'),B_68) ) ),
    inference(resolution,[status(thm)],[c_137,c_157])).

tff(c_164,plain,(
    ! [B_68] : ~ r2_hidden(k2_mcart_1('#skF_3'),B_68) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_159])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_137])).

tff(c_170,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_176,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_56])).

tff(c_169,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_231,plain,(
    ! [A_94,B_95,C_96] :
      ( r2_hidden(k1_mcart_1(A_94),B_95)
      | ~ r2_hidden(A_94,k2_zfmisc_1(B_95,C_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_234,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_231])).

tff(c_344,plain,(
    ! [A_129,B_130,C_131] :
      ( k4_xboole_0(k2_tarski(A_129,B_130),C_131) = k2_tarski(A_129,B_130)
      | r2_hidden(B_130,C_131)
      | r2_hidden(A_129,C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_40,plain,(
    ! [C_20,B_19] : ~ r2_hidden(C_20,k4_xboole_0(B_19,k1_tarski(C_20))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_417,plain,(
    ! [C_136,A_137,B_138] :
      ( ~ r2_hidden(C_136,k2_tarski(A_137,B_138))
      | r2_hidden(B_138,k1_tarski(C_136))
      | r2_hidden(A_137,k1_tarski(C_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_40])).

tff(c_426,plain,
    ( r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3')))
    | r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_234,c_417])).

tff(c_431,plain,(
    r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_317,plain,(
    ! [A_121,B_122,C_123] :
      ( r2_hidden(A_121,k4_xboole_0(B_122,k1_tarski(C_123)))
      | C_123 = A_121
      | ~ r2_hidden(A_121,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_329,plain,(
    ! [A_121,C_123,B_122] :
      ( ~ r2_hidden(A_121,k1_tarski(C_123))
      | C_123 = A_121
      | ~ r2_hidden(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_317,c_4])).

tff(c_437,plain,(
    ! [B_122] :
      ( k1_mcart_1('#skF_3') = '#skF_4'
      | ~ r2_hidden('#skF_4',B_122) ) ),
    inference(resolution,[status(thm)],[c_431,c_329])).

tff(c_442,plain,(
    ! [B_122] : ~ r2_hidden('#skF_4',B_122) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_437])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_442,c_431])).

tff(c_445,plain,(
    r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_452,plain,(
    ! [B_122] :
      ( k1_mcart_1('#skF_3') = '#skF_5'
      | ~ r2_hidden('#skF_5',B_122) ) ),
    inference(resolution,[status(thm)],[c_445,c_329])).

tff(c_457,plain,(
    ! [B_122] : ~ r2_hidden('#skF_5',B_122) ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_452])).

tff(c_459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_457,c_445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:57:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.34  
% 2.51/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.34  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.51/1.34  
% 2.51/1.34  %Foreground sorts:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Background operators:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Foreground operators:
% 2.51/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.34  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.51/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.34  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.51/1.34  
% 2.51/1.35  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 2.51/1.35  tff(f_74, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.51/1.35  tff(f_60, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.51/1.35  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.51/1.35  tff(f_68, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.51/1.35  tff(c_58, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.51/1.35  tff(c_70, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_58])).
% 2.51/1.35  tff(c_54, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.51/1.35  tff(c_134, plain, (![A_57, C_58, B_59]: (r2_hidden(k2_mcart_1(A_57), C_58) | ~r2_hidden(A_57, k2_zfmisc_1(B_59, C_58)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.51/1.35  tff(c_137, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_134])).
% 2.51/1.35  tff(c_142, plain, (![A_63, B_64, C_65]: (r2_hidden(A_63, k4_xboole_0(B_64, k1_tarski(C_65))) | C_65=A_63 | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.35  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.35  tff(c_157, plain, (![A_66, C_67, B_68]: (~r2_hidden(A_66, k1_tarski(C_67)) | C_67=A_66 | ~r2_hidden(A_66, B_68))), inference(resolution, [status(thm)], [c_142, c_4])).
% 2.51/1.35  tff(c_159, plain, (![B_68]: (k2_mcart_1('#skF_3')='#skF_6' | ~r2_hidden(k2_mcart_1('#skF_3'), B_68))), inference(resolution, [status(thm)], [c_137, c_157])).
% 2.51/1.35  tff(c_164, plain, (![B_68]: (~r2_hidden(k2_mcart_1('#skF_3'), B_68))), inference(negUnitSimplification, [status(thm)], [c_70, c_159])).
% 2.51/1.35  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_137])).
% 2.51/1.35  tff(c_170, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_58])).
% 2.51/1.35  tff(c_56, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.51/1.35  tff(c_176, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_56])).
% 2.51/1.35  tff(c_169, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_58])).
% 2.51/1.35  tff(c_231, plain, (![A_94, B_95, C_96]: (r2_hidden(k1_mcart_1(A_94), B_95) | ~r2_hidden(A_94, k2_zfmisc_1(B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.51/1.35  tff(c_234, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_231])).
% 2.51/1.35  tff(c_344, plain, (![A_129, B_130, C_131]: (k4_xboole_0(k2_tarski(A_129, B_130), C_131)=k2_tarski(A_129, B_130) | r2_hidden(B_130, C_131) | r2_hidden(A_129, C_131))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.51/1.35  tff(c_40, plain, (![C_20, B_19]: (~r2_hidden(C_20, k4_xboole_0(B_19, k1_tarski(C_20))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.35  tff(c_417, plain, (![C_136, A_137, B_138]: (~r2_hidden(C_136, k2_tarski(A_137, B_138)) | r2_hidden(B_138, k1_tarski(C_136)) | r2_hidden(A_137, k1_tarski(C_136)))), inference(superposition, [status(thm), theory('equality')], [c_344, c_40])).
% 2.51/1.35  tff(c_426, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3'))) | r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_234, c_417])).
% 2.51/1.35  tff(c_431, plain, (r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_426])).
% 2.51/1.35  tff(c_317, plain, (![A_121, B_122, C_123]: (r2_hidden(A_121, k4_xboole_0(B_122, k1_tarski(C_123))) | C_123=A_121 | ~r2_hidden(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.35  tff(c_329, plain, (![A_121, C_123, B_122]: (~r2_hidden(A_121, k1_tarski(C_123)) | C_123=A_121 | ~r2_hidden(A_121, B_122))), inference(resolution, [status(thm)], [c_317, c_4])).
% 2.51/1.35  tff(c_437, plain, (![B_122]: (k1_mcart_1('#skF_3')='#skF_4' | ~r2_hidden('#skF_4', B_122))), inference(resolution, [status(thm)], [c_431, c_329])).
% 2.51/1.35  tff(c_442, plain, (![B_122]: (~r2_hidden('#skF_4', B_122))), inference(negUnitSimplification, [status(thm)], [c_169, c_437])).
% 2.51/1.35  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_442, c_431])).
% 2.51/1.35  tff(c_445, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitRight, [status(thm)], [c_426])).
% 2.51/1.35  tff(c_452, plain, (![B_122]: (k1_mcart_1('#skF_3')='#skF_5' | ~r2_hidden('#skF_5', B_122))), inference(resolution, [status(thm)], [c_445, c_329])).
% 2.51/1.35  tff(c_457, plain, (![B_122]: (~r2_hidden('#skF_5', B_122))), inference(negUnitSimplification, [status(thm)], [c_176, c_452])).
% 2.51/1.35  tff(c_459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_457, c_445])).
% 2.51/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.35  
% 2.51/1.35  Inference rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Ref     : 0
% 2.51/1.35  #Sup     : 85
% 2.51/1.35  #Fact    : 0
% 2.51/1.35  #Define  : 0
% 2.51/1.35  #Split   : 2
% 2.51/1.35  #Chain   : 0
% 2.51/1.35  #Close   : 0
% 2.51/1.35  
% 2.51/1.35  Ordering : KBO
% 2.51/1.35  
% 2.51/1.35  Simplification rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Subsume      : 6
% 2.51/1.35  #Demod        : 19
% 2.51/1.35  #Tautology    : 50
% 2.51/1.36  #SimpNegUnit  : 6
% 2.51/1.36  #BackRed      : 3
% 2.51/1.36  
% 2.51/1.36  #Partial instantiations: 0
% 2.51/1.36  #Strategies tried      : 1
% 2.51/1.36  
% 2.51/1.36  Timing (in seconds)
% 2.51/1.36  ----------------------
% 2.51/1.36  Preprocessing        : 0.32
% 2.51/1.36  Parsing              : 0.16
% 2.51/1.36  CNF conversion       : 0.02
% 2.51/1.36  Main loop            : 0.27
% 2.51/1.36  Inferencing          : 0.10
% 2.51/1.36  Reduction            : 0.08
% 2.51/1.36  Demodulation         : 0.06
% 2.51/1.36  BG Simplification    : 0.02
% 2.51/1.36  Subsumption          : 0.05
% 2.51/1.36  Abstraction          : 0.02
% 2.51/1.36  MUC search           : 0.00
% 2.51/1.36  Cooper               : 0.00
% 2.51/1.36  Total                : 0.63
% 2.51/1.36  Index Insertion      : 0.00
% 2.51/1.36  Index Deletion       : 0.00
% 2.51/1.36  Index Matching       : 0.00
% 2.51/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
