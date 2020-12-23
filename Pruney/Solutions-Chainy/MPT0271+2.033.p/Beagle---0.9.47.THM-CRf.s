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
% DateTime   : Thu Dec  3 09:53:05 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 103 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 147 expanded)
%              Number of equality atoms :   26 (  59 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_52,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_83,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_56,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_125,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_157,plain,(
    ! [C_52,B_53,A_54] :
      ( r2_hidden(C_52,B_53)
      | ~ r2_hidden(C_52,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,(
    ! [C_55,B_56] :
      ( r2_hidden(C_55,B_56)
      | ~ r1_tarski(k1_tarski(C_55),B_56) ) ),
    inference(resolution,[status(thm)],[c_16,c_157])).

tff(c_212,plain,(
    ! [C_63,B_64] :
      ( r2_hidden(C_63,B_64)
      | k4_xboole_0(k1_tarski(C_63),B_64) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_170])).

tff(c_215,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_212])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_215])).

tff(c_225,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_242,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_54])).

tff(c_224,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_109,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,B_46),A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_355,plain,(
    ! [A_90,B_91] :
      ( '#skF_1'(k1_tarski(A_90),B_91) = A_90
      | r1_tarski(k1_tarski(A_90),B_91) ) ),
    inference(resolution,[status(thm)],[c_109,c_14])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_412,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(k1_tarski(A_104),B_105) = k1_xboole_0
      | '#skF_1'(k1_tarski(A_104),B_105) = A_104 ) ),
    inference(resolution,[status(thm)],[c_355,c_10])).

tff(c_438,plain,(
    '#skF_1'(k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_242])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_452,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_4])).

tff(c_462,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_452])).

tff(c_473,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_462,c_10])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_473])).

tff(c_483,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_xboole_0
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_484,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_484])).

tff(c_487,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_482,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_507,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_1'(A_114,B_115),A_114)
      | r1_tarski(A_114,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_683,plain,(
    ! [A_147,B_148] :
      ( '#skF_1'(k1_tarski(A_147),B_148) = A_147
      | r1_tarski(k1_tarski(A_147),B_148) ) ),
    inference(resolution,[status(thm)],[c_507,c_14])).

tff(c_762,plain,(
    ! [A_167,B_168] :
      ( k4_xboole_0(k1_tarski(A_167),B_168) = k1_xboole_0
      | '#skF_1'(k1_tarski(A_167),B_168) = A_167 ) ),
    inference(resolution,[status(thm)],[c_683,c_10])).

tff(c_786,plain,(
    '#skF_1'(k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_487])).

tff(c_798,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_4])).

tff(c_808,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_798])).

tff(c_821,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_808,c_10])).

tff(c_830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_487,c_821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 19:52:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.36  
% 2.57/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.36  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 2.57/1.36  
% 2.57/1.36  %Foreground sorts:
% 2.57/1.36  
% 2.57/1.36  
% 2.57/1.36  %Background operators:
% 2.57/1.36  
% 2.57/1.36  
% 2.57/1.36  %Foreground operators:
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.57/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.57/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.57/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.57/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.57/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.57/1.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.57/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.36  tff('#skF_9', type, '#skF_9': $i).
% 2.57/1.36  tff('#skF_8', type, '#skF_8': $i).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.57/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.57/1.36  
% 2.57/1.38  tff(f_65, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 2.57/1.38  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.57/1.38  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.57/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.57/1.38  tff(c_52, plain, (r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.57/1.38  tff(c_83, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_52])).
% 2.57/1.38  tff(c_56, plain, (r2_hidden('#skF_6', '#skF_7') | k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.57/1.38  tff(c_125, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 2.57/1.38  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.57/1.38  tff(c_16, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.57/1.38  tff(c_157, plain, (![C_52, B_53, A_54]: (r2_hidden(C_52, B_53) | ~r2_hidden(C_52, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.57/1.38  tff(c_170, plain, (![C_55, B_56]: (r2_hidden(C_55, B_56) | ~r1_tarski(k1_tarski(C_55), B_56))), inference(resolution, [status(thm)], [c_16, c_157])).
% 2.57/1.38  tff(c_212, plain, (![C_63, B_64]: (r2_hidden(C_63, B_64) | k4_xboole_0(k1_tarski(C_63), B_64)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_170])).
% 2.57/1.38  tff(c_215, plain, (r2_hidden('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_125, c_212])).
% 2.57/1.38  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_215])).
% 2.57/1.38  tff(c_225, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 2.57/1.38  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.57/1.38  tff(c_242, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_225, c_54])).
% 2.57/1.38  tff(c_224, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_56])).
% 2.57/1.38  tff(c_109, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, B_46), A_45) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.57/1.38  tff(c_14, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.57/1.38  tff(c_355, plain, (![A_90, B_91]: ('#skF_1'(k1_tarski(A_90), B_91)=A_90 | r1_tarski(k1_tarski(A_90), B_91))), inference(resolution, [status(thm)], [c_109, c_14])).
% 2.57/1.38  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.57/1.38  tff(c_412, plain, (![A_104, B_105]: (k4_xboole_0(k1_tarski(A_104), B_105)=k1_xboole_0 | '#skF_1'(k1_tarski(A_104), B_105)=A_104)), inference(resolution, [status(thm)], [c_355, c_10])).
% 2.57/1.38  tff(c_438, plain, ('#skF_1'(k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_412, c_242])).
% 2.57/1.38  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.57/1.38  tff(c_452, plain, (~r2_hidden('#skF_6', '#skF_7') | r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_438, c_4])).
% 2.57/1.38  tff(c_462, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_452])).
% 2.57/1.38  tff(c_473, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_462, c_10])).
% 2.57/1.38  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_242, c_473])).
% 2.57/1.38  tff(c_483, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_52])).
% 2.57/1.38  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_xboole_0 | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.57/1.38  tff(c_484, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_50])).
% 2.57/1.38  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_483, c_484])).
% 2.57/1.38  tff(c_487, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.57/1.38  tff(c_482, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 2.57/1.38  tff(c_507, plain, (![A_114, B_115]: (r2_hidden('#skF_1'(A_114, B_115), A_114) | r1_tarski(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.57/1.38  tff(c_683, plain, (![A_147, B_148]: ('#skF_1'(k1_tarski(A_147), B_148)=A_147 | r1_tarski(k1_tarski(A_147), B_148))), inference(resolution, [status(thm)], [c_507, c_14])).
% 2.57/1.38  tff(c_762, plain, (![A_167, B_168]: (k4_xboole_0(k1_tarski(A_167), B_168)=k1_xboole_0 | '#skF_1'(k1_tarski(A_167), B_168)=A_167)), inference(resolution, [status(thm)], [c_683, c_10])).
% 2.57/1.38  tff(c_786, plain, ('#skF_1'(k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_762, c_487])).
% 2.57/1.38  tff(c_798, plain, (~r2_hidden('#skF_6', '#skF_7') | r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_786, c_4])).
% 2.57/1.38  tff(c_808, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_482, c_798])).
% 2.57/1.38  tff(c_821, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_808, c_10])).
% 2.57/1.38  tff(c_830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_487, c_821])).
% 2.57/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.38  
% 2.57/1.38  Inference rules
% 2.57/1.38  ----------------------
% 2.57/1.38  #Ref     : 0
% 2.57/1.38  #Sup     : 168
% 2.57/1.38  #Fact    : 0
% 2.57/1.38  #Define  : 0
% 2.57/1.38  #Split   : 3
% 2.57/1.38  #Chain   : 0
% 2.57/1.38  #Close   : 0
% 2.57/1.38  
% 2.57/1.38  Ordering : KBO
% 2.57/1.38  
% 2.57/1.38  Simplification rules
% 2.57/1.38  ----------------------
% 2.57/1.38  #Subsume      : 24
% 2.57/1.38  #Demod        : 35
% 2.57/1.38  #Tautology    : 81
% 2.57/1.38  #SimpNegUnit  : 4
% 2.57/1.38  #BackRed      : 0
% 2.57/1.38  
% 2.57/1.38  #Partial instantiations: 0
% 2.57/1.38  #Strategies tried      : 1
% 2.57/1.38  
% 2.57/1.38  Timing (in seconds)
% 2.57/1.38  ----------------------
% 2.57/1.38  Preprocessing        : 0.31
% 2.57/1.38  Parsing              : 0.16
% 2.57/1.38  CNF conversion       : 0.02
% 2.57/1.38  Main loop            : 0.31
% 2.57/1.38  Inferencing          : 0.12
% 2.57/1.38  Reduction            : 0.09
% 2.73/1.38  Demodulation         : 0.06
% 2.73/1.38  BG Simplification    : 0.02
% 2.73/1.38  Subsumption          : 0.06
% 2.73/1.38  Abstraction          : 0.02
% 2.73/1.38  MUC search           : 0.00
% 2.73/1.38  Cooper               : 0.00
% 2.73/1.38  Total                : 0.65
% 2.73/1.38  Index Insertion      : 0.00
% 2.73/1.38  Index Deletion       : 0.00
% 2.73/1.38  Index Matching       : 0.00
% 2.73/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
