%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:42 EST 2020

% Result     : Theorem 7.54s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :   51 (  75 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 121 expanded)
%              Number of equality atoms :   25 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_44,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_88,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_61,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1024,plain,(
    ! [A_889,B_890,C_891] :
      ( r2_hidden('#skF_1'(A_889,B_890,C_891),A_889)
      | r2_hidden('#skF_2'(A_889,B_890,C_891),C_891)
      | k4_xboole_0(A_889,B_890) = C_891 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1070,plain,(
    ! [A_889,B_890] :
      ( r2_hidden('#skF_2'(A_889,B_890,A_889),A_889)
      | k4_xboole_0(A_889,B_890) = A_889 ) ),
    inference(resolution,[status(thm)],[c_1024,c_14])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1616,plain,(
    ! [A_1133,B_1134,C_1135] :
      ( ~ r2_hidden('#skF_1'(A_1133,B_1134,C_1135),C_1135)
      | r2_hidden('#skF_2'(A_1133,B_1134,C_1135),B_1134)
      | ~ r2_hidden('#skF_2'(A_1133,B_1134,C_1135),A_1133)
      | k4_xboole_0(A_1133,B_1134) = C_1135 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2525,plain,(
    ! [A_1335,B_1336] :
      ( r2_hidden('#skF_2'(A_1335,B_1336,A_1335),B_1336)
      | ~ r2_hidden('#skF_2'(A_1335,B_1336,A_1335),A_1335)
      | k4_xboole_0(A_1335,B_1336) = A_1335 ) ),
    inference(resolution,[status(thm)],[c_12,c_1616])).

tff(c_2557,plain,(
    ! [A_1359,B_1360] :
      ( r2_hidden('#skF_2'(A_1359,B_1360,A_1359),B_1360)
      | k4_xboole_0(A_1359,B_1360) = A_1359 ) ),
    inference(resolution,[status(thm)],[c_1070,c_2525])).

tff(c_22,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_13060,plain,(
    ! [A_3886,A_3887] :
      ( '#skF_2'(A_3886,k1_tarski(A_3887),A_3886) = A_3887
      | k4_xboole_0(A_3886,k1_tarski(A_3887)) = A_3886 ) ),
    inference(resolution,[status(thm)],[c_2557,c_22])).

tff(c_13759,plain,(
    '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_13060,c_88])).

tff(c_13773,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_13759,c_1070])).

tff(c_14044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_61,c_13773])).

tff(c_14045,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_14046,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14068,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14046,c_48])).

tff(c_40,plain,(
    ! [C_19,B_18] : ~ r2_hidden(C_19,k4_xboole_0(B_18,k1_tarski(C_19))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14078,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_14068,c_40])).

tff(c_14083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14045,c_14078])).

tff(c_14084,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_14085,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14114,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14085,c_50])).

tff(c_14121,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_14114,c_40])).

tff(c_14126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14084,c_14121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.54/2.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.54/2.84  
% 7.54/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.54/2.84  %$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 7.54/2.84  
% 7.54/2.84  %Foreground sorts:
% 7.54/2.84  
% 7.54/2.84  
% 7.54/2.84  %Background operators:
% 7.54/2.84  
% 7.54/2.84  
% 7.54/2.84  %Foreground operators:
% 7.54/2.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.54/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.54/2.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.54/2.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.54/2.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.54/2.84  tff('#skF_7', type, '#skF_7': $i).
% 7.54/2.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.54/2.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.54/2.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.54/2.84  tff('#skF_5', type, '#skF_5': $i).
% 7.54/2.84  tff('#skF_6', type, '#skF_6': $i).
% 7.54/2.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.54/2.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.54/2.84  tff('#skF_8', type, '#skF_8': $i).
% 7.54/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.54/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.54/2.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.54/2.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.54/2.84  
% 7.54/2.85  tff(f_61, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.54/2.85  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.54/2.85  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.54/2.85  tff(f_55, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 7.54/2.85  tff(c_44, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.54/2.85  tff(c_88, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_44])).
% 7.54/2.85  tff(c_46, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.54/2.85  tff(c_61, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_46])).
% 7.54/2.85  tff(c_1024, plain, (![A_889, B_890, C_891]: (r2_hidden('#skF_1'(A_889, B_890, C_891), A_889) | r2_hidden('#skF_2'(A_889, B_890, C_891), C_891) | k4_xboole_0(A_889, B_890)=C_891)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.54/2.85  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.54/2.85  tff(c_1070, plain, (![A_889, B_890]: (r2_hidden('#skF_2'(A_889, B_890, A_889), A_889) | k4_xboole_0(A_889, B_890)=A_889)), inference(resolution, [status(thm)], [c_1024, c_14])).
% 7.54/2.85  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.54/2.85  tff(c_1616, plain, (![A_1133, B_1134, C_1135]: (~r2_hidden('#skF_1'(A_1133, B_1134, C_1135), C_1135) | r2_hidden('#skF_2'(A_1133, B_1134, C_1135), B_1134) | ~r2_hidden('#skF_2'(A_1133, B_1134, C_1135), A_1133) | k4_xboole_0(A_1133, B_1134)=C_1135)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.54/2.85  tff(c_2525, plain, (![A_1335, B_1336]: (r2_hidden('#skF_2'(A_1335, B_1336, A_1335), B_1336) | ~r2_hidden('#skF_2'(A_1335, B_1336, A_1335), A_1335) | k4_xboole_0(A_1335, B_1336)=A_1335)), inference(resolution, [status(thm)], [c_12, c_1616])).
% 7.54/2.85  tff(c_2557, plain, (![A_1359, B_1360]: (r2_hidden('#skF_2'(A_1359, B_1360, A_1359), B_1360) | k4_xboole_0(A_1359, B_1360)=A_1359)), inference(resolution, [status(thm)], [c_1070, c_2525])).
% 7.54/2.85  tff(c_22, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.54/2.85  tff(c_13060, plain, (![A_3886, A_3887]: ('#skF_2'(A_3886, k1_tarski(A_3887), A_3886)=A_3887 | k4_xboole_0(A_3886, k1_tarski(A_3887))=A_3886)), inference(resolution, [status(thm)], [c_2557, c_22])).
% 7.54/2.85  tff(c_13759, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_13060, c_88])).
% 7.54/2.85  tff(c_13773, plain, (r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_13759, c_1070])).
% 7.54/2.85  tff(c_14044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_61, c_13773])).
% 7.54/2.85  tff(c_14045, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 7.54/2.85  tff(c_14046, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_44])).
% 7.54/2.85  tff(c_48, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.54/2.85  tff(c_14068, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14046, c_48])).
% 7.54/2.85  tff(c_40, plain, (![C_19, B_18]: (~r2_hidden(C_19, k4_xboole_0(B_18, k1_tarski(C_19))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.54/2.85  tff(c_14078, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_14068, c_40])).
% 7.54/2.85  tff(c_14083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14045, c_14078])).
% 7.54/2.85  tff(c_14084, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 7.54/2.85  tff(c_14085, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 7.54/2.85  tff(c_50, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.54/2.85  tff(c_14114, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14085, c_50])).
% 7.54/2.85  tff(c_14121, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_14114, c_40])).
% 7.54/2.85  tff(c_14126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14084, c_14121])).
% 7.54/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.54/2.85  
% 7.54/2.85  Inference rules
% 7.54/2.85  ----------------------
% 7.54/2.85  #Ref     : 0
% 7.54/2.85  #Sup     : 2322
% 7.54/2.85  #Fact    : 0
% 7.54/2.85  #Define  : 0
% 7.54/2.85  #Split   : 4
% 7.54/2.85  #Chain   : 0
% 7.54/2.85  #Close   : 0
% 7.54/2.85  
% 7.54/2.85  Ordering : KBO
% 7.54/2.85  
% 7.54/2.85  Simplification rules
% 7.54/2.85  ----------------------
% 7.54/2.85  #Subsume      : 478
% 7.54/2.85  #Demod        : 512
% 7.54/2.85  #Tautology    : 189
% 7.54/2.85  #SimpNegUnit  : 36
% 7.54/2.85  #BackRed      : 0
% 7.54/2.85  
% 7.54/2.85  #Partial instantiations: 2436
% 7.54/2.85  #Strategies tried      : 1
% 7.54/2.85  
% 7.54/2.85  Timing (in seconds)
% 7.54/2.85  ----------------------
% 7.54/2.86  Preprocessing        : 0.30
% 7.54/2.86  Parsing              : 0.15
% 7.54/2.86  CNF conversion       : 0.02
% 7.54/2.86  Main loop            : 1.80
% 7.54/2.86  Inferencing          : 0.59
% 7.54/2.86  Reduction            : 0.55
% 7.54/2.86  Demodulation         : 0.39
% 7.54/2.86  BG Simplification    : 0.09
% 7.54/2.86  Subsumption          : 0.48
% 7.54/2.86  Abstraction          : 0.12
% 7.54/2.86  MUC search           : 0.00
% 7.54/2.86  Cooper               : 0.00
% 7.54/2.86  Total                : 2.12
% 7.54/2.86  Index Insertion      : 0.00
% 7.54/2.86  Index Deletion       : 0.00
% 7.54/2.86  Index Matching       : 0.00
% 7.54/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
