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
% DateTime   : Thu Dec  3 09:48:35 EST 2020

% Result     : Theorem 6.68s
% Output     : CNFRefutation 6.88s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 103 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 179 expanded)
%              Number of equality atoms :   38 ( 107 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_22,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,
    ( '#skF_5' != '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_45,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_613,plain,(
    ! [A_643,B_644,C_645] :
      ( r2_hidden('#skF_1'(A_643,B_644,C_645),A_643)
      | r2_hidden('#skF_2'(A_643,B_644,C_645),C_645)
      | k4_xboole_0(A_643,B_644) = C_645 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_648,plain,(
    ! [A_643,B_644] :
      ( r2_hidden('#skF_2'(A_643,B_644,A_643),A_643)
      | k4_xboole_0(A_643,B_644) = A_643 ) ),
    inference(resolution,[status(thm)],[c_613,c_14])).

tff(c_1544,plain,(
    ! [A_1133,B_1134,C_1135] :
      ( r2_hidden('#skF_1'(A_1133,B_1134,C_1135),A_1133)
      | r2_hidden('#skF_2'(A_1133,B_1134,C_1135),B_1134)
      | ~ r2_hidden('#skF_2'(A_1133,B_1134,C_1135),A_1133)
      | k4_xboole_0(A_1133,B_1134) = C_1135 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2073,plain,(
    ! [A_1232,B_1233] :
      ( r2_hidden('#skF_2'(A_1232,B_1233,A_1232),B_1233)
      | ~ r2_hidden('#skF_2'(A_1232,B_1233,A_1232),A_1232)
      | k4_xboole_0(A_1232,B_1233) = A_1232 ) ),
    inference(resolution,[status(thm)],[c_1544,c_8])).

tff(c_2113,plain,(
    ! [A_1256,B_1257] :
      ( r2_hidden('#skF_2'(A_1256,B_1257,A_1256),B_1257)
      | k4_xboole_0(A_1256,B_1257) = A_1256 ) ),
    inference(resolution,[status(thm)],[c_648,c_2073])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3070,plain,(
    ! [A_1402,A_1403] :
      ( '#skF_2'(A_1402,k1_tarski(A_1403),A_1402) = A_1403
      | k4_xboole_0(A_1402,k1_tarski(A_1403)) = A_1402 ) ),
    inference(resolution,[status(thm)],[c_2113,c_20])).

tff(c_3094,plain,(
    ! [A_1403,A_1402] :
      ( r2_hidden(A_1403,A_1402)
      | k4_xboole_0(A_1402,k1_tarski(A_1403)) = A_1402
      | k4_xboole_0(A_1402,k1_tarski(A_1403)) = A_1402 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3070,c_648])).

tff(c_8872,plain,(
    ! [A_2073,A_2074] :
      ( r2_hidden(A_2073,A_2074)
      | k4_xboole_0(A_2074,k1_tarski(A_2073)) = A_2074 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3094])).

tff(c_38,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_73,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_9294,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8872,c_73])).

tff(c_9318,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9294,c_20])).

tff(c_9360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_9318])).

tff(c_9362,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_9361,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_9367,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9361,c_9361,c_42])).

tff(c_9368,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_9367])).

tff(c_9380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9362,c_9368])).

tff(c_9381,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_9367])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_9419,plain,(
    ! [D_2123] :
      ( ~ r2_hidden(D_2123,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_2123,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9381,c_4])).

tff(c_9422,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_22,c_9419])).

tff(c_9426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_9422])).

tff(c_9427,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_9428,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( '#skF_5' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_9467,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9427,c_9427,c_9428,c_44])).

tff(c_9478,plain,(
    ! [D_2136] :
      ( ~ r2_hidden(D_2136,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_2136,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9467,c_4])).

tff(c_9481,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_22,c_9478])).

tff(c_9485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_9481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:01:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.68/2.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.88/2.40  
% 6.88/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.88/2.40  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 6.88/2.40  
% 6.88/2.40  %Foreground sorts:
% 6.88/2.40  
% 6.88/2.40  
% 6.88/2.40  %Background operators:
% 6.88/2.40  
% 6.88/2.40  
% 6.88/2.40  %Foreground operators:
% 6.88/2.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.88/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.88/2.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.88/2.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.88/2.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.88/2.40  tff('#skF_7', type, '#skF_7': $i).
% 6.88/2.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.88/2.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.88/2.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.88/2.40  tff('#skF_5', type, '#skF_5': $i).
% 6.88/2.40  tff('#skF_6', type, '#skF_6': $i).
% 6.88/2.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.88/2.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.88/2.40  tff('#skF_8', type, '#skF_8': $i).
% 6.88/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.88/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.88/2.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.88/2.40  
% 6.88/2.41  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 6.88/2.41  tff(f_54, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 6.88/2.41  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.88/2.41  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.88/2.41  tff(c_40, plain, ('#skF_5'!='#skF_6' | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.88/2.41  tff(c_45, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_40])).
% 6.88/2.41  tff(c_613, plain, (![A_643, B_644, C_645]: (r2_hidden('#skF_1'(A_643, B_644, C_645), A_643) | r2_hidden('#skF_2'(A_643, B_644, C_645), C_645) | k4_xboole_0(A_643, B_644)=C_645)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.88/2.41  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.88/2.41  tff(c_648, plain, (![A_643, B_644]: (r2_hidden('#skF_2'(A_643, B_644, A_643), A_643) | k4_xboole_0(A_643, B_644)=A_643)), inference(resolution, [status(thm)], [c_613, c_14])).
% 6.88/2.41  tff(c_1544, plain, (![A_1133, B_1134, C_1135]: (r2_hidden('#skF_1'(A_1133, B_1134, C_1135), A_1133) | r2_hidden('#skF_2'(A_1133, B_1134, C_1135), B_1134) | ~r2_hidden('#skF_2'(A_1133, B_1134, C_1135), A_1133) | k4_xboole_0(A_1133, B_1134)=C_1135)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.88/2.41  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.88/2.41  tff(c_2073, plain, (![A_1232, B_1233]: (r2_hidden('#skF_2'(A_1232, B_1233, A_1232), B_1233) | ~r2_hidden('#skF_2'(A_1232, B_1233, A_1232), A_1232) | k4_xboole_0(A_1232, B_1233)=A_1232)), inference(resolution, [status(thm)], [c_1544, c_8])).
% 6.88/2.41  tff(c_2113, plain, (![A_1256, B_1257]: (r2_hidden('#skF_2'(A_1256, B_1257, A_1256), B_1257) | k4_xboole_0(A_1256, B_1257)=A_1256)), inference(resolution, [status(thm)], [c_648, c_2073])).
% 6.88/2.41  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.88/2.41  tff(c_3070, plain, (![A_1402, A_1403]: ('#skF_2'(A_1402, k1_tarski(A_1403), A_1402)=A_1403 | k4_xboole_0(A_1402, k1_tarski(A_1403))=A_1402)), inference(resolution, [status(thm)], [c_2113, c_20])).
% 6.88/2.41  tff(c_3094, plain, (![A_1403, A_1402]: (r2_hidden(A_1403, A_1402) | k4_xboole_0(A_1402, k1_tarski(A_1403))=A_1402 | k4_xboole_0(A_1402, k1_tarski(A_1403))=A_1402)), inference(superposition, [status(thm), theory('equality')], [c_3070, c_648])).
% 6.88/2.41  tff(c_8872, plain, (![A_2073, A_2074]: (r2_hidden(A_2073, A_2074) | k4_xboole_0(A_2074, k1_tarski(A_2073))=A_2074)), inference(factorization, [status(thm), theory('equality')], [c_3094])).
% 6.88/2.41  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.88/2.41  tff(c_73, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_38])).
% 6.88/2.41  tff(c_9294, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8872, c_73])).
% 6.88/2.41  tff(c_9318, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_9294, c_20])).
% 6.88/2.41  tff(c_9360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_9318])).
% 6.88/2.41  tff(c_9362, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 6.88/2.41  tff(c_9361, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_38])).
% 6.88/2.41  tff(c_42, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.88/2.41  tff(c_9367, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9361, c_9361, c_42])).
% 6.88/2.41  tff(c_9368, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_9367])).
% 6.88/2.41  tff(c_9380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9362, c_9368])).
% 6.88/2.41  tff(c_9381, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_9367])).
% 6.88/2.41  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.88/2.41  tff(c_9419, plain, (![D_2123]: (~r2_hidden(D_2123, k1_tarski('#skF_8')) | ~r2_hidden(D_2123, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_9381, c_4])).
% 6.88/2.41  tff(c_9422, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_22, c_9419])).
% 6.88/2.41  tff(c_9426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_9422])).
% 6.88/2.41  tff(c_9427, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_40])).
% 6.88/2.41  tff(c_9428, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_40])).
% 6.88/2.41  tff(c_44, plain, ('#skF_5'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.88/2.41  tff(c_9467, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9427, c_9427, c_9428, c_44])).
% 6.88/2.41  tff(c_9478, plain, (![D_2136]: (~r2_hidden(D_2136, k1_tarski('#skF_8')) | ~r2_hidden(D_2136, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_9467, c_4])).
% 6.88/2.41  tff(c_9481, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_22, c_9478])).
% 6.88/2.41  tff(c_9485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_9481])).
% 6.88/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.88/2.41  
% 6.88/2.41  Inference rules
% 6.88/2.41  ----------------------
% 6.88/2.41  #Ref     : 0
% 6.88/2.41  #Sup     : 2098
% 6.88/2.41  #Fact    : 10
% 6.88/2.41  #Define  : 0
% 6.88/2.41  #Split   : 6
% 6.88/2.41  #Chain   : 0
% 6.88/2.41  #Close   : 0
% 6.88/2.41  
% 6.88/2.41  Ordering : KBO
% 6.88/2.41  
% 6.88/2.41  Simplification rules
% 6.88/2.41  ----------------------
% 6.88/2.41  #Subsume      : 740
% 6.88/2.41  #Demod        : 599
% 6.88/2.41  #Tautology    : 757
% 6.88/2.41  #SimpNegUnit  : 112
% 6.88/2.41  #BackRed      : 0
% 6.88/2.41  
% 6.88/2.41  #Partial instantiations: 1105
% 6.88/2.41  #Strategies tried      : 1
% 6.88/2.41  
% 6.88/2.41  Timing (in seconds)
% 6.88/2.41  ----------------------
% 6.88/2.42  Preprocessing        : 0.30
% 6.88/2.42  Parsing              : 0.15
% 6.88/2.42  CNF conversion       : 0.02
% 6.88/2.42  Main loop            : 1.35
% 6.88/2.42  Inferencing          : 0.53
% 6.88/2.42  Reduction            : 0.43
% 6.88/2.42  Demodulation         : 0.33
% 6.88/2.42  BG Simplification    : 0.06
% 6.88/2.42  Subsumption          : 0.24
% 6.88/2.42  Abstraction          : 0.08
% 6.88/2.42  MUC search           : 0.00
% 6.88/2.42  Cooper               : 0.00
% 6.88/2.42  Total                : 1.68
% 6.88/2.42  Index Insertion      : 0.00
% 6.88/2.42  Index Deletion       : 0.00
% 6.88/2.42  Index Matching       : 0.00
% 6.88/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
