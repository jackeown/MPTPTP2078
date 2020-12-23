%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:34 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   65 (  81 expanded)
%              Number of leaves         :   34 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :   62 (  96 expanded)
%              Number of equality atoms :   35 (  59 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_94,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_47,axiom,(
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

tff(c_44,plain,(
    ! [C_24] : r2_hidden(C_24,k1_tarski(C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_72,plain,
    ( '#skF_7' != '#skF_6'
    | '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_77,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(k1_tarski(A_53),k1_tarski(B_54))
      | B_54 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_108,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(A_73,B_74) = k1_xboole_0
      | ~ r1_xboole_0(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_186,plain,(
    ! [A_91,B_92] :
      ( k3_xboole_0(k1_tarski(A_91),k1_tarski(B_92)) = k1_xboole_0
      | B_92 = A_91 ) ),
    inference(resolution,[status(thm)],[c_68,c_108])).

tff(c_12,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_192,plain,(
    ! [A_91,B_92] :
      ( k4_xboole_0(k1_tarski(A_91),k1_tarski(B_92)) = k5_xboole_0(k1_tarski(A_91),k1_xboole_0)
      | B_92 = A_91 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_12])).

tff(c_274,plain,(
    ! [A_108,B_109] :
      ( k4_xboole_0(k1_tarski(A_108),k1_tarski(B_109)) = k1_tarski(A_108)
      | B_109 = A_108 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_192])).

tff(c_70,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6')
    | '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_158,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_286,plain,(
    '#skF_7' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_158])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_286])).

tff(c_302,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_303,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6')
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_334,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_303,c_74])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_xboole_0(k4_xboole_0(A_11,B_12),B_12) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_341,plain,(
    r1_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_16])).

tff(c_381,plain,(
    ! [A_116,B_117,C_118] :
      ( ~ r1_xboole_0(A_116,B_117)
      | ~ r2_hidden(C_118,B_117)
      | ~ r2_hidden(C_118,A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_397,plain,(
    ! [C_119] : ~ r2_hidden(C_119,k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_341,c_381])).

tff(c_412,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_44,c_397])).

tff(c_413,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_414,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_76,plain,
    ( '#skF_7' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_455,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_414,c_76])).

tff(c_459,plain,(
    r1_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_16])).

tff(c_578,plain,(
    ! [A_158,B_159,C_160] :
      ( ~ r1_xboole_0(A_158,B_159)
      | ~ r2_hidden(C_160,B_159)
      | ~ r2_hidden(C_160,A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_591,plain,(
    ! [C_161] : ~ r2_hidden(C_161,k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_459,c_578])).

tff(c_606,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_44,c_591])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.34  
% 2.69/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.34  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.69/1.34  
% 2.69/1.34  %Foreground sorts:
% 2.69/1.34  
% 2.69/1.34  
% 2.69/1.34  %Background operators:
% 2.69/1.34  
% 2.69/1.34  
% 2.69/1.34  %Foreground operators:
% 2.69/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.69/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.69/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.69/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.69/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.69/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.69/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.34  tff('#skF_9', type, '#skF_9': $i).
% 2.69/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.34  tff('#skF_8', type, '#skF_8': $i).
% 2.69/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.69/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.69/1.34  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.69/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.69/1.34  
% 2.69/1.35  tff(f_75, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.69/1.35  tff(f_100, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.69/1.35  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.69/1.35  tff(f_94, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.69/1.35  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.69/1.35  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.69/1.35  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.69/1.35  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.69/1.35  tff(c_44, plain, (![C_24]: (r2_hidden(C_24, k1_tarski(C_24)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.69/1.35  tff(c_72, plain, ('#skF_7'!='#skF_6' | '#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.69/1.35  tff(c_77, plain, ('#skF_7'!='#skF_6'), inference(splitLeft, [status(thm)], [c_72])).
% 2.69/1.35  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.69/1.35  tff(c_68, plain, (![A_53, B_54]: (r1_xboole_0(k1_tarski(A_53), k1_tarski(B_54)) | B_54=A_53)), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.69/1.35  tff(c_108, plain, (![A_73, B_74]: (k3_xboole_0(A_73, B_74)=k1_xboole_0 | ~r1_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.35  tff(c_186, plain, (![A_91, B_92]: (k3_xboole_0(k1_tarski(A_91), k1_tarski(B_92))=k1_xboole_0 | B_92=A_91)), inference(resolution, [status(thm)], [c_68, c_108])).
% 2.69/1.35  tff(c_12, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.69/1.35  tff(c_192, plain, (![A_91, B_92]: (k4_xboole_0(k1_tarski(A_91), k1_tarski(B_92))=k5_xboole_0(k1_tarski(A_91), k1_xboole_0) | B_92=A_91)), inference(superposition, [status(thm), theory('equality')], [c_186, c_12])).
% 2.69/1.35  tff(c_274, plain, (![A_108, B_109]: (k4_xboole_0(k1_tarski(A_108), k1_tarski(B_109))=k1_tarski(A_108) | B_109=A_108)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_192])).
% 2.69/1.35  tff(c_70, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6') | '#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.69/1.35  tff(c_158, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_70])).
% 2.69/1.35  tff(c_286, plain, ('#skF_7'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_274, c_158])).
% 2.69/1.35  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_286])).
% 2.69/1.35  tff(c_302, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_70])).
% 2.69/1.35  tff(c_303, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 2.69/1.35  tff(c_74, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6') | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.69/1.35  tff(c_334, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_303, c_74])).
% 2.69/1.35  tff(c_16, plain, (![A_11, B_12]: (r1_xboole_0(k4_xboole_0(A_11, B_12), B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.69/1.35  tff(c_341, plain, (r1_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_334, c_16])).
% 2.69/1.35  tff(c_381, plain, (![A_116, B_117, C_118]: (~r1_xboole_0(A_116, B_117) | ~r2_hidden(C_118, B_117) | ~r2_hidden(C_118, A_116))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.69/1.35  tff(c_397, plain, (![C_119]: (~r2_hidden(C_119, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_341, c_381])).
% 2.69/1.35  tff(c_412, plain, $false, inference(resolution, [status(thm)], [c_44, c_397])).
% 2.69/1.35  tff(c_413, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_72])).
% 2.69/1.35  tff(c_414, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_72])).
% 2.69/1.35  tff(c_76, plain, ('#skF_7'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.69/1.35  tff(c_455, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_414, c_76])).
% 2.69/1.35  tff(c_459, plain, (r1_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_455, c_16])).
% 2.69/1.35  tff(c_578, plain, (![A_158, B_159, C_160]: (~r1_xboole_0(A_158, B_159) | ~r2_hidden(C_160, B_159) | ~r2_hidden(C_160, A_158))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.69/1.35  tff(c_591, plain, (![C_161]: (~r2_hidden(C_161, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_459, c_578])).
% 2.69/1.35  tff(c_606, plain, $false, inference(resolution, [status(thm)], [c_44, c_591])).
% 2.69/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.35  
% 2.69/1.35  Inference rules
% 2.69/1.35  ----------------------
% 2.69/1.35  #Ref     : 0
% 2.69/1.35  #Sup     : 127
% 2.69/1.35  #Fact    : 0
% 2.69/1.35  #Define  : 0
% 2.69/1.35  #Split   : 2
% 2.69/1.35  #Chain   : 0
% 2.69/1.35  #Close   : 0
% 2.69/1.35  
% 2.69/1.35  Ordering : KBO
% 2.69/1.35  
% 2.69/1.35  Simplification rules
% 2.69/1.35  ----------------------
% 2.69/1.35  #Subsume      : 3
% 2.69/1.35  #Demod        : 35
% 2.69/1.35  #Tautology    : 74
% 2.69/1.35  #SimpNegUnit  : 1
% 2.69/1.35  #BackRed      : 0
% 2.69/1.35  
% 2.69/1.35  #Partial instantiations: 0
% 2.69/1.35  #Strategies tried      : 1
% 2.69/1.35  
% 2.69/1.35  Timing (in seconds)
% 2.69/1.35  ----------------------
% 2.69/1.35  Preprocessing        : 0.34
% 2.69/1.35  Parsing              : 0.17
% 2.69/1.35  CNF conversion       : 0.03
% 2.69/1.35  Main loop            : 0.26
% 2.69/1.35  Inferencing          : 0.10
% 2.69/1.35  Reduction            : 0.08
% 2.69/1.35  Demodulation         : 0.06
% 2.69/1.35  BG Simplification    : 0.02
% 2.69/1.35  Subsumption          : 0.04
% 2.69/1.35  Abstraction          : 0.02
% 2.69/1.35  MUC search           : 0.00
% 2.69/1.35  Cooper               : 0.00
% 2.69/1.36  Total                : 0.63
% 2.69/1.36  Index Insertion      : 0.00
% 2.69/1.36  Index Deletion       : 0.00
% 2.69/1.36  Index Matching       : 0.00
% 2.69/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
