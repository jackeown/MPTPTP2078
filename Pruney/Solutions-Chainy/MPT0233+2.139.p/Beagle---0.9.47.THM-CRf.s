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
% DateTime   : Thu Dec  3 09:49:39 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 248 expanded)
%              Number of leaves         :   24 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :   89 ( 535 expanded)
%              Number of equality atoms :   62 ( 411 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
     => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_48,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_182,plain,(
    ! [B_71,C_72,A_73] :
      ( k2_tarski(B_71,C_72) = A_73
      | k1_tarski(C_72) = A_73
      | k1_tarski(B_71) = A_73
      | k1_xboole_0 = A_73
      | ~ r1_tarski(A_73,k2_tarski(B_71,C_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_204,plain,
    ( k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_182])).

tff(c_227,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_46,plain,(
    ! [C_24,A_22,B_23] :
      ( C_24 = A_22
      | ~ r1_tarski(k2_tarski(A_22,B_23),k1_tarski(C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_242,plain,(
    ! [C_24] :
      ( C_24 = '#skF_3'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(C_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_46])).

tff(c_266,plain,(
    ! [C_88] : C_88 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_242])).

tff(c_345,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_48])).

tff(c_346,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6')
    | k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_348,plain,(
    k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_86,plain,(
    ! [A_43,B_44] : k1_enumset1(A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [E_8,B_3,C_4] : r2_hidden(E_8,k1_enumset1(E_8,B_3,C_4)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_98,plain,(
    ! [A_43,B_44] : r2_hidden(A_43,k2_tarski(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_10])).

tff(c_360,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_98])).

tff(c_30,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_143,plain,(
    ! [E_62,C_63,B_64,A_65] :
      ( E_62 = C_63
      | E_62 = B_64
      | E_62 = A_65
      | ~ r2_hidden(E_62,k1_enumset1(A_65,B_64,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_146,plain,(
    ! [E_62,B_11,A_10] :
      ( E_62 = B_11
      | E_62 = A_10
      | E_62 = A_10
      | ~ r2_hidden(E_62,k2_tarski(A_10,B_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_143])).

tff(c_403,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_360,c_146])).

tff(c_406,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_403])).

tff(c_409,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_50])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [E_8,A_2,B_3] : r2_hidden(E_8,k1_enumset1(A_2,B_3,E_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_92,plain,(
    ! [B_44,A_43] : r2_hidden(B_44,k2_tarski(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_6])).

tff(c_366,plain,(
    r2_hidden('#skF_6',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_92])).

tff(c_417,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_366,c_146])).

tff(c_420,plain,(
    '#skF_6' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_417])).

tff(c_408,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_348])).

tff(c_430,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_420,c_408])).

tff(c_441,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_98])).

tff(c_162,plain,(
    ! [E_66,B_67,A_68] :
      ( E_66 = B_67
      | E_66 = A_68
      | E_66 = A_68
      | ~ r2_hidden(E_66,k2_tarski(A_68,B_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_143])).

tff(c_171,plain,(
    ! [E_66,A_9] :
      ( E_66 = A_9
      | E_66 = A_9
      | E_66 = A_9
      | ~ r2_hidden(E_66,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_162])).

tff(c_471,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_441,c_171])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_409,c_409,c_471])).

tff(c_476,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6')
    | k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_478,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_476])).

tff(c_492,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_98])).

tff(c_519,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_492,c_171])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_50,c_519])).

tff(c_524,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_476])).

tff(c_539,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_98])).

tff(c_566,plain,(
    '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_539,c_171])).

tff(c_570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_48,c_566])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:47:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.35  
% 2.34/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.35  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.34/1.35  
% 2.34/1.35  %Foreground sorts:
% 2.34/1.35  
% 2.34/1.35  
% 2.34/1.35  %Background operators:
% 2.34/1.35  
% 2.34/1.35  
% 2.34/1.35  %Foreground operators:
% 2.34/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.34/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.34/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.34/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.34/1.35  
% 2.34/1.36  tff(f_79, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.34/1.36  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.34/1.36  tff(f_65, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.34/1.36  tff(f_69, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.34/1.36  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.34/1.36  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.34/1.36  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.34/1.36  tff(c_48, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.34/1.36  tff(c_50, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.34/1.36  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.34/1.36  tff(c_52, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.34/1.36  tff(c_182, plain, (![B_71, C_72, A_73]: (k2_tarski(B_71, C_72)=A_73 | k1_tarski(C_72)=A_73 | k1_tarski(B_71)=A_73 | k1_xboole_0=A_73 | ~r1_tarski(A_73, k2_tarski(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.34/1.36  tff(c_204, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_182])).
% 2.34/1.36  tff(c_227, plain, (k2_tarski('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_204])).
% 2.34/1.36  tff(c_46, plain, (![C_24, A_22, B_23]: (C_24=A_22 | ~r1_tarski(k2_tarski(A_22, B_23), k1_tarski(C_24)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.34/1.36  tff(c_242, plain, (![C_24]: (C_24='#skF_3' | ~r1_tarski(k1_xboole_0, k1_tarski(C_24)))), inference(superposition, [status(thm), theory('equality')], [c_227, c_46])).
% 2.34/1.36  tff(c_266, plain, (![C_88]: (C_88='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_242])).
% 2.34/1.36  tff(c_345, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_266, c_48])).
% 2.34/1.36  tff(c_346, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6') | k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_204])).
% 2.34/1.36  tff(c_348, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_346])).
% 2.34/1.36  tff(c_86, plain, (![A_43, B_44]: (k1_enumset1(A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.34/1.36  tff(c_10, plain, (![E_8, B_3, C_4]: (r2_hidden(E_8, k1_enumset1(E_8, B_3, C_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.34/1.36  tff(c_98, plain, (![A_43, B_44]: (r2_hidden(A_43, k2_tarski(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_10])).
% 2.34/1.36  tff(c_360, plain, (r2_hidden('#skF_5', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_348, c_98])).
% 2.34/1.36  tff(c_30, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.34/1.36  tff(c_143, plain, (![E_62, C_63, B_64, A_65]: (E_62=C_63 | E_62=B_64 | E_62=A_65 | ~r2_hidden(E_62, k1_enumset1(A_65, B_64, C_63)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.34/1.36  tff(c_146, plain, (![E_62, B_11, A_10]: (E_62=B_11 | E_62=A_10 | E_62=A_10 | ~r2_hidden(E_62, k2_tarski(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_143])).
% 2.34/1.36  tff(c_403, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_360, c_146])).
% 2.34/1.36  tff(c_406, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_403])).
% 2.34/1.36  tff(c_409, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_406, c_50])).
% 2.34/1.36  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.34/1.36  tff(c_6, plain, (![E_8, A_2, B_3]: (r2_hidden(E_8, k1_enumset1(A_2, B_3, E_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.34/1.36  tff(c_92, plain, (![B_44, A_43]: (r2_hidden(B_44, k2_tarski(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_6])).
% 2.34/1.36  tff(c_366, plain, (r2_hidden('#skF_6', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_348, c_92])).
% 2.34/1.36  tff(c_417, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_366, c_146])).
% 2.34/1.36  tff(c_420, plain, ('#skF_6'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_417])).
% 2.34/1.36  tff(c_408, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_406, c_348])).
% 2.34/1.36  tff(c_430, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_420, c_408])).
% 2.34/1.36  tff(c_441, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_430, c_98])).
% 2.34/1.36  tff(c_162, plain, (![E_66, B_67, A_68]: (E_66=B_67 | E_66=A_68 | E_66=A_68 | ~r2_hidden(E_66, k2_tarski(A_68, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_143])).
% 2.34/1.36  tff(c_171, plain, (![E_66, A_9]: (E_66=A_9 | E_66=A_9 | E_66=A_9 | ~r2_hidden(E_66, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_162])).
% 2.34/1.36  tff(c_471, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_441, c_171])).
% 2.34/1.36  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_409, c_409, c_409, c_471])).
% 2.34/1.36  tff(c_476, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6') | k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_346])).
% 2.34/1.36  tff(c_478, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_476])).
% 2.34/1.36  tff(c_492, plain, (r2_hidden('#skF_3', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_478, c_98])).
% 2.34/1.36  tff(c_519, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_492, c_171])).
% 2.34/1.36  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_50, c_519])).
% 2.34/1.36  tff(c_524, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_476])).
% 2.34/1.36  tff(c_539, plain, (r2_hidden('#skF_3', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_524, c_98])).
% 2.34/1.36  tff(c_566, plain, ('#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_539, c_171])).
% 2.34/1.36  tff(c_570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_48, c_566])).
% 2.34/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.36  
% 2.34/1.36  Inference rules
% 2.34/1.36  ----------------------
% 2.34/1.36  #Ref     : 0
% 2.34/1.36  #Sup     : 139
% 2.34/1.36  #Fact    : 0
% 2.34/1.36  #Define  : 0
% 2.34/1.36  #Split   : 3
% 2.34/1.36  #Chain   : 0
% 2.34/1.36  #Close   : 0
% 2.34/1.36  
% 2.34/1.36  Ordering : KBO
% 2.34/1.36  
% 2.34/1.36  Simplification rules
% 2.34/1.36  ----------------------
% 2.34/1.36  #Subsume      : 6
% 2.34/1.36  #Demod        : 61
% 2.34/1.36  #Tautology    : 61
% 2.34/1.36  #SimpNegUnit  : 5
% 2.34/1.36  #BackRed      : 14
% 2.34/1.36  
% 2.34/1.36  #Partial instantiations: 30
% 2.34/1.36  #Strategies tried      : 1
% 2.34/1.36  
% 2.34/1.36  Timing (in seconds)
% 2.34/1.36  ----------------------
% 2.34/1.37  Preprocessing        : 0.30
% 2.34/1.37  Parsing              : 0.16
% 2.34/1.37  CNF conversion       : 0.02
% 2.34/1.37  Main loop            : 0.29
% 2.34/1.37  Inferencing          : 0.12
% 2.34/1.37  Reduction            : 0.09
% 2.34/1.37  Demodulation         : 0.07
% 2.34/1.37  BG Simplification    : 0.02
% 2.34/1.37  Subsumption          : 0.06
% 2.34/1.37  Abstraction          : 0.01
% 2.34/1.37  MUC search           : 0.00
% 2.34/1.37  Cooper               : 0.00
% 2.34/1.37  Total                : 0.63
% 2.34/1.37  Index Insertion      : 0.00
% 2.34/1.37  Index Deletion       : 0.00
% 2.34/1.37  Index Matching       : 0.00
% 2.34/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
