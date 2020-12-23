%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:32 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   72 (  96 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :    6
%              Number of atoms          :   83 ( 134 expanded)
%              Number of equality atoms :   39 (  69 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_81,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(c_48,plain,(
    ! [C_27] : r2_hidden(C_27,k1_tarski(C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_492,plain,(
    ! [A_144,B_145] :
      ( r1_xboole_0(A_144,B_145)
      | k4_xboole_0(A_144,B_145) != A_144 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_495,plain,(
    ! [B_145,A_144] :
      ( r1_xboole_0(B_145,A_144)
      | k4_xboole_0(A_144,B_145) != A_144 ) ),
    inference(resolution,[status(thm)],[c_492,c_2])).

tff(c_12,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_496,plain,(
    ! [A_146,B_147] :
      ( k3_xboole_0(A_146,B_147) = A_146
      | ~ r1_tarski(A_146,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_500,plain,(
    ! [B_9] : k3_xboole_0(B_9,B_9) = B_9 ),
    inference(resolution,[status(thm)],[c_12,c_496])).

tff(c_602,plain,(
    ! [A_168,B_169,C_170] :
      ( ~ r1_xboole_0(A_168,B_169)
      | ~ r2_hidden(C_170,k3_xboole_0(A_168,B_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_606,plain,(
    ! [B_171,C_172] :
      ( ~ r1_xboole_0(B_171,B_171)
      | ~ r2_hidden(C_172,B_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_602])).

tff(c_625,plain,(
    ! [C_173,A_174] :
      ( ~ r2_hidden(C_173,A_174)
      | k4_xboole_0(A_174,A_174) != A_174 ) ),
    inference(resolution,[status(thm)],[c_495,c_606])).

tff(c_643,plain,(
    ! [C_27] : k4_xboole_0(k1_tarski(C_27),k1_tarski(C_27)) != k1_tarski(C_27) ),
    inference(resolution,[status(thm)],[c_48,c_625])).

tff(c_313,plain,(
    ! [A_101,B_102] :
      ( r1_xboole_0(A_101,B_102)
      | k4_xboole_0(A_101,B_102) != A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_320,plain,(
    ! [B_102,A_101] :
      ( r1_xboole_0(B_102,A_101)
      | k4_xboole_0(A_101,B_102) != A_101 ) ),
    inference(resolution,[status(thm)],[c_313,c_2])).

tff(c_321,plain,(
    ! [A_103,B_104] :
      ( k3_xboole_0(A_103,B_104) = A_103
      | ~ r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_325,plain,(
    ! [B_9] : k3_xboole_0(B_9,B_9) = B_9 ),
    inference(resolution,[status(thm)],[c_12,c_321])).

tff(c_397,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ r1_xboole_0(A_117,B_118)
      | ~ r2_hidden(C_119,k3_xboole_0(A_117,B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_410,plain,(
    ! [B_123,C_124] :
      ( ~ r1_xboole_0(B_123,B_123)
      | ~ r2_hidden(C_124,B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_397])).

tff(c_429,plain,(
    ! [C_125,A_126] :
      ( ~ r2_hidden(C_125,A_126)
      | k4_xboole_0(A_126,A_126) != A_126 ) ),
    inference(resolution,[status(thm)],[c_320,c_410])).

tff(c_447,plain,(
    ! [C_27] : k4_xboole_0(k1_tarski(C_27),k1_tarski(C_27)) != k1_tarski(C_27) ),
    inference(resolution,[status(thm)],[c_48,c_429])).

tff(c_70,plain,
    ( '#skF_7' != '#skF_6'
    | '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_77,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_136,plain,(
    ! [A_63,B_64] :
      ( r1_xboole_0(k1_tarski(A_63),B_64)
      | r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_159,plain,(
    ! [B_71,A_72] :
      ( r1_xboole_0(B_71,k1_tarski(A_72))
      | r2_hidden(A_72,B_71) ) ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_246,plain,(
    ! [B_88,A_89] :
      ( k4_xboole_0(B_88,k1_tarski(A_89)) = B_88
      | r2_hidden(A_89,B_88) ) ),
    inference(resolution,[status(thm)],[c_159,c_18])).

tff(c_68,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6')
    | '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_97,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_263,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_97])).

tff(c_46,plain,(
    ! [C_27,A_23] :
      ( C_27 = A_23
      | ~ r2_hidden(C_27,k1_tarski(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_269,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_263,c_46])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_269])).

tff(c_275,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_276,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6')
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_356,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_276,c_72])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_447,c_356])).

tff(c_461,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_462,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( '#skF_7' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_548,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_462,c_74])).

tff(c_646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_643,c_548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:23:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.39  
% 2.49/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.49/1.40  
% 2.49/1.40  %Foreground sorts:
% 2.49/1.40  
% 2.49/1.40  
% 2.49/1.40  %Background operators:
% 2.49/1.40  
% 2.49/1.40  
% 2.49/1.40  %Foreground operators:
% 2.49/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.49/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.49/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.49/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.49/1.40  tff('#skF_9', type, '#skF_9': $i).
% 2.49/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.49/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.49/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.40  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.49/1.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.49/1.40  
% 2.49/1.41  tff(f_81, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.49/1.41  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.49/1.41  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.49/1.41  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.49/1.41  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.49/1.41  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.49/1.41  tff(f_100, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.49/1.41  tff(f_94, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.49/1.41  tff(c_48, plain, (![C_27]: (r2_hidden(C_27, k1_tarski(C_27)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.49/1.41  tff(c_492, plain, (![A_144, B_145]: (r1_xboole_0(A_144, B_145) | k4_xboole_0(A_144, B_145)!=A_144)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.49/1.41  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.41  tff(c_495, plain, (![B_145, A_144]: (r1_xboole_0(B_145, A_144) | k4_xboole_0(A_144, B_145)!=A_144)), inference(resolution, [status(thm)], [c_492, c_2])).
% 2.49/1.41  tff(c_12, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.49/1.41  tff(c_496, plain, (![A_146, B_147]: (k3_xboole_0(A_146, B_147)=A_146 | ~r1_tarski(A_146, B_147))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.49/1.41  tff(c_500, plain, (![B_9]: (k3_xboole_0(B_9, B_9)=B_9)), inference(resolution, [status(thm)], [c_12, c_496])).
% 2.49/1.41  tff(c_602, plain, (![A_168, B_169, C_170]: (~r1_xboole_0(A_168, B_169) | ~r2_hidden(C_170, k3_xboole_0(A_168, B_169)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.41  tff(c_606, plain, (![B_171, C_172]: (~r1_xboole_0(B_171, B_171) | ~r2_hidden(C_172, B_171))), inference(superposition, [status(thm), theory('equality')], [c_500, c_602])).
% 2.49/1.41  tff(c_625, plain, (![C_173, A_174]: (~r2_hidden(C_173, A_174) | k4_xboole_0(A_174, A_174)!=A_174)), inference(resolution, [status(thm)], [c_495, c_606])).
% 2.49/1.41  tff(c_643, plain, (![C_27]: (k4_xboole_0(k1_tarski(C_27), k1_tarski(C_27))!=k1_tarski(C_27))), inference(resolution, [status(thm)], [c_48, c_625])).
% 2.49/1.41  tff(c_313, plain, (![A_101, B_102]: (r1_xboole_0(A_101, B_102) | k4_xboole_0(A_101, B_102)!=A_101)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.49/1.41  tff(c_320, plain, (![B_102, A_101]: (r1_xboole_0(B_102, A_101) | k4_xboole_0(A_101, B_102)!=A_101)), inference(resolution, [status(thm)], [c_313, c_2])).
% 2.49/1.41  tff(c_321, plain, (![A_103, B_104]: (k3_xboole_0(A_103, B_104)=A_103 | ~r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.49/1.41  tff(c_325, plain, (![B_9]: (k3_xboole_0(B_9, B_9)=B_9)), inference(resolution, [status(thm)], [c_12, c_321])).
% 2.49/1.41  tff(c_397, plain, (![A_117, B_118, C_119]: (~r1_xboole_0(A_117, B_118) | ~r2_hidden(C_119, k3_xboole_0(A_117, B_118)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.41  tff(c_410, plain, (![B_123, C_124]: (~r1_xboole_0(B_123, B_123) | ~r2_hidden(C_124, B_123))), inference(superposition, [status(thm), theory('equality')], [c_325, c_397])).
% 2.49/1.41  tff(c_429, plain, (![C_125, A_126]: (~r2_hidden(C_125, A_126) | k4_xboole_0(A_126, A_126)!=A_126)), inference(resolution, [status(thm)], [c_320, c_410])).
% 2.49/1.41  tff(c_447, plain, (![C_27]: (k4_xboole_0(k1_tarski(C_27), k1_tarski(C_27))!=k1_tarski(C_27))), inference(resolution, [status(thm)], [c_48, c_429])).
% 2.49/1.41  tff(c_70, plain, ('#skF_7'!='#skF_6' | '#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.49/1.41  tff(c_77, plain, ('#skF_7'!='#skF_6'), inference(splitLeft, [status(thm)], [c_70])).
% 2.49/1.41  tff(c_136, plain, (![A_63, B_64]: (r1_xboole_0(k1_tarski(A_63), B_64) | r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.49/1.41  tff(c_159, plain, (![B_71, A_72]: (r1_xboole_0(B_71, k1_tarski(A_72)) | r2_hidden(A_72, B_71))), inference(resolution, [status(thm)], [c_136, c_2])).
% 2.49/1.41  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.49/1.41  tff(c_246, plain, (![B_88, A_89]: (k4_xboole_0(B_88, k1_tarski(A_89))=B_88 | r2_hidden(A_89, B_88))), inference(resolution, [status(thm)], [c_159, c_18])).
% 2.49/1.41  tff(c_68, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6') | '#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.49/1.41  tff(c_97, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_68])).
% 2.49/1.41  tff(c_263, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_246, c_97])).
% 2.49/1.41  tff(c_46, plain, (![C_27, A_23]: (C_27=A_23 | ~r2_hidden(C_27, k1_tarski(A_23)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.49/1.41  tff(c_269, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_263, c_46])).
% 2.49/1.41  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_269])).
% 2.49/1.41  tff(c_275, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_68])).
% 2.49/1.41  tff(c_276, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 2.49/1.41  tff(c_72, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6') | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.49/1.41  tff(c_356, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_276, c_72])).
% 2.49/1.41  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_447, c_356])).
% 2.49/1.41  tff(c_461, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_70])).
% 2.49/1.41  tff(c_462, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_70])).
% 2.49/1.41  tff(c_74, plain, ('#skF_7'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.49/1.41  tff(c_548, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_462, c_74])).
% 2.49/1.41  tff(c_646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_643, c_548])).
% 2.49/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.41  
% 2.49/1.41  Inference rules
% 2.49/1.41  ----------------------
% 2.49/1.41  #Ref     : 0
% 2.49/1.41  #Sup     : 134
% 2.49/1.41  #Fact    : 0
% 2.49/1.41  #Define  : 0
% 2.49/1.41  #Split   : 2
% 2.49/1.41  #Chain   : 0
% 2.49/1.41  #Close   : 0
% 2.49/1.41  
% 2.49/1.41  Ordering : KBO
% 2.49/1.41  
% 2.49/1.41  Simplification rules
% 2.49/1.41  ----------------------
% 2.49/1.41  #Subsume      : 13
% 2.49/1.41  #Demod        : 30
% 2.49/1.41  #Tautology    : 72
% 2.49/1.41  #SimpNegUnit  : 3
% 2.49/1.41  #BackRed      : 2
% 2.49/1.41  
% 2.49/1.41  #Partial instantiations: 0
% 2.49/1.41  #Strategies tried      : 1
% 2.49/1.41  
% 2.49/1.41  Timing (in seconds)
% 2.49/1.41  ----------------------
% 2.49/1.41  Preprocessing        : 0.32
% 2.49/1.41  Parsing              : 0.16
% 2.49/1.41  CNF conversion       : 0.03
% 2.49/1.41  Main loop            : 0.27
% 2.49/1.41  Inferencing          : 0.10
% 2.49/1.41  Reduction            : 0.08
% 2.49/1.41  Demodulation         : 0.06
% 2.49/1.41  BG Simplification    : 0.02
% 2.49/1.41  Subsumption          : 0.05
% 2.49/1.42  Abstraction          : 0.02
% 2.49/1.42  MUC search           : 0.00
% 2.49/1.42  Cooper               : 0.00
% 2.49/1.42  Total                : 0.63
% 2.49/1.42  Index Insertion      : 0.00
% 2.49/1.42  Index Deletion       : 0.00
% 2.49/1.42  Index Matching       : 0.00
% 2.49/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
