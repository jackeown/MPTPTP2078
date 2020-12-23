%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:10 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 152 expanded)
%              Number of leaves         :   29 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 236 expanded)
%              Number of equality atoms :   64 ( 164 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_412,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k1_xboole_0
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_416,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_412])).

tff(c_24,plain,(
    ! [B_20] : k4_xboole_0(k1_tarski(B_20),k1_tarski(B_20)) != k1_tarski(B_20) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_417,plain,(
    ! [B_20] : k1_tarski(B_20) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_24])).

tff(c_38,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_1'(A_27),A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_491,plain,(
    ! [A_108,B_109] :
      ( k4_xboole_0(k1_tarski(A_108),k1_tarski(B_109)) = k1_tarski(A_108)
      | B_109 = A_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( ~ r2_hidden(B_22,A_21)
      | k4_xboole_0(A_21,k1_tarski(B_22)) != A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_526,plain,(
    ! [B_110,A_111] :
      ( ~ r2_hidden(B_110,k1_tarski(A_111))
      | B_110 = A_111 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_28])).

tff(c_533,plain,(
    ! [A_111] :
      ( '#skF_1'(k1_tarski(A_111)) = A_111
      | k1_tarski(A_111) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_526])).

tff(c_538,plain,(
    ! [A_111] : '#skF_1'(k1_tarski(A_111)) = A_111 ),
    inference(negUnitSimplification,[status(thm)],[c_417,c_533])).

tff(c_466,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,k1_tarski(B_106)) = A_105
      | r2_hidden(B_106,A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_476,plain,(
    ! [B_106] :
      ( k1_tarski(B_106) = k1_xboole_0
      | r2_hidden(B_106,k1_tarski(B_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_416])).

tff(c_486,plain,(
    ! [B_106] : r2_hidden(B_106,k1_tarski(B_106)) ),
    inference(negUnitSimplification,[status(thm)],[c_417,c_476])).

tff(c_574,plain,(
    ! [D_118,A_119,C_120] :
      ( ~ r2_hidden(D_118,A_119)
      | k4_tarski(C_120,D_118) != '#skF_1'(A_119)
      | k1_xboole_0 = A_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_576,plain,(
    ! [C_120,B_106] :
      ( k4_tarski(C_120,B_106) != '#skF_1'(k1_tarski(B_106))
      | k1_tarski(B_106) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_486,c_574])).

tff(c_580,plain,(
    ! [C_120,B_106] :
      ( k4_tarski(C_120,B_106) != B_106
      | k1_tarski(B_106) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_576])).

tff(c_581,plain,(
    ! [C_120,B_106] : k4_tarski(C_120,B_106) != B_106 ),
    inference(negUnitSimplification,[status(thm)],[c_417,c_580])).

tff(c_134,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_134])).

tff(c_150,plain,(
    ! [B_20] : k1_tarski(B_20) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_24])).

tff(c_253,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(k1_tarski(A_71),k1_tarski(B_72)) = k1_tarski(A_71)
      | B_72 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_287,plain,(
    ! [B_73,A_74] :
      ( ~ r2_hidden(B_73,k1_tarski(A_74))
      | B_73 = A_74 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_28])).

tff(c_294,plain,(
    ! [A_74] :
      ( '#skF_1'(k1_tarski(A_74)) = A_74
      | k1_tarski(A_74) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_287])).

tff(c_299,plain,(
    ! [A_74] : '#skF_1'(k1_tarski(A_74)) = A_74 ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_294])).

tff(c_218,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,k1_tarski(B_66)) = A_65
      | r2_hidden(B_66,A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_228,plain,(
    ! [B_66] :
      ( k1_tarski(B_66) = k1_xboole_0
      | r2_hidden(B_66,k1_tarski(B_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_142])).

tff(c_238,plain,(
    ! [B_66] : r2_hidden(B_66,k1_tarski(B_66)) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_228])).

tff(c_339,plain,(
    ! [C_83,A_84,D_85] :
      ( ~ r2_hidden(C_83,A_84)
      | k4_tarski(C_83,D_85) != '#skF_1'(A_84)
      | k1_xboole_0 = A_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_341,plain,(
    ! [B_66,D_85] :
      ( k4_tarski(B_66,D_85) != '#skF_1'(k1_tarski(B_66))
      | k1_tarski(B_66) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_238,c_339])).

tff(c_345,plain,(
    ! [B_66,D_85] :
      ( k4_tarski(B_66,D_85) != B_66
      | k1_tarski(B_66) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_341])).

tff(c_346,plain,(
    ! [B_66,D_85] : k4_tarski(B_66,D_85) != B_66 ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_345])).

tff(c_46,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_83,plain,(
    ! [A_44,B_45] : k1_mcart_1(k4_tarski(A_44,B_45)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_92,plain,(
    k1_mcart_1('#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_83])).

tff(c_71,plain,(
    ! [A_42,B_43] : k2_mcart_1(k4_tarski(A_42,B_43)) = B_43 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    k2_mcart_1('#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_71])).

tff(c_44,plain,
    ( k2_mcart_1('#skF_2') = '#skF_2'
    | k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_104,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_80,c_44])).

tff(c_105,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_108,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_46])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_108])).

tff(c_350,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_354,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_46])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:47:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.27  
% 2.20/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.28  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.20/1.28  
% 2.20/1.28  %Foreground sorts:
% 2.20/1.28  
% 2.20/1.28  
% 2.20/1.28  %Background operators:
% 2.20/1.28  
% 2.20/1.28  
% 2.20/1.28  %Foreground operators:
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.20/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.20/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.20/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.20/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.28  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.20/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.28  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.20/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.20/1.28  
% 2.20/1.29  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.20/1.29  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.20/1.29  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.20/1.29  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.20/1.29  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.20/1.29  tff(f_89, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.20/1.29  tff(f_63, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.20/1.29  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.29  tff(c_412, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k1_xboole_0 | ~r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.29  tff(c_416, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_412])).
% 2.20/1.29  tff(c_24, plain, (![B_20]: (k4_xboole_0(k1_tarski(B_20), k1_tarski(B_20))!=k1_tarski(B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.20/1.29  tff(c_417, plain, (![B_20]: (k1_tarski(B_20)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_416, c_24])).
% 2.20/1.29  tff(c_38, plain, (![A_27]: (r2_hidden('#skF_1'(A_27), A_27) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.20/1.29  tff(c_491, plain, (![A_108, B_109]: (k4_xboole_0(k1_tarski(A_108), k1_tarski(B_109))=k1_tarski(A_108) | B_109=A_108)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.20/1.29  tff(c_28, plain, (![B_22, A_21]: (~r2_hidden(B_22, A_21) | k4_xboole_0(A_21, k1_tarski(B_22))!=A_21)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.29  tff(c_526, plain, (![B_110, A_111]: (~r2_hidden(B_110, k1_tarski(A_111)) | B_110=A_111)), inference(superposition, [status(thm), theory('equality')], [c_491, c_28])).
% 2.20/1.29  tff(c_533, plain, (![A_111]: ('#skF_1'(k1_tarski(A_111))=A_111 | k1_tarski(A_111)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_526])).
% 2.20/1.29  tff(c_538, plain, (![A_111]: ('#skF_1'(k1_tarski(A_111))=A_111)), inference(negUnitSimplification, [status(thm)], [c_417, c_533])).
% 2.20/1.29  tff(c_466, plain, (![A_105, B_106]: (k4_xboole_0(A_105, k1_tarski(B_106))=A_105 | r2_hidden(B_106, A_105))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.29  tff(c_476, plain, (![B_106]: (k1_tarski(B_106)=k1_xboole_0 | r2_hidden(B_106, k1_tarski(B_106)))), inference(superposition, [status(thm), theory('equality')], [c_466, c_416])).
% 2.20/1.29  tff(c_486, plain, (![B_106]: (r2_hidden(B_106, k1_tarski(B_106)))), inference(negUnitSimplification, [status(thm)], [c_417, c_476])).
% 2.20/1.29  tff(c_574, plain, (![D_118, A_119, C_120]: (~r2_hidden(D_118, A_119) | k4_tarski(C_120, D_118)!='#skF_1'(A_119) | k1_xboole_0=A_119)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.20/1.29  tff(c_576, plain, (![C_120, B_106]: (k4_tarski(C_120, B_106)!='#skF_1'(k1_tarski(B_106)) | k1_tarski(B_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_486, c_574])).
% 2.20/1.29  tff(c_580, plain, (![C_120, B_106]: (k4_tarski(C_120, B_106)!=B_106 | k1_tarski(B_106)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_538, c_576])).
% 2.20/1.29  tff(c_581, plain, (![C_120, B_106]: (k4_tarski(C_120, B_106)!=B_106)), inference(negUnitSimplification, [status(thm)], [c_417, c_580])).
% 2.20/1.29  tff(c_134, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=k1_xboole_0 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.29  tff(c_142, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_134])).
% 2.20/1.29  tff(c_150, plain, (![B_20]: (k1_tarski(B_20)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_24])).
% 2.20/1.29  tff(c_253, plain, (![A_71, B_72]: (k4_xboole_0(k1_tarski(A_71), k1_tarski(B_72))=k1_tarski(A_71) | B_72=A_71)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.20/1.29  tff(c_287, plain, (![B_73, A_74]: (~r2_hidden(B_73, k1_tarski(A_74)) | B_73=A_74)), inference(superposition, [status(thm), theory('equality')], [c_253, c_28])).
% 2.20/1.29  tff(c_294, plain, (![A_74]: ('#skF_1'(k1_tarski(A_74))=A_74 | k1_tarski(A_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_287])).
% 2.20/1.29  tff(c_299, plain, (![A_74]: ('#skF_1'(k1_tarski(A_74))=A_74)), inference(negUnitSimplification, [status(thm)], [c_150, c_294])).
% 2.20/1.29  tff(c_218, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k1_tarski(B_66))=A_65 | r2_hidden(B_66, A_65))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.29  tff(c_228, plain, (![B_66]: (k1_tarski(B_66)=k1_xboole_0 | r2_hidden(B_66, k1_tarski(B_66)))), inference(superposition, [status(thm), theory('equality')], [c_218, c_142])).
% 2.20/1.29  tff(c_238, plain, (![B_66]: (r2_hidden(B_66, k1_tarski(B_66)))), inference(negUnitSimplification, [status(thm)], [c_150, c_228])).
% 2.20/1.29  tff(c_339, plain, (![C_83, A_84, D_85]: (~r2_hidden(C_83, A_84) | k4_tarski(C_83, D_85)!='#skF_1'(A_84) | k1_xboole_0=A_84)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.20/1.29  tff(c_341, plain, (![B_66, D_85]: (k4_tarski(B_66, D_85)!='#skF_1'(k1_tarski(B_66)) | k1_tarski(B_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_238, c_339])).
% 2.20/1.29  tff(c_345, plain, (![B_66, D_85]: (k4_tarski(B_66, D_85)!=B_66 | k1_tarski(B_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_299, c_341])).
% 2.20/1.29  tff(c_346, plain, (![B_66, D_85]: (k4_tarski(B_66, D_85)!=B_66)), inference(negUnitSimplification, [status(thm)], [c_150, c_345])).
% 2.20/1.29  tff(c_46, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.20/1.29  tff(c_83, plain, (![A_44, B_45]: (k1_mcart_1(k4_tarski(A_44, B_45))=A_44)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.20/1.29  tff(c_92, plain, (k1_mcart_1('#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_46, c_83])).
% 2.20/1.29  tff(c_71, plain, (![A_42, B_43]: (k2_mcart_1(k4_tarski(A_42, B_43))=B_43)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.20/1.29  tff(c_80, plain, (k2_mcart_1('#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_46, c_71])).
% 2.20/1.29  tff(c_44, plain, (k2_mcart_1('#skF_2')='#skF_2' | k1_mcart_1('#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.20/1.29  tff(c_104, plain, ('#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_80, c_44])).
% 2.20/1.29  tff(c_105, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_104])).
% 2.20/1.29  tff(c_108, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_46])).
% 2.20/1.29  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_346, c_108])).
% 2.20/1.29  tff(c_350, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_104])).
% 2.20/1.29  tff(c_354, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_350, c_46])).
% 2.20/1.29  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_581, c_354])).
% 2.20/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.29  
% 2.20/1.29  Inference rules
% 2.20/1.29  ----------------------
% 2.20/1.29  #Ref     : 0
% 2.20/1.29  #Sup     : 123
% 2.20/1.29  #Fact    : 0
% 2.20/1.29  #Define  : 0
% 2.20/1.29  #Split   : 1
% 2.20/1.29  #Chain   : 0
% 2.20/1.29  #Close   : 0
% 2.20/1.29  
% 2.20/1.29  Ordering : KBO
% 2.20/1.29  
% 2.20/1.29  Simplification rules
% 2.20/1.29  ----------------------
% 2.20/1.29  #Subsume      : 2
% 2.20/1.29  #Demod        : 31
% 2.20/1.29  #Tautology    : 97
% 2.20/1.29  #SimpNegUnit  : 17
% 2.20/1.29  #BackRed      : 9
% 2.20/1.29  
% 2.20/1.29  #Partial instantiations: 0
% 2.20/1.29  #Strategies tried      : 1
% 2.20/1.29  
% 2.20/1.29  Timing (in seconds)
% 2.20/1.29  ----------------------
% 2.20/1.29  Preprocessing        : 0.31
% 2.20/1.29  Parsing              : 0.17
% 2.20/1.29  CNF conversion       : 0.02
% 2.20/1.29  Main loop            : 0.22
% 2.20/1.29  Inferencing          : 0.09
% 2.20/1.30  Reduction            : 0.07
% 2.20/1.30  Demodulation         : 0.05
% 2.20/1.30  BG Simplification    : 0.01
% 2.20/1.30  Subsumption          : 0.03
% 2.20/1.30  Abstraction          : 0.02
% 2.20/1.30  MUC search           : 0.00
% 2.20/1.30  Cooper               : 0.00
% 2.20/1.30  Total                : 0.57
% 2.20/1.30  Index Insertion      : 0.00
% 2.20/1.30  Index Deletion       : 0.00
% 2.20/1.30  Index Matching       : 0.00
% 2.20/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
