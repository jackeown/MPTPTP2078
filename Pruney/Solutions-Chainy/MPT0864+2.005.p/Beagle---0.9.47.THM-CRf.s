%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:09 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 118 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 176 expanded)
%              Number of equality atoms :   57 ( 130 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_81,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_322,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,B_83) = k1_xboole_0
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_326,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_322])).

tff(c_36,plain,(
    ! [B_25] : k4_xboole_0(k1_tarski(B_25),k1_tarski(B_25)) != k1_tarski(B_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_334,plain,(
    ! [B_25] : k1_tarski(B_25) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_36])).

tff(c_46,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_3'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_311,plain,(
    ! [C_80,A_81] :
      ( C_80 = A_81
      | ~ r2_hidden(C_80,k1_tarski(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_319,plain,(
    ! [A_81] :
      ( '#skF_3'(k1_tarski(A_81)) = A_81
      | k1_tarski(A_81) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_311])).

tff(c_372,plain,(
    ! [A_81] : '#skF_3'(k1_tarski(A_81)) = A_81 ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_319])).

tff(c_18,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_460,plain,(
    ! [D_106,A_107,C_108] :
      ( ~ r2_hidden(D_106,A_107)
      | k4_tarski(C_108,D_106) != '#skF_3'(A_107)
      | k1_xboole_0 = A_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_464,plain,(
    ! [C_108,C_13] :
      ( k4_tarski(C_108,C_13) != '#skF_3'(k1_tarski(C_13))
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_460])).

tff(c_467,plain,(
    ! [C_108,C_13] :
      ( k4_tarski(C_108,C_13) != C_13
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_464])).

tff(c_468,plain,(
    ! [C_108,C_13] : k4_tarski(C_108,C_13) != C_13 ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_467])).

tff(c_172,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k1_xboole_0
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_172])).

tff(c_181,plain,(
    ! [B_25] : k1_tarski(B_25) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_36])).

tff(c_142,plain,(
    ! [A_52] :
      ( r2_hidden('#skF_3'(A_52),A_52)
      | k1_xboole_0 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_147,plain,(
    ! [A_9] :
      ( '#skF_3'(k1_tarski(A_9)) = A_9
      | k1_tarski(A_9) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_142,c_16])).

tff(c_199,plain,(
    ! [A_9] : '#skF_3'(k1_tarski(A_9)) = A_9 ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_147])).

tff(c_275,plain,(
    ! [C_76,A_77,D_78] :
      ( ~ r2_hidden(C_76,A_77)
      | k4_tarski(C_76,D_78) != '#skF_3'(A_77)
      | k1_xboole_0 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_279,plain,(
    ! [C_13,D_78] :
      ( k4_tarski(C_13,D_78) != '#skF_3'(k1_tarski(C_13))
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_275])).

tff(c_282,plain,(
    ! [C_13,D_78] :
      ( k4_tarski(C_13,D_78) != C_13
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_279])).

tff(c_283,plain,(
    ! [C_13,D_78] : k4_tarski(C_13,D_78) != C_13 ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_282])).

tff(c_54,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_83,plain,(
    ! [A_47,B_48] : k1_mcart_1(k4_tarski(A_47,B_48)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_92,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_83])).

tff(c_71,plain,(
    ! [A_45,B_46] : k2_mcart_1(k4_tarski(A_45,B_46)) = B_46 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_80,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_71])).

tff(c_52,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_112,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_80,c_52])).

tff(c_113,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_115,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_54])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_283,c_115])).

tff(c_286,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_289,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_54])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_468,c_289])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:29:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.26  
% 2.16/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.26  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.16/1.26  
% 2.16/1.26  %Foreground sorts:
% 2.16/1.26  
% 2.16/1.26  
% 2.16/1.26  %Background operators:
% 2.16/1.26  
% 2.16/1.26  
% 2.16/1.26  %Foreground operators:
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.16/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.16/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.26  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.16/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.26  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.16/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.26  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.16/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.16/1.26  
% 2.16/1.27  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.27  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.16/1.27  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.16/1.27  tff(f_81, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.16/1.27  tff(f_46, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.16/1.27  tff(f_91, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.16/1.27  tff(f_65, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.16/1.27  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.27  tff(c_322, plain, (![A_82, B_83]: (k4_xboole_0(A_82, B_83)=k1_xboole_0 | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.27  tff(c_326, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_322])).
% 2.16/1.27  tff(c_36, plain, (![B_25]: (k4_xboole_0(k1_tarski(B_25), k1_tarski(B_25))!=k1_tarski(B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.27  tff(c_334, plain, (![B_25]: (k1_tarski(B_25)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_326, c_36])).
% 2.16/1.27  tff(c_46, plain, (![A_30]: (r2_hidden('#skF_3'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.16/1.27  tff(c_311, plain, (![C_80, A_81]: (C_80=A_81 | ~r2_hidden(C_80, k1_tarski(A_81)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.16/1.27  tff(c_319, plain, (![A_81]: ('#skF_3'(k1_tarski(A_81))=A_81 | k1_tarski(A_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_311])).
% 2.16/1.27  tff(c_372, plain, (![A_81]: ('#skF_3'(k1_tarski(A_81))=A_81)), inference(negUnitSimplification, [status(thm)], [c_334, c_319])).
% 2.16/1.27  tff(c_18, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.16/1.27  tff(c_460, plain, (![D_106, A_107, C_108]: (~r2_hidden(D_106, A_107) | k4_tarski(C_108, D_106)!='#skF_3'(A_107) | k1_xboole_0=A_107)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.16/1.27  tff(c_464, plain, (![C_108, C_13]: (k4_tarski(C_108, C_13)!='#skF_3'(k1_tarski(C_13)) | k1_tarski(C_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_460])).
% 2.16/1.27  tff(c_467, plain, (![C_108, C_13]: (k4_tarski(C_108, C_13)!=C_13 | k1_tarski(C_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_372, c_464])).
% 2.16/1.27  tff(c_468, plain, (![C_108, C_13]: (k4_tarski(C_108, C_13)!=C_13)), inference(negUnitSimplification, [status(thm)], [c_334, c_467])).
% 2.16/1.27  tff(c_172, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k1_xboole_0 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.27  tff(c_180, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_172])).
% 2.16/1.27  tff(c_181, plain, (![B_25]: (k1_tarski(B_25)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_180, c_36])).
% 2.16/1.27  tff(c_142, plain, (![A_52]: (r2_hidden('#skF_3'(A_52), A_52) | k1_xboole_0=A_52)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.16/1.27  tff(c_16, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.16/1.27  tff(c_147, plain, (![A_9]: ('#skF_3'(k1_tarski(A_9))=A_9 | k1_tarski(A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_142, c_16])).
% 2.16/1.27  tff(c_199, plain, (![A_9]: ('#skF_3'(k1_tarski(A_9))=A_9)), inference(negUnitSimplification, [status(thm)], [c_181, c_147])).
% 2.16/1.27  tff(c_275, plain, (![C_76, A_77, D_78]: (~r2_hidden(C_76, A_77) | k4_tarski(C_76, D_78)!='#skF_3'(A_77) | k1_xboole_0=A_77)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.16/1.27  tff(c_279, plain, (![C_13, D_78]: (k4_tarski(C_13, D_78)!='#skF_3'(k1_tarski(C_13)) | k1_tarski(C_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_275])).
% 2.16/1.27  tff(c_282, plain, (![C_13, D_78]: (k4_tarski(C_13, D_78)!=C_13 | k1_tarski(C_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_199, c_279])).
% 2.16/1.27  tff(c_283, plain, (![C_13, D_78]: (k4_tarski(C_13, D_78)!=C_13)), inference(negUnitSimplification, [status(thm)], [c_181, c_282])).
% 2.16/1.27  tff(c_54, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.16/1.27  tff(c_83, plain, (![A_47, B_48]: (k1_mcart_1(k4_tarski(A_47, B_48))=A_47)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.16/1.27  tff(c_92, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_54, c_83])).
% 2.16/1.27  tff(c_71, plain, (![A_45, B_46]: (k2_mcart_1(k4_tarski(A_45, B_46))=B_46)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.16/1.27  tff(c_80, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_54, c_71])).
% 2.16/1.27  tff(c_52, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.16/1.27  tff(c_112, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_80, c_52])).
% 2.16/1.27  tff(c_113, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_112])).
% 2.16/1.27  tff(c_115, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_54])).
% 2.16/1.27  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_283, c_115])).
% 2.16/1.27  tff(c_286, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_112])).
% 2.16/1.27  tff(c_289, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_54])).
% 2.16/1.27  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_468, c_289])).
% 2.16/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.27  
% 2.16/1.27  Inference rules
% 2.16/1.27  ----------------------
% 2.16/1.27  #Ref     : 0
% 2.16/1.27  #Sup     : 96
% 2.16/1.27  #Fact    : 0
% 2.16/1.27  #Define  : 0
% 2.16/1.27  #Split   : 1
% 2.16/1.27  #Chain   : 0
% 2.16/1.27  #Close   : 0
% 2.16/1.27  
% 2.16/1.27  Ordering : KBO
% 2.16/1.27  
% 2.16/1.27  Simplification rules
% 2.16/1.27  ----------------------
% 2.16/1.27  #Subsume      : 0
% 2.16/1.27  #Demod        : 24
% 2.16/1.27  #Tautology    : 80
% 2.16/1.27  #SimpNegUnit  : 12
% 2.16/1.27  #BackRed      : 7
% 2.16/1.27  
% 2.16/1.27  #Partial instantiations: 0
% 2.16/1.27  #Strategies tried      : 1
% 2.16/1.27  
% 2.16/1.27  Timing (in seconds)
% 2.16/1.27  ----------------------
% 2.16/1.28  Preprocessing        : 0.31
% 2.16/1.28  Parsing              : 0.16
% 2.16/1.28  CNF conversion       : 0.02
% 2.16/1.28  Main loop            : 0.20
% 2.16/1.28  Inferencing          : 0.08
% 2.16/1.28  Reduction            : 0.06
% 2.16/1.28  Demodulation         : 0.04
% 2.16/1.28  BG Simplification    : 0.01
% 2.16/1.28  Subsumption          : 0.03
% 2.16/1.28  Abstraction          : 0.01
% 2.16/1.28  MUC search           : 0.00
% 2.16/1.28  Cooper               : 0.00
% 2.16/1.28  Total                : 0.54
% 2.16/1.28  Index Insertion      : 0.00
% 2.16/1.28  Index Deletion       : 0.00
% 2.16/1.28  Index Matching       : 0.00
% 2.16/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
