%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:18 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 153 expanded)
%              Number of leaves         :   30 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 204 expanded)
%              Number of equality atoms :   65 ( 172 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_82,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_425,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k2_xboole_0(A_94,B_95)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_432,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_425])).

tff(c_20,plain,(
    ! [B_21] : k4_xboole_0(k1_tarski(B_21),k1_tarski(B_21)) != k1_tarski(B_21) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_496,plain,(
    ! [B_21] : k1_tarski(B_21) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_20])).

tff(c_40,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_1'(A_31),A_31)
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_619,plain,(
    ! [A_122,B_123] :
      ( k4_xboole_0(k1_tarski(A_122),k1_tarski(B_123)) = k1_tarski(A_122)
      | B_123 = A_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( ~ r2_hidden(B_26,A_25)
      | k4_xboole_0(A_25,k1_tarski(B_26)) != A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_659,plain,(
    ! [B_124,A_125] :
      ( ~ r2_hidden(B_124,k1_tarski(A_125))
      | B_124 = A_125 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_30])).

tff(c_666,plain,(
    ! [A_125] :
      ( '#skF_1'(k1_tarski(A_125)) = A_125
      | k1_tarski(A_125) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_659])).

tff(c_671,plain,(
    ! [A_125] : '#skF_1'(k1_tarski(A_125)) = A_125 ),
    inference(negUnitSimplification,[status(thm)],[c_496,c_666])).

tff(c_539,plain,(
    ! [A_110,B_111] :
      ( k4_xboole_0(A_110,k1_tarski(B_111)) = A_110
      | r2_hidden(B_111,A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_546,plain,(
    ! [B_111] :
      ( k1_tarski(B_111) = k1_xboole_0
      | r2_hidden(B_111,k1_tarski(B_111)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_432])).

tff(c_558,plain,(
    ! [B_111] : r2_hidden(B_111,k1_tarski(B_111)) ),
    inference(negUnitSimplification,[status(thm)],[c_496,c_546])).

tff(c_695,plain,(
    ! [D_130,A_131,C_132] :
      ( ~ r2_hidden(D_130,A_131)
      | k4_tarski(C_132,D_130) != '#skF_1'(A_131)
      | k1_xboole_0 = A_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_697,plain,(
    ! [C_132,B_111] :
      ( k4_tarski(C_132,B_111) != '#skF_1'(k1_tarski(B_111))
      | k1_tarski(B_111) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_558,c_695])).

tff(c_701,plain,(
    ! [C_132,B_111] :
      ( k4_tarski(C_132,B_111) != B_111
      | k1_tarski(B_111) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_697])).

tff(c_702,plain,(
    ! [C_132,B_111] : k4_tarski(C_132,B_111) != B_111 ),
    inference(negUnitSimplification,[status(thm)],[c_496,c_701])).

tff(c_141,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k2_xboole_0(A_50,B_51)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_148,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_141])).

tff(c_183,plain,(
    ! [B_21] : k1_tarski(B_21) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_20])).

tff(c_315,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(k1_tarski(A_78),k1_tarski(B_79)) = k1_tarski(A_78)
      | B_79 = A_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_355,plain,(
    ! [B_80,A_81] :
      ( ~ r2_hidden(B_80,k1_tarski(A_81))
      | B_80 = A_81 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_30])).

tff(c_362,plain,(
    ! [A_81] :
      ( '#skF_1'(k1_tarski(A_81)) = A_81
      | k1_tarski(A_81) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_355])).

tff(c_367,plain,(
    ! [A_81] : '#skF_1'(k1_tarski(A_81)) = A_81 ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_362])).

tff(c_246,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,k1_tarski(B_68)) = A_67
      | r2_hidden(B_68,A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_256,plain,(
    ! [B_68] :
      ( k1_tarski(B_68) = k1_xboole_0
      | r2_hidden(B_68,k1_tarski(B_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_148])).

tff(c_265,plain,(
    ! [B_68] : r2_hidden(B_68,k1_tarski(B_68)) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_256])).

tff(c_404,plain,(
    ! [C_91,A_92,D_93] :
      ( ~ r2_hidden(C_91,A_92)
      | k4_tarski(C_91,D_93) != '#skF_1'(A_92)
      | k1_xboole_0 = A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_406,plain,(
    ! [B_68,D_93] :
      ( k4_tarski(B_68,D_93) != '#skF_1'(k1_tarski(B_68))
      | k1_tarski(B_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_265,c_404])).

tff(c_410,plain,(
    ! [B_68,D_93] :
      ( k4_tarski(B_68,D_93) != B_68
      | k1_tarski(B_68) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_406])).

tff(c_411,plain,(
    ! [B_68,D_93] : k4_tarski(B_68,D_93) != B_68 ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_410])).

tff(c_48,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_92,plain,(
    ! [A_48,B_49] : k1_mcart_1(k4_tarski(A_48,B_49)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_101,plain,(
    k1_mcart_1('#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_92])).

tff(c_80,plain,(
    ! [A_46,B_47] : k2_mcart_1(k4_tarski(A_46,B_47)) = B_47 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_89,plain,(
    k2_mcart_1('#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_80])).

tff(c_46,plain,
    ( k2_mcart_1('#skF_2') = '#skF_2'
    | k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_112,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_89,c_46])).

tff(c_113,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_116,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_48])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_116])).

tff(c_415,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_419,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_48])).

tff(c_705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_702,c_419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.33  
% 2.20/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.33  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.20/1.33  
% 2.20/1.33  %Foreground sorts:
% 2.20/1.33  
% 2.20/1.33  
% 2.20/1.33  %Background operators:
% 2.20/1.33  
% 2.20/1.33  
% 2.20/1.33  %Foreground operators:
% 2.20/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.20/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.20/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.20/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.20/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.33  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.20/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.20/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.33  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.20/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.20/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.20/1.33  
% 2.64/1.35  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.64/1.35  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.64/1.35  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.64/1.35  tff(f_82, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.64/1.35  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.64/1.35  tff(f_92, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.64/1.35  tff(f_66, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.64/1.35  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.35  tff(c_425, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k2_xboole_0(A_94, B_95))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.35  tff(c_432, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_425])).
% 2.64/1.35  tff(c_20, plain, (![B_21]: (k4_xboole_0(k1_tarski(B_21), k1_tarski(B_21))!=k1_tarski(B_21))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.64/1.35  tff(c_496, plain, (![B_21]: (k1_tarski(B_21)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_432, c_20])).
% 2.64/1.35  tff(c_40, plain, (![A_31]: (r2_hidden('#skF_1'(A_31), A_31) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.64/1.35  tff(c_619, plain, (![A_122, B_123]: (k4_xboole_0(k1_tarski(A_122), k1_tarski(B_123))=k1_tarski(A_122) | B_123=A_122)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.64/1.35  tff(c_30, plain, (![B_26, A_25]: (~r2_hidden(B_26, A_25) | k4_xboole_0(A_25, k1_tarski(B_26))!=A_25)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.64/1.35  tff(c_659, plain, (![B_124, A_125]: (~r2_hidden(B_124, k1_tarski(A_125)) | B_124=A_125)), inference(superposition, [status(thm), theory('equality')], [c_619, c_30])).
% 2.64/1.35  tff(c_666, plain, (![A_125]: ('#skF_1'(k1_tarski(A_125))=A_125 | k1_tarski(A_125)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_659])).
% 2.64/1.35  tff(c_671, plain, (![A_125]: ('#skF_1'(k1_tarski(A_125))=A_125)), inference(negUnitSimplification, [status(thm)], [c_496, c_666])).
% 2.64/1.35  tff(c_539, plain, (![A_110, B_111]: (k4_xboole_0(A_110, k1_tarski(B_111))=A_110 | r2_hidden(B_111, A_110))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.64/1.35  tff(c_546, plain, (![B_111]: (k1_tarski(B_111)=k1_xboole_0 | r2_hidden(B_111, k1_tarski(B_111)))), inference(superposition, [status(thm), theory('equality')], [c_539, c_432])).
% 2.64/1.35  tff(c_558, plain, (![B_111]: (r2_hidden(B_111, k1_tarski(B_111)))), inference(negUnitSimplification, [status(thm)], [c_496, c_546])).
% 2.64/1.35  tff(c_695, plain, (![D_130, A_131, C_132]: (~r2_hidden(D_130, A_131) | k4_tarski(C_132, D_130)!='#skF_1'(A_131) | k1_xboole_0=A_131)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.64/1.35  tff(c_697, plain, (![C_132, B_111]: (k4_tarski(C_132, B_111)!='#skF_1'(k1_tarski(B_111)) | k1_tarski(B_111)=k1_xboole_0)), inference(resolution, [status(thm)], [c_558, c_695])).
% 2.64/1.35  tff(c_701, plain, (![C_132, B_111]: (k4_tarski(C_132, B_111)!=B_111 | k1_tarski(B_111)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_671, c_697])).
% 2.64/1.35  tff(c_702, plain, (![C_132, B_111]: (k4_tarski(C_132, B_111)!=B_111)), inference(negUnitSimplification, [status(thm)], [c_496, c_701])).
% 2.64/1.35  tff(c_141, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k2_xboole_0(A_50, B_51))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.35  tff(c_148, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_141])).
% 2.64/1.35  tff(c_183, plain, (![B_21]: (k1_tarski(B_21)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_20])).
% 2.64/1.35  tff(c_315, plain, (![A_78, B_79]: (k4_xboole_0(k1_tarski(A_78), k1_tarski(B_79))=k1_tarski(A_78) | B_79=A_78)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.64/1.35  tff(c_355, plain, (![B_80, A_81]: (~r2_hidden(B_80, k1_tarski(A_81)) | B_80=A_81)), inference(superposition, [status(thm), theory('equality')], [c_315, c_30])).
% 2.64/1.35  tff(c_362, plain, (![A_81]: ('#skF_1'(k1_tarski(A_81))=A_81 | k1_tarski(A_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_355])).
% 2.64/1.35  tff(c_367, plain, (![A_81]: ('#skF_1'(k1_tarski(A_81))=A_81)), inference(negUnitSimplification, [status(thm)], [c_183, c_362])).
% 2.64/1.35  tff(c_246, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k1_tarski(B_68))=A_67 | r2_hidden(B_68, A_67))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.64/1.35  tff(c_256, plain, (![B_68]: (k1_tarski(B_68)=k1_xboole_0 | r2_hidden(B_68, k1_tarski(B_68)))), inference(superposition, [status(thm), theory('equality')], [c_246, c_148])).
% 2.64/1.35  tff(c_265, plain, (![B_68]: (r2_hidden(B_68, k1_tarski(B_68)))), inference(negUnitSimplification, [status(thm)], [c_183, c_256])).
% 2.64/1.35  tff(c_404, plain, (![C_91, A_92, D_93]: (~r2_hidden(C_91, A_92) | k4_tarski(C_91, D_93)!='#skF_1'(A_92) | k1_xboole_0=A_92)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.64/1.35  tff(c_406, plain, (![B_68, D_93]: (k4_tarski(B_68, D_93)!='#skF_1'(k1_tarski(B_68)) | k1_tarski(B_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_265, c_404])).
% 2.64/1.35  tff(c_410, plain, (![B_68, D_93]: (k4_tarski(B_68, D_93)!=B_68 | k1_tarski(B_68)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_367, c_406])).
% 2.64/1.35  tff(c_411, plain, (![B_68, D_93]: (k4_tarski(B_68, D_93)!=B_68)), inference(negUnitSimplification, [status(thm)], [c_183, c_410])).
% 2.64/1.35  tff(c_48, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.64/1.35  tff(c_92, plain, (![A_48, B_49]: (k1_mcart_1(k4_tarski(A_48, B_49))=A_48)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.64/1.35  tff(c_101, plain, (k1_mcart_1('#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_48, c_92])).
% 2.64/1.35  tff(c_80, plain, (![A_46, B_47]: (k2_mcart_1(k4_tarski(A_46, B_47))=B_47)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.64/1.35  tff(c_89, plain, (k2_mcart_1('#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_48, c_80])).
% 2.64/1.35  tff(c_46, plain, (k2_mcart_1('#skF_2')='#skF_2' | k1_mcart_1('#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.64/1.35  tff(c_112, plain, ('#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_89, c_46])).
% 2.64/1.35  tff(c_113, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_112])).
% 2.64/1.35  tff(c_116, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_48])).
% 2.64/1.35  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_411, c_116])).
% 2.64/1.35  tff(c_415, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_112])).
% 2.64/1.35  tff(c_419, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_415, c_48])).
% 2.64/1.35  tff(c_705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_702, c_419])).
% 2.64/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.35  
% 2.64/1.35  Inference rules
% 2.64/1.35  ----------------------
% 2.64/1.35  #Ref     : 0
% 2.64/1.35  #Sup     : 157
% 2.64/1.35  #Fact    : 0
% 2.64/1.35  #Define  : 0
% 2.64/1.35  #Split   : 1
% 2.64/1.35  #Chain   : 0
% 2.64/1.35  #Close   : 0
% 2.64/1.35  
% 2.64/1.35  Ordering : KBO
% 2.64/1.35  
% 2.64/1.35  Simplification rules
% 2.64/1.35  ----------------------
% 2.64/1.35  #Subsume      : 7
% 2.64/1.35  #Demod        : 30
% 2.64/1.35  #Tautology    : 122
% 2.64/1.35  #SimpNegUnit  : 17
% 2.64/1.35  #BackRed      : 8
% 2.64/1.35  
% 2.64/1.35  #Partial instantiations: 0
% 2.64/1.35  #Strategies tried      : 1
% 2.64/1.35  
% 2.64/1.35  Timing (in seconds)
% 2.64/1.35  ----------------------
% 2.64/1.35  Preprocessing        : 0.32
% 2.64/1.35  Parsing              : 0.17
% 2.64/1.35  CNF conversion       : 0.02
% 2.64/1.35  Main loop            : 0.26
% 2.64/1.35  Inferencing          : 0.11
% 2.64/1.35  Reduction            : 0.08
% 2.64/1.35  Demodulation         : 0.05
% 2.64/1.35  BG Simplification    : 0.02
% 2.64/1.35  Subsumption          : 0.04
% 2.64/1.35  Abstraction          : 0.02
% 2.64/1.35  MUC search           : 0.00
% 2.64/1.35  Cooper               : 0.00
% 2.64/1.35  Total                : 0.62
% 2.64/1.35  Index Insertion      : 0.00
% 2.64/1.35  Index Deletion       : 0.00
% 2.64/1.35  Index Matching       : 0.00
% 2.64/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
