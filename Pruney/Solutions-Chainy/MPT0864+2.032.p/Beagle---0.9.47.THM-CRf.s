%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:12 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 118 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 160 expanded)
%              Number of equality atoms :   58 ( 134 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_356,plain,(
    ! [A_81,B_82] : k2_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = A_81 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_362,plain,(
    ! [A_81] : k4_xboole_0(A_81,A_81) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_8])).

tff(c_30,plain,(
    ! [B_23] : k4_xboole_0(k1_tarski(B_23),k1_tarski(B_23)) != k1_tarski(B_23) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_372,plain,(
    ! [B_23] : k1_tarski(B_23) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_30])).

tff(c_40,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_3'(A_28),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_326,plain,(
    ! [C_77,A_78] :
      ( C_77 = A_78
      | ~ r2_hidden(C_77,k1_tarski(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_334,plain,(
    ! [A_78] :
      ( '#skF_3'(k1_tarski(A_78)) = A_78
      | k1_tarski(A_78) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_326])).

tff(c_447,plain,(
    ! [A_78] : '#skF_3'(k1_tarski(A_78)) = A_78 ),
    inference(negUnitSimplification,[status(thm)],[c_372,c_334])).

tff(c_12,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_526,plain,(
    ! [D_109,A_110,C_111] :
      ( ~ r2_hidden(D_109,A_110)
      | k4_tarski(C_111,D_109) != '#skF_3'(A_110)
      | k1_xboole_0 = A_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_530,plain,(
    ! [C_111,C_13] :
      ( k4_tarski(C_111,C_13) != '#skF_3'(k1_tarski(C_13))
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_526])).

tff(c_533,plain,(
    ! [C_111,C_13] :
      ( k4_tarski(C_111,C_13) != C_13
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_530])).

tff(c_534,plain,(
    ! [C_111,C_13] : k4_tarski(C_111,C_13) != C_13 ),
    inference(negUnitSimplification,[status(thm)],[c_372,c_533])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k2_xboole_0(A_53,B_54)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_171,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_161])).

tff(c_204,plain,(
    ! [B_23] : k1_tarski(B_23) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_30])).

tff(c_150,plain,(
    ! [C_51,A_52] :
      ( C_51 = A_52
      | ~ r2_hidden(C_51,k1_tarski(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_158,plain,(
    ! [A_52] :
      ( '#skF_3'(k1_tarski(A_52)) = A_52
      | k1_tarski(A_52) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_150])).

tff(c_257,plain,(
    ! [A_52] : '#skF_3'(k1_tarski(A_52)) = A_52 ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_158])).

tff(c_303,plain,(
    ! [C_74,A_75,D_76] :
      ( ~ r2_hidden(C_74,A_75)
      | k4_tarski(C_74,D_76) != '#skF_3'(A_75)
      | k1_xboole_0 = A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_307,plain,(
    ! [C_13,D_76] :
      ( k4_tarski(C_13,D_76) != '#skF_3'(k1_tarski(C_13))
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_303])).

tff(c_310,plain,(
    ! [C_13,D_76] :
      ( k4_tarski(C_13,D_76) != C_13
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_307])).

tff(c_311,plain,(
    ! [C_13,D_76] : k4_tarski(C_13,D_76) != C_13 ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_310])).

tff(c_48,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_79,plain,(
    ! [A_44,B_45] : k1_mcart_1(k4_tarski(A_44,B_45)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_79])).

tff(c_63,plain,(
    ! [A_42,B_43] : k2_mcart_1(k4_tarski(A_42,B_43)) = B_43 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_63])).

tff(c_46,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_105,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_72,c_46])).

tff(c_106,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_108,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_48])).

tff(c_313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_108])).

tff(c_314,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_317,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_48])).

tff(c_536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:03:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.33  
% 2.48/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.33  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.48/1.33  
% 2.48/1.33  %Foreground sorts:
% 2.48/1.33  
% 2.48/1.33  
% 2.48/1.33  %Background operators:
% 2.48/1.33  
% 2.48/1.33  
% 2.48/1.33  %Foreground operators:
% 2.48/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.48/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.48/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.33  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.48/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.48/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.33  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.48/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.48/1.33  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.48/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.48/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.48/1.33  
% 2.48/1.34  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.48/1.34  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.48/1.34  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.48/1.34  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.48/1.34  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.48/1.34  tff(f_85, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.48/1.34  tff(f_59, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.48/1.34  tff(c_356, plain, (![A_81, B_82]: (k2_xboole_0(A_81, k3_xboole_0(A_81, B_82))=A_81)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.34  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.48/1.34  tff(c_362, plain, (![A_81]: (k4_xboole_0(A_81, A_81)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_356, c_8])).
% 2.48/1.34  tff(c_30, plain, (![B_23]: (k4_xboole_0(k1_tarski(B_23), k1_tarski(B_23))!=k1_tarski(B_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.48/1.34  tff(c_372, plain, (![B_23]: (k1_tarski(B_23)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_362, c_30])).
% 2.48/1.34  tff(c_40, plain, (![A_28]: (r2_hidden('#skF_3'(A_28), A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.48/1.34  tff(c_326, plain, (![C_77, A_78]: (C_77=A_78 | ~r2_hidden(C_77, k1_tarski(A_78)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.48/1.34  tff(c_334, plain, (![A_78]: ('#skF_3'(k1_tarski(A_78))=A_78 | k1_tarski(A_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_326])).
% 2.48/1.34  tff(c_447, plain, (![A_78]: ('#skF_3'(k1_tarski(A_78))=A_78)), inference(negUnitSimplification, [status(thm)], [c_372, c_334])).
% 2.48/1.34  tff(c_12, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.48/1.34  tff(c_526, plain, (![D_109, A_110, C_111]: (~r2_hidden(D_109, A_110) | k4_tarski(C_111, D_109)!='#skF_3'(A_110) | k1_xboole_0=A_110)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.48/1.34  tff(c_530, plain, (![C_111, C_13]: (k4_tarski(C_111, C_13)!='#skF_3'(k1_tarski(C_13)) | k1_tarski(C_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_526])).
% 2.48/1.34  tff(c_533, plain, (![C_111, C_13]: (k4_tarski(C_111, C_13)!=C_13 | k1_tarski(C_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_447, c_530])).
% 2.48/1.34  tff(c_534, plain, (![C_111, C_13]: (k4_tarski(C_111, C_13)!=C_13)), inference(negUnitSimplification, [status(thm)], [c_372, c_533])).
% 2.48/1.34  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.34  tff(c_161, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k2_xboole_0(A_53, B_54))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.48/1.34  tff(c_171, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_161])).
% 2.48/1.34  tff(c_204, plain, (![B_23]: (k1_tarski(B_23)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_30])).
% 2.48/1.34  tff(c_150, plain, (![C_51, A_52]: (C_51=A_52 | ~r2_hidden(C_51, k1_tarski(A_52)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.48/1.34  tff(c_158, plain, (![A_52]: ('#skF_3'(k1_tarski(A_52))=A_52 | k1_tarski(A_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_150])).
% 2.48/1.34  tff(c_257, plain, (![A_52]: ('#skF_3'(k1_tarski(A_52))=A_52)), inference(negUnitSimplification, [status(thm)], [c_204, c_158])).
% 2.48/1.34  tff(c_303, plain, (![C_74, A_75, D_76]: (~r2_hidden(C_74, A_75) | k4_tarski(C_74, D_76)!='#skF_3'(A_75) | k1_xboole_0=A_75)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.48/1.34  tff(c_307, plain, (![C_13, D_76]: (k4_tarski(C_13, D_76)!='#skF_3'(k1_tarski(C_13)) | k1_tarski(C_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_303])).
% 2.48/1.34  tff(c_310, plain, (![C_13, D_76]: (k4_tarski(C_13, D_76)!=C_13 | k1_tarski(C_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_307])).
% 2.48/1.34  tff(c_311, plain, (![C_13, D_76]: (k4_tarski(C_13, D_76)!=C_13)), inference(negUnitSimplification, [status(thm)], [c_204, c_310])).
% 2.48/1.34  tff(c_48, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.48/1.34  tff(c_79, plain, (![A_44, B_45]: (k1_mcart_1(k4_tarski(A_44, B_45))=A_44)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.48/1.34  tff(c_88, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_48, c_79])).
% 2.48/1.34  tff(c_63, plain, (![A_42, B_43]: (k2_mcart_1(k4_tarski(A_42, B_43))=B_43)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.48/1.34  tff(c_72, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_48, c_63])).
% 2.48/1.34  tff(c_46, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.48/1.34  tff(c_105, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_72, c_46])).
% 2.48/1.34  tff(c_106, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_105])).
% 2.48/1.34  tff(c_108, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_48])).
% 2.48/1.34  tff(c_313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_311, c_108])).
% 2.48/1.34  tff(c_314, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_105])).
% 2.48/1.34  tff(c_317, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_314, c_48])).
% 2.48/1.34  tff(c_536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_534, c_317])).
% 2.48/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.34  
% 2.48/1.34  Inference rules
% 2.48/1.34  ----------------------
% 2.48/1.34  #Ref     : 0
% 2.48/1.34  #Sup     : 117
% 2.48/1.34  #Fact    : 0
% 2.48/1.34  #Define  : 0
% 2.48/1.34  #Split   : 1
% 2.48/1.34  #Chain   : 0
% 2.48/1.34  #Close   : 0
% 2.48/1.34  
% 2.48/1.34  Ordering : KBO
% 2.48/1.34  
% 2.48/1.34  Simplification rules
% 2.48/1.34  ----------------------
% 2.48/1.34  #Subsume      : 1
% 2.48/1.34  #Demod        : 25
% 2.48/1.34  #Tautology    : 96
% 2.48/1.34  #SimpNegUnit  : 13
% 2.48/1.34  #BackRed      : 7
% 2.48/1.34  
% 2.48/1.34  #Partial instantiations: 0
% 2.48/1.34  #Strategies tried      : 1
% 2.48/1.34  
% 2.48/1.34  Timing (in seconds)
% 2.48/1.34  ----------------------
% 2.48/1.35  Preprocessing        : 0.33
% 2.48/1.35  Parsing              : 0.18
% 2.48/1.35  CNF conversion       : 0.02
% 2.48/1.35  Main loop            : 0.23
% 2.48/1.35  Inferencing          : 0.09
% 2.48/1.35  Reduction            : 0.07
% 2.48/1.35  Demodulation         : 0.05
% 2.48/1.35  BG Simplification    : 0.02
% 2.48/1.35  Subsumption          : 0.03
% 2.48/1.35  Abstraction          : 0.02
% 2.48/1.35  MUC search           : 0.00
% 2.48/1.35  Cooper               : 0.00
% 2.48/1.35  Total                : 0.59
% 2.48/1.35  Index Insertion      : 0.00
% 2.48/1.35  Index Deletion       : 0.00
% 2.48/1.35  Index Matching       : 0.00
% 2.48/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
