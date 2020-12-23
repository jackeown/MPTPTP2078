%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:19 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 176 expanded)
%              Number of leaves         :   29 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 258 expanded)
%              Number of equality atoms :   64 ( 204 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_46,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

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

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_392,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k2_xboole_0(A_87,B_88)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_402,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_392])).

tff(c_18,plain,(
    ! [B_18] : k4_xboole_0(k1_tarski(B_18),k1_tarski(B_18)) != k1_tarski(B_18) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_433,plain,(
    ! [B_18] : k1_tarski(B_18) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_18])).

tff(c_34,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26),A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_519,plain,(
    ! [A_111,B_112] :
      ( k4_xboole_0(k1_tarski(A_111),k1_tarski(B_112)) = k1_tarski(A_111)
      | B_112 = A_111 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [C_21,B_20] : ~ r2_hidden(C_21,k4_xboole_0(B_20,k1_tarski(C_21))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_546,plain,(
    ! [B_113,A_114] :
      ( ~ r2_hidden(B_113,k1_tarski(A_114))
      | B_113 = A_114 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_24])).

tff(c_550,plain,(
    ! [A_114] :
      ( '#skF_1'(k1_tarski(A_114)) = A_114
      | k1_tarski(A_114) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_546])).

tff(c_553,plain,(
    ! [A_114] : '#skF_1'(k1_tarski(A_114)) = A_114 ),
    inference(negUnitSimplification,[status(thm)],[c_433,c_550])).

tff(c_554,plain,(
    ! [A_115] : '#skF_1'(k1_tarski(A_115)) = A_115 ),
    inference(negUnitSimplification,[status(thm)],[c_433,c_550])).

tff(c_560,plain,(
    ! [A_115] :
      ( r2_hidden(A_115,k1_tarski(A_115))
      | k1_tarski(A_115) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_34])).

tff(c_565,plain,(
    ! [A_115] : r2_hidden(A_115,k1_tarski(A_115)) ),
    inference(negUnitSimplification,[status(thm)],[c_433,c_560])).

tff(c_582,plain,(
    ! [D_120,A_121,C_122] :
      ( ~ r2_hidden(D_120,A_121)
      | k4_tarski(C_122,D_120) != '#skF_1'(A_121)
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_584,plain,(
    ! [C_122,A_115] :
      ( k4_tarski(C_122,A_115) != '#skF_1'(k1_tarski(A_115))
      | k1_tarski(A_115) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_565,c_582])).

tff(c_588,plain,(
    ! [C_122,A_115] :
      ( k4_tarski(C_122,A_115) != A_115
      | k1_tarski(A_115) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_584])).

tff(c_589,plain,(
    ! [C_122,A_115] : k4_tarski(C_122,A_115) != A_115 ),
    inference(negUnitSimplification,[status(thm)],[c_433,c_588])).

tff(c_148,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k2_xboole_0(A_48,B_49)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_158,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_148])).

tff(c_233,plain,(
    ! [B_18] : k1_tarski(B_18) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_18])).

tff(c_256,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(k1_tarski(A_66),k1_tarski(B_67)) = k1_tarski(A_66)
      | B_67 = A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_289,plain,(
    ! [B_71,A_72] :
      ( ~ r2_hidden(B_71,k1_tarski(A_72))
      | B_71 = A_72 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_24])).

tff(c_293,plain,(
    ! [A_72] :
      ( '#skF_1'(k1_tarski(A_72)) = A_72
      | k1_tarski(A_72) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_289])).

tff(c_296,plain,(
    ! [A_72] : '#skF_1'(k1_tarski(A_72)) = A_72 ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_293])).

tff(c_297,plain,(
    ! [A_73] : '#skF_1'(k1_tarski(A_73)) = A_73 ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_293])).

tff(c_303,plain,(
    ! [A_73] :
      ( r2_hidden(A_73,k1_tarski(A_73))
      | k1_tarski(A_73) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_34])).

tff(c_308,plain,(
    ! [A_73] : r2_hidden(A_73,k1_tarski(A_73)) ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_303])).

tff(c_338,plain,(
    ! [C_81,A_82,D_83] :
      ( ~ r2_hidden(C_81,A_82)
      | k4_tarski(C_81,D_83) != '#skF_1'(A_82)
      | k1_xboole_0 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_340,plain,(
    ! [A_73,D_83] :
      ( k4_tarski(A_73,D_83) != '#skF_1'(k1_tarski(A_73))
      | k1_tarski(A_73) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_308,c_338])).

tff(c_344,plain,(
    ! [A_73,D_83] :
      ( k4_tarski(A_73,D_83) != A_73
      | k1_tarski(A_73) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_340])).

tff(c_345,plain,(
    ! [A_73,D_83] : k4_tarski(A_73,D_83) != A_73 ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_344])).

tff(c_42,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_81,plain,(
    ! [A_42,B_43] : k1_mcart_1(k4_tarski(A_42,B_43)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_90,plain,(
    k1_mcart_1('#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_81])).

tff(c_65,plain,(
    ! [A_40,B_41] : k2_mcart_1(k4_tarski(A_40,B_41)) = B_41 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,(
    k2_mcart_1('#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_65])).

tff(c_40,plain,
    ( k2_mcart_1('#skF_2') = '#skF_2'
    | k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_110,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_74,c_40])).

tff(c_111,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_114,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_42])).

tff(c_352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_345,c_114])).

tff(c_353,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_357,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_42])).

tff(c_596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_589,c_357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.41  
% 2.46/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.41  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.46/1.41  
% 2.46/1.41  %Foreground sorts:
% 2.46/1.41  
% 2.46/1.41  
% 2.46/1.41  %Background operators:
% 2.46/1.41  
% 2.46/1.41  
% 2.46/1.41  %Foreground operators:
% 2.46/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.46/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.46/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.46/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.46/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.46/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.46/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.46/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.46/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.46/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.46/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.46/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.46/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.46/1.41  
% 2.46/1.43  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.46/1.43  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.46/1.43  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.46/1.43  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.46/1.43  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.46/1.43  tff(f_85, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.46/1.43  tff(f_59, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.46/1.43  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.43  tff(c_392, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k2_xboole_0(A_87, B_88))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.43  tff(c_402, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_392])).
% 2.46/1.43  tff(c_18, plain, (![B_18]: (k4_xboole_0(k1_tarski(B_18), k1_tarski(B_18))!=k1_tarski(B_18))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.46/1.43  tff(c_433, plain, (![B_18]: (k1_tarski(B_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_402, c_18])).
% 2.46/1.43  tff(c_34, plain, (![A_26]: (r2_hidden('#skF_1'(A_26), A_26) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.46/1.43  tff(c_519, plain, (![A_111, B_112]: (k4_xboole_0(k1_tarski(A_111), k1_tarski(B_112))=k1_tarski(A_111) | B_112=A_111)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.46/1.43  tff(c_24, plain, (![C_21, B_20]: (~r2_hidden(C_21, k4_xboole_0(B_20, k1_tarski(C_21))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.46/1.43  tff(c_546, plain, (![B_113, A_114]: (~r2_hidden(B_113, k1_tarski(A_114)) | B_113=A_114)), inference(superposition, [status(thm), theory('equality')], [c_519, c_24])).
% 2.46/1.43  tff(c_550, plain, (![A_114]: ('#skF_1'(k1_tarski(A_114))=A_114 | k1_tarski(A_114)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_546])).
% 2.46/1.43  tff(c_553, plain, (![A_114]: ('#skF_1'(k1_tarski(A_114))=A_114)), inference(negUnitSimplification, [status(thm)], [c_433, c_550])).
% 2.46/1.43  tff(c_554, plain, (![A_115]: ('#skF_1'(k1_tarski(A_115))=A_115)), inference(negUnitSimplification, [status(thm)], [c_433, c_550])).
% 2.46/1.43  tff(c_560, plain, (![A_115]: (r2_hidden(A_115, k1_tarski(A_115)) | k1_tarski(A_115)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_554, c_34])).
% 2.46/1.43  tff(c_565, plain, (![A_115]: (r2_hidden(A_115, k1_tarski(A_115)))), inference(negUnitSimplification, [status(thm)], [c_433, c_560])).
% 2.46/1.43  tff(c_582, plain, (![D_120, A_121, C_122]: (~r2_hidden(D_120, A_121) | k4_tarski(C_122, D_120)!='#skF_1'(A_121) | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.46/1.43  tff(c_584, plain, (![C_122, A_115]: (k4_tarski(C_122, A_115)!='#skF_1'(k1_tarski(A_115)) | k1_tarski(A_115)=k1_xboole_0)), inference(resolution, [status(thm)], [c_565, c_582])).
% 2.46/1.43  tff(c_588, plain, (![C_122, A_115]: (k4_tarski(C_122, A_115)!=A_115 | k1_tarski(A_115)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_553, c_584])).
% 2.46/1.43  tff(c_589, plain, (![C_122, A_115]: (k4_tarski(C_122, A_115)!=A_115)), inference(negUnitSimplification, [status(thm)], [c_433, c_588])).
% 2.46/1.43  tff(c_148, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k2_xboole_0(A_48, B_49))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.43  tff(c_158, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_148])).
% 2.46/1.43  tff(c_233, plain, (![B_18]: (k1_tarski(B_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_158, c_18])).
% 2.46/1.43  tff(c_256, plain, (![A_66, B_67]: (k4_xboole_0(k1_tarski(A_66), k1_tarski(B_67))=k1_tarski(A_66) | B_67=A_66)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.46/1.43  tff(c_289, plain, (![B_71, A_72]: (~r2_hidden(B_71, k1_tarski(A_72)) | B_71=A_72)), inference(superposition, [status(thm), theory('equality')], [c_256, c_24])).
% 2.46/1.43  tff(c_293, plain, (![A_72]: ('#skF_1'(k1_tarski(A_72))=A_72 | k1_tarski(A_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_289])).
% 2.46/1.43  tff(c_296, plain, (![A_72]: ('#skF_1'(k1_tarski(A_72))=A_72)), inference(negUnitSimplification, [status(thm)], [c_233, c_293])).
% 2.46/1.43  tff(c_297, plain, (![A_73]: ('#skF_1'(k1_tarski(A_73))=A_73)), inference(negUnitSimplification, [status(thm)], [c_233, c_293])).
% 2.46/1.43  tff(c_303, plain, (![A_73]: (r2_hidden(A_73, k1_tarski(A_73)) | k1_tarski(A_73)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_297, c_34])).
% 2.46/1.43  tff(c_308, plain, (![A_73]: (r2_hidden(A_73, k1_tarski(A_73)))), inference(negUnitSimplification, [status(thm)], [c_233, c_303])).
% 2.46/1.43  tff(c_338, plain, (![C_81, A_82, D_83]: (~r2_hidden(C_81, A_82) | k4_tarski(C_81, D_83)!='#skF_1'(A_82) | k1_xboole_0=A_82)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.46/1.43  tff(c_340, plain, (![A_73, D_83]: (k4_tarski(A_73, D_83)!='#skF_1'(k1_tarski(A_73)) | k1_tarski(A_73)=k1_xboole_0)), inference(resolution, [status(thm)], [c_308, c_338])).
% 2.46/1.43  tff(c_344, plain, (![A_73, D_83]: (k4_tarski(A_73, D_83)!=A_73 | k1_tarski(A_73)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_296, c_340])).
% 2.46/1.43  tff(c_345, plain, (![A_73, D_83]: (k4_tarski(A_73, D_83)!=A_73)), inference(negUnitSimplification, [status(thm)], [c_233, c_344])).
% 2.46/1.43  tff(c_42, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.46/1.43  tff(c_81, plain, (![A_42, B_43]: (k1_mcart_1(k4_tarski(A_42, B_43))=A_42)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.46/1.43  tff(c_90, plain, (k1_mcart_1('#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_42, c_81])).
% 2.46/1.43  tff(c_65, plain, (![A_40, B_41]: (k2_mcart_1(k4_tarski(A_40, B_41))=B_41)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.46/1.43  tff(c_74, plain, (k2_mcart_1('#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_42, c_65])).
% 2.46/1.43  tff(c_40, plain, (k2_mcart_1('#skF_2')='#skF_2' | k1_mcart_1('#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.46/1.43  tff(c_110, plain, ('#skF_2'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_74, c_40])).
% 2.46/1.43  tff(c_111, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_110])).
% 2.46/1.43  tff(c_114, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_42])).
% 2.46/1.43  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_345, c_114])).
% 2.46/1.43  tff(c_353, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_110])).
% 2.46/1.43  tff(c_357, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_353, c_42])).
% 2.46/1.43  tff(c_596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_589, c_357])).
% 2.46/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.43  
% 2.46/1.43  Inference rules
% 2.46/1.43  ----------------------
% 2.46/1.43  #Ref     : 0
% 2.46/1.43  #Sup     : 133
% 2.46/1.43  #Fact    : 0
% 2.46/1.43  #Define  : 0
% 2.46/1.43  #Split   : 1
% 2.46/1.43  #Chain   : 0
% 2.46/1.43  #Close   : 0
% 2.46/1.43  
% 2.46/1.43  Ordering : KBO
% 2.46/1.43  
% 2.46/1.43  Simplification rules
% 2.46/1.43  ----------------------
% 2.46/1.43  #Subsume      : 3
% 2.46/1.43  #Demod        : 27
% 2.46/1.43  #Tautology    : 100
% 2.46/1.43  #SimpNegUnit  : 14
% 2.46/1.43  #BackRed      : 8
% 2.46/1.43  
% 2.46/1.43  #Partial instantiations: 0
% 2.46/1.43  #Strategies tried      : 1
% 2.46/1.43  
% 2.46/1.43  Timing (in seconds)
% 2.46/1.43  ----------------------
% 2.46/1.43  Preprocessing        : 0.32
% 2.46/1.43  Parsing              : 0.18
% 2.46/1.43  CNF conversion       : 0.02
% 2.46/1.43  Main loop            : 0.27
% 2.46/1.43  Inferencing          : 0.11
% 2.46/1.43  Reduction            : 0.08
% 2.46/1.43  Demodulation         : 0.05
% 2.46/1.43  BG Simplification    : 0.02
% 2.46/1.43  Subsumption          : 0.04
% 2.46/1.43  Abstraction          : 0.02
% 2.46/1.43  MUC search           : 0.00
% 2.46/1.43  Cooper               : 0.00
% 2.46/1.43  Total                : 0.63
% 2.46/1.43  Index Insertion      : 0.00
% 2.46/1.43  Index Deletion       : 0.00
% 2.46/1.43  Index Matching       : 0.00
% 2.46/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
