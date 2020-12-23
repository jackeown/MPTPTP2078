%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:13 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 115 expanded)
%              Number of leaves         :   28 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 160 expanded)
%              Number of equality atoms :   57 ( 134 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_310,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k2_xboole_0(A_69,B_70)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_317,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_310])).

tff(c_26,plain,(
    ! [B_18] : k4_xboole_0(k1_tarski(B_18),k1_tarski(B_18)) != k1_tarski(B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_370,plain,(
    ! [B_18] : k1_tarski(B_18) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_26])).

tff(c_34,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_3'(A_21),A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_299,plain,(
    ! [C_67,A_68] :
      ( C_67 = A_68
      | ~ r2_hidden(C_67,k1_tarski(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_307,plain,(
    ! [A_68] :
      ( '#skF_3'(k1_tarski(A_68)) = A_68
      | k1_tarski(A_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_299])).

tff(c_381,plain,(
    ! [A_68] : '#skF_3'(k1_tarski(A_68)) = A_68 ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_307])).

tff(c_8,plain,(
    ! [C_8] : r2_hidden(C_8,k1_tarski(C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_427,plain,(
    ! [D_85,A_86,C_87] :
      ( ~ r2_hidden(D_85,A_86)
      | k4_tarski(C_87,D_85) != '#skF_3'(A_86)
      | k1_xboole_0 = A_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_431,plain,(
    ! [C_87,C_8] :
      ( k4_tarski(C_87,C_8) != '#skF_3'(k1_tarski(C_8))
      | k1_tarski(C_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_427])).

tff(c_434,plain,(
    ! [C_87,C_8] :
      ( k4_tarski(C_87,C_8) != C_8
      | k1_tarski(C_8) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_431])).

tff(c_435,plain,(
    ! [C_87,C_8] : k4_tarski(C_87,C_8) != C_8 ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_434])).

tff(c_123,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k2_xboole_0(A_41,B_42)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_130,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_123])).

tff(c_160,plain,(
    ! [B_18] : k1_tarski(B_18) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_26])).

tff(c_140,plain,(
    ! [C_44,A_45] :
      ( C_44 = A_45
      | ~ r2_hidden(C_44,k1_tarski(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_148,plain,(
    ! [A_45] :
      ( '#skF_3'(k1_tarski(A_45)) = A_45
      | k1_tarski(A_45) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_140])).

tff(c_227,plain,(
    ! [A_45] : '#skF_3'(k1_tarski(A_45)) = A_45 ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_148])).

tff(c_260,plain,(
    ! [C_62,A_63,D_64] :
      ( ~ r2_hidden(C_62,A_63)
      | k4_tarski(C_62,D_64) != '#skF_3'(A_63)
      | k1_xboole_0 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_264,plain,(
    ! [C_8,D_64] :
      ( k4_tarski(C_8,D_64) != '#skF_3'(k1_tarski(C_8))
      | k1_tarski(C_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_260])).

tff(c_267,plain,(
    ! [C_8,D_64] :
      ( k4_tarski(C_8,D_64) != C_8
      | k1_tarski(C_8) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_264])).

tff(c_268,plain,(
    ! [C_8,D_64] : k4_tarski(C_8,D_64) != C_8 ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_267])).

tff(c_42,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_82,plain,(
    ! [A_38,B_39] : k1_mcart_1(k4_tarski(A_38,B_39)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_91,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_82])).

tff(c_57,plain,(
    ! [A_35,B_36] : k2_mcart_1(k4_tarski(A_35,B_36)) = B_36 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_57])).

tff(c_40,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_99,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_66,c_40])).

tff(c_100,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_102,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_42])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_102])).

tff(c_275,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_278,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_42])).

tff(c_446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.24  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.12/1.24  
% 2.12/1.24  %Foreground sorts:
% 2.12/1.24  
% 2.12/1.24  
% 2.12/1.24  %Background operators:
% 2.12/1.24  
% 2.12/1.24  
% 2.12/1.24  %Foreground operators:
% 2.12/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.12/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.12/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.24  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.12/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.12/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.24  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.12/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.24  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.12/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.24  
% 2.21/1.26  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.21/1.26  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.21/1.26  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.21/1.26  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.21/1.26  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.21/1.26  tff(f_79, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.21/1.26  tff(f_53, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.21/1.26  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.26  tff(c_310, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k2_xboole_0(A_69, B_70))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.26  tff(c_317, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_310])).
% 2.21/1.26  tff(c_26, plain, (![B_18]: (k4_xboole_0(k1_tarski(B_18), k1_tarski(B_18))!=k1_tarski(B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.26  tff(c_370, plain, (![B_18]: (k1_tarski(B_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_317, c_26])).
% 2.21/1.26  tff(c_34, plain, (![A_21]: (r2_hidden('#skF_3'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.26  tff(c_299, plain, (![C_67, A_68]: (C_67=A_68 | ~r2_hidden(C_67, k1_tarski(A_68)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.21/1.26  tff(c_307, plain, (![A_68]: ('#skF_3'(k1_tarski(A_68))=A_68 | k1_tarski(A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_299])).
% 2.21/1.26  tff(c_381, plain, (![A_68]: ('#skF_3'(k1_tarski(A_68))=A_68)), inference(negUnitSimplification, [status(thm)], [c_370, c_307])).
% 2.21/1.26  tff(c_8, plain, (![C_8]: (r2_hidden(C_8, k1_tarski(C_8)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.21/1.26  tff(c_427, plain, (![D_85, A_86, C_87]: (~r2_hidden(D_85, A_86) | k4_tarski(C_87, D_85)!='#skF_3'(A_86) | k1_xboole_0=A_86)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.26  tff(c_431, plain, (![C_87, C_8]: (k4_tarski(C_87, C_8)!='#skF_3'(k1_tarski(C_8)) | k1_tarski(C_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_427])).
% 2.21/1.26  tff(c_434, plain, (![C_87, C_8]: (k4_tarski(C_87, C_8)!=C_8 | k1_tarski(C_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_381, c_431])).
% 2.21/1.26  tff(c_435, plain, (![C_87, C_8]: (k4_tarski(C_87, C_8)!=C_8)), inference(negUnitSimplification, [status(thm)], [c_370, c_434])).
% 2.21/1.26  tff(c_123, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k2_xboole_0(A_41, B_42))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.26  tff(c_130, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_123])).
% 2.21/1.26  tff(c_160, plain, (![B_18]: (k1_tarski(B_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_26])).
% 2.21/1.26  tff(c_140, plain, (![C_44, A_45]: (C_44=A_45 | ~r2_hidden(C_44, k1_tarski(A_45)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.21/1.26  tff(c_148, plain, (![A_45]: ('#skF_3'(k1_tarski(A_45))=A_45 | k1_tarski(A_45)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_140])).
% 2.21/1.26  tff(c_227, plain, (![A_45]: ('#skF_3'(k1_tarski(A_45))=A_45)), inference(negUnitSimplification, [status(thm)], [c_160, c_148])).
% 2.21/1.26  tff(c_260, plain, (![C_62, A_63, D_64]: (~r2_hidden(C_62, A_63) | k4_tarski(C_62, D_64)!='#skF_3'(A_63) | k1_xboole_0=A_63)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.26  tff(c_264, plain, (![C_8, D_64]: (k4_tarski(C_8, D_64)!='#skF_3'(k1_tarski(C_8)) | k1_tarski(C_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_260])).
% 2.21/1.26  tff(c_267, plain, (![C_8, D_64]: (k4_tarski(C_8, D_64)!=C_8 | k1_tarski(C_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_227, c_264])).
% 2.21/1.26  tff(c_268, plain, (![C_8, D_64]: (k4_tarski(C_8, D_64)!=C_8)), inference(negUnitSimplification, [status(thm)], [c_160, c_267])).
% 2.21/1.26  tff(c_42, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.21/1.26  tff(c_82, plain, (![A_38, B_39]: (k1_mcart_1(k4_tarski(A_38, B_39))=A_38)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.21/1.26  tff(c_91, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_42, c_82])).
% 2.21/1.26  tff(c_57, plain, (![A_35, B_36]: (k2_mcart_1(k4_tarski(A_35, B_36))=B_36)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.21/1.26  tff(c_66, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_42, c_57])).
% 2.21/1.26  tff(c_40, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.21/1.26  tff(c_99, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_66, c_40])).
% 2.21/1.26  tff(c_100, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_99])).
% 2.21/1.26  tff(c_102, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_42])).
% 2.21/1.26  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_268, c_102])).
% 2.21/1.26  tff(c_275, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_99])).
% 2.21/1.26  tff(c_278, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_42])).
% 2.21/1.26  tff(c_446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_435, c_278])).
% 2.21/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  Inference rules
% 2.21/1.26  ----------------------
% 2.21/1.26  #Ref     : 0
% 2.21/1.26  #Sup     : 99
% 2.21/1.26  #Fact    : 0
% 2.21/1.26  #Define  : 0
% 2.21/1.26  #Split   : 1
% 2.21/1.26  #Chain   : 0
% 2.21/1.26  #Close   : 0
% 2.21/1.26  
% 2.21/1.26  Ordering : KBO
% 2.21/1.26  
% 2.21/1.26  Simplification rules
% 2.21/1.26  ----------------------
% 2.21/1.26  #Subsume      : 0
% 2.21/1.26  #Demod        : 20
% 2.21/1.26  #Tautology    : 80
% 2.21/1.26  #SimpNegUnit  : 14
% 2.21/1.26  #BackRed      : 6
% 2.21/1.26  
% 2.21/1.26  #Partial instantiations: 0
% 2.21/1.26  #Strategies tried      : 1
% 2.21/1.26  
% 2.21/1.26  Timing (in seconds)
% 2.21/1.26  ----------------------
% 2.21/1.26  Preprocessing        : 0.30
% 2.21/1.26  Parsing              : 0.15
% 2.21/1.26  CNF conversion       : 0.02
% 2.21/1.26  Main loop            : 0.20
% 2.21/1.26  Inferencing          : 0.08
% 2.21/1.26  Reduction            : 0.06
% 2.21/1.26  Demodulation         : 0.04
% 2.21/1.26  BG Simplification    : 0.01
% 2.21/1.26  Subsumption          : 0.03
% 2.21/1.26  Abstraction          : 0.02
% 2.21/1.26  MUC search           : 0.00
% 2.21/1.26  Cooper               : 0.00
% 2.21/1.26  Total                : 0.53
% 2.21/1.26  Index Insertion      : 0.00
% 2.21/1.26  Index Deletion       : 0.00
% 2.21/1.26  Index Matching       : 0.00
% 2.21/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
