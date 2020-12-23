%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:14 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 103 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 148 expanded)
%              Number of equality atoms :   60 ( 118 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    ! [A_35,B_36] : k2_xboole_0(k1_tarski(A_35),B_36) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_62,plain,(
    ! [A_35] : k1_tarski(A_35) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_34,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_3'(A_18),A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_269,plain,(
    ! [D_66,B_67,A_68] :
      ( D_66 = B_67
      | D_66 = A_68
      | ~ r2_hidden(D_66,k2_tarski(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_297,plain,(
    ! [D_72,A_73] :
      ( D_72 = A_73
      | D_72 = A_73
      | ~ r2_hidden(D_72,k1_tarski(A_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_269])).

tff(c_301,plain,(
    ! [A_73] :
      ( '#skF_3'(k1_tarski(A_73)) = A_73
      | k1_tarski(A_73) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_297])).

tff(c_307,plain,(
    ! [A_73] : '#skF_3'(k1_tarski(A_73)) = A_73 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_301])).

tff(c_63,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [D_7,A_2] : r2_hidden(D_7,k2_tarski(A_2,D_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_69,plain,(
    ! [A_37] : r2_hidden(A_37,k1_tarski(A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_6])).

tff(c_324,plain,(
    ! [D_75,A_76,C_77] :
      ( ~ r2_hidden(D_75,A_76)
      | k4_tarski(C_77,D_75) != '#skF_3'(A_76)
      | k1_xboole_0 = A_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_328,plain,(
    ! [C_77,A_37] :
      ( k4_tarski(C_77,A_37) != '#skF_3'(k1_tarski(A_37))
      | k1_tarski(A_37) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_69,c_324])).

tff(c_335,plain,(
    ! [C_77,A_37] :
      ( k4_tarski(C_77,A_37) != A_37
      | k1_tarski(A_37) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_328])).

tff(c_336,plain,(
    ! [C_77,A_37] : k4_tarski(C_77,A_37) != A_37 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_335])).

tff(c_147,plain,(
    ! [D_50,B_51,A_52] :
      ( D_50 = B_51
      | D_50 = A_52
      | ~ r2_hidden(D_50,k2_tarski(A_52,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_166,plain,(
    ! [D_53,A_54] :
      ( D_53 = A_54
      | D_53 = A_54
      | ~ r2_hidden(D_53,k1_tarski(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_147])).

tff(c_170,plain,(
    ! [A_54] :
      ( '#skF_3'(k1_tarski(A_54)) = A_54
      | k1_tarski(A_54) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_166])).

tff(c_176,plain,(
    ! [A_54] : '#skF_3'(k1_tarski(A_54)) = A_54 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_170])).

tff(c_193,plain,(
    ! [C_56,A_57,D_58] :
      ( ~ r2_hidden(C_56,A_57)
      | k4_tarski(C_56,D_58) != '#skF_3'(A_57)
      | k1_xboole_0 = A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_197,plain,(
    ! [A_37,D_58] :
      ( k4_tarski(A_37,D_58) != '#skF_3'(k1_tarski(A_37))
      | k1_tarski(A_37) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_69,c_193])).

tff(c_204,plain,(
    ! [A_37,D_58] :
      ( k4_tarski(A_37,D_58) != A_37
      | k1_tarski(A_37) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_197])).

tff(c_205,plain,(
    ! [A_37,D_58] : k4_tarski(A_37,D_58) != A_37 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_204])).

tff(c_40,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_81,plain,(
    k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_86,plain,(
    ! [A_40,B_41] : k1_mcart_1(k4_tarski(A_40,B_41)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_95,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_86])).

tff(c_98,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_95])).

tff(c_99,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_42])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_99])).

tff(c_210,plain,(
    k2_mcart_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_216,plain,(
    ! [A_59,B_60] : k2_mcart_1(k4_tarski(A_59,B_60)) = B_60 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_225,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_216])).

tff(c_228,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_225])).

tff(c_229,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_42])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:37:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.29  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.06/1.29  
% 2.06/1.29  %Foreground sorts:
% 2.06/1.29  
% 2.06/1.29  
% 2.06/1.29  %Background operators:
% 2.06/1.29  
% 2.06/1.29  
% 2.06/1.29  %Foreground operators:
% 2.06/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.06/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.29  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.06/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.29  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.29  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.06/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.29  
% 2.06/1.31  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.06/1.31  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.06/1.31  tff(f_65, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.06/1.31  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.06/1.31  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.06/1.31  tff(f_75, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.06/1.31  tff(f_49, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.06/1.31  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.31  tff(c_58, plain, (![A_35, B_36]: (k2_xboole_0(k1_tarski(A_35), B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.31  tff(c_62, plain, (![A_35]: (k1_tarski(A_35)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_58])).
% 2.06/1.31  tff(c_34, plain, (![A_18]: (r2_hidden('#skF_3'(A_18), A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.06/1.31  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.31  tff(c_269, plain, (![D_66, B_67, A_68]: (D_66=B_67 | D_66=A_68 | ~r2_hidden(D_66, k2_tarski(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.06/1.31  tff(c_297, plain, (![D_72, A_73]: (D_72=A_73 | D_72=A_73 | ~r2_hidden(D_72, k1_tarski(A_73)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_269])).
% 2.06/1.31  tff(c_301, plain, (![A_73]: ('#skF_3'(k1_tarski(A_73))=A_73 | k1_tarski(A_73)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_297])).
% 2.06/1.31  tff(c_307, plain, (![A_73]: ('#skF_3'(k1_tarski(A_73))=A_73)), inference(negUnitSimplification, [status(thm)], [c_62, c_301])).
% 2.06/1.31  tff(c_63, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.31  tff(c_6, plain, (![D_7, A_2]: (r2_hidden(D_7, k2_tarski(A_2, D_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.06/1.31  tff(c_69, plain, (![A_37]: (r2_hidden(A_37, k1_tarski(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_6])).
% 2.06/1.31  tff(c_324, plain, (![D_75, A_76, C_77]: (~r2_hidden(D_75, A_76) | k4_tarski(C_77, D_75)!='#skF_3'(A_76) | k1_xboole_0=A_76)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.06/1.31  tff(c_328, plain, (![C_77, A_37]: (k4_tarski(C_77, A_37)!='#skF_3'(k1_tarski(A_37)) | k1_tarski(A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_69, c_324])).
% 2.06/1.31  tff(c_335, plain, (![C_77, A_37]: (k4_tarski(C_77, A_37)!=A_37 | k1_tarski(A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_307, c_328])).
% 2.06/1.31  tff(c_336, plain, (![C_77, A_37]: (k4_tarski(C_77, A_37)!=A_37)), inference(negUnitSimplification, [status(thm)], [c_62, c_335])).
% 2.06/1.31  tff(c_147, plain, (![D_50, B_51, A_52]: (D_50=B_51 | D_50=A_52 | ~r2_hidden(D_50, k2_tarski(A_52, B_51)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.06/1.31  tff(c_166, plain, (![D_53, A_54]: (D_53=A_54 | D_53=A_54 | ~r2_hidden(D_53, k1_tarski(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_147])).
% 2.06/1.31  tff(c_170, plain, (![A_54]: ('#skF_3'(k1_tarski(A_54))=A_54 | k1_tarski(A_54)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_166])).
% 2.06/1.31  tff(c_176, plain, (![A_54]: ('#skF_3'(k1_tarski(A_54))=A_54)), inference(negUnitSimplification, [status(thm)], [c_62, c_170])).
% 2.06/1.31  tff(c_193, plain, (![C_56, A_57, D_58]: (~r2_hidden(C_56, A_57) | k4_tarski(C_56, D_58)!='#skF_3'(A_57) | k1_xboole_0=A_57)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.06/1.31  tff(c_197, plain, (![A_37, D_58]: (k4_tarski(A_37, D_58)!='#skF_3'(k1_tarski(A_37)) | k1_tarski(A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_69, c_193])).
% 2.06/1.31  tff(c_204, plain, (![A_37, D_58]: (k4_tarski(A_37, D_58)!=A_37 | k1_tarski(A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_176, c_197])).
% 2.06/1.31  tff(c_205, plain, (![A_37, D_58]: (k4_tarski(A_37, D_58)!=A_37)), inference(negUnitSimplification, [status(thm)], [c_62, c_204])).
% 2.06/1.31  tff(c_40, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.06/1.31  tff(c_81, plain, (k1_mcart_1('#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_40])).
% 2.06/1.31  tff(c_42, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.06/1.31  tff(c_86, plain, (![A_40, B_41]: (k1_mcart_1(k4_tarski(A_40, B_41))=A_40)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.31  tff(c_95, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_42, c_86])).
% 2.06/1.31  tff(c_98, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_95])).
% 2.06/1.31  tff(c_99, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_42])).
% 2.06/1.31  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_99])).
% 2.06/1.31  tff(c_210, plain, (k2_mcart_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 2.06/1.31  tff(c_216, plain, (![A_59, B_60]: (k2_mcart_1(k4_tarski(A_59, B_60))=B_60)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.31  tff(c_225, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_42, c_216])).
% 2.06/1.31  tff(c_228, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_210, c_225])).
% 2.06/1.31  tff(c_229, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_228, c_42])).
% 2.06/1.31  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_336, c_229])).
% 2.06/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.31  
% 2.06/1.31  Inference rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Ref     : 0
% 2.06/1.31  #Sup     : 77
% 2.06/1.31  #Fact    : 0
% 2.06/1.31  #Define  : 0
% 2.06/1.31  #Split   : 1
% 2.06/1.31  #Chain   : 0
% 2.06/1.31  #Close   : 0
% 2.06/1.31  
% 2.06/1.31  Ordering : KBO
% 2.06/1.31  
% 2.06/1.31  Simplification rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Subsume      : 0
% 2.06/1.31  #Demod        : 13
% 2.06/1.31  #Tautology    : 53
% 2.06/1.31  #SimpNegUnit  : 9
% 2.06/1.31  #BackRed      : 5
% 2.06/1.31  
% 2.06/1.31  #Partial instantiations: 0
% 2.06/1.31  #Strategies tried      : 1
% 2.06/1.31  
% 2.06/1.31  Timing (in seconds)
% 2.06/1.31  ----------------------
% 2.06/1.31  Preprocessing        : 0.30
% 2.06/1.31  Parsing              : 0.15
% 2.06/1.31  CNF conversion       : 0.02
% 2.06/1.31  Main loop            : 0.24
% 2.06/1.31  Inferencing          : 0.09
% 2.06/1.31  Reduction            : 0.07
% 2.06/1.31  Demodulation         : 0.05
% 2.06/1.31  BG Simplification    : 0.01
% 2.06/1.31  Subsumption          : 0.03
% 2.06/1.31  Abstraction          : 0.02
% 2.06/1.31  MUC search           : 0.00
% 2.06/1.31  Cooper               : 0.00
% 2.06/1.31  Total                : 0.57
% 2.06/1.31  Index Insertion      : 0.00
% 2.06/1.31  Index Deletion       : 0.00
% 2.06/1.31  Index Matching       : 0.00
% 2.06/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
