%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:14 EST 2020

% Result     : Theorem 10.79s
% Output     : CNFRefutation 10.79s
% Verified   : 
% Statistics : Number of formulae       :   50 (  91 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 ( 136 expanded)
%              Number of equality atoms :   33 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != B
          & A != C
          & k4_xboole_0(k1_enumset1(A,B,C),k1_tarski(A)) != k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_43,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_67,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_48,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,(
    '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    ! [B_20,C_21,A_19] : k1_enumset1(B_20,C_21,A_19) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,(
    k4_xboole_0(k1_enumset1('#skF_6','#skF_7','#skF_8'),k1_tarski('#skF_6')) != k2_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_49,plain,(
    k4_xboole_0(k1_enumset1('#skF_8','#skF_6','#skF_7'),k1_tarski('#skF_6')) != k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44])).

tff(c_65,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_1'(A_34,B_35),B_35)
      | r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_70,plain,(
    ! [A_34,A_8] :
      ( '#skF_1'(A_34,k1_tarski(A_8)) = A_8
      | r1_xboole_0(A_34,k1_tarski(A_8)) ) ),
    inference(resolution,[status(thm)],[c_65,c_10])).

tff(c_139,plain,(
    ! [A_51,B_52,C_53] : k2_xboole_0(k2_tarski(A_51,B_52),k1_tarski(C_53)) = k1_enumset1(A_51,B_52,C_53) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(k2_xboole_0(A_6,B_7),B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2417,plain,(
    ! [A_3130,B_3131,C_3132] :
      ( k4_xboole_0(k1_enumset1(A_3130,B_3131,C_3132),k1_tarski(C_3132)) = k2_tarski(A_3130,B_3131)
      | ~ r1_xboole_0(k2_tarski(A_3130,B_3131),k1_tarski(C_3132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_8])).

tff(c_13760,plain,(
    ! [A_7850,B_7851,A_7852] :
      ( k4_xboole_0(k1_enumset1(A_7850,B_7851,A_7852),k1_tarski(A_7852)) = k2_tarski(A_7850,B_7851)
      | '#skF_1'(k2_tarski(A_7850,B_7851),k1_tarski(A_7852)) = A_7852 ) ),
    inference(resolution,[status(thm)],[c_70,c_2417])).

tff(c_23933,plain,(
    ! [B_12833,C_12834,A_12835] :
      ( k4_xboole_0(k1_enumset1(B_12833,C_12834,A_12835),k1_tarski(C_12834)) = k2_tarski(A_12835,B_12833)
      | '#skF_1'(k2_tarski(A_12835,B_12833),k1_tarski(C_12834)) = C_12834 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_13760])).

tff(c_24090,plain,(
    '#skF_1'(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_6')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_23933,c_49])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24153,plain,
    ( r2_hidden('#skF_6',k2_tarski('#skF_7','#skF_8'))
    | r1_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24090,c_6])).

tff(c_24325,plain,(
    r1_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_24153])).

tff(c_145,plain,(
    ! [A_51,B_52,C_53] :
      ( k4_xboole_0(k1_enumset1(A_51,B_52,C_53),k1_tarski(C_53)) = k2_tarski(A_51,B_52)
      | ~ r1_xboole_0(k2_tarski(A_51,B_52),k1_tarski(C_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_8])).

tff(c_24327,plain,(
    k4_xboole_0(k1_enumset1('#skF_7','#skF_8','#skF_6'),k1_tarski('#skF_6')) = k2_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_24325,c_145])).

tff(c_24415,plain,(
    k4_xboole_0(k1_enumset1('#skF_8','#skF_6','#skF_7'),k1_tarski('#skF_6')) = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_24327])).

tff(c_24417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_24415])).

tff(c_24418,plain,(
    r2_hidden('#skF_6',k2_tarski('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_24153])).

tff(c_22,plain,(
    ! [D_18,B_14,A_13] :
      ( D_18 = B_14
      | D_18 = A_13
      | ~ r2_hidden(D_18,k2_tarski(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24424,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_24418,c_22])).

tff(c_24511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46,c_24424])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:29:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.79/3.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.79/3.87  
% 10.79/3.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.79/3.88  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1
% 10.79/3.88  
% 10.79/3.88  %Foreground sorts:
% 10.79/3.88  
% 10.79/3.88  
% 10.79/3.88  %Background operators:
% 10.79/3.88  
% 10.79/3.88  
% 10.79/3.88  %Foreground operators:
% 10.79/3.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.79/3.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.79/3.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.79/3.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.79/3.88  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.79/3.88  tff('#skF_7', type, '#skF_7': $i).
% 10.79/3.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.79/3.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.79/3.88  tff('#skF_6', type, '#skF_6': $i).
% 10.79/3.88  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.79/3.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.79/3.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.79/3.88  tff('#skF_8', type, '#skF_8': $i).
% 10.79/3.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.79/3.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.79/3.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.79/3.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.79/3.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.79/3.88  
% 10.79/3.89  tff(f_78, negated_conjecture, ~(![A, B, C]: ~((~(A = B) & ~(A = C)) & ~(k4_xboole_0(k1_enumset1(A, B, C), k1_tarski(A)) = k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_enumset1)).
% 10.79/3.89  tff(f_65, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 10.79/3.89  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.79/3.89  tff(f_54, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 10.79/3.89  tff(f_67, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 10.79/3.89  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 10.79/3.89  tff(f_63, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 10.79/3.89  tff(c_48, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.79/3.89  tff(c_46, plain, ('#skF_6'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.79/3.89  tff(c_40, plain, (![B_20, C_21, A_19]: (k1_enumset1(B_20, C_21, A_19)=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.79/3.89  tff(c_44, plain, (k4_xboole_0(k1_enumset1('#skF_6', '#skF_7', '#skF_8'), k1_tarski('#skF_6'))!=k2_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.79/3.89  tff(c_49, plain, (k4_xboole_0(k1_enumset1('#skF_8', '#skF_6', '#skF_7'), k1_tarski('#skF_6'))!=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44])).
% 10.79/3.89  tff(c_65, plain, (![A_34, B_35]: (r2_hidden('#skF_1'(A_34, B_35), B_35) | r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.79/3.89  tff(c_10, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.79/3.89  tff(c_70, plain, (![A_34, A_8]: ('#skF_1'(A_34, k1_tarski(A_8))=A_8 | r1_xboole_0(A_34, k1_tarski(A_8)))), inference(resolution, [status(thm)], [c_65, c_10])).
% 10.79/3.89  tff(c_139, plain, (![A_51, B_52, C_53]: (k2_xboole_0(k2_tarski(A_51, B_52), k1_tarski(C_53))=k1_enumset1(A_51, B_52, C_53))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.79/3.89  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(k2_xboole_0(A_6, B_7), B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.79/3.89  tff(c_2417, plain, (![A_3130, B_3131, C_3132]: (k4_xboole_0(k1_enumset1(A_3130, B_3131, C_3132), k1_tarski(C_3132))=k2_tarski(A_3130, B_3131) | ~r1_xboole_0(k2_tarski(A_3130, B_3131), k1_tarski(C_3132)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_8])).
% 10.79/3.89  tff(c_13760, plain, (![A_7850, B_7851, A_7852]: (k4_xboole_0(k1_enumset1(A_7850, B_7851, A_7852), k1_tarski(A_7852))=k2_tarski(A_7850, B_7851) | '#skF_1'(k2_tarski(A_7850, B_7851), k1_tarski(A_7852))=A_7852)), inference(resolution, [status(thm)], [c_70, c_2417])).
% 10.79/3.89  tff(c_23933, plain, (![B_12833, C_12834, A_12835]: (k4_xboole_0(k1_enumset1(B_12833, C_12834, A_12835), k1_tarski(C_12834))=k2_tarski(A_12835, B_12833) | '#skF_1'(k2_tarski(A_12835, B_12833), k1_tarski(C_12834))=C_12834)), inference(superposition, [status(thm), theory('equality')], [c_40, c_13760])).
% 10.79/3.89  tff(c_24090, plain, ('#skF_1'(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_6'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_23933, c_49])).
% 10.79/3.89  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.79/3.89  tff(c_24153, plain, (r2_hidden('#skF_6', k2_tarski('#skF_7', '#skF_8')) | r1_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_24090, c_6])).
% 10.79/3.89  tff(c_24325, plain, (r1_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_24153])).
% 10.79/3.89  tff(c_145, plain, (![A_51, B_52, C_53]: (k4_xboole_0(k1_enumset1(A_51, B_52, C_53), k1_tarski(C_53))=k2_tarski(A_51, B_52) | ~r1_xboole_0(k2_tarski(A_51, B_52), k1_tarski(C_53)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_8])).
% 10.79/3.89  tff(c_24327, plain, (k4_xboole_0(k1_enumset1('#skF_7', '#skF_8', '#skF_6'), k1_tarski('#skF_6'))=k2_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_24325, c_145])).
% 10.79/3.89  tff(c_24415, plain, (k4_xboole_0(k1_enumset1('#skF_8', '#skF_6', '#skF_7'), k1_tarski('#skF_6'))=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_24327])).
% 10.79/3.89  tff(c_24417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_24415])).
% 10.79/3.89  tff(c_24418, plain, (r2_hidden('#skF_6', k2_tarski('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_24153])).
% 10.79/3.89  tff(c_22, plain, (![D_18, B_14, A_13]: (D_18=B_14 | D_18=A_13 | ~r2_hidden(D_18, k2_tarski(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.79/3.89  tff(c_24424, plain, ('#skF_6'='#skF_8' | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_24418, c_22])).
% 10.79/3.89  tff(c_24511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_46, c_24424])).
% 10.79/3.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.79/3.89  
% 10.79/3.89  Inference rules
% 10.79/3.89  ----------------------
% 10.79/3.89  #Ref     : 0
% 10.79/3.89  #Sup     : 4099
% 10.79/3.89  #Fact    : 22
% 10.79/3.89  #Define  : 0
% 10.79/3.89  #Split   : 1
% 10.79/3.89  #Chain   : 0
% 10.79/3.89  #Close   : 0
% 10.79/3.89  
% 10.79/3.89  Ordering : KBO
% 10.79/3.89  
% 10.79/3.89  Simplification rules
% 10.79/3.89  ----------------------
% 10.79/3.89  #Subsume      : 981
% 10.79/3.89  #Demod        : 563
% 10.79/3.89  #Tautology    : 1076
% 10.79/3.89  #SimpNegUnit  : 2
% 10.79/3.89  #BackRed      : 0
% 10.79/3.89  
% 10.79/3.89  #Partial instantiations: 7644
% 10.79/3.89  #Strategies tried      : 1
% 10.79/3.89  
% 10.79/3.89  Timing (in seconds)
% 10.79/3.89  ----------------------
% 10.89/3.89  Preprocessing        : 0.33
% 10.89/3.89  Parsing              : 0.17
% 10.89/3.89  CNF conversion       : 0.03
% 10.89/3.89  Main loop            : 2.75
% 10.89/3.89  Inferencing          : 1.17
% 10.89/3.89  Reduction            : 0.57
% 10.89/3.89  Demodulation         : 0.40
% 10.89/3.89  BG Simplification    : 0.14
% 10.89/3.89  Subsumption          : 0.75
% 10.89/3.89  Abstraction          : 0.18
% 10.89/3.89  MUC search           : 0.00
% 10.89/3.89  Cooper               : 0.00
% 10.89/3.89  Total                : 3.11
% 10.89/3.89  Index Insertion      : 0.00
% 10.89/3.89  Index Deletion       : 0.00
% 10.89/3.89  Index Matching       : 0.00
% 10.89/3.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
