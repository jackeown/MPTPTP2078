%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:13 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 104 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 ( 144 expanded)
%              Number of equality atoms :   52 ( 118 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_289,plain,(
    ! [A_65,B_66] : k2_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = A_65 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),B_17) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_296,plain,(
    ! [A_16] : k1_tarski(A_16) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_24])).

tff(c_32,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_3'(A_22),A_22)
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_303,plain,(
    ! [C_68,A_69] :
      ( C_68 = A_69
      | ~ r2_hidden(C_68,k1_tarski(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_307,plain,(
    ! [A_69] :
      ( '#skF_3'(k1_tarski(A_69)) = A_69
      | k1_tarski(A_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_303])).

tff(c_313,plain,(
    ! [A_69] : '#skF_3'(k1_tarski(A_69)) = A_69 ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_307])).

tff(c_6,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_440,plain,(
    ! [D_87,A_88,C_89] :
      ( ~ r2_hidden(D_87,A_88)
      | k4_tarski(C_89,D_87) != '#skF_3'(A_88)
      | k1_xboole_0 = A_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_444,plain,(
    ! [C_89,C_7] :
      ( k4_tarski(C_89,C_7) != '#skF_3'(k1_tarski(C_7))
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_440])).

tff(c_447,plain,(
    ! [C_89,C_7] :
      ( k4_tarski(C_89,C_7) != C_7
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_444])).

tff(c_448,plain,(
    ! [C_89,C_7] : k4_tarski(C_89,C_7) != C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_447])).

tff(c_124,plain,(
    ! [A_45,B_46] : k2_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_131,plain,(
    ! [A_16] : k1_tarski(A_16) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_24])).

tff(c_113,plain,(
    ! [C_43,A_44] :
      ( C_43 = A_44
      | ~ r2_hidden(C_43,k1_tarski(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_121,plain,(
    ! [A_44] :
      ( '#skF_3'(k1_tarski(A_44)) = A_44
      | k1_tarski(A_44) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_230,plain,(
    ! [A_44] : '#skF_3'(k1_tarski(A_44)) = A_44 ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_121])).

tff(c_254,plain,(
    ! [C_62,A_63,D_64] :
      ( ~ r2_hidden(C_62,A_63)
      | k4_tarski(C_62,D_64) != '#skF_3'(A_63)
      | k1_xboole_0 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_258,plain,(
    ! [C_7,D_64] :
      ( k4_tarski(C_7,D_64) != '#skF_3'(k1_tarski(C_7))
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_254])).

tff(c_261,plain,(
    ! [C_7,D_64] :
      ( k4_tarski(C_7,D_64) != C_7
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_258])).

tff(c_262,plain,(
    ! [C_7,D_64] : k4_tarski(C_7,D_64) != C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_261])).

tff(c_40,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_72,plain,(
    ! [A_40,B_41] : k1_mcart_1(k4_tarski(A_40,B_41)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_81,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_72])).

tff(c_47,plain,(
    ! [A_37,B_38] : k2_mcart_1(k4_tarski(A_37,B_38)) = B_38 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_47])).

tff(c_38,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_89,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_56,c_38])).

tff(c_90,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_92,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_40])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_92])).

tff(c_265,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_268,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_40])).

tff(c_454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_448,c_268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:48:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.27  
% 2.16/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.27  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.16/1.27  
% 2.16/1.27  %Foreground sorts:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Background operators:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Foreground operators:
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.16/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.16/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.27  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.16/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.16/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.27  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.27  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.16/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.16/1.27  
% 2.16/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.16/1.29  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.16/1.29  tff(f_67, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.16/1.29  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.16/1.29  tff(f_77, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.16/1.29  tff(f_51, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.16/1.29  tff(c_289, plain, (![A_65, B_66]: (k2_xboole_0(A_65, k3_xboole_0(A_65, B_66))=A_65)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.29  tff(c_24, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.29  tff(c_296, plain, (![A_16]: (k1_tarski(A_16)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_289, c_24])).
% 2.16/1.29  tff(c_32, plain, (![A_22]: (r2_hidden('#skF_3'(A_22), A_22) | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.29  tff(c_303, plain, (![C_68, A_69]: (C_68=A_69 | ~r2_hidden(C_68, k1_tarski(A_69)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.16/1.29  tff(c_307, plain, (![A_69]: ('#skF_3'(k1_tarski(A_69))=A_69 | k1_tarski(A_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_303])).
% 2.16/1.29  tff(c_313, plain, (![A_69]: ('#skF_3'(k1_tarski(A_69))=A_69)), inference(negUnitSimplification, [status(thm)], [c_296, c_307])).
% 2.16/1.29  tff(c_6, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.16/1.29  tff(c_440, plain, (![D_87, A_88, C_89]: (~r2_hidden(D_87, A_88) | k4_tarski(C_89, D_87)!='#skF_3'(A_88) | k1_xboole_0=A_88)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.29  tff(c_444, plain, (![C_89, C_7]: (k4_tarski(C_89, C_7)!='#skF_3'(k1_tarski(C_7)) | k1_tarski(C_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_440])).
% 2.16/1.29  tff(c_447, plain, (![C_89, C_7]: (k4_tarski(C_89, C_7)!=C_7 | k1_tarski(C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_313, c_444])).
% 2.16/1.29  tff(c_448, plain, (![C_89, C_7]: (k4_tarski(C_89, C_7)!=C_7)), inference(negUnitSimplification, [status(thm)], [c_296, c_447])).
% 2.16/1.29  tff(c_124, plain, (![A_45, B_46]: (k2_xboole_0(A_45, k3_xboole_0(A_45, B_46))=A_45)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.29  tff(c_131, plain, (![A_16]: (k1_tarski(A_16)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_124, c_24])).
% 2.16/1.29  tff(c_113, plain, (![C_43, A_44]: (C_43=A_44 | ~r2_hidden(C_43, k1_tarski(A_44)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.16/1.29  tff(c_121, plain, (![A_44]: ('#skF_3'(k1_tarski(A_44))=A_44 | k1_tarski(A_44)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_113])).
% 2.16/1.29  tff(c_230, plain, (![A_44]: ('#skF_3'(k1_tarski(A_44))=A_44)), inference(negUnitSimplification, [status(thm)], [c_131, c_121])).
% 2.16/1.29  tff(c_254, plain, (![C_62, A_63, D_64]: (~r2_hidden(C_62, A_63) | k4_tarski(C_62, D_64)!='#skF_3'(A_63) | k1_xboole_0=A_63)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.29  tff(c_258, plain, (![C_7, D_64]: (k4_tarski(C_7, D_64)!='#skF_3'(k1_tarski(C_7)) | k1_tarski(C_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_254])).
% 2.16/1.29  tff(c_261, plain, (![C_7, D_64]: (k4_tarski(C_7, D_64)!=C_7 | k1_tarski(C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_230, c_258])).
% 2.16/1.29  tff(c_262, plain, (![C_7, D_64]: (k4_tarski(C_7, D_64)!=C_7)), inference(negUnitSimplification, [status(thm)], [c_131, c_261])).
% 2.16/1.29  tff(c_40, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.16/1.29  tff(c_72, plain, (![A_40, B_41]: (k1_mcart_1(k4_tarski(A_40, B_41))=A_40)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.29  tff(c_81, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_40, c_72])).
% 2.16/1.29  tff(c_47, plain, (![A_37, B_38]: (k2_mcart_1(k4_tarski(A_37, B_38))=B_38)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.29  tff(c_56, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_40, c_47])).
% 2.16/1.29  tff(c_38, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.16/1.29  tff(c_89, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_56, c_38])).
% 2.16/1.29  tff(c_90, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_89])).
% 2.16/1.29  tff(c_92, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_40])).
% 2.16/1.29  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_262, c_92])).
% 2.16/1.29  tff(c_265, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_89])).
% 2.16/1.29  tff(c_268, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_265, c_40])).
% 2.16/1.29  tff(c_454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_448, c_268])).
% 2.16/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  Inference rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Ref     : 0
% 2.16/1.29  #Sup     : 101
% 2.16/1.29  #Fact    : 0
% 2.16/1.29  #Define  : 0
% 2.16/1.29  #Split   : 1
% 2.16/1.29  #Chain   : 0
% 2.16/1.29  #Close   : 0
% 2.16/1.29  
% 2.16/1.29  Ordering : KBO
% 2.16/1.29  
% 2.16/1.29  Simplification rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Subsume      : 3
% 2.16/1.29  #Demod        : 17
% 2.16/1.29  #Tautology    : 78
% 2.16/1.29  #SimpNegUnit  : 9
% 2.16/1.29  #BackRed      : 6
% 2.16/1.29  
% 2.16/1.29  #Partial instantiations: 0
% 2.16/1.29  #Strategies tried      : 1
% 2.16/1.29  
% 2.16/1.29  Timing (in seconds)
% 2.16/1.29  ----------------------
% 2.16/1.29  Preprocessing        : 0.31
% 2.16/1.29  Parsing              : 0.16
% 2.16/1.29  CNF conversion       : 0.02
% 2.16/1.29  Main loop            : 0.21
% 2.16/1.29  Inferencing          : 0.08
% 2.16/1.29  Reduction            : 0.06
% 2.16/1.29  Demodulation         : 0.05
% 2.16/1.29  BG Simplification    : 0.01
% 2.16/1.29  Subsumption          : 0.03
% 2.16/1.29  Abstraction          : 0.01
% 2.16/1.29  MUC search           : 0.00
% 2.16/1.29  Cooper               : 0.00
% 2.16/1.29  Total                : 0.55
% 2.16/1.29  Index Insertion      : 0.00
% 2.16/1.29  Index Deletion       : 0.00
% 2.16/1.29  Index Matching       : 0.00
% 2.16/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
