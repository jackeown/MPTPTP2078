%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:13 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 100 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 ( 144 expanded)
%              Number of equality atoms :   51 ( 118 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_49,plain,(
    ! [A_28,B_29] : k2_xboole_0(k1_tarski(A_28),B_29) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [A_28] : k1_tarski(A_28) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_49])).

tff(c_220,plain,(
    ! [A_53] :
      ( r2_hidden('#skF_3'(A_53),A_53)
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_224,plain,(
    ! [A_2] :
      ( '#skF_3'(k1_tarski(A_2)) = A_2
      | k1_tarski(A_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_220,c_4])).

tff(c_227,plain,(
    ! [A_2] : '#skF_3'(k1_tarski(A_2)) = A_2 ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_224])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_251,plain,(
    ! [D_57,A_58,C_59] :
      ( ~ r2_hidden(D_57,A_58)
      | k4_tarski(C_59,D_57) != '#skF_3'(A_58)
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_255,plain,(
    ! [C_59,C_6] :
      ( k4_tarski(C_59,C_6) != '#skF_3'(k1_tarski(C_6))
      | k1_tarski(C_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_251])).

tff(c_258,plain,(
    ! [C_59,C_6] :
      ( k4_tarski(C_59,C_6) != C_6
      | k1_tarski(C_6) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_255])).

tff(c_259,plain,(
    ! [C_59,C_6] : k4_tarski(C_59,C_6) != C_6 ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_258])).

tff(c_26,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_3'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_121,plain,(
    ! [C_37,A_38] :
      ( C_37 = A_38
      | ~ r2_hidden(C_37,k1_tarski(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_125,plain,(
    ! [A_38] :
      ( '#skF_3'(k1_tarski(A_38)) = A_38
      | k1_tarski(A_38) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_121])).

tff(c_131,plain,(
    ! [A_38] : '#skF_3'(k1_tarski(A_38)) = A_38 ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_125])).

tff(c_166,plain,(
    ! [C_45,A_46,D_47] :
      ( ~ r2_hidden(C_45,A_46)
      | k4_tarski(C_45,D_47) != '#skF_3'(A_46)
      | k1_xboole_0 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_170,plain,(
    ! [C_6,D_47] :
      ( k4_tarski(C_6,D_47) != '#skF_3'(k1_tarski(C_6))
      | k1_tarski(C_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_173,plain,(
    ! [C_6,D_47] :
      ( k4_tarski(C_6,D_47) != C_6
      | k1_tarski(C_6) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_170])).

tff(c_174,plain,(
    ! [C_6,D_47] : k4_tarski(C_6,D_47) != C_6 ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_173])).

tff(c_34,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_55,plain,(
    ! [A_31,B_32] : k1_mcart_1(k4_tarski(A_31,B_32)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_64,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_55])).

tff(c_71,plain,(
    ! [A_33,B_34] : k2_mcart_1(k4_tarski(A_33,B_34)) = B_34 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_71])).

tff(c_32,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_87,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_80,c_32])).

tff(c_88,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_90,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_34])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_90])).

tff(c_181,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_184,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_34])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:52:55 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.23  %$ r2_hidden > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.06/1.23  
% 2.06/1.23  %Foreground sorts:
% 2.06/1.23  
% 2.06/1.23  
% 2.06/1.23  %Background operators:
% 2.06/1.23  
% 2.06/1.23  
% 2.06/1.23  %Foreground operators:
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.06/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.23  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.23  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.06/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.23  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.23  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.06/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.23  
% 2.06/1.25  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.06/1.25  tff(f_41, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.06/1.25  tff(f_61, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.06/1.25  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.06/1.25  tff(f_71, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.06/1.25  tff(f_45, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.06/1.25  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.25  tff(c_49, plain, (![A_28, B_29]: (k2_xboole_0(k1_tarski(A_28), B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.25  tff(c_53, plain, (![A_28]: (k1_tarski(A_28)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_49])).
% 2.06/1.25  tff(c_220, plain, (![A_53]: (r2_hidden('#skF_3'(A_53), A_53) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.25  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.25  tff(c_224, plain, (![A_2]: ('#skF_3'(k1_tarski(A_2))=A_2 | k1_tarski(A_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_220, c_4])).
% 2.06/1.25  tff(c_227, plain, (![A_2]: ('#skF_3'(k1_tarski(A_2))=A_2)), inference(negUnitSimplification, [status(thm)], [c_53, c_224])).
% 2.06/1.25  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.25  tff(c_251, plain, (![D_57, A_58, C_59]: (~r2_hidden(D_57, A_58) | k4_tarski(C_59, D_57)!='#skF_3'(A_58) | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.25  tff(c_255, plain, (![C_59, C_6]: (k4_tarski(C_59, C_6)!='#skF_3'(k1_tarski(C_6)) | k1_tarski(C_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_251])).
% 2.06/1.25  tff(c_258, plain, (![C_59, C_6]: (k4_tarski(C_59, C_6)!=C_6 | k1_tarski(C_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_227, c_255])).
% 2.06/1.25  tff(c_259, plain, (![C_59, C_6]: (k4_tarski(C_59, C_6)!=C_6)), inference(negUnitSimplification, [status(thm)], [c_53, c_258])).
% 2.06/1.25  tff(c_26, plain, (![A_14]: (r2_hidden('#skF_3'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.25  tff(c_121, plain, (![C_37, A_38]: (C_37=A_38 | ~r2_hidden(C_37, k1_tarski(A_38)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.25  tff(c_125, plain, (![A_38]: ('#skF_3'(k1_tarski(A_38))=A_38 | k1_tarski(A_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_121])).
% 2.06/1.25  tff(c_131, plain, (![A_38]: ('#skF_3'(k1_tarski(A_38))=A_38)), inference(negUnitSimplification, [status(thm)], [c_53, c_125])).
% 2.06/1.25  tff(c_166, plain, (![C_45, A_46, D_47]: (~r2_hidden(C_45, A_46) | k4_tarski(C_45, D_47)!='#skF_3'(A_46) | k1_xboole_0=A_46)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.25  tff(c_170, plain, (![C_6, D_47]: (k4_tarski(C_6, D_47)!='#skF_3'(k1_tarski(C_6)) | k1_tarski(C_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_166])).
% 2.06/1.25  tff(c_173, plain, (![C_6, D_47]: (k4_tarski(C_6, D_47)!=C_6 | k1_tarski(C_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_170])).
% 2.06/1.25  tff(c_174, plain, (![C_6, D_47]: (k4_tarski(C_6, D_47)!=C_6)), inference(negUnitSimplification, [status(thm)], [c_53, c_173])).
% 2.06/1.25  tff(c_34, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.06/1.25  tff(c_55, plain, (![A_31, B_32]: (k1_mcart_1(k4_tarski(A_31, B_32))=A_31)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.25  tff(c_64, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_34, c_55])).
% 2.06/1.25  tff(c_71, plain, (![A_33, B_34]: (k2_mcart_1(k4_tarski(A_33, B_34))=B_34)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.25  tff(c_80, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_34, c_71])).
% 2.06/1.25  tff(c_32, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.06/1.25  tff(c_87, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_80, c_32])).
% 2.06/1.25  tff(c_88, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_87])).
% 2.06/1.25  tff(c_90, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_34])).
% 2.06/1.25  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_90])).
% 2.06/1.25  tff(c_181, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_87])).
% 2.06/1.25  tff(c_184, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_181, c_34])).
% 2.06/1.25  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_184])).
% 2.06/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.25  
% 2.06/1.25  Inference rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Ref     : 0
% 2.06/1.25  #Sup     : 56
% 2.06/1.25  #Fact    : 0
% 2.06/1.25  #Define  : 0
% 2.06/1.25  #Split   : 1
% 2.06/1.25  #Chain   : 0
% 2.06/1.25  #Close   : 0
% 2.06/1.25  
% 2.06/1.25  Ordering : KBO
% 2.06/1.25  
% 2.06/1.25  Simplification rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Subsume      : 0
% 2.06/1.25  #Demod        : 15
% 2.06/1.25  #Tautology    : 44
% 2.06/1.25  #SimpNegUnit  : 9
% 2.06/1.25  #BackRed      : 6
% 2.06/1.25  
% 2.06/1.25  #Partial instantiations: 0
% 2.06/1.25  #Strategies tried      : 1
% 2.06/1.25  
% 2.06/1.25  Timing (in seconds)
% 2.06/1.25  ----------------------
% 2.06/1.25  Preprocessing        : 0.31
% 2.06/1.25  Parsing              : 0.17
% 2.06/1.25  CNF conversion       : 0.02
% 2.06/1.25  Main loop            : 0.17
% 2.06/1.25  Inferencing          : 0.06
% 2.06/1.25  Reduction            : 0.05
% 2.06/1.25  Demodulation         : 0.04
% 2.06/1.25  BG Simplification    : 0.01
% 2.06/1.25  Subsumption          : 0.02
% 2.06/1.25  Abstraction          : 0.01
% 2.06/1.25  MUC search           : 0.00
% 2.06/1.25  Cooper               : 0.00
% 2.06/1.25  Total                : 0.51
% 2.06/1.25  Index Insertion      : 0.00
% 2.06/1.25  Index Deletion       : 0.00
% 2.06/1.25  Index Matching       : 0.00
% 2.06/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
