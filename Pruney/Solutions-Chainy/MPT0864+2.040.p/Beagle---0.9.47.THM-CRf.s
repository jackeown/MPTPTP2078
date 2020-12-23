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

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 125 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 172 expanded)
%              Number of equality atoms :   61 ( 146 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

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

tff(f_38,axiom,(
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

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_352,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k4_xboole_0(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_367,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_352])).

tff(c_370,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_367])).

tff(c_24,plain,(
    ! [B_14] : k4_xboole_0(k1_tarski(B_14),k1_tarski(B_14)) != k1_tarski(B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_390,plain,(
    ! [B_14] : k1_tarski(B_14) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_24])).

tff(c_32,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_3'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_317,plain,(
    ! [C_61,A_62] :
      ( C_61 = A_62
      | ~ r2_hidden(C_61,k1_tarski(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_325,plain,(
    ! [A_62] :
      ( '#skF_3'(k1_tarski(A_62)) = A_62
      | k1_tarski(A_62) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_317])).

tff(c_422,plain,(
    ! [A_62] : '#skF_3'(k1_tarski(A_62)) = A_62 ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_325])).

tff(c_10,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_466,plain,(
    ! [D_78,A_79,C_80] :
      ( ~ r2_hidden(D_78,A_79)
      | k4_tarski(C_80,D_78) != '#skF_3'(A_79)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_470,plain,(
    ! [C_80,C_9] :
      ( k4_tarski(C_80,C_9) != '#skF_3'(k1_tarski(C_9))
      | k1_tarski(C_9) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_466])).

tff(c_473,plain,(
    ! [C_80,C_9] :
      ( k4_tarski(C_80,C_9) != C_9
      | k1_tarski(C_9) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_470])).

tff(c_474,plain,(
    ! [C_80,C_9] : k4_tarski(C_80,C_9) != C_9 ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_473])).

tff(c_163,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_178,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_163])).

tff(c_181,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_201,plain,(
    ! [B_14] : k1_tarski(B_14) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_24])).

tff(c_128,plain,(
    ! [C_38,A_39] :
      ( C_38 = A_39
      | ~ r2_hidden(C_38,k1_tarski(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_136,plain,(
    ! [A_39] :
      ( '#skF_3'(k1_tarski(A_39)) = A_39
      | k1_tarski(A_39) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_128])).

tff(c_233,plain,(
    ! [A_39] : '#skF_3'(k1_tarski(A_39)) = A_39 ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_136])).

tff(c_277,plain,(
    ! [C_55,A_56,D_57] :
      ( ~ r2_hidden(C_55,A_56)
      | k4_tarski(C_55,D_57) != '#skF_3'(A_56)
      | k1_xboole_0 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_281,plain,(
    ! [C_9,D_57] :
      ( k4_tarski(C_9,D_57) != '#skF_3'(k1_tarski(C_9))
      | k1_tarski(C_9) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_277])).

tff(c_284,plain,(
    ! [C_9,D_57] :
      ( k4_tarski(C_9,D_57) != C_9
      | k1_tarski(C_9) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_281])).

tff(c_285,plain,(
    ! [C_9,D_57] : k4_tarski(C_9,D_57) != C_9 ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_284])).

tff(c_40,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_87,plain,(
    ! [A_35,B_36] : k1_mcart_1(k4_tarski(A_35,B_36)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_87])).

tff(c_71,plain,(
    ! [A_33,B_34] : k2_mcart_1(k4_tarski(A_33,B_34)) = B_34 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_80,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_71])).

tff(c_38,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_103,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_80,c_38])).

tff(c_104,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_106,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_40])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_106])).

tff(c_292,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_295,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_40])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:31:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.30  
% 1.98/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.30  %$ r2_hidden > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.98/1.30  
% 1.98/1.30  %Foreground sorts:
% 1.98/1.30  
% 1.98/1.30  
% 1.98/1.30  %Background operators:
% 1.98/1.30  
% 1.98/1.30  
% 1.98/1.30  %Foreground operators:
% 1.98/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.98/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.30  tff('#skF_6', type, '#skF_6': $i).
% 1.98/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.30  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.98/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.30  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.98/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.98/1.30  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.98/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.30  
% 2.21/1.32  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.21/1.32  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.21/1.32  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.21/1.32  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.21/1.32  tff(f_67, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.21/1.32  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.21/1.32  tff(f_77, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.21/1.32  tff(f_51, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.21/1.32  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.32  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.32  tff(c_352, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k4_xboole_0(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.32  tff(c_367, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_352])).
% 2.21/1.32  tff(c_370, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_367])).
% 2.21/1.32  tff(c_24, plain, (![B_14]: (k4_xboole_0(k1_tarski(B_14), k1_tarski(B_14))!=k1_tarski(B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.32  tff(c_390, plain, (![B_14]: (k1_tarski(B_14)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_370, c_24])).
% 2.21/1.32  tff(c_32, plain, (![A_17]: (r2_hidden('#skF_3'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.32  tff(c_317, plain, (![C_61, A_62]: (C_61=A_62 | ~r2_hidden(C_61, k1_tarski(A_62)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.21/1.32  tff(c_325, plain, (![A_62]: ('#skF_3'(k1_tarski(A_62))=A_62 | k1_tarski(A_62)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_317])).
% 2.21/1.32  tff(c_422, plain, (![A_62]: ('#skF_3'(k1_tarski(A_62))=A_62)), inference(negUnitSimplification, [status(thm)], [c_390, c_325])).
% 2.21/1.32  tff(c_10, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.21/1.32  tff(c_466, plain, (![D_78, A_79, C_80]: (~r2_hidden(D_78, A_79) | k4_tarski(C_80, D_78)!='#skF_3'(A_79) | k1_xboole_0=A_79)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.32  tff(c_470, plain, (![C_80, C_9]: (k4_tarski(C_80, C_9)!='#skF_3'(k1_tarski(C_9)) | k1_tarski(C_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_466])).
% 2.21/1.32  tff(c_473, plain, (![C_80, C_9]: (k4_tarski(C_80, C_9)!=C_9 | k1_tarski(C_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_422, c_470])).
% 2.21/1.32  tff(c_474, plain, (![C_80, C_9]: (k4_tarski(C_80, C_9)!=C_9)), inference(negUnitSimplification, [status(thm)], [c_390, c_473])).
% 2.21/1.32  tff(c_163, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.32  tff(c_178, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_163])).
% 2.21/1.32  tff(c_181, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_178])).
% 2.21/1.32  tff(c_201, plain, (![B_14]: (k1_tarski(B_14)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_181, c_24])).
% 2.21/1.32  tff(c_128, plain, (![C_38, A_39]: (C_38=A_39 | ~r2_hidden(C_38, k1_tarski(A_39)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.21/1.32  tff(c_136, plain, (![A_39]: ('#skF_3'(k1_tarski(A_39))=A_39 | k1_tarski(A_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_128])).
% 2.21/1.32  tff(c_233, plain, (![A_39]: ('#skF_3'(k1_tarski(A_39))=A_39)), inference(negUnitSimplification, [status(thm)], [c_201, c_136])).
% 2.21/1.32  tff(c_277, plain, (![C_55, A_56, D_57]: (~r2_hidden(C_55, A_56) | k4_tarski(C_55, D_57)!='#skF_3'(A_56) | k1_xboole_0=A_56)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.32  tff(c_281, plain, (![C_9, D_57]: (k4_tarski(C_9, D_57)!='#skF_3'(k1_tarski(C_9)) | k1_tarski(C_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_277])).
% 2.21/1.32  tff(c_284, plain, (![C_9, D_57]: (k4_tarski(C_9, D_57)!=C_9 | k1_tarski(C_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_233, c_281])).
% 2.21/1.32  tff(c_285, plain, (![C_9, D_57]: (k4_tarski(C_9, D_57)!=C_9)), inference(negUnitSimplification, [status(thm)], [c_201, c_284])).
% 2.21/1.32  tff(c_40, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.21/1.32  tff(c_87, plain, (![A_35, B_36]: (k1_mcart_1(k4_tarski(A_35, B_36))=A_35)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.32  tff(c_96, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_40, c_87])).
% 2.21/1.32  tff(c_71, plain, (![A_33, B_34]: (k2_mcart_1(k4_tarski(A_33, B_34))=B_34)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.32  tff(c_80, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_40, c_71])).
% 2.21/1.32  tff(c_38, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.21/1.32  tff(c_103, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_80, c_38])).
% 2.21/1.32  tff(c_104, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_103])).
% 2.21/1.32  tff(c_106, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_40])).
% 2.21/1.32  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_106])).
% 2.21/1.32  tff(c_292, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_103])).
% 2.21/1.32  tff(c_295, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_292, c_40])).
% 2.21/1.32  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_474, c_295])).
% 2.21/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.32  
% 2.21/1.32  Inference rules
% 2.21/1.32  ----------------------
% 2.21/1.32  #Ref     : 0
% 2.21/1.32  #Sup     : 104
% 2.21/1.32  #Fact    : 0
% 2.21/1.32  #Define  : 0
% 2.21/1.32  #Split   : 1
% 2.21/1.32  #Chain   : 0
% 2.21/1.32  #Close   : 0
% 2.21/1.32  
% 2.21/1.32  Ordering : KBO
% 2.21/1.32  
% 2.21/1.32  Simplification rules
% 2.21/1.32  ----------------------
% 2.21/1.32  #Subsume      : 1
% 2.21/1.32  #Demod        : 24
% 2.21/1.32  #Tautology    : 80
% 2.21/1.32  #SimpNegUnit  : 10
% 2.21/1.32  #BackRed      : 10
% 2.21/1.32  
% 2.21/1.32  #Partial instantiations: 0
% 2.21/1.32  #Strategies tried      : 1
% 2.21/1.32  
% 2.21/1.32  Timing (in seconds)
% 2.21/1.32  ----------------------
% 2.21/1.32  Preprocessing        : 0.31
% 2.21/1.32  Parsing              : 0.16
% 2.21/1.32  CNF conversion       : 0.02
% 2.21/1.32  Main loop            : 0.22
% 2.21/1.32  Inferencing          : 0.09
% 2.21/1.32  Reduction            : 0.07
% 2.21/1.32  Demodulation         : 0.04
% 2.21/1.32  BG Simplification    : 0.01
% 2.21/1.32  Subsumption          : 0.03
% 2.21/1.32  Abstraction          : 0.02
% 2.21/1.32  MUC search           : 0.00
% 2.21/1.32  Cooper               : 0.00
% 2.21/1.32  Total                : 0.56
% 2.21/1.32  Index Insertion      : 0.00
% 2.21/1.32  Index Deletion       : 0.00
% 2.21/1.32  Index Matching       : 0.00
% 2.21/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
