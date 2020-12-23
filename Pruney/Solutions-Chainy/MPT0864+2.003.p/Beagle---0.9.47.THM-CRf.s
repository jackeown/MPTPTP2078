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
% DateTime   : Thu Dec  3 10:09:09 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 129 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 204 expanded)
%              Number of equality atoms :   59 ( 138 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_6 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_96,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_40,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_405,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(A_103,B_104) = k1_xboole_0
      | ~ r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_413,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_405])).

tff(c_497,plain,(
    ! [B_116,A_117] :
      ( ~ r2_hidden(B_116,A_117)
      | k4_xboole_0(A_117,k1_tarski(B_116)) != A_117 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_504,plain,(
    ! [B_116] :
      ( ~ r2_hidden(B_116,k1_tarski(B_116))
      | k1_tarski(B_116) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_497])).

tff(c_507,plain,(
    ! [B_116] : k1_tarski(B_116) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_504])).

tff(c_64,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_6'(A_29),A_29)
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_388,plain,(
    ! [C_99,A_100] :
      ( C_99 = A_100
      | ~ r2_hidden(C_99,k1_tarski(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_400,plain,(
    ! [A_100] :
      ( '#skF_6'(k1_tarski(A_100)) = A_100
      | k1_tarski(A_100) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_64,c_388])).

tff(c_509,plain,(
    ! [A_100] : '#skF_6'(k1_tarski(A_100)) = A_100 ),
    inference(negUnitSimplification,[status(thm)],[c_507,c_400])).

tff(c_558,plain,(
    ! [D_126,A_127,C_128] :
      ( ~ r2_hidden(D_126,A_127)
      | k4_tarski(C_128,D_126) != '#skF_6'(A_127)
      | k1_xboole_0 = A_127 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_574,plain,(
    ! [C_128,C_18] :
      ( k4_tarski(C_128,C_18) != '#skF_6'(k1_tarski(C_18))
      | k1_tarski(C_18) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_558])).

tff(c_583,plain,(
    ! [C_128,C_18] :
      ( k4_tarski(C_128,C_18) != C_18
      | k1_tarski(C_18) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_574])).

tff(c_584,plain,(
    ! [C_128,C_18] : k4_tarski(C_128,C_18) != C_18 ),
    inference(negUnitSimplification,[status(thm)],[c_507,c_583])).

tff(c_201,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = k1_xboole_0
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_209,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_201])).

tff(c_264,plain,(
    ! [B_76,A_77] :
      ( ~ r2_hidden(B_76,A_77)
      | k4_xboole_0(A_77,k1_tarski(B_76)) != A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_268,plain,(
    ! [B_76] :
      ( ~ r2_hidden(B_76,k1_tarski(B_76))
      | k1_tarski(B_76) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_264])).

tff(c_273,plain,(
    ! [B_76] : k1_tarski(B_76) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_268])).

tff(c_162,plain,(
    ! [A_51] :
      ( r2_hidden('#skF_6'(A_51),A_51)
      | k1_xboole_0 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_167,plain,(
    ! [A_14] :
      ( '#skF_6'(k1_tarski(A_14)) = A_14
      | k1_tarski(A_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_162,c_38])).

tff(c_275,plain,(
    ! [A_14] : '#skF_6'(k1_tarski(A_14)) = A_14 ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_167])).

tff(c_325,plain,(
    ! [C_86,A_87,D_88] :
      ( ~ r2_hidden(C_86,A_87)
      | k4_tarski(C_86,D_88) != '#skF_6'(A_87)
      | k1_xboole_0 = A_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_341,plain,(
    ! [C_18,D_88] :
      ( k4_tarski(C_18,D_88) != '#skF_6'(k1_tarski(C_18))
      | k1_tarski(C_18) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_325])).

tff(c_350,plain,(
    ! [C_18,D_88] :
      ( k4_tarski(C_18,D_88) != C_18
      | k1_tarski(C_18) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_341])).

tff(c_351,plain,(
    ! [C_18,D_88] : k4_tarski(C_18,D_88) != C_18 ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_350])).

tff(c_72,plain,(
    k4_tarski('#skF_8','#skF_9') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_105,plain,(
    ! [A_46,B_47] : k1_mcart_1(k4_tarski(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_114,plain,(
    k1_mcart_1('#skF_7') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_105])).

tff(c_80,plain,(
    ! [A_43,B_44] : k2_mcart_1(k4_tarski(A_43,B_44)) = B_44 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_89,plain,(
    k2_mcart_1('#skF_7') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_80])).

tff(c_70,plain,
    ( k2_mcart_1('#skF_7') = '#skF_7'
    | k1_mcart_1('#skF_7') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_122,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_89,c_70])).

tff(c_123,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_126,plain,(
    k4_tarski('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_72])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_126])).

tff(c_354,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_358,plain,(
    k4_tarski('#skF_8','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_72])).

tff(c_586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_584,c_358])).
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
% 0.12/0.34  % DateTime   : Tue Dec  1 16:22:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.41  
% 2.22/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.41  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 2.22/1.41  
% 2.22/1.41  %Foreground sorts:
% 2.22/1.41  
% 2.22/1.41  
% 2.22/1.41  %Background operators:
% 2.22/1.41  
% 2.22/1.41  
% 2.22/1.41  %Foreground operators:
% 2.22/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.22/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.22/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.22/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.22/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.41  tff('#skF_9', type, '#skF_9': $i).
% 2.22/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.22/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.22/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.22/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.22/1.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.22/1.41  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.22/1.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.22/1.41  
% 2.22/1.43  tff(f_65, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.22/1.43  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.22/1.43  tff(f_43, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.22/1.43  tff(f_76, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.22/1.43  tff(f_96, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.22/1.43  tff(f_106, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.22/1.43  tff(f_80, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.22/1.43  tff(c_40, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.43  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.43  tff(c_405, plain, (![A_103, B_104]: (k4_xboole_0(A_103, B_104)=k1_xboole_0 | ~r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.43  tff(c_413, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_405])).
% 2.22/1.43  tff(c_497, plain, (![B_116, A_117]: (~r2_hidden(B_116, A_117) | k4_xboole_0(A_117, k1_tarski(B_116))!=A_117)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.22/1.43  tff(c_504, plain, (![B_116]: (~r2_hidden(B_116, k1_tarski(B_116)) | k1_tarski(B_116)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_413, c_497])).
% 2.22/1.43  tff(c_507, plain, (![B_116]: (k1_tarski(B_116)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_504])).
% 2.22/1.43  tff(c_64, plain, (![A_29]: (r2_hidden('#skF_6'(A_29), A_29) | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.22/1.43  tff(c_388, plain, (![C_99, A_100]: (C_99=A_100 | ~r2_hidden(C_99, k1_tarski(A_100)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.43  tff(c_400, plain, (![A_100]: ('#skF_6'(k1_tarski(A_100))=A_100 | k1_tarski(A_100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_388])).
% 2.22/1.43  tff(c_509, plain, (![A_100]: ('#skF_6'(k1_tarski(A_100))=A_100)), inference(negUnitSimplification, [status(thm)], [c_507, c_400])).
% 2.22/1.43  tff(c_558, plain, (![D_126, A_127, C_128]: (~r2_hidden(D_126, A_127) | k4_tarski(C_128, D_126)!='#skF_6'(A_127) | k1_xboole_0=A_127)), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.22/1.43  tff(c_574, plain, (![C_128, C_18]: (k4_tarski(C_128, C_18)!='#skF_6'(k1_tarski(C_18)) | k1_tarski(C_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_558])).
% 2.22/1.43  tff(c_583, plain, (![C_128, C_18]: (k4_tarski(C_128, C_18)!=C_18 | k1_tarski(C_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_509, c_574])).
% 2.22/1.43  tff(c_584, plain, (![C_128, C_18]: (k4_tarski(C_128, C_18)!=C_18)), inference(negUnitSimplification, [status(thm)], [c_507, c_583])).
% 2.22/1.43  tff(c_201, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=k1_xboole_0 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.43  tff(c_209, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_201])).
% 2.22/1.43  tff(c_264, plain, (![B_76, A_77]: (~r2_hidden(B_76, A_77) | k4_xboole_0(A_77, k1_tarski(B_76))!=A_77)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.22/1.43  tff(c_268, plain, (![B_76]: (~r2_hidden(B_76, k1_tarski(B_76)) | k1_tarski(B_76)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_209, c_264])).
% 2.22/1.43  tff(c_273, plain, (![B_76]: (k1_tarski(B_76)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_268])).
% 2.22/1.43  tff(c_162, plain, (![A_51]: (r2_hidden('#skF_6'(A_51), A_51) | k1_xboole_0=A_51)), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.22/1.43  tff(c_38, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.43  tff(c_167, plain, (![A_14]: ('#skF_6'(k1_tarski(A_14))=A_14 | k1_tarski(A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_162, c_38])).
% 2.22/1.43  tff(c_275, plain, (![A_14]: ('#skF_6'(k1_tarski(A_14))=A_14)), inference(negUnitSimplification, [status(thm)], [c_273, c_167])).
% 2.22/1.43  tff(c_325, plain, (![C_86, A_87, D_88]: (~r2_hidden(C_86, A_87) | k4_tarski(C_86, D_88)!='#skF_6'(A_87) | k1_xboole_0=A_87)), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.22/1.43  tff(c_341, plain, (![C_18, D_88]: (k4_tarski(C_18, D_88)!='#skF_6'(k1_tarski(C_18)) | k1_tarski(C_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_325])).
% 2.22/1.43  tff(c_350, plain, (![C_18, D_88]: (k4_tarski(C_18, D_88)!=C_18 | k1_tarski(C_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_275, c_341])).
% 2.22/1.43  tff(c_351, plain, (![C_18, D_88]: (k4_tarski(C_18, D_88)!=C_18)), inference(negUnitSimplification, [status(thm)], [c_273, c_350])).
% 2.22/1.43  tff(c_72, plain, (k4_tarski('#skF_8', '#skF_9')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.22/1.43  tff(c_105, plain, (![A_46, B_47]: (k1_mcart_1(k4_tarski(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.43  tff(c_114, plain, (k1_mcart_1('#skF_7')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_72, c_105])).
% 2.22/1.43  tff(c_80, plain, (![A_43, B_44]: (k2_mcart_1(k4_tarski(A_43, B_44))=B_44)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.43  tff(c_89, plain, (k2_mcart_1('#skF_7')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_72, c_80])).
% 2.22/1.43  tff(c_70, plain, (k2_mcart_1('#skF_7')='#skF_7' | k1_mcart_1('#skF_7')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.22/1.43  tff(c_122, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_89, c_70])).
% 2.22/1.43  tff(c_123, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_122])).
% 2.22/1.43  tff(c_126, plain, (k4_tarski('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_72])).
% 2.22/1.43  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_351, c_126])).
% 2.22/1.43  tff(c_354, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_122])).
% 2.22/1.43  tff(c_358, plain, (k4_tarski('#skF_8', '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_354, c_72])).
% 2.22/1.43  tff(c_586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_584, c_358])).
% 2.22/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.43  
% 2.22/1.43  Inference rules
% 2.22/1.43  ----------------------
% 2.22/1.43  #Ref     : 0
% 2.22/1.43  #Sup     : 122
% 2.22/1.43  #Fact    : 0
% 2.22/1.43  #Define  : 0
% 2.22/1.43  #Split   : 1
% 2.22/1.43  #Chain   : 0
% 2.22/1.43  #Close   : 0
% 2.22/1.43  
% 2.22/1.43  Ordering : KBO
% 2.22/1.43  
% 2.22/1.43  Simplification rules
% 2.22/1.43  ----------------------
% 2.22/1.43  #Subsume      : 0
% 2.22/1.43  #Demod        : 38
% 2.22/1.43  #Tautology    : 91
% 2.22/1.43  #SimpNegUnit  : 12
% 2.22/1.43  #BackRed      : 12
% 2.22/1.43  
% 2.22/1.43  #Partial instantiations: 0
% 2.22/1.43  #Strategies tried      : 1
% 2.22/1.43  
% 2.22/1.43  Timing (in seconds)
% 2.22/1.43  ----------------------
% 2.22/1.43  Preprocessing        : 0.32
% 2.22/1.43  Parsing              : 0.16
% 2.22/1.43  CNF conversion       : 0.03
% 2.22/1.43  Main loop            : 0.24
% 2.22/1.43  Inferencing          : 0.09
% 2.22/1.43  Reduction            : 0.08
% 2.22/1.43  Demodulation         : 0.05
% 2.22/1.43  BG Simplification    : 0.02
% 2.22/1.43  Subsumption          : 0.04
% 2.22/1.43  Abstraction          : 0.02
% 2.22/1.43  MUC search           : 0.00
% 2.22/1.43  Cooper               : 0.00
% 2.22/1.43  Total                : 0.59
% 2.22/1.43  Index Insertion      : 0.00
% 2.22/1.43  Index Deletion       : 0.00
% 2.22/1.43  Index Matching       : 0.00
% 2.22/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
