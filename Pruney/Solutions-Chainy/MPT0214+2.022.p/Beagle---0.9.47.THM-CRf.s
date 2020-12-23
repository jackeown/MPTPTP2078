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
% DateTime   : Thu Dec  3 09:47:32 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   61 (  70 expanded)
%              Number of leaves         :   35 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  76 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_84,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_118,plain,(
    ! [A_71,B_72] : k1_enumset1(A_71,A_71,B_72) = k2_tarski(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_127,plain,(
    ! [B_72,A_71] : r2_hidden(B_72,k2_tarski(A_71,B_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_30])).

tff(c_26,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(A_77,B_78) = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_159,plain,(
    ! [A_11] : k3_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_147])).

tff(c_181,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_196,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_181])).

tff(c_200,plain,(
    ! [A_86] : k4_xboole_0(k1_xboole_0,A_86) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_196])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_210,plain,(
    ! [D_87,A_88] :
      ( ~ r2_hidden(D_87,A_88)
      | ~ r2_hidden(D_87,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_4])).

tff(c_223,plain,(
    ! [B_72] : ~ r2_hidden(B_72,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_127,c_210])).

tff(c_86,plain,(
    r1_tarski(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_239,plain,(
    ! [B_93,A_94] :
      ( k1_tarski(B_93) = A_94
      | k1_xboole_0 = A_94
      | ~ r1_tarski(A_94,k1_tarski(B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_252,plain,
    ( k1_tarski('#skF_7') = k1_tarski('#skF_8')
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_239])).

tff(c_255,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_54,plain,(
    ! [C_24] : r2_hidden(C_24,k1_tarski(C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_283,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_54])).

tff(c_292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_283])).

tff(c_293,plain,(
    k1_tarski('#skF_7') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_331,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_54])).

tff(c_52,plain,(
    ! [C_24,A_20] :
      ( C_24 = A_20
      | ~ r2_hidden(C_24,k1_tarski(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_342,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_331,c_52])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.74  
% 2.93/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.75  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 2.93/1.75  
% 2.93/1.75  %Foreground sorts:
% 2.93/1.75  
% 2.93/1.75  
% 2.93/1.75  %Background operators:
% 2.93/1.75  
% 2.93/1.75  
% 2.93/1.75  %Foreground operators:
% 2.93/1.75  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.93/1.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.93/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.93/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.75  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.93/1.75  tff('#skF_7', type, '#skF_7': $i).
% 2.93/1.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.93/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.93/1.75  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.75  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.93/1.75  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.75  tff('#skF_8', type, '#skF_8': $i).
% 2.93/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.93/1.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.93/1.75  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.75  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.93/1.75  
% 2.99/1.77  tff(f_92, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.99/1.77  tff(f_71, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.99/1.77  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.99/1.77  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.99/1.77  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.99/1.77  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.99/1.77  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.99/1.77  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.99/1.77  tff(f_87, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.99/1.77  tff(f_67, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.99/1.77  tff(c_84, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.99/1.77  tff(c_118, plain, (![A_71, B_72]: (k1_enumset1(A_71, A_71, B_72)=k2_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.99/1.77  tff(c_30, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.99/1.77  tff(c_127, plain, (![B_72, A_71]: (r2_hidden(B_72, k2_tarski(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_118, c_30])).
% 2.99/1.77  tff(c_26, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.99/1.77  tff(c_24, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.99/1.77  tff(c_147, plain, (![A_77, B_78]: (k3_xboole_0(A_77, B_78)=A_77 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.99/1.77  tff(c_159, plain, (![A_11]: (k3_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_147])).
% 2.99/1.77  tff(c_181, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.77  tff(c_196, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_159, c_181])).
% 2.99/1.77  tff(c_200, plain, (![A_86]: (k4_xboole_0(k1_xboole_0, A_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_196])).
% 2.99/1.77  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.99/1.77  tff(c_210, plain, (![D_87, A_88]: (~r2_hidden(D_87, A_88) | ~r2_hidden(D_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_200, c_4])).
% 2.99/1.77  tff(c_223, plain, (![B_72]: (~r2_hidden(B_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_127, c_210])).
% 2.99/1.77  tff(c_86, plain, (r1_tarski(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.99/1.77  tff(c_239, plain, (![B_93, A_94]: (k1_tarski(B_93)=A_94 | k1_xboole_0=A_94 | ~r1_tarski(A_94, k1_tarski(B_93)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.99/1.77  tff(c_252, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_8') | k1_tarski('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_239])).
% 2.99/1.77  tff(c_255, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_252])).
% 2.99/1.77  tff(c_54, plain, (![C_24]: (r2_hidden(C_24, k1_tarski(C_24)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.77  tff(c_283, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_255, c_54])).
% 2.99/1.77  tff(c_292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_283])).
% 2.99/1.77  tff(c_293, plain, (k1_tarski('#skF_7')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_252])).
% 2.99/1.77  tff(c_331, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_54])).
% 2.99/1.77  tff(c_52, plain, (![C_24, A_20]: (C_24=A_20 | ~r2_hidden(C_24, k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.77  tff(c_342, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_331, c_52])).
% 2.99/1.77  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_342])).
% 2.99/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.77  
% 2.99/1.77  Inference rules
% 2.99/1.77  ----------------------
% 2.99/1.77  #Ref     : 0
% 2.99/1.77  #Sup     : 62
% 2.99/1.77  #Fact    : 0
% 2.99/1.77  #Define  : 0
% 2.99/1.77  #Split   : 1
% 2.99/1.77  #Chain   : 0
% 2.99/1.77  #Close   : 0
% 2.99/1.77  
% 2.99/1.77  Ordering : KBO
% 2.99/1.77  
% 2.99/1.77  Simplification rules
% 2.99/1.77  ----------------------
% 2.99/1.77  #Subsume      : 9
% 2.99/1.77  #Demod        : 44
% 2.99/1.77  #Tautology    : 43
% 2.99/1.77  #SimpNegUnit  : 3
% 2.99/1.77  #BackRed      : 7
% 2.99/1.77  
% 2.99/1.77  #Partial instantiations: 0
% 2.99/1.77  #Strategies tried      : 1
% 2.99/1.77  
% 2.99/1.77  Timing (in seconds)
% 2.99/1.77  ----------------------
% 2.99/1.77  Preprocessing        : 0.54
% 2.99/1.77  Parsing              : 0.26
% 2.99/1.77  CNF conversion       : 0.05
% 2.99/1.77  Main loop            : 0.34
% 2.99/1.77  Inferencing          : 0.09
% 2.99/1.77  Reduction            : 0.12
% 2.99/1.77  Demodulation         : 0.09
% 2.99/1.77  BG Simplification    : 0.03
% 2.99/1.77  Subsumption          : 0.06
% 2.99/1.77  Abstraction          : 0.02
% 2.99/1.77  MUC search           : 0.00
% 2.99/1.77  Cooper               : 0.00
% 2.99/1.77  Total                : 0.92
% 2.99/1.77  Index Insertion      : 0.00
% 2.99/1.77  Index Deletion       : 0.00
% 2.99/1.77  Index Matching       : 0.00
% 2.99/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
