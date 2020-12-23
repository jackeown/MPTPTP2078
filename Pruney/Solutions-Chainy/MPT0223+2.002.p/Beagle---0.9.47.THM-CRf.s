%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:17 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   63 (  69 expanded)
%              Number of leaves         :   34 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 (  56 expanded)
%              Number of equality atoms :   42 (  49 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_64,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_56,plain,(
    ! [A_31,B_32,C_33] : k2_enumset1(A_31,A_31,B_32,C_33) = k1_enumset1(A_31,B_32,C_33) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1207,plain,(
    ! [A_1839,B_1840,C_1841,D_1842] : k2_xboole_0(k1_enumset1(A_1839,B_1840,C_1841),k1_tarski(D_1842)) = k2_enumset1(A_1839,B_1840,C_1841,D_1842) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1291,plain,(
    ! [A_29,B_30,D_1842] : k2_xboole_0(k2_tarski(A_29,B_30),k1_tarski(D_1842)) = k2_enumset1(A_29,A_29,B_30,D_1842) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1207])).

tff(c_1302,plain,(
    ! [A_1891,B_1892,D_1893] : k2_xboole_0(k2_tarski(A_1891,B_1892),k1_tarski(D_1893)) = k1_enumset1(A_1891,B_1892,D_1893) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1291])).

tff(c_1392,plain,(
    ! [A_28,D_1893] : k2_xboole_0(k1_tarski(A_28),k1_tarski(D_1893)) = k1_enumset1(A_28,A_28,D_1893) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1302])).

tff(c_1428,plain,(
    ! [A_1992,D_1993] : k2_xboole_0(k1_tarski(A_1992),k1_tarski(D_1993)) = k2_tarski(A_1992,D_1993) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1392])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_206,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_218,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_206])).

tff(c_221,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_218])).

tff(c_66,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_215,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_206])).

tff(c_290,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_215])).

tff(c_10,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_294,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_10])).

tff(c_297,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_294])).

tff(c_1449,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1428,c_297])).

tff(c_148,plain,(
    ! [A_69,B_70] : k1_enumset1(A_69,A_69,B_70) = k2_tarski(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [E_18,A_12,B_13] : r2_hidden(E_18,k1_enumset1(A_12,B_13,E_18)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_157,plain,(
    ! [B_70,A_69] : r2_hidden(B_70,k2_tarski(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_16])).

tff(c_1584,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1449,c_157])).

tff(c_38,plain,(
    ! [C_23,A_19] :
      ( C_23 = A_19
      | ~ r2_hidden(C_23,k1_tarski(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1614,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1584,c_38])).

tff(c_1654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:17:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.53  
% 2.94/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.53  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 2.94/1.53  
% 2.94/1.53  %Foreground sorts:
% 2.94/1.53  
% 2.94/1.53  
% 2.94/1.53  %Background operators:
% 2.94/1.53  
% 2.94/1.53  
% 2.94/1.53  %Foreground operators:
% 2.94/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.94/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.94/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.94/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.94/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.94/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.94/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.94/1.53  tff('#skF_5', type, '#skF_5': $i).
% 2.94/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.94/1.53  tff('#skF_6', type, '#skF_6': $i).
% 2.94/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.94/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.94/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.94/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.94/1.53  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.94/1.53  
% 3.27/1.54  tff(f_78, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.27/1.54  tff(f_65, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.27/1.54  tff(f_63, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.27/1.54  tff(f_67, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.27/1.54  tff(f_61, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.27/1.54  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.27/1.54  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.27/1.54  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.27/1.54  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.27/1.54  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.27/1.54  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.27/1.54  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.27/1.54  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.27/1.54  tff(c_54, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.54  tff(c_52, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.27/1.54  tff(c_56, plain, (![A_31, B_32, C_33]: (k2_enumset1(A_31, A_31, B_32, C_33)=k1_enumset1(A_31, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.27/1.54  tff(c_1207, plain, (![A_1839, B_1840, C_1841, D_1842]: (k2_xboole_0(k1_enumset1(A_1839, B_1840, C_1841), k1_tarski(D_1842))=k2_enumset1(A_1839, B_1840, C_1841, D_1842))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.27/1.54  tff(c_1291, plain, (![A_29, B_30, D_1842]: (k2_xboole_0(k2_tarski(A_29, B_30), k1_tarski(D_1842))=k2_enumset1(A_29, A_29, B_30, D_1842))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1207])).
% 3.27/1.54  tff(c_1302, plain, (![A_1891, B_1892, D_1893]: (k2_xboole_0(k2_tarski(A_1891, B_1892), k1_tarski(D_1893))=k1_enumset1(A_1891, B_1892, D_1893))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1291])).
% 3.27/1.54  tff(c_1392, plain, (![A_28, D_1893]: (k2_xboole_0(k1_tarski(A_28), k1_tarski(D_1893))=k1_enumset1(A_28, A_28, D_1893))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1302])).
% 3.27/1.54  tff(c_1428, plain, (![A_1992, D_1993]: (k2_xboole_0(k1_tarski(A_1992), k1_tarski(D_1993))=k2_tarski(A_1992, D_1993))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1392])).
% 3.27/1.54  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.54  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.54  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.27/1.54  tff(c_206, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.27/1.54  tff(c_218, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_206])).
% 3.27/1.54  tff(c_221, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_218])).
% 3.27/1.54  tff(c_66, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.27/1.54  tff(c_215, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_206])).
% 3.27/1.54  tff(c_290, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_221, c_215])).
% 3.27/1.54  tff(c_10, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.27/1.54  tff(c_294, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_290, c_10])).
% 3.27/1.54  tff(c_297, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_294])).
% 3.27/1.54  tff(c_1449, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1428, c_297])).
% 3.27/1.54  tff(c_148, plain, (![A_69, B_70]: (k1_enumset1(A_69, A_69, B_70)=k2_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.54  tff(c_16, plain, (![E_18, A_12, B_13]: (r2_hidden(E_18, k1_enumset1(A_12, B_13, E_18)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.27/1.54  tff(c_157, plain, (![B_70, A_69]: (r2_hidden(B_70, k2_tarski(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_148, c_16])).
% 3.27/1.54  tff(c_1584, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1449, c_157])).
% 3.27/1.54  tff(c_38, plain, (![C_23, A_19]: (C_23=A_19 | ~r2_hidden(C_23, k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.27/1.54  tff(c_1614, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1584, c_38])).
% 3.27/1.54  tff(c_1654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1614])).
% 3.27/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.54  
% 3.27/1.54  Inference rules
% 3.27/1.54  ----------------------
% 3.27/1.54  #Ref     : 0
% 3.27/1.54  #Sup     : 218
% 3.27/1.54  #Fact    : 0
% 3.27/1.54  #Define  : 0
% 3.27/1.54  #Split   : 1
% 3.27/1.54  #Chain   : 0
% 3.27/1.54  #Close   : 0
% 3.27/1.54  
% 3.27/1.54  Ordering : KBO
% 3.27/1.54  
% 3.27/1.54  Simplification rules
% 3.27/1.54  ----------------------
% 3.27/1.54  #Subsume      : 0
% 3.27/1.54  #Demod        : 118
% 3.27/1.54  #Tautology    : 108
% 3.27/1.54  #SimpNegUnit  : 1
% 3.27/1.54  #BackRed      : 0
% 3.27/1.54  
% 3.27/1.54  #Partial instantiations: 738
% 3.27/1.54  #Strategies tried      : 1
% 3.27/1.54  
% 3.27/1.54  Timing (in seconds)
% 3.27/1.54  ----------------------
% 3.27/1.55  Preprocessing        : 0.32
% 3.27/1.55  Parsing              : 0.16
% 3.27/1.55  CNF conversion       : 0.02
% 3.27/1.55  Main loop            : 0.41
% 3.27/1.55  Inferencing          : 0.20
% 3.27/1.55  Reduction            : 0.12
% 3.27/1.55  Demodulation         : 0.09
% 3.27/1.55  BG Simplification    : 0.02
% 3.27/1.55  Subsumption          : 0.05
% 3.27/1.55  Abstraction          : 0.02
% 3.27/1.55  MUC search           : 0.00
% 3.27/1.55  Cooper               : 0.00
% 3.27/1.55  Total                : 0.76
% 3.27/1.55  Index Insertion      : 0.00
% 3.27/1.55  Index Deletion       : 0.00
% 3.27/1.55  Index Matching       : 0.00
% 3.27/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
