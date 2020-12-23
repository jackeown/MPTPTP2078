%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:41 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   58 (  63 expanded)
%              Number of leaves         :   32 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   51 (  60 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_46,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    ! [A_41,B_42] :
      ( r1_xboole_0(k1_tarski(A_41),B_42)
      | r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    ! [C_25] : r2_hidden(C_25,k1_tarski(C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,(
    ! [B_46,A_47] :
      ( ~ r2_hidden(B_46,A_47)
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_80,plain,(
    ! [C_25] : ~ v1_xboole_0(k1_tarski(C_25)) ),
    inference(resolution,[status(thm)],[c_24,c_76])).

tff(c_14,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [B_52,A_53] : k5_xboole_0(B_52,A_53) = k5_xboole_0(A_53,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [A_53] : k5_xboole_0(k1_xboole_0,A_53) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_14])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_389,plain,(
    ! [A_78,B_79,C_80] : k5_xboole_0(k5_xboole_0(A_78,B_79),C_80) = k5_xboole_0(A_78,k5_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_475,plain,(
    ! [A_18,C_80] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_80)) = k5_xboole_0(k1_xboole_0,C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_389])).

tff(c_489,plain,(
    ! [A_81,C_82] : k5_xboole_0(A_81,k5_xboole_0(A_81,C_82)) = C_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_475])).

tff(c_1336,plain,(
    ! [A_1311,B_1312] : k5_xboole_0(A_1311,k4_xboole_0(A_1311,B_1312)) = k3_xboole_0(A_1311,B_1312) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_489])).

tff(c_1392,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k5_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1336])).

tff(c_1399,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1392])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_234,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_239,plain,(
    ! [A_61,B_62] :
      ( ~ r1_xboole_0(A_61,B_62)
      | v1_xboole_0(k3_xboole_0(A_61,B_62)) ) ),
    inference(resolution,[status(thm)],[c_6,c_234])).

tff(c_1462,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6'))
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1399,c_239])).

tff(c_1556,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1462])).

tff(c_1571,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_1556])).

tff(c_22,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1574,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1571,c_22])).

tff(c_1615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:56:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.48  
% 3.19/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.48  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.19/1.48  
% 3.19/1.48  %Foreground sorts:
% 3.19/1.48  
% 3.19/1.48  
% 3.19/1.48  %Background operators:
% 3.19/1.48  
% 3.19/1.48  
% 3.19/1.48  %Foreground operators:
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.19/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.19/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.19/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.19/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.19/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.19/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.19/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.19/1.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.19/1.48  
% 3.19/1.49  tff(f_84, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 3.19/1.49  tff(f_79, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.19/1.49  tff(f_64, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.19/1.49  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.19/1.49  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.19/1.49  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.19/1.49  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.19/1.49  tff(f_55, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.19/1.49  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.19/1.49  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.19/1.49  tff(c_46, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.19/1.49  tff(c_44, plain, (![A_41, B_42]: (r1_xboole_0(k1_tarski(A_41), B_42) | r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.19/1.49  tff(c_24, plain, (![C_25]: (r2_hidden(C_25, k1_tarski(C_25)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.19/1.49  tff(c_76, plain, (![B_46, A_47]: (~r2_hidden(B_46, A_47) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.49  tff(c_80, plain, (![C_25]: (~v1_xboole_0(k1_tarski(C_25)))), inference(resolution, [status(thm)], [c_24, c_76])).
% 3.19/1.49  tff(c_14, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.49  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.19/1.49  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.19/1.49  tff(c_101, plain, (![B_52, A_53]: (k5_xboole_0(B_52, A_53)=k5_xboole_0(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.19/1.49  tff(c_117, plain, (![A_53]: (k5_xboole_0(k1_xboole_0, A_53)=A_53)), inference(superposition, [status(thm), theory('equality')], [c_101, c_14])).
% 3.19/1.49  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.19/1.49  tff(c_389, plain, (![A_78, B_79, C_80]: (k5_xboole_0(k5_xboole_0(A_78, B_79), C_80)=k5_xboole_0(A_78, k5_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.19/1.49  tff(c_475, plain, (![A_18, C_80]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_80))=k5_xboole_0(k1_xboole_0, C_80))), inference(superposition, [status(thm), theory('equality')], [c_18, c_389])).
% 3.19/1.49  tff(c_489, plain, (![A_81, C_82]: (k5_xboole_0(A_81, k5_xboole_0(A_81, C_82))=C_82)), inference(demodulation, [status(thm), theory('equality')], [c_117, c_475])).
% 3.19/1.49  tff(c_1336, plain, (![A_1311, B_1312]: (k5_xboole_0(A_1311, k4_xboole_0(A_1311, B_1312))=k3_xboole_0(A_1311, B_1312))), inference(superposition, [status(thm), theory('equality')], [c_12, c_489])).
% 3.19/1.49  tff(c_1392, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k5_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_1336])).
% 3.19/1.49  tff(c_1399, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1392])).
% 3.19/1.49  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.49  tff(c_234, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.49  tff(c_239, plain, (![A_61, B_62]: (~r1_xboole_0(A_61, B_62) | v1_xboole_0(k3_xboole_0(A_61, B_62)))), inference(resolution, [status(thm)], [c_6, c_234])).
% 3.19/1.49  tff(c_1462, plain, (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6')) | v1_xboole_0(k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1399, c_239])).
% 3.19/1.49  tff(c_1556, plain, (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_1462])).
% 3.19/1.49  tff(c_1571, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_1556])).
% 3.19/1.49  tff(c_22, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.19/1.49  tff(c_1574, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1571, c_22])).
% 3.19/1.49  tff(c_1615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1574])).
% 3.19/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.49  
% 3.19/1.49  Inference rules
% 3.19/1.49  ----------------------
% 3.19/1.49  #Ref     : 0
% 3.19/1.49  #Sup     : 282
% 3.19/1.49  #Fact    : 0
% 3.19/1.49  #Define  : 0
% 3.19/1.49  #Split   : 3
% 3.19/1.49  #Chain   : 0
% 3.19/1.49  #Close   : 0
% 3.19/1.49  
% 3.19/1.49  Ordering : KBO
% 3.19/1.49  
% 3.19/1.49  Simplification rules
% 3.19/1.49  ----------------------
% 3.19/1.49  #Subsume      : 8
% 3.19/1.49  #Demod        : 102
% 3.19/1.49  #Tautology    : 160
% 3.19/1.49  #SimpNegUnit  : 6
% 3.19/1.49  #BackRed      : 0
% 3.19/1.49  
% 3.19/1.49  #Partial instantiations: 736
% 3.19/1.49  #Strategies tried      : 1
% 3.19/1.49  
% 3.19/1.49  Timing (in seconds)
% 3.19/1.49  ----------------------
% 3.19/1.50  Preprocessing        : 0.32
% 3.19/1.50  Parsing              : 0.17
% 3.19/1.50  CNF conversion       : 0.02
% 3.19/1.50  Main loop            : 0.42
% 3.19/1.50  Inferencing          : 0.19
% 3.19/1.50  Reduction            : 0.14
% 3.19/1.50  Demodulation         : 0.11
% 3.19/1.50  BG Simplification    : 0.02
% 3.19/1.50  Subsumption          : 0.05
% 3.19/1.50  Abstraction          : 0.02
% 3.19/1.50  MUC search           : 0.00
% 3.19/1.50  Cooper               : 0.00
% 3.19/1.50  Total                : 0.77
% 3.19/1.50  Index Insertion      : 0.00
% 3.19/1.50  Index Deletion       : 0.00
% 3.19/1.50  Index Matching       : 0.00
% 3.19/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
