%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:34 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   61 (  61 expanded)
%              Number of leaves         :   36 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  51 expanded)
%              Number of equality atoms :   30 (  30 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_82,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A] : k6_subset_1(k1_ordinal1(A),k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_ordinal1)).

tff(c_20,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(k1_tarski(A_26),B_27)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13,D_14] : k3_enumset1(A_11,A_11,B_12,C_13,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_353,plain,(
    ! [C_151,A_155,B_153,D_152,E_154] : k4_enumset1(A_155,A_155,B_153,C_151,D_152,E_154) = k3_enumset1(A_155,B_153,C_151,D_152,E_154) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    ! [B_33,H_41,C_34,E_36,F_37,D_35] : r2_hidden(H_41,k4_enumset1(H_41,B_33,C_34,D_35,E_36,F_37)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_399,plain,(
    ! [C_156,D_159,A_157,B_158,E_160] : r2_hidden(A_157,k3_enumset1(A_157,B_158,C_156,D_159,E_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_40])).

tff(c_416,plain,(
    ! [A_167,B_168,C_169,D_170] : r2_hidden(A_167,k2_enumset1(A_167,B_168,C_169,D_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_399])).

tff(c_424,plain,(
    ! [A_171,B_172,C_173] : r2_hidden(A_171,k1_enumset1(A_171,B_172,C_173)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_416])).

tff(c_432,plain,(
    ! [A_174,B_175] : r2_hidden(A_174,k2_tarski(A_174,B_175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_424])).

tff(c_440,plain,(
    ! [A_176] : r2_hidden(A_176,k1_tarski(A_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_432])).

tff(c_76,plain,(
    ! [B_48,A_47] :
      ( ~ r1_tarski(B_48,A_47)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_445,plain,(
    ! [A_177] : ~ r1_tarski(k1_tarski(A_177),A_177) ),
    inference(resolution,[status(thm)],[c_440,c_76])).

tff(c_450,plain,(
    ! [B_27] : ~ r2_hidden(B_27,B_27) ),
    inference(resolution,[status(thm)],[c_20,c_445])).

tff(c_26,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,k1_tarski(B_31)) = A_30
      | r2_hidden(B_31,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_74,plain,(
    ! [A_46] : k2_xboole_0(A_46,k1_tarski(A_46)) = k1_ordinal1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_199,plain,(
    ! [A_71,B_72] : k4_xboole_0(k2_xboole_0(A_71,B_72),B_72) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_223,plain,(
    ! [A_46] : k4_xboole_0(k1_ordinal1(A_46),k1_tarski(A_46)) = k4_xboole_0(A_46,k1_tarski(A_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_199])).

tff(c_70,plain,(
    ! [A_42,B_43] : k6_subset_1(A_42,B_43) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_78,plain,(
    k6_subset_1(k1_ordinal1('#skF_3'),k1_tarski('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_79,plain,(
    k4_xboole_0(k1_ordinal1('#skF_3'),k1_tarski('#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_78])).

tff(c_329,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_79])).

tff(c_352,plain,(
    r2_hidden('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_329])).

tff(c_486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_450,c_352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:00:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.42  
% 2.63/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.42  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 2.63/1.42  
% 2.63/1.42  %Foreground sorts:
% 2.63/1.42  
% 2.63/1.42  
% 2.63/1.42  %Background operators:
% 2.63/1.42  
% 2.63/1.42  
% 2.63/1.42  %Foreground operators:
% 2.63/1.42  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.63/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.63/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.42  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.63/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.63/1.42  
% 2.63/1.44  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.63/1.44  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.63/1.44  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.63/1.44  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.63/1.44  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.63/1.44  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.63/1.44  tff(f_76, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 2.63/1.44  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.63/1.44  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.63/1.44  tff(f_82, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.63/1.44  tff(f_29, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.63/1.44  tff(f_78, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.63/1.44  tff(f_90, negated_conjecture, ~(![A]: (k6_subset_1(k1_ordinal1(A), k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_ordinal1)).
% 2.63/1.44  tff(c_20, plain, (![A_26, B_27]: (r1_tarski(k1_tarski(A_26), B_27) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.44  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.44  tff(c_8, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.44  tff(c_10, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.44  tff(c_12, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.63/1.44  tff(c_353, plain, (![C_151, A_155, B_153, D_152, E_154]: (k4_enumset1(A_155, A_155, B_153, C_151, D_152, E_154)=k3_enumset1(A_155, B_153, C_151, D_152, E_154))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.63/1.44  tff(c_40, plain, (![B_33, H_41, C_34, E_36, F_37, D_35]: (r2_hidden(H_41, k4_enumset1(H_41, B_33, C_34, D_35, E_36, F_37)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.63/1.44  tff(c_399, plain, (![C_156, D_159, A_157, B_158, E_160]: (r2_hidden(A_157, k3_enumset1(A_157, B_158, C_156, D_159, E_160)))), inference(superposition, [status(thm), theory('equality')], [c_353, c_40])).
% 2.63/1.44  tff(c_416, plain, (![A_167, B_168, C_169, D_170]: (r2_hidden(A_167, k2_enumset1(A_167, B_168, C_169, D_170)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_399])).
% 2.63/1.44  tff(c_424, plain, (![A_171, B_172, C_173]: (r2_hidden(A_171, k1_enumset1(A_171, B_172, C_173)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_416])).
% 2.63/1.44  tff(c_432, plain, (![A_174, B_175]: (r2_hidden(A_174, k2_tarski(A_174, B_175)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_424])).
% 2.63/1.44  tff(c_440, plain, (![A_176]: (r2_hidden(A_176, k1_tarski(A_176)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_432])).
% 2.63/1.44  tff(c_76, plain, (![B_48, A_47]: (~r1_tarski(B_48, A_47) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.63/1.44  tff(c_445, plain, (![A_177]: (~r1_tarski(k1_tarski(A_177), A_177))), inference(resolution, [status(thm)], [c_440, c_76])).
% 2.63/1.44  tff(c_450, plain, (![B_27]: (~r2_hidden(B_27, B_27))), inference(resolution, [status(thm)], [c_20, c_445])).
% 2.63/1.44  tff(c_26, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k1_tarski(B_31))=A_30 | r2_hidden(B_31, A_30))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.63/1.44  tff(c_74, plain, (![A_46]: (k2_xboole_0(A_46, k1_tarski(A_46))=k1_ordinal1(A_46))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.63/1.44  tff(c_199, plain, (![A_71, B_72]: (k4_xboole_0(k2_xboole_0(A_71, B_72), B_72)=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.44  tff(c_223, plain, (![A_46]: (k4_xboole_0(k1_ordinal1(A_46), k1_tarski(A_46))=k4_xboole_0(A_46, k1_tarski(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_199])).
% 2.63/1.44  tff(c_70, plain, (![A_42, B_43]: (k6_subset_1(A_42, B_43)=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.63/1.44  tff(c_78, plain, (k6_subset_1(k1_ordinal1('#skF_3'), k1_tarski('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.63/1.44  tff(c_79, plain, (k4_xboole_0(k1_ordinal1('#skF_3'), k1_tarski('#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_78])).
% 2.63/1.44  tff(c_329, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_223, c_79])).
% 2.63/1.44  tff(c_352, plain, (r2_hidden('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_329])).
% 2.63/1.44  tff(c_486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_450, c_352])).
% 2.63/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.44  
% 2.63/1.44  Inference rules
% 2.63/1.44  ----------------------
% 2.63/1.44  #Ref     : 0
% 2.63/1.44  #Sup     : 95
% 2.63/1.44  #Fact    : 0
% 2.63/1.44  #Define  : 0
% 2.63/1.44  #Split   : 1
% 2.63/1.44  #Chain   : 0
% 2.63/1.44  #Close   : 0
% 2.63/1.44  
% 2.63/1.44  Ordering : KBO
% 2.63/1.44  
% 2.63/1.44  Simplification rules
% 2.63/1.44  ----------------------
% 2.63/1.44  #Subsume      : 0
% 2.63/1.44  #Demod        : 4
% 2.63/1.44  #Tautology    : 50
% 2.63/1.44  #SimpNegUnit  : 1
% 2.63/1.44  #BackRed      : 2
% 2.63/1.44  
% 2.63/1.44  #Partial instantiations: 0
% 2.63/1.44  #Strategies tried      : 1
% 2.63/1.44  
% 2.63/1.44  Timing (in seconds)
% 2.63/1.44  ----------------------
% 2.63/1.44  Preprocessing        : 0.35
% 2.63/1.44  Parsing              : 0.18
% 2.63/1.44  CNF conversion       : 0.02
% 2.63/1.44  Main loop            : 0.25
% 2.63/1.44  Inferencing          : 0.09
% 2.63/1.44  Reduction            : 0.07
% 2.63/1.44  Demodulation         : 0.05
% 2.63/1.44  BG Simplification    : 0.02
% 2.63/1.44  Subsumption          : 0.06
% 2.63/1.44  Abstraction          : 0.02
% 2.63/1.44  MUC search           : 0.00
% 2.63/1.44  Cooper               : 0.00
% 2.63/1.44  Total                : 0.64
% 2.63/1.44  Index Insertion      : 0.00
% 2.63/1.44  Index Deletion       : 0.00
% 2.63/1.44  Index Matching       : 0.00
% 2.63/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
