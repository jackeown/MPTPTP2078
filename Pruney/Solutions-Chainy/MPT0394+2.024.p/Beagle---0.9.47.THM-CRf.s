%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:24 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   65 (  99 expanded)
%              Number of leaves         :   32 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 113 expanded)
%              Number of equality atoms :   50 (  80 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_58,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_38,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_82,plain,(
    ! [A_44,B_45] : k1_enumset1(A_44,A_44,B_45) = k2_tarski(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [E_13,A_7,B_8] : r2_hidden(E_13,k1_enumset1(A_7,B_8,E_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_100,plain,(
    ! [B_46,A_47] : r2_hidden(B_46,k2_tarski(A_47,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_14])).

tff(c_103,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_100])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = A_51
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_154,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k4_xboole_0(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_169,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_154])).

tff(c_172,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_169])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden(A_56,B_57)
      | ~ r1_xboole_0(k1_tarski(A_56),B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_239,plain,(
    ! [A_69,B_70] :
      ( ~ r2_hidden(A_69,B_70)
      | k4_xboole_0(k1_tarski(A_69),B_70) != k1_tarski(A_69) ) ),
    inference(resolution,[status(thm)],[c_10,c_130])).

tff(c_243,plain,(
    ! [A_69] :
      ( ~ r2_hidden(A_69,k1_tarski(A_69))
      | k1_tarski(A_69) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_239])).

tff(c_253,plain,(
    ! [A_69] : k1_tarski(A_69) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_243])).

tff(c_50,plain,(
    ! [A_30] : k1_setfam_1(k1_tarski(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42,plain,(
    ! [A_21,B_22,C_23] : k2_enumset1(A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_255,plain,(
    ! [A_71,B_72,C_73,D_74] : k2_xboole_0(k1_enumset1(A_71,B_72,C_73),k1_tarski(D_74)) = k2_enumset1(A_71,B_72,C_73,D_74) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_264,plain,(
    ! [A_19,B_20,D_74] : k2_xboole_0(k2_tarski(A_19,B_20),k1_tarski(D_74)) = k2_enumset1(A_19,A_19,B_20,D_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_255])).

tff(c_269,plain,(
    ! [A_76,B_77,D_78] : k2_xboole_0(k2_tarski(A_76,B_77),k1_tarski(D_78)) = k1_enumset1(A_76,B_77,D_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_264])).

tff(c_278,plain,(
    ! [A_18,D_78] : k2_xboole_0(k1_tarski(A_18),k1_tarski(D_78)) = k1_enumset1(A_18,A_18,D_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_269])).

tff(c_281,plain,(
    ! [A_18,D_78] : k2_xboole_0(k1_tarski(A_18),k1_tarski(D_78)) = k2_tarski(A_18,D_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_278])).

tff(c_369,plain,(
    ! [A_91,B_92] :
      ( k3_xboole_0(k1_setfam_1(A_91),k1_setfam_1(B_92)) = k1_setfam_1(k2_xboole_0(A_91,B_92))
      | k1_xboole_0 = B_92
      | k1_xboole_0 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_389,plain,(
    ! [A_30,B_92] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_30),B_92)) = k3_xboole_0(A_30,k1_setfam_1(B_92))
      | k1_xboole_0 = B_92
      | k1_tarski(A_30) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_369])).

tff(c_451,plain,(
    ! [A_101,B_102] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_101),B_102)) = k3_xboole_0(A_101,k1_setfam_1(B_102))
      | k1_xboole_0 = B_102 ) ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_389])).

tff(c_474,plain,(
    ! [A_18,D_78] :
      ( k3_xboole_0(A_18,k1_setfam_1(k1_tarski(D_78))) = k1_setfam_1(k2_tarski(A_18,D_78))
      | k1_tarski(D_78) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_451])).

tff(c_485,plain,(
    ! [A_18,D_78] :
      ( k1_setfam_1(k2_tarski(A_18,D_78)) = k3_xboole_0(A_18,D_78)
      | k1_tarski(D_78) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_474])).

tff(c_486,plain,(
    ! [A_18,D_78] : k1_setfam_1(k2_tarski(A_18,D_78)) = k3_xboole_0(A_18,D_78) ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_485])).

tff(c_52,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.38  
% 2.26/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.38  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.26/1.38  
% 2.26/1.38  %Foreground sorts:
% 2.26/1.38  
% 2.26/1.38  
% 2.26/1.38  %Background operators:
% 2.26/1.38  
% 2.26/1.38  
% 2.26/1.38  %Foreground operators:
% 2.26/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.26/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.26/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.26/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.26/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.26/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.26/1.38  
% 2.60/1.39  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.60/1.39  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.60/1.39  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.60/1.39  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.60/1.39  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.60/1.39  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.60/1.39  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.60/1.39  tff(f_63, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.60/1.39  tff(f_77, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.60/1.39  tff(f_58, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.60/1.39  tff(f_52, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.60/1.39  tff(f_75, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.60/1.39  tff(f_80, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.60/1.39  tff(c_38, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.60/1.39  tff(c_82, plain, (![A_44, B_45]: (k1_enumset1(A_44, A_44, B_45)=k2_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.39  tff(c_14, plain, (![E_13, A_7, B_8]: (r2_hidden(E_13, k1_enumset1(A_7, B_8, E_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.60/1.39  tff(c_100, plain, (![B_46, A_47]: (r2_hidden(B_46, k2_tarski(A_47, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_14])).
% 2.60/1.39  tff(c_103, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_100])).
% 2.60/1.39  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.39  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.39  tff(c_111, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=A_51 | ~r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.39  tff(c_115, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(resolution, [status(thm)], [c_6, c_111])).
% 2.60/1.39  tff(c_154, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k4_xboole_0(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.39  tff(c_169, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_115, c_154])).
% 2.60/1.39  tff(c_172, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_169])).
% 2.60/1.39  tff(c_10, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k4_xboole_0(A_5, B_6)!=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.39  tff(c_130, plain, (![A_56, B_57]: (~r2_hidden(A_56, B_57) | ~r1_xboole_0(k1_tarski(A_56), B_57))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.60/1.39  tff(c_239, plain, (![A_69, B_70]: (~r2_hidden(A_69, B_70) | k4_xboole_0(k1_tarski(A_69), B_70)!=k1_tarski(A_69))), inference(resolution, [status(thm)], [c_10, c_130])).
% 2.60/1.39  tff(c_243, plain, (![A_69]: (~r2_hidden(A_69, k1_tarski(A_69)) | k1_tarski(A_69)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_172, c_239])).
% 2.60/1.39  tff(c_253, plain, (![A_69]: (k1_tarski(A_69)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_243])).
% 2.60/1.39  tff(c_50, plain, (![A_30]: (k1_setfam_1(k1_tarski(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.60/1.39  tff(c_40, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.39  tff(c_42, plain, (![A_21, B_22, C_23]: (k2_enumset1(A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.60/1.39  tff(c_255, plain, (![A_71, B_72, C_73, D_74]: (k2_xboole_0(k1_enumset1(A_71, B_72, C_73), k1_tarski(D_74))=k2_enumset1(A_71, B_72, C_73, D_74))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.60/1.39  tff(c_264, plain, (![A_19, B_20, D_74]: (k2_xboole_0(k2_tarski(A_19, B_20), k1_tarski(D_74))=k2_enumset1(A_19, A_19, B_20, D_74))), inference(superposition, [status(thm), theory('equality')], [c_40, c_255])).
% 2.60/1.39  tff(c_269, plain, (![A_76, B_77, D_78]: (k2_xboole_0(k2_tarski(A_76, B_77), k1_tarski(D_78))=k1_enumset1(A_76, B_77, D_78))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_264])).
% 2.60/1.39  tff(c_278, plain, (![A_18, D_78]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(D_78))=k1_enumset1(A_18, A_18, D_78))), inference(superposition, [status(thm), theory('equality')], [c_38, c_269])).
% 2.60/1.39  tff(c_281, plain, (![A_18, D_78]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(D_78))=k2_tarski(A_18, D_78))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_278])).
% 2.60/1.39  tff(c_369, plain, (![A_91, B_92]: (k3_xboole_0(k1_setfam_1(A_91), k1_setfam_1(B_92))=k1_setfam_1(k2_xboole_0(A_91, B_92)) | k1_xboole_0=B_92 | k1_xboole_0=A_91)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.60/1.39  tff(c_389, plain, (![A_30, B_92]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_30), B_92))=k3_xboole_0(A_30, k1_setfam_1(B_92)) | k1_xboole_0=B_92 | k1_tarski(A_30)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_369])).
% 2.60/1.39  tff(c_451, plain, (![A_101, B_102]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_101), B_102))=k3_xboole_0(A_101, k1_setfam_1(B_102)) | k1_xboole_0=B_102)), inference(negUnitSimplification, [status(thm)], [c_253, c_389])).
% 2.60/1.39  tff(c_474, plain, (![A_18, D_78]: (k3_xboole_0(A_18, k1_setfam_1(k1_tarski(D_78)))=k1_setfam_1(k2_tarski(A_18, D_78)) | k1_tarski(D_78)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_281, c_451])).
% 2.60/1.39  tff(c_485, plain, (![A_18, D_78]: (k1_setfam_1(k2_tarski(A_18, D_78))=k3_xboole_0(A_18, D_78) | k1_tarski(D_78)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_474])).
% 2.60/1.39  tff(c_486, plain, (![A_18, D_78]: (k1_setfam_1(k2_tarski(A_18, D_78))=k3_xboole_0(A_18, D_78))), inference(negUnitSimplification, [status(thm)], [c_253, c_485])).
% 2.60/1.39  tff(c_52, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.39  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_486, c_52])).
% 2.60/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.39  
% 2.60/1.39  Inference rules
% 2.60/1.39  ----------------------
% 2.60/1.39  #Ref     : 0
% 2.60/1.39  #Sup     : 98
% 2.60/1.39  #Fact    : 0
% 2.60/1.39  #Define  : 0
% 2.60/1.39  #Split   : 0
% 2.60/1.39  #Chain   : 0
% 2.60/1.39  #Close   : 0
% 2.60/1.39  
% 2.60/1.39  Ordering : KBO
% 2.60/1.39  
% 2.60/1.39  Simplification rules
% 2.60/1.39  ----------------------
% 2.60/1.39  #Subsume      : 3
% 2.60/1.39  #Demod        : 34
% 2.60/1.39  #Tautology    : 64
% 2.60/1.39  #SimpNegUnit  : 8
% 2.60/1.39  #BackRed      : 1
% 2.60/1.39  
% 2.60/1.39  #Partial instantiations: 0
% 2.60/1.39  #Strategies tried      : 1
% 2.60/1.39  
% 2.60/1.39  Timing (in seconds)
% 2.60/1.39  ----------------------
% 2.60/1.40  Preprocessing        : 0.33
% 2.60/1.40  Parsing              : 0.17
% 2.60/1.40  CNF conversion       : 0.02
% 2.60/1.40  Main loop            : 0.24
% 2.60/1.40  Inferencing          : 0.09
% 2.60/1.40  Reduction            : 0.07
% 2.60/1.40  Demodulation         : 0.05
% 2.60/1.40  BG Simplification    : 0.02
% 2.60/1.40  Subsumption          : 0.04
% 2.60/1.40  Abstraction          : 0.02
% 2.60/1.40  MUC search           : 0.00
% 2.60/1.40  Cooper               : 0.00
% 2.60/1.40  Total                : 0.59
% 2.60/1.40  Index Insertion      : 0.00
% 2.60/1.40  Index Deletion       : 0.00
% 2.60/1.40  Index Matching       : 0.00
% 2.60/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
