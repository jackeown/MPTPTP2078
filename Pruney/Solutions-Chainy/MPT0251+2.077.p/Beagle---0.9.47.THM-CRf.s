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
% DateTime   : Thu Dec  3 09:50:56 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 176 expanded)
%              Number of leaves         :   35 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :   87 ( 238 expanded)
%              Number of equality atoms :   41 (  96 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_72,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_74,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_52,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ! [B_46,A_47] : k2_xboole_0(B_46,A_47) = k2_xboole_0(A_47,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_47] : k2_xboole_0(k1_xboole_0,A_47) = A_47 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_24])).

tff(c_597,plain,(
    ! [A_102,B_103] : k2_xboole_0(A_102,k4_xboole_0(B_103,A_102)) = k2_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_607,plain,(
    ! [B_103] : k4_xboole_0(B_103,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_91])).

tff(c_652,plain,(
    ! [B_104] : k4_xboole_0(B_104,k1_xboole_0) = B_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_607])).

tff(c_249,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_1'(A_72,B_73),A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    ! [A_26] : r1_xboole_0(A_26,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_160,plain,(
    ! [B_49,A_50] :
      ( r1_xboole_0(B_49,A_50)
      | ~ r1_xboole_0(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_163,plain,(
    ! [A_26] : r1_xboole_0(k1_xboole_0,A_26) ),
    inference(resolution,[status(thm)],[c_32,c_160])).

tff(c_20,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_180,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_184,plain,(
    ! [B_16] : k3_xboole_0(B_16,B_16) = B_16 ),
    inference(resolution,[status(thm)],[c_20,c_180])).

tff(c_221,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,k3_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_239,plain,(
    ! [B_69,C_70] :
      ( ~ r1_xboole_0(B_69,B_69)
      | ~ r2_hidden(C_70,B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_221])).

tff(c_246,plain,(
    ! [C_70] : ~ r2_hidden(C_70,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_163,c_239])).

tff(c_260,plain,(
    ! [B_74] : r1_tarski(k1_xboole_0,B_74) ),
    inference(resolution,[status(thm)],[c_249,c_246])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_264,plain,(
    ! [B_74] : k3_xboole_0(k1_xboole_0,B_74) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_260,c_26])).

tff(c_294,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_318,plain,(
    ! [B_81] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_294])).

tff(c_303,plain,(
    ! [B_74] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_294])).

tff(c_321,plain,(
    ! [B_81,B_74] : k4_xboole_0(k1_xboole_0,B_81) = k4_xboole_0(k1_xboole_0,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_303])).

tff(c_682,plain,(
    ! [B_74] : k4_xboole_0(k1_xboole_0,B_74) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_321])).

tff(c_381,plain,(
    ! [A_87,B_88] : k4_xboole_0(k2_xboole_0(A_87,B_88),B_88) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_413,plain,(
    ! [A_91] : k4_xboole_0(k1_xboole_0,A_91) = k4_xboole_0(A_91,A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_381])).

tff(c_437,plain,(
    ! [B_74,B_81] : k4_xboole_0(k1_xboole_0,B_74) = k4_xboole_0(B_81,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_413])).

tff(c_724,plain,(
    ! [B_81] : k4_xboole_0(B_81,B_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_437])).

tff(c_306,plain,(
    ! [B_16] : k5_xboole_0(B_16,B_16) = k4_xboole_0(B_16,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_294])).

tff(c_773,plain,(
    ! [B_16] : k5_xboole_0(B_16,B_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_724,c_306])).

tff(c_34,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_950,plain,(
    ! [A_126,B_127,C_128] :
      ( r1_tarski(k2_tarski(A_126,B_127),C_128)
      | ~ r2_hidden(B_127,C_128)
      | ~ r2_hidden(A_126,C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1223,plain,(
    ! [A_147,C_148] :
      ( r1_tarski(k1_tarski(A_147),C_148)
      | ~ r2_hidden(A_147,C_148)
      | ~ r2_hidden(A_147,C_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_950])).

tff(c_3222,plain,(
    ! [A_210,C_211] :
      ( k3_xboole_0(k1_tarski(A_210),C_211) = k1_tarski(A_210)
      | ~ r2_hidden(A_210,C_211) ) ),
    inference(resolution,[status(thm)],[c_1223,c_26])).

tff(c_22,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3244,plain,(
    ! [A_210,C_211] :
      ( k5_xboole_0(k1_tarski(A_210),k1_tarski(A_210)) = k4_xboole_0(k1_tarski(A_210),C_211)
      | ~ r2_hidden(A_210,C_211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3222,c_22])).

tff(c_3272,plain,(
    ! [A_212,C_213] :
      ( k4_xboole_0(k1_tarski(A_212),C_213) = k1_xboole_0
      | ~ r2_hidden(A_212,C_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_3244])).

tff(c_28,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3309,plain,(
    ! [C_213,A_212] :
      ( k2_xboole_0(C_213,k1_tarski(A_212)) = k2_xboole_0(C_213,k1_xboole_0)
      | ~ r2_hidden(A_212,C_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3272,c_28])).

tff(c_3347,plain,(
    ! [C_214,A_215] :
      ( k2_xboole_0(C_214,k1_tarski(A_215)) = C_214
      | ~ r2_hidden(A_215,C_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3309])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_54,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_3438,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3347,c_54])).

tff(c_3500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3438])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.76  
% 4.15/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.77  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.15/1.77  
% 4.15/1.77  %Foreground sorts:
% 4.15/1.77  
% 4.15/1.77  
% 4.15/1.77  %Background operators:
% 4.15/1.77  
% 4.15/1.77  
% 4.15/1.77  %Foreground operators:
% 4.15/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.15/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.15/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.15/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.15/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.15/1.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.15/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.15/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.15/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.15/1.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.15/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.15/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.15/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.15/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.15/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.15/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.15/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.15/1.77  
% 4.15/1.78  tff(f_93, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.15/1.78  tff(f_62, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.15/1.78  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.15/1.78  tff(f_68, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.15/1.78  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.15/1.78  tff(f_72, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.15/1.78  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.15/1.78  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.15/1.78  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.15/1.78  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.15/1.78  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.15/1.78  tff(f_70, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.15/1.78  tff(f_74, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.15/1.78  tff(f_88, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.15/1.78  tff(c_52, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.15/1.78  tff(c_24, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.15/1.78  tff(c_75, plain, (![B_46, A_47]: (k2_xboole_0(B_46, A_47)=k2_xboole_0(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.15/1.78  tff(c_91, plain, (![A_47]: (k2_xboole_0(k1_xboole_0, A_47)=A_47)), inference(superposition, [status(thm), theory('equality')], [c_75, c_24])).
% 4.15/1.78  tff(c_597, plain, (![A_102, B_103]: (k2_xboole_0(A_102, k4_xboole_0(B_103, A_102))=k2_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.15/1.78  tff(c_607, plain, (![B_103]: (k4_xboole_0(B_103, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_103))), inference(superposition, [status(thm), theory('equality')], [c_597, c_91])).
% 4.15/1.78  tff(c_652, plain, (![B_104]: (k4_xboole_0(B_104, k1_xboole_0)=B_104)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_607])).
% 4.15/1.78  tff(c_249, plain, (![A_72, B_73]: (r2_hidden('#skF_1'(A_72, B_73), A_72) | r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.15/1.78  tff(c_32, plain, (![A_26]: (r1_xboole_0(A_26, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.15/1.78  tff(c_160, plain, (![B_49, A_50]: (r1_xboole_0(B_49, A_50) | ~r1_xboole_0(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.15/1.78  tff(c_163, plain, (![A_26]: (r1_xboole_0(k1_xboole_0, A_26))), inference(resolution, [status(thm)], [c_32, c_160])).
% 4.15/1.78  tff(c_20, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.15/1.78  tff(c_180, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.15/1.78  tff(c_184, plain, (![B_16]: (k3_xboole_0(B_16, B_16)=B_16)), inference(resolution, [status(thm)], [c_20, c_180])).
% 4.15/1.78  tff(c_221, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, k3_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.15/1.78  tff(c_239, plain, (![B_69, C_70]: (~r1_xboole_0(B_69, B_69) | ~r2_hidden(C_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_184, c_221])).
% 4.15/1.78  tff(c_246, plain, (![C_70]: (~r2_hidden(C_70, k1_xboole_0))), inference(resolution, [status(thm)], [c_163, c_239])).
% 4.15/1.78  tff(c_260, plain, (![B_74]: (r1_tarski(k1_xboole_0, B_74))), inference(resolution, [status(thm)], [c_249, c_246])).
% 4.15/1.78  tff(c_26, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.15/1.78  tff(c_264, plain, (![B_74]: (k3_xboole_0(k1_xboole_0, B_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_260, c_26])).
% 4.15/1.78  tff(c_294, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.15/1.78  tff(c_318, plain, (![B_81]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_81))), inference(superposition, [status(thm), theory('equality')], [c_264, c_294])).
% 4.15/1.78  tff(c_303, plain, (![B_74]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_74))), inference(superposition, [status(thm), theory('equality')], [c_264, c_294])).
% 4.15/1.78  tff(c_321, plain, (![B_81, B_74]: (k4_xboole_0(k1_xboole_0, B_81)=k4_xboole_0(k1_xboole_0, B_74))), inference(superposition, [status(thm), theory('equality')], [c_318, c_303])).
% 4.15/1.78  tff(c_682, plain, (![B_74]: (k4_xboole_0(k1_xboole_0, B_74)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_652, c_321])).
% 4.15/1.78  tff(c_381, plain, (![A_87, B_88]: (k4_xboole_0(k2_xboole_0(A_87, B_88), B_88)=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.15/1.78  tff(c_413, plain, (![A_91]: (k4_xboole_0(k1_xboole_0, A_91)=k4_xboole_0(A_91, A_91))), inference(superposition, [status(thm), theory('equality')], [c_91, c_381])).
% 4.15/1.78  tff(c_437, plain, (![B_74, B_81]: (k4_xboole_0(k1_xboole_0, B_74)=k4_xboole_0(B_81, B_81))), inference(superposition, [status(thm), theory('equality')], [c_321, c_413])).
% 4.15/1.78  tff(c_724, plain, (![B_81]: (k4_xboole_0(B_81, B_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_682, c_437])).
% 4.15/1.78  tff(c_306, plain, (![B_16]: (k5_xboole_0(B_16, B_16)=k4_xboole_0(B_16, B_16))), inference(superposition, [status(thm), theory('equality')], [c_184, c_294])).
% 4.15/1.78  tff(c_773, plain, (![B_16]: (k5_xboole_0(B_16, B_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_724, c_306])).
% 4.15/1.78  tff(c_34, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.15/1.78  tff(c_950, plain, (![A_126, B_127, C_128]: (r1_tarski(k2_tarski(A_126, B_127), C_128) | ~r2_hidden(B_127, C_128) | ~r2_hidden(A_126, C_128))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.15/1.78  tff(c_1223, plain, (![A_147, C_148]: (r1_tarski(k1_tarski(A_147), C_148) | ~r2_hidden(A_147, C_148) | ~r2_hidden(A_147, C_148))), inference(superposition, [status(thm), theory('equality')], [c_34, c_950])).
% 4.15/1.78  tff(c_3222, plain, (![A_210, C_211]: (k3_xboole_0(k1_tarski(A_210), C_211)=k1_tarski(A_210) | ~r2_hidden(A_210, C_211))), inference(resolution, [status(thm)], [c_1223, c_26])).
% 4.15/1.78  tff(c_22, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.15/1.78  tff(c_3244, plain, (![A_210, C_211]: (k5_xboole_0(k1_tarski(A_210), k1_tarski(A_210))=k4_xboole_0(k1_tarski(A_210), C_211) | ~r2_hidden(A_210, C_211))), inference(superposition, [status(thm), theory('equality')], [c_3222, c_22])).
% 4.15/1.78  tff(c_3272, plain, (![A_212, C_213]: (k4_xboole_0(k1_tarski(A_212), C_213)=k1_xboole_0 | ~r2_hidden(A_212, C_213))), inference(demodulation, [status(thm), theory('equality')], [c_773, c_3244])).
% 4.15/1.78  tff(c_28, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.15/1.78  tff(c_3309, plain, (![C_213, A_212]: (k2_xboole_0(C_213, k1_tarski(A_212))=k2_xboole_0(C_213, k1_xboole_0) | ~r2_hidden(A_212, C_213))), inference(superposition, [status(thm), theory('equality')], [c_3272, c_28])).
% 4.15/1.78  tff(c_3347, plain, (![C_214, A_215]: (k2_xboole_0(C_214, k1_tarski(A_215))=C_214 | ~r2_hidden(A_215, C_214))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3309])).
% 4.15/1.78  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.15/1.78  tff(c_50, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.15/1.78  tff(c_54, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50])).
% 4.15/1.78  tff(c_3438, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3347, c_54])).
% 4.15/1.78  tff(c_3500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_3438])).
% 4.15/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.78  
% 4.15/1.78  Inference rules
% 4.15/1.78  ----------------------
% 4.15/1.78  #Ref     : 0
% 4.15/1.78  #Sup     : 849
% 4.15/1.78  #Fact    : 0
% 4.15/1.78  #Define  : 0
% 4.15/1.78  #Split   : 0
% 4.15/1.78  #Chain   : 0
% 4.15/1.78  #Close   : 0
% 4.15/1.78  
% 4.15/1.78  Ordering : KBO
% 4.15/1.78  
% 4.15/1.78  Simplification rules
% 4.15/1.78  ----------------------
% 4.15/1.78  #Subsume      : 151
% 4.15/1.78  #Demod        : 875
% 4.15/1.78  #Tautology    : 543
% 4.15/1.78  #SimpNegUnit  : 2
% 4.15/1.78  #BackRed      : 5
% 4.15/1.78  
% 4.15/1.78  #Partial instantiations: 0
% 4.15/1.78  #Strategies tried      : 1
% 4.15/1.78  
% 4.15/1.78  Timing (in seconds)
% 4.15/1.78  ----------------------
% 4.15/1.78  Preprocessing        : 0.31
% 4.15/1.78  Parsing              : 0.17
% 4.15/1.79  CNF conversion       : 0.02
% 4.15/1.79  Main loop            : 0.70
% 4.15/1.79  Inferencing          : 0.24
% 4.15/1.79  Reduction            : 0.30
% 4.15/1.79  Demodulation         : 0.25
% 4.15/1.79  BG Simplification    : 0.02
% 4.15/1.79  Subsumption          : 0.09
% 4.15/1.79  Abstraction          : 0.04
% 4.15/1.79  MUC search           : 0.00
% 4.15/1.79  Cooper               : 0.00
% 4.15/1.79  Total                : 1.05
% 4.15/1.79  Index Insertion      : 0.00
% 4.15/1.79  Index Deletion       : 0.00
% 4.15/1.79  Index Matching       : 0.00
% 4.15/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
