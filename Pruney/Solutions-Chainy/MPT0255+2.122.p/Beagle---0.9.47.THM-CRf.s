%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:54 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   58 (  61 expanded)
%              Number of leaves         :   36 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  48 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_49,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_30,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_72,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_76,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_72])).

tff(c_77,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_30])).

tff(c_40,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_169,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_178,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = k4_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_169])).

tff(c_182,plain,(
    ! [A_73] : k4_xboole_0(A_73,k1_xboole_0) = A_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_178])).

tff(c_62,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_99,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k2_xboole_0(A_55,B_56)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_106,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_99])).

tff(c_191,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_106])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_233,plain,(
    ! [A_74,B_75] :
      ( ~ r2_hidden('#skF_2'(A_74,B_75),B_75)
      | r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_248,plain,(
    ! [A_79] : r1_tarski(A_79,A_79) ),
    inference(resolution,[status(thm)],[c_10,c_233])).

tff(c_60,plain,(
    ! [A_47,C_49,B_48] :
      ( r2_hidden(A_47,C_49)
      | ~ r1_tarski(k2_tarski(A_47,B_48),C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_254,plain,(
    ! [A_80,B_81] : r2_hidden(A_80,k2_tarski(A_80,B_81)) ),
    inference(resolution,[status(thm)],[c_248,c_60])).

tff(c_260,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_254])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_266,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_260,c_2])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:57:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.24  
% 2.33/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.24  %$ r2_hidden > r1_tarski > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 2.33/1.24  
% 2.33/1.24  %Foreground sorts:
% 2.33/1.24  
% 2.33/1.24  
% 2.33/1.24  %Background operators:
% 2.33/1.24  
% 2.33/1.24  
% 2.33/1.24  %Foreground operators:
% 2.33/1.24  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.33/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.33/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.33/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.33/1.24  tff('#skF_7', type, '#skF_7': $i).
% 2.33/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.33/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.33/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.33/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.33/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.33/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.33/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.24  
% 2.33/1.26  tff(f_49, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 2.33/1.26  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.33/1.26  tff(f_61, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.33/1.26  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.33/1.26  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.33/1.26  tff(f_85, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.33/1.26  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.33/1.26  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.33/1.26  tff(f_81, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.33/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.33/1.26  tff(c_30, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.33/1.26  tff(c_72, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.33/1.26  tff(c_76, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_72])).
% 2.33/1.26  tff(c_77, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_30])).
% 2.33/1.26  tff(c_40, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.33/1.26  tff(c_36, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.33/1.26  tff(c_169, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.33/1.26  tff(c_178, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=k4_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_169])).
% 2.33/1.26  tff(c_182, plain, (![A_73]: (k4_xboole_0(A_73, k1_xboole_0)=A_73)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_178])).
% 2.33/1.26  tff(c_62, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.33/1.26  tff(c_99, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k2_xboole_0(A_55, B_56))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.26  tff(c_106, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_62, c_99])).
% 2.33/1.26  tff(c_191, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_182, c_106])).
% 2.33/1.26  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.33/1.26  tff(c_233, plain, (![A_74, B_75]: (~r2_hidden('#skF_2'(A_74, B_75), B_75) | r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.33/1.26  tff(c_248, plain, (![A_79]: (r1_tarski(A_79, A_79))), inference(resolution, [status(thm)], [c_10, c_233])).
% 2.33/1.26  tff(c_60, plain, (![A_47, C_49, B_48]: (r2_hidden(A_47, C_49) | ~r1_tarski(k2_tarski(A_47, B_48), C_49))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.33/1.26  tff(c_254, plain, (![A_80, B_81]: (r2_hidden(A_80, k2_tarski(A_80, B_81)))), inference(resolution, [status(thm)], [c_248, c_60])).
% 2.33/1.26  tff(c_260, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_191, c_254])).
% 2.33/1.26  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.26  tff(c_266, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_260, c_2])).
% 2.33/1.26  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_266])).
% 2.33/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.26  
% 2.33/1.26  Inference rules
% 2.33/1.26  ----------------------
% 2.33/1.26  #Ref     : 0
% 2.33/1.26  #Sup     : 55
% 2.33/1.26  #Fact    : 0
% 2.33/1.26  #Define  : 0
% 2.33/1.26  #Split   : 0
% 2.33/1.26  #Chain   : 0
% 2.33/1.26  #Close   : 0
% 2.33/1.26  
% 2.33/1.26  Ordering : KBO
% 2.33/1.26  
% 2.33/1.26  Simplification rules
% 2.33/1.26  ----------------------
% 2.33/1.26  #Subsume      : 1
% 2.33/1.26  #Demod        : 9
% 2.33/1.26  #Tautology    : 35
% 2.33/1.26  #SimpNegUnit  : 0
% 2.33/1.26  #BackRed      : 3
% 2.33/1.26  
% 2.33/1.26  #Partial instantiations: 0
% 2.33/1.26  #Strategies tried      : 1
% 2.33/1.26  
% 2.33/1.26  Timing (in seconds)
% 2.33/1.26  ----------------------
% 2.33/1.26  Preprocessing        : 0.34
% 2.33/1.26  Parsing              : 0.17
% 2.33/1.26  CNF conversion       : 0.03
% 2.33/1.26  Main loop            : 0.16
% 2.33/1.26  Inferencing          : 0.05
% 2.33/1.26  Reduction            : 0.05
% 2.33/1.26  Demodulation         : 0.04
% 2.33/1.26  BG Simplification    : 0.02
% 2.33/1.26  Subsumption          : 0.03
% 2.33/1.26  Abstraction          : 0.01
% 2.33/1.26  MUC search           : 0.00
% 2.33/1.26  Cooper               : 0.00
% 2.33/1.26  Total                : 0.52
% 2.33/1.26  Index Insertion      : 0.00
% 2.33/1.26  Index Deletion       : 0.00
% 2.33/1.26  Index Matching       : 0.00
% 2.33/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
