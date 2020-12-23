%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:39 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   49 (  52 expanded)
%              Number of leaves         :   29 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  42 expanded)
%              Number of equality atoms :   25 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ r2_hidden(A,B)
       => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(c_40,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,k1_tarski(B_45)) = A_44
      | r2_hidden(B_45,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [B_49,A_50] : k5_xboole_0(B_49,A_50) = k5_xboole_0(A_50,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [A_50] : k5_xboole_0(k1_xboole_0,A_50) = A_50 ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_10])).

tff(c_430,plain,(
    ! [A_78,B_79,C_80] : k5_xboole_0(k5_xboole_0(A_78,B_79),C_80) = k5_xboole_0(A_78,k5_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_509,plain,(
    ! [A_13,C_80] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_80)) = k5_xboole_0(k1_xboole_0,C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_430])).

tff(c_539,plain,(
    ! [A_85,C_86] : k5_xboole_0(A_85,k5_xboole_0(A_85,C_86)) = C_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_509])).

tff(c_994,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k4_xboole_0(A_106,B_107)) = k3_xboole_0(A_106,B_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_539])).

tff(c_1037,plain,(
    ! [A_44,B_45] :
      ( k5_xboole_0(A_44,A_44) = k3_xboole_0(A_44,k1_tarski(B_45))
      | r2_hidden(B_45,A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_994])).

tff(c_1200,plain,(
    ! [A_120,B_121] :
      ( k3_xboole_0(A_120,k1_tarski(B_121)) = k1_xboole_0
      | r2_hidden(B_121,A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1037])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_362,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(k2_xboole_0(A_74,B_75),B_75) = A_74
      | ~ r1_xboole_0(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_38,plain,(
    k4_xboole_0(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_396,plain,(
    ~ r1_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_38])).

tff(c_401,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_396])).

tff(c_1216,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1200,c_401])).

tff(c_1241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:24:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.42  
% 2.81/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.42  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.81/1.42  
% 2.81/1.42  %Foreground sorts:
% 2.81/1.42  
% 2.81/1.42  
% 2.81/1.42  %Background operators:
% 2.81/1.42  
% 2.81/1.42  
% 2.81/1.42  %Foreground operators:
% 2.81/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.81/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.81/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.81/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.42  
% 3.11/1.43  tff(f_70, negated_conjecture, ~(![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 3.11/1.43  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.11/1.43  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.11/1.43  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.11/1.43  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.11/1.43  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.11/1.43  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.11/1.43  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.11/1.43  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 3.11/1.43  tff(c_40, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.11/1.43  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.11/1.43  tff(c_36, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k1_tarski(B_45))=A_44 | r2_hidden(B_45, A_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.11/1.43  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.11/1.43  tff(c_76, plain, (![B_49, A_50]: (k5_xboole_0(B_49, A_50)=k5_xboole_0(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.11/1.43  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.11/1.43  tff(c_92, plain, (![A_50]: (k5_xboole_0(k1_xboole_0, A_50)=A_50)), inference(superposition, [status(thm), theory('equality')], [c_76, c_10])).
% 3.11/1.43  tff(c_430, plain, (![A_78, B_79, C_80]: (k5_xboole_0(k5_xboole_0(A_78, B_79), C_80)=k5_xboole_0(A_78, k5_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.11/1.43  tff(c_509, plain, (![A_13, C_80]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_80))=k5_xboole_0(k1_xboole_0, C_80))), inference(superposition, [status(thm), theory('equality')], [c_16, c_430])).
% 3.11/1.43  tff(c_539, plain, (![A_85, C_86]: (k5_xboole_0(A_85, k5_xboole_0(A_85, C_86))=C_86)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_509])).
% 3.11/1.43  tff(c_994, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k4_xboole_0(A_106, B_107))=k3_xboole_0(A_106, B_107))), inference(superposition, [status(thm), theory('equality')], [c_8, c_539])).
% 3.11/1.43  tff(c_1037, plain, (![A_44, B_45]: (k5_xboole_0(A_44, A_44)=k3_xboole_0(A_44, k1_tarski(B_45)) | r2_hidden(B_45, A_44))), inference(superposition, [status(thm), theory('equality')], [c_36, c_994])).
% 3.11/1.43  tff(c_1200, plain, (![A_120, B_121]: (k3_xboole_0(A_120, k1_tarski(B_121))=k1_xboole_0 | r2_hidden(B_121, A_120))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1037])).
% 3.11/1.43  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.43  tff(c_362, plain, (![A_74, B_75]: (k4_xboole_0(k2_xboole_0(A_74, B_75), B_75)=A_74 | ~r1_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.11/1.43  tff(c_38, plain, (k4_xboole_0(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.11/1.43  tff(c_396, plain, (~r1_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_362, c_38])).
% 3.11/1.43  tff(c_401, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_396])).
% 3.11/1.43  tff(c_1216, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1200, c_401])).
% 3.11/1.43  tff(c_1241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1216])).
% 3.11/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.43  
% 3.11/1.43  Inference rules
% 3.11/1.43  ----------------------
% 3.11/1.43  #Ref     : 0
% 3.11/1.43  #Sup     : 295
% 3.11/1.43  #Fact    : 0
% 3.11/1.43  #Define  : 0
% 3.11/1.43  #Split   : 1
% 3.11/1.43  #Chain   : 0
% 3.11/1.43  #Close   : 0
% 3.11/1.43  
% 3.11/1.43  Ordering : KBO
% 3.11/1.43  
% 3.11/1.43  Simplification rules
% 3.11/1.43  ----------------------
% 3.11/1.43  #Subsume      : 16
% 3.11/1.43  #Demod        : 129
% 3.11/1.43  #Tautology    : 184
% 3.11/1.43  #SimpNegUnit  : 1
% 3.11/1.43  #BackRed      : 0
% 3.11/1.43  
% 3.11/1.43  #Partial instantiations: 0
% 3.11/1.43  #Strategies tried      : 1
% 3.11/1.43  
% 3.11/1.43  Timing (in seconds)
% 3.11/1.43  ----------------------
% 3.11/1.44  Preprocessing        : 0.31
% 3.11/1.44  Parsing              : 0.17
% 3.11/1.44  CNF conversion       : 0.02
% 3.11/1.44  Main loop            : 0.37
% 3.11/1.44  Inferencing          : 0.14
% 3.11/1.44  Reduction            : 0.14
% 3.11/1.44  Demodulation         : 0.11
% 3.11/1.44  BG Simplification    : 0.02
% 3.11/1.44  Subsumption          : 0.05
% 3.11/1.44  Abstraction          : 0.02
% 3.11/1.44  MUC search           : 0.00
% 3.11/1.44  Cooper               : 0.00
% 3.11/1.44  Total                : 0.71
% 3.11/1.44  Index Insertion      : 0.00
% 3.11/1.44  Index Deletion       : 0.00
% 3.11/1.44  Index Matching       : 0.00
% 3.11/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
