%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:09 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   52 (  56 expanded)
%              Number of leaves         :   30 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  49 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    ! [A_48,B_49] : k3_xboole_0(k1_tarski(A_48),k2_tarski(A_48,B_49)) = k1_tarski(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_63,plain,(
    ! [A_55,B_56] : r1_tarski(k3_xboole_0(A_55,B_56),A_55) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_68,plain,(
    ! [B_56] : k3_xboole_0(k1_xboole_0,B_56) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63,c_16])).

tff(c_42,plain,(
    r1_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_249,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = k1_xboole_0
      | ~ r1_xboole_0(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_269,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_249])).

tff(c_333,plain,(
    k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_2])).

tff(c_690,plain,(
    ! [A_105,B_106,C_107] : k3_xboole_0(k3_xboole_0(A_105,B_106),C_107) = k3_xboole_0(A_105,k3_xboole_0(B_106,C_107)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_741,plain,(
    ! [C_107] : k3_xboole_0('#skF_3',k3_xboole_0(k2_tarski('#skF_1','#skF_2'),C_107)) = k3_xboole_0(k1_xboole_0,C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_690])).

tff(c_1832,plain,(
    ! [C_145] : k3_xboole_0('#skF_3',k3_xboole_0(k2_tarski('#skF_1','#skF_2'),C_145)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_741])).

tff(c_2750,plain,(
    ! [A_173] : k3_xboole_0('#skF_3',k3_xboole_0(A_173,k2_tarski('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1832])).

tff(c_2823,plain,(
    k3_xboole_0('#skF_3',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2750])).

tff(c_233,plain,(
    ! [A_70,B_71] :
      ( r1_xboole_0(A_70,B_71)
      | k3_xboole_0(A_70,B_71) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_651,plain,(
    ! [B_100,A_101] :
      ( r1_xboole_0(B_100,A_101)
      | k3_xboole_0(A_101,B_100) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_233,c_8])).

tff(c_36,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden(A_46,B_47)
      | ~ r1_xboole_0(k1_tarski(A_46),B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_662,plain,(
    ! [A_46,A_101] :
      ( ~ r2_hidden(A_46,A_101)
      | k3_xboole_0(A_101,k1_tarski(A_46)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_651,c_36])).

tff(c_2889,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2823,c_662])).

tff(c_2926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:53:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.53  
% 3.42/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.68/1.53  
% 3.68/1.53  %Foreground sorts:
% 3.68/1.53  
% 3.68/1.53  
% 3.68/1.53  %Background operators:
% 3.68/1.53  
% 3.68/1.53  
% 3.68/1.53  %Foreground operators:
% 3.68/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.68/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.68/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.68/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.68/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.68/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.68/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.68/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.68/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.68/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.68/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.68/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.68/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.68/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.68/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.68/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.68/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.68/1.53  
% 3.68/1.54  tff(f_76, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.68/1.54  tff(f_70, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.68/1.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.68/1.54  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.68/1.54  tff(f_45, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.68/1.54  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.68/1.54  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.68/1.54  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.68/1.54  tff(f_68, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.68/1.54  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.68/1.54  tff(c_38, plain, (![A_48, B_49]: (k3_xboole_0(k1_tarski(A_48), k2_tarski(A_48, B_49))=k1_tarski(A_48))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.68/1.54  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.68/1.54  tff(c_63, plain, (![A_55, B_56]: (r1_tarski(k3_xboole_0(A_55, B_56), A_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.68/1.54  tff(c_16, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.68/1.54  tff(c_68, plain, (![B_56]: (k3_xboole_0(k1_xboole_0, B_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_63, c_16])).
% 3.68/1.54  tff(c_42, plain, (r1_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.68/1.54  tff(c_249, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=k1_xboole_0 | ~r1_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.68/1.54  tff(c_269, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_249])).
% 3.68/1.54  tff(c_333, plain, (k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_269, c_2])).
% 3.68/1.54  tff(c_690, plain, (![A_105, B_106, C_107]: (k3_xboole_0(k3_xboole_0(A_105, B_106), C_107)=k3_xboole_0(A_105, k3_xboole_0(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.68/1.54  tff(c_741, plain, (![C_107]: (k3_xboole_0('#skF_3', k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), C_107))=k3_xboole_0(k1_xboole_0, C_107))), inference(superposition, [status(thm), theory('equality')], [c_333, c_690])).
% 3.68/1.54  tff(c_1832, plain, (![C_145]: (k3_xboole_0('#skF_3', k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), C_145))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_741])).
% 3.68/1.54  tff(c_2750, plain, (![A_173]: (k3_xboole_0('#skF_3', k3_xboole_0(A_173, k2_tarski('#skF_1', '#skF_2')))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1832])).
% 3.68/1.54  tff(c_2823, plain, (k3_xboole_0('#skF_3', k1_tarski('#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_2750])).
% 3.68/1.54  tff(c_233, plain, (![A_70, B_71]: (r1_xboole_0(A_70, B_71) | k3_xboole_0(A_70, B_71)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.68/1.54  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.68/1.54  tff(c_651, plain, (![B_100, A_101]: (r1_xboole_0(B_100, A_101) | k3_xboole_0(A_101, B_100)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_233, c_8])).
% 3.68/1.54  tff(c_36, plain, (![A_46, B_47]: (~r2_hidden(A_46, B_47) | ~r1_xboole_0(k1_tarski(A_46), B_47))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.68/1.54  tff(c_662, plain, (![A_46, A_101]: (~r2_hidden(A_46, A_101) | k3_xboole_0(A_101, k1_tarski(A_46))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_651, c_36])).
% 3.68/1.54  tff(c_2889, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2823, c_662])).
% 3.68/1.54  tff(c_2926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_2889])).
% 3.68/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.54  
% 3.68/1.54  Inference rules
% 3.68/1.54  ----------------------
% 3.68/1.54  #Ref     : 0
% 3.68/1.54  #Sup     : 732
% 3.68/1.54  #Fact    : 0
% 3.68/1.54  #Define  : 0
% 3.68/1.54  #Split   : 0
% 3.68/1.54  #Chain   : 0
% 3.68/1.54  #Close   : 0
% 3.68/1.54  
% 3.68/1.54  Ordering : KBO
% 3.68/1.54  
% 3.68/1.54  Simplification rules
% 3.68/1.54  ----------------------
% 3.68/1.54  #Subsume      : 13
% 3.68/1.54  #Demod        : 563
% 3.68/1.54  #Tautology    : 556
% 3.68/1.54  #SimpNegUnit  : 0
% 3.68/1.54  #BackRed      : 0
% 3.68/1.54  
% 3.68/1.54  #Partial instantiations: 0
% 3.68/1.54  #Strategies tried      : 1
% 3.68/1.54  
% 3.68/1.54  Timing (in seconds)
% 3.68/1.54  ----------------------
% 3.68/1.55  Preprocessing        : 0.29
% 3.68/1.55  Parsing              : 0.16
% 3.68/1.55  CNF conversion       : 0.02
% 3.68/1.55  Main loop            : 0.56
% 3.68/1.55  Inferencing          : 0.19
% 3.68/1.55  Reduction            : 0.25
% 3.68/1.55  Demodulation         : 0.21
% 3.68/1.55  BG Simplification    : 0.02
% 3.68/1.55  Subsumption          : 0.07
% 3.68/1.55  Abstraction          : 0.03
% 3.68/1.55  MUC search           : 0.00
% 3.68/1.55  Cooper               : 0.00
% 3.68/1.55  Total                : 0.88
% 3.68/1.55  Index Insertion      : 0.00
% 3.68/1.55  Index Deletion       : 0.00
% 3.68/1.55  Index Matching       : 0.00
% 3.68/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
