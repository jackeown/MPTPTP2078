%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:49 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   50 (  65 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  71 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k10_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_35,plain,(
    ! [B_50,A_51] : k3_xboole_0(B_50,A_51) = k3_xboole_0(A_51,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [B_50,A_51] : r1_tarski(k3_xboole_0(B_50,A_51),A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_6])).

tff(c_93,plain,(
    ! [A_56,B_57] :
      ( k2_xboole_0(A_56,B_57) = B_57
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [B_50,A_51] : k2_xboole_0(k3_xboole_0(B_50,A_51),A_51) = A_51 ),
    inference(resolution,[status(thm)],[c_50,c_93])).

tff(c_751,plain,(
    ! [C_110,A_111,B_112] :
      ( k2_xboole_0(k10_relat_1(C_110,A_111),k10_relat_1(C_110,B_112)) = k10_relat_1(C_110,k2_xboole_0(A_111,B_112))
      | ~ v1_relat_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_776,plain,(
    ! [C_113,A_114,B_115] :
      ( r1_tarski(k10_relat_1(C_113,A_114),k10_relat_1(C_113,k2_xboole_0(A_114,B_115)))
      | ~ v1_relat_1(C_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_12])).

tff(c_816,plain,(
    ! [C_119,B_120,A_121] :
      ( r1_tarski(k10_relat_1(C_119,k3_xboole_0(B_120,A_121)),k10_relat_1(C_119,A_121))
      | ~ v1_relat_1(C_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_776])).

tff(c_104,plain,(
    ! [A_5,B_6] : k2_xboole_0(k3_xboole_0(A_5,B_6),A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_616,plain,(
    ! [C_99,A_100,B_101] :
      ( k2_xboole_0(k10_relat_1(C_99,A_100),k10_relat_1(C_99,B_101)) = k10_relat_1(C_99,k2_xboole_0(A_100,B_101))
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_631,plain,(
    ! [C_102,A_103,B_104] :
      ( r1_tarski(k10_relat_1(C_102,A_103),k10_relat_1(C_102,k2_xboole_0(A_103,B_104)))
      | ~ v1_relat_1(C_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_12])).

tff(c_651,plain,(
    ! [C_105,A_106,B_107] :
      ( r1_tarski(k10_relat_1(C_105,k3_xboole_0(A_106,B_107)),k10_relat_1(C_105,A_106))
      | ~ v1_relat_1(C_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_631])).

tff(c_279,plain,(
    ! [A_79,B_80,C_81] :
      ( r1_tarski(A_79,k3_xboole_0(B_80,C_81))
      | ~ r1_tarski(A_79,C_81)
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_292,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_279,c_30])).

tff(c_556,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_292])).

tff(c_654,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_651,c_556])).

tff(c_673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_654])).

tff(c_674,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_819,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_816,c_674])).

tff(c_838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_819])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:38:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.43  
% 2.73/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.44  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.73/1.44  
% 2.73/1.44  %Foreground sorts:
% 2.73/1.44  
% 2.73/1.44  
% 2.73/1.44  %Background operators:
% 2.73/1.44  
% 2.73/1.44  
% 2.73/1.44  %Foreground operators:
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.73/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.73/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.73/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.73/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.73/1.44  
% 2.73/1.45  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_relat_1)).
% 2.73/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.73/1.45  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.73/1.45  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.73/1.45  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 2.73/1.45  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.73/1.45  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.73/1.45  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.73/1.45  tff(c_35, plain, (![B_50, A_51]: (k3_xboole_0(B_50, A_51)=k3_xboole_0(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.73/1.45  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.73/1.45  tff(c_50, plain, (![B_50, A_51]: (r1_tarski(k3_xboole_0(B_50, A_51), A_51))), inference(superposition, [status(thm), theory('equality')], [c_35, c_6])).
% 2.73/1.45  tff(c_93, plain, (![A_56, B_57]: (k2_xboole_0(A_56, B_57)=B_57 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.45  tff(c_103, plain, (![B_50, A_51]: (k2_xboole_0(k3_xboole_0(B_50, A_51), A_51)=A_51)), inference(resolution, [status(thm)], [c_50, c_93])).
% 2.73/1.45  tff(c_751, plain, (![C_110, A_111, B_112]: (k2_xboole_0(k10_relat_1(C_110, A_111), k10_relat_1(C_110, B_112))=k10_relat_1(C_110, k2_xboole_0(A_111, B_112)) | ~v1_relat_1(C_110))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.73/1.45  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.45  tff(c_776, plain, (![C_113, A_114, B_115]: (r1_tarski(k10_relat_1(C_113, A_114), k10_relat_1(C_113, k2_xboole_0(A_114, B_115))) | ~v1_relat_1(C_113))), inference(superposition, [status(thm), theory('equality')], [c_751, c_12])).
% 2.73/1.45  tff(c_816, plain, (![C_119, B_120, A_121]: (r1_tarski(k10_relat_1(C_119, k3_xboole_0(B_120, A_121)), k10_relat_1(C_119, A_121)) | ~v1_relat_1(C_119))), inference(superposition, [status(thm), theory('equality')], [c_103, c_776])).
% 2.73/1.45  tff(c_104, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_93])).
% 2.73/1.45  tff(c_616, plain, (![C_99, A_100, B_101]: (k2_xboole_0(k10_relat_1(C_99, A_100), k10_relat_1(C_99, B_101))=k10_relat_1(C_99, k2_xboole_0(A_100, B_101)) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.73/1.45  tff(c_631, plain, (![C_102, A_103, B_104]: (r1_tarski(k10_relat_1(C_102, A_103), k10_relat_1(C_102, k2_xboole_0(A_103, B_104))) | ~v1_relat_1(C_102))), inference(superposition, [status(thm), theory('equality')], [c_616, c_12])).
% 2.73/1.45  tff(c_651, plain, (![C_105, A_106, B_107]: (r1_tarski(k10_relat_1(C_105, k3_xboole_0(A_106, B_107)), k10_relat_1(C_105, A_106)) | ~v1_relat_1(C_105))), inference(superposition, [status(thm), theory('equality')], [c_104, c_631])).
% 2.73/1.45  tff(c_279, plain, (![A_79, B_80, C_81]: (r1_tarski(A_79, k3_xboole_0(B_80, C_81)) | ~r1_tarski(A_79, C_81) | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.73/1.45  tff(c_30, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.73/1.45  tff(c_292, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_279, c_30])).
% 2.73/1.45  tff(c_556, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_292])).
% 2.73/1.45  tff(c_654, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_651, c_556])).
% 2.73/1.45  tff(c_673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_654])).
% 2.73/1.45  tff(c_674, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_292])).
% 2.73/1.45  tff(c_819, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_816, c_674])).
% 2.73/1.45  tff(c_838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_819])).
% 2.73/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.45  
% 2.73/1.45  Inference rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Ref     : 0
% 2.73/1.45  #Sup     : 205
% 2.73/1.45  #Fact    : 0
% 2.73/1.45  #Define  : 0
% 2.73/1.45  #Split   : 1
% 2.73/1.45  #Chain   : 0
% 2.73/1.45  #Close   : 0
% 2.73/1.45  
% 2.73/1.45  Ordering : KBO
% 2.73/1.45  
% 2.73/1.45  Simplification rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Subsume      : 16
% 2.73/1.45  #Demod        : 89
% 2.73/1.45  #Tautology    : 104
% 2.73/1.45  #SimpNegUnit  : 0
% 2.73/1.45  #BackRed      : 0
% 2.73/1.45  
% 2.73/1.45  #Partial instantiations: 0
% 2.73/1.45  #Strategies tried      : 1
% 2.73/1.45  
% 2.73/1.45  Timing (in seconds)
% 2.73/1.45  ----------------------
% 2.73/1.45  Preprocessing        : 0.32
% 2.73/1.45  Parsing              : 0.17
% 2.73/1.45  CNF conversion       : 0.02
% 2.73/1.45  Main loop            : 0.36
% 2.73/1.45  Inferencing          : 0.12
% 2.73/1.45  Reduction            : 0.15
% 2.73/1.45  Demodulation         : 0.12
% 3.10/1.45  BG Simplification    : 0.02
% 3.10/1.45  Subsumption          : 0.05
% 3.10/1.45  Abstraction          : 0.02
% 3.10/1.45  MUC search           : 0.00
% 3.10/1.45  Cooper               : 0.00
% 3.10/1.45  Total                : 0.71
% 3.10/1.45  Index Insertion      : 0.00
% 3.10/1.45  Index Deletion       : 0.00
% 3.10/1.45  Index Matching       : 0.00
% 3.10/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
