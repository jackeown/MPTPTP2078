%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:04 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   43 (  57 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 (  68 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_13,A_12)),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_213,plain,(
    ! [C_37,B_38,A_39] :
      ( k7_relat_1(k7_relat_1(C_37,B_38),A_39) = k7_relat_1(C_37,A_39)
      | ~ r1_tarski(A_39,B_38)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_16] :
      ( k7_relat_1(A_16,k1_relat_1(A_16)) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_373,plain,(
    ! [C_44,B_45] :
      ( k7_relat_1(C_44,k1_relat_1(k7_relat_1(C_44,B_45))) = k7_relat_1(C_44,B_45)
      | ~ v1_relat_1(k7_relat_1(C_44,B_45))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_44,B_45)),B_45)
      | ~ v1_relat_1(C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_16])).

tff(c_389,plain,(
    ! [B_46,A_47] :
      ( k7_relat_1(B_46,k1_relat_1(k7_relat_1(B_46,A_47))) = k7_relat_1(B_46,A_47)
      | ~ v1_relat_1(k7_relat_1(B_46,A_47))
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_12,c_373])).

tff(c_154,plain,(
    ! [B_33,A_34] :
      ( k3_xboole_0(k1_relat_1(B_33),A_34) = k1_relat_1(k7_relat_1(B_33,A_34))
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [B_26,A_27] : k1_setfam_1(k2_tarski(B_26,A_27)) = k3_xboole_0(A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [B_26,A_27] : k3_xboole_0(B_26,A_27) = k3_xboole_0(A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_6])).

tff(c_177,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,k1_relat_1(B_36)) = k1_relat_1(k7_relat_1(B_36,A_35))
      | ~ v1_relat_1(B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_97])).

tff(c_18,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_147,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_18])).

tff(c_187,plain,
    ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_147])).

tff(c_211,plain,(
    k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_187])).

tff(c_401,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_211])).

tff(c_441,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_401])).

tff(c_447,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_441])).

tff(c_451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:55:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.44  
% 2.35/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.45  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.35/1.45  
% 2.35/1.45  %Foreground sorts:
% 2.35/1.45  
% 2.35/1.45  
% 2.35/1.45  %Background operators:
% 2.35/1.45  
% 2.35/1.45  
% 2.35/1.45  %Foreground operators:
% 2.35/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.35/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.35/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.35/1.45  
% 2.35/1.46  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 2.35/1.46  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.35/1.46  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.35/1.46  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 2.35/1.46  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.35/1.46  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.35/1.46  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.35/1.46  tff(f_31, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.35/1.46  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.35/1.46  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.46  tff(c_12, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(k7_relat_1(B_13, A_12)), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.35/1.46  tff(c_213, plain, (![C_37, B_38, A_39]: (k7_relat_1(k7_relat_1(C_37, B_38), A_39)=k7_relat_1(C_37, A_39) | ~r1_tarski(A_39, B_38) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.35/1.46  tff(c_16, plain, (![A_16]: (k7_relat_1(A_16, k1_relat_1(A_16))=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.35/1.46  tff(c_373, plain, (![C_44, B_45]: (k7_relat_1(C_44, k1_relat_1(k7_relat_1(C_44, B_45)))=k7_relat_1(C_44, B_45) | ~v1_relat_1(k7_relat_1(C_44, B_45)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_44, B_45)), B_45) | ~v1_relat_1(C_44))), inference(superposition, [status(thm), theory('equality')], [c_213, c_16])).
% 2.35/1.46  tff(c_389, plain, (![B_46, A_47]: (k7_relat_1(B_46, k1_relat_1(k7_relat_1(B_46, A_47)))=k7_relat_1(B_46, A_47) | ~v1_relat_1(k7_relat_1(B_46, A_47)) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_12, c_373])).
% 2.35/1.46  tff(c_154, plain, (![B_33, A_34]: (k3_xboole_0(k1_relat_1(B_33), A_34)=k1_relat_1(k7_relat_1(B_33, A_34)) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.35/1.46  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.35/1.46  tff(c_64, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.46  tff(c_91, plain, (![B_26, A_27]: (k1_setfam_1(k2_tarski(B_26, A_27))=k3_xboole_0(A_27, B_26))), inference(superposition, [status(thm), theory('equality')], [c_2, c_64])).
% 2.35/1.46  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.46  tff(c_97, plain, (![B_26, A_27]: (k3_xboole_0(B_26, A_27)=k3_xboole_0(A_27, B_26))), inference(superposition, [status(thm), theory('equality')], [c_91, c_6])).
% 2.35/1.46  tff(c_177, plain, (![A_35, B_36]: (k3_xboole_0(A_35, k1_relat_1(B_36))=k1_relat_1(k7_relat_1(B_36, A_35)) | ~v1_relat_1(B_36))), inference(superposition, [status(thm), theory('equality')], [c_154, c_97])).
% 2.35/1.46  tff(c_18, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.35/1.46  tff(c_147, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_18])).
% 2.35/1.46  tff(c_187, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_177, c_147])).
% 2.35/1.46  tff(c_211, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_187])).
% 2.35/1.46  tff(c_401, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_389, c_211])).
% 2.35/1.46  tff(c_441, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_401])).
% 2.35/1.46  tff(c_447, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_441])).
% 2.35/1.46  tff(c_451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_447])).
% 2.35/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.46  
% 2.35/1.46  Inference rules
% 2.35/1.46  ----------------------
% 2.35/1.46  #Ref     : 0
% 2.35/1.46  #Sup     : 116
% 2.35/1.46  #Fact    : 0
% 2.35/1.46  #Define  : 0
% 2.35/1.46  #Split   : 0
% 2.35/1.46  #Chain   : 0
% 2.35/1.46  #Close   : 0
% 2.35/1.46  
% 2.35/1.46  Ordering : KBO
% 2.35/1.46  
% 2.35/1.46  Simplification rules
% 2.35/1.46  ----------------------
% 2.35/1.46  #Subsume      : 18
% 2.35/1.46  #Demod        : 7
% 2.35/1.46  #Tautology    : 48
% 2.35/1.46  #SimpNegUnit  : 0
% 2.35/1.46  #BackRed      : 0
% 2.35/1.46  
% 2.35/1.46  #Partial instantiations: 0
% 2.35/1.46  #Strategies tried      : 1
% 2.35/1.46  
% 2.35/1.46  Timing (in seconds)
% 2.35/1.46  ----------------------
% 2.35/1.46  Preprocessing        : 0.34
% 2.35/1.46  Parsing              : 0.20
% 2.35/1.46  CNF conversion       : 0.01
% 2.35/1.46  Main loop            : 0.24
% 2.35/1.46  Inferencing          : 0.10
% 2.35/1.46  Reduction            : 0.07
% 2.35/1.46  Demodulation         : 0.05
% 2.35/1.46  BG Simplification    : 0.02
% 2.35/1.46  Subsumption          : 0.05
% 2.35/1.46  Abstraction          : 0.02
% 2.35/1.46  MUC search           : 0.00
% 2.35/1.46  Cooper               : 0.00
% 2.35/1.46  Total                : 0.60
% 2.35/1.46  Index Insertion      : 0.00
% 2.35/1.46  Index Deletion       : 0.00
% 2.35/1.46  Index Matching       : 0.00
% 2.35/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
