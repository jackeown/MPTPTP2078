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
% DateTime   : Thu Dec  3 10:02:34 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   42 (  55 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  59 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_12,B_13] : k6_subset_1(A_12,B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [C_20,A_18,B_19] :
      ( k7_relat_1(C_20,k6_subset_1(A_18,B_19)) = k6_subset_1(C_20,k7_relat_1(C_20,B_19))
      | ~ r1_tarski(k1_relat_1(C_20),A_18)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_172,plain,(
    ! [C_47,A_48,B_49] :
      ( k7_relat_1(C_47,k4_xboole_0(A_48,B_49)) = k4_xboole_0(C_47,k7_relat_1(C_47,B_49))
      | ~ r1_tarski(k1_relat_1(C_47),A_48)
      | ~ v1_relat_1(C_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_22])).

tff(c_179,plain,(
    ! [C_50,B_51] :
      ( k7_relat_1(C_50,k4_xboole_0(k1_relat_1(C_50),B_51)) = k4_xboole_0(C_50,k7_relat_1(C_50,B_51))
      | ~ v1_relat_1(C_50) ) ),
    inference(resolution,[status(thm)],[c_6,c_172])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( k1_relat_1(k7_relat_1(B_17,k6_subset_1(k1_relat_1(B_17),A_16))) = k6_subset_1(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_31,plain,(
    ! [B_17,A_16] :
      ( k1_relat_1(k7_relat_1(B_17,k4_xboole_0(k1_relat_1(B_17),A_16))) = k4_xboole_0(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_20])).

tff(c_207,plain,(
    ! [C_52,B_53] :
      ( k1_relat_1(k4_xboole_0(C_52,k7_relat_1(C_52,B_53))) = k4_xboole_0(k1_relat_1(C_52),B_53)
      | ~ v1_relat_1(C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_31])).

tff(c_95,plain,(
    ! [B_39,A_40] :
      ( k3_xboole_0(k1_relat_1(B_39),A_40) = k1_relat_1(k7_relat_1(B_39,A_40))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_148,plain,(
    ! [B_45,A_46] :
      ( k4_xboole_0(k1_relat_1(B_45),k1_relat_1(k7_relat_1(B_45,A_46))) = k4_xboole_0(k1_relat_1(B_45),A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_10])).

tff(c_26,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_29,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_26])).

tff(c_157,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_29])).

tff(c_169,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_157])).

tff(c_218,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_169])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:39:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.24  
% 2.08/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.24  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.08/1.24  
% 2.08/1.24  %Foreground sorts:
% 2.08/1.24  
% 2.08/1.24  
% 2.08/1.24  %Background operators:
% 2.08/1.24  
% 2.08/1.24  
% 2.08/1.24  %Foreground operators:
% 2.08/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.08/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.08/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.24  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.08/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.08/1.24  
% 2.08/1.25  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 2.08/1.25  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.08/1.25  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.08/1.25  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 2.08/1.25  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 2.08/1.25  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.08/1.25  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.08/1.25  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.08/1.25  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.25  tff(c_16, plain, (![A_12, B_13]: (k6_subset_1(A_12, B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.25  tff(c_22, plain, (![C_20, A_18, B_19]: (k7_relat_1(C_20, k6_subset_1(A_18, B_19))=k6_subset_1(C_20, k7_relat_1(C_20, B_19)) | ~r1_tarski(k1_relat_1(C_20), A_18) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.25  tff(c_172, plain, (![C_47, A_48, B_49]: (k7_relat_1(C_47, k4_xboole_0(A_48, B_49))=k4_xboole_0(C_47, k7_relat_1(C_47, B_49)) | ~r1_tarski(k1_relat_1(C_47), A_48) | ~v1_relat_1(C_47))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_22])).
% 2.08/1.25  tff(c_179, plain, (![C_50, B_51]: (k7_relat_1(C_50, k4_xboole_0(k1_relat_1(C_50), B_51))=k4_xboole_0(C_50, k7_relat_1(C_50, B_51)) | ~v1_relat_1(C_50))), inference(resolution, [status(thm)], [c_6, c_172])).
% 2.08/1.25  tff(c_20, plain, (![B_17, A_16]: (k1_relat_1(k7_relat_1(B_17, k6_subset_1(k1_relat_1(B_17), A_16)))=k6_subset_1(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.25  tff(c_31, plain, (![B_17, A_16]: (k1_relat_1(k7_relat_1(B_17, k4_xboole_0(k1_relat_1(B_17), A_16)))=k4_xboole_0(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_20])).
% 2.08/1.25  tff(c_207, plain, (![C_52, B_53]: (k1_relat_1(k4_xboole_0(C_52, k7_relat_1(C_52, B_53)))=k4_xboole_0(k1_relat_1(C_52), B_53) | ~v1_relat_1(C_52) | ~v1_relat_1(C_52))), inference(superposition, [status(thm), theory('equality')], [c_179, c_31])).
% 2.08/1.25  tff(c_95, plain, (![B_39, A_40]: (k3_xboole_0(k1_relat_1(B_39), A_40)=k1_relat_1(k7_relat_1(B_39, A_40)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.08/1.25  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.25  tff(c_148, plain, (![B_45, A_46]: (k4_xboole_0(k1_relat_1(B_45), k1_relat_1(k7_relat_1(B_45, A_46)))=k4_xboole_0(k1_relat_1(B_45), A_46) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_95, c_10])).
% 2.08/1.25  tff(c_26, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.08/1.25  tff(c_29, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_26])).
% 2.08/1.25  tff(c_157, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_148, c_29])).
% 2.08/1.25  tff(c_169, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_157])).
% 2.08/1.25  tff(c_218, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_207, c_169])).
% 2.08/1.25  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_218])).
% 2.08/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  
% 2.08/1.25  Inference rules
% 2.08/1.25  ----------------------
% 2.08/1.25  #Ref     : 0
% 2.08/1.25  #Sup     : 53
% 2.08/1.25  #Fact    : 0
% 2.08/1.25  #Define  : 0
% 2.08/1.25  #Split   : 0
% 2.08/1.25  #Chain   : 0
% 2.08/1.25  #Close   : 0
% 2.08/1.25  
% 2.08/1.25  Ordering : KBO
% 2.08/1.25  
% 2.08/1.25  Simplification rules
% 2.08/1.25  ----------------------
% 2.08/1.25  #Subsume      : 1
% 2.08/1.25  #Demod        : 11
% 2.08/1.25  #Tautology    : 26
% 2.08/1.25  #SimpNegUnit  : 0
% 2.08/1.25  #BackRed      : 0
% 2.08/1.25  
% 2.08/1.25  #Partial instantiations: 0
% 2.08/1.25  #Strategies tried      : 1
% 2.08/1.25  
% 2.08/1.25  Timing (in seconds)
% 2.08/1.25  ----------------------
% 2.08/1.25  Preprocessing        : 0.31
% 2.08/1.25  Parsing              : 0.16
% 2.08/1.25  CNF conversion       : 0.02
% 2.08/1.25  Main loop            : 0.17
% 2.08/1.25  Inferencing          : 0.07
% 2.08/1.25  Reduction            : 0.06
% 2.08/1.25  Demodulation         : 0.04
% 2.08/1.25  BG Simplification    : 0.02
% 2.08/1.25  Subsumption          : 0.02
% 2.08/1.25  Abstraction          : 0.02
% 2.08/1.25  MUC search           : 0.00
% 2.08/1.25  Cooper               : 0.00
% 2.08/1.25  Total                : 0.51
% 2.08/1.25  Index Insertion      : 0.00
% 2.08/1.25  Index Deletion       : 0.00
% 2.08/1.25  Index Matching       : 0.00
% 2.08/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
