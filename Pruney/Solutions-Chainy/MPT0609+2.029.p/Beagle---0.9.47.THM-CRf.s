%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:34 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   41 (  54 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  59 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_72,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_9,B_10] : k6_subset_1(A_9,B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(C_17,k6_subset_1(A_15,B_16)) = k6_subset_1(C_17,k7_relat_1(C_17,B_16))
      | ~ r1_tarski(k1_relat_1(C_17),A_15)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_193,plain,(
    ! [C_47,A_48,B_49] :
      ( k7_relat_1(C_47,k4_xboole_0(A_48,B_49)) = k4_xboole_0(C_47,k7_relat_1(C_47,B_49))
      | ~ r1_tarski(k1_relat_1(C_47),A_48)
      | ~ v1_relat_1(C_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_20])).

tff(c_261,plain,(
    ! [C_54,B_55] :
      ( k7_relat_1(C_54,k4_xboole_0(k1_relat_1(C_54),B_55)) = k4_xboole_0(C_54,k7_relat_1(C_54,B_55))
      | ~ v1_relat_1(C_54) ) ),
    inference(resolution,[status(thm)],[c_6,c_193])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,k6_subset_1(k1_relat_1(B_14),A_13))) = k6_subset_1(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,k4_xboole_0(k1_relat_1(B_14),A_13))) = k4_xboole_0(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_18])).

tff(c_313,plain,(
    ! [C_57,B_58] :
      ( k1_relat_1(k4_xboole_0(C_57,k7_relat_1(C_57,B_58))) = k4_xboole_0(k1_relat_1(C_57),B_58)
      | ~ v1_relat_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_32])).

tff(c_88,plain,(
    ! [B_37,A_38] :
      ( k3_xboole_0(k1_relat_1(B_37),A_38) = k1_relat_1(k7_relat_1(B_37,A_38))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_202,plain,(
    ! [B_50,A_51] :
      ( k4_xboole_0(k1_relat_1(B_50),k1_relat_1(k7_relat_1(B_50,A_51))) = k4_xboole_0(k1_relat_1(B_50),A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_10])).

tff(c_28,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_33,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_28])).

tff(c_211,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_33])).

tff(c_232,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_211])).

tff(c_331,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_232])).

tff(c_368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:02 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.28  
% 2.32/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.28  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.32/1.28  
% 2.32/1.28  %Foreground sorts:
% 2.32/1.28  
% 2.32/1.28  
% 2.32/1.28  %Background operators:
% 2.32/1.28  
% 2.32/1.28  
% 2.32/1.28  %Foreground operators:
% 2.32/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.32/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.32/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.28  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.32/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.32/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.32/1.28  
% 2.32/1.29  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 2.32/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.32/1.29  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.32/1.29  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 2.32/1.29  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 2.32/1.29  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.32/1.29  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.32/1.29  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.32/1.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.29  tff(c_14, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.32/1.29  tff(c_20, plain, (![C_17, A_15, B_16]: (k7_relat_1(C_17, k6_subset_1(A_15, B_16))=k6_subset_1(C_17, k7_relat_1(C_17, B_16)) | ~r1_tarski(k1_relat_1(C_17), A_15) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.32/1.29  tff(c_193, plain, (![C_47, A_48, B_49]: (k7_relat_1(C_47, k4_xboole_0(A_48, B_49))=k4_xboole_0(C_47, k7_relat_1(C_47, B_49)) | ~r1_tarski(k1_relat_1(C_47), A_48) | ~v1_relat_1(C_47))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_20])).
% 2.32/1.29  tff(c_261, plain, (![C_54, B_55]: (k7_relat_1(C_54, k4_xboole_0(k1_relat_1(C_54), B_55))=k4_xboole_0(C_54, k7_relat_1(C_54, B_55)) | ~v1_relat_1(C_54))), inference(resolution, [status(thm)], [c_6, c_193])).
% 2.32/1.29  tff(c_18, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, k6_subset_1(k1_relat_1(B_14), A_13)))=k6_subset_1(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.32/1.29  tff(c_32, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, k4_xboole_0(k1_relat_1(B_14), A_13)))=k4_xboole_0(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 2.32/1.29  tff(c_313, plain, (![C_57, B_58]: (k1_relat_1(k4_xboole_0(C_57, k7_relat_1(C_57, B_58)))=k4_xboole_0(k1_relat_1(C_57), B_58) | ~v1_relat_1(C_57) | ~v1_relat_1(C_57))), inference(superposition, [status(thm), theory('equality')], [c_261, c_32])).
% 2.32/1.29  tff(c_88, plain, (![B_37, A_38]: (k3_xboole_0(k1_relat_1(B_37), A_38)=k1_relat_1(k7_relat_1(B_37, A_38)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.32/1.29  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.32/1.29  tff(c_202, plain, (![B_50, A_51]: (k4_xboole_0(k1_relat_1(B_50), k1_relat_1(k7_relat_1(B_50, A_51)))=k4_xboole_0(k1_relat_1(B_50), A_51) | ~v1_relat_1(B_50))), inference(superposition, [status(thm), theory('equality')], [c_88, c_10])).
% 2.32/1.29  tff(c_28, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.32/1.29  tff(c_33, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_28])).
% 2.32/1.29  tff(c_211, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_202, c_33])).
% 2.32/1.29  tff(c_232, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_211])).
% 2.32/1.29  tff(c_331, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_313, c_232])).
% 2.32/1.29  tff(c_368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_331])).
% 2.32/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.29  
% 2.32/1.29  Inference rules
% 2.32/1.29  ----------------------
% 2.32/1.29  #Ref     : 0
% 2.32/1.29  #Sup     : 90
% 2.32/1.29  #Fact    : 0
% 2.32/1.29  #Define  : 0
% 2.32/1.29  #Split   : 0
% 2.32/1.29  #Chain   : 0
% 2.32/1.29  #Close   : 0
% 2.32/1.29  
% 2.32/1.29  Ordering : KBO
% 2.32/1.29  
% 2.32/1.29  Simplification rules
% 2.32/1.29  ----------------------
% 2.32/1.29  #Subsume      : 2
% 2.32/1.29  #Demod        : 11
% 2.32/1.29  #Tautology    : 33
% 2.32/1.29  #SimpNegUnit  : 0
% 2.32/1.29  #BackRed      : 0
% 2.32/1.29  
% 2.32/1.29  #Partial instantiations: 0
% 2.32/1.29  #Strategies tried      : 1
% 2.32/1.29  
% 2.32/1.29  Timing (in seconds)
% 2.32/1.29  ----------------------
% 2.32/1.29  Preprocessing        : 0.31
% 2.32/1.29  Parsing              : 0.17
% 2.32/1.29  CNF conversion       : 0.02
% 2.32/1.29  Main loop            : 0.21
% 2.32/1.30  Inferencing          : 0.08
% 2.32/1.30  Reduction            : 0.06
% 2.32/1.30  Demodulation         : 0.05
% 2.32/1.30  BG Simplification    : 0.02
% 2.32/1.30  Subsumption          : 0.04
% 2.32/1.30  Abstraction          : 0.02
% 2.32/1.30  MUC search           : 0.00
% 2.32/1.30  Cooper               : 0.00
% 2.32/1.30  Total                : 0.55
% 2.32/1.30  Index Insertion      : 0.00
% 2.32/1.30  Index Deletion       : 0.00
% 2.32/1.30  Index Matching       : 0.00
% 2.32/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
