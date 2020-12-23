%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:36 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  58 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :   40 (  66 expanded)
%              Number of equality atoms :   24 (  41 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_3,B_4] : k6_subset_1(A_3,B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k1_relat_1(k6_subset_1(B_8,k7_relat_1(B_8,A_7))) = k6_subset_1(k1_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_15,plain,(
    ! [B_8,A_7] :
      ( k1_relat_1(k4_xboole_0(B_8,k7_relat_1(B_8,A_7))) = k4_xboole_0(k1_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_8])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k1_relat_1(k7_relat_1(B_6,k6_subset_1(k1_relat_1(B_6),A_5))) = k6_subset_1(k1_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_17,plain,(
    ! [B_6,A_5] :
      ( k1_relat_1(k7_relat_1(B_6,k4_xboole_0(k1_relat_1(B_6),A_5))) = k4_xboole_0(k1_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_6])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k3_xboole_0(k1_relat_1(B_10),A_9) = k1_relat_1(k7_relat_1(B_10,A_9))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_27,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,k4_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_2])).

tff(c_250,plain,(
    ! [B_31,A_32] :
      ( k4_xboole_0(k1_relat_1(B_31),k1_relat_1(k7_relat_1(B_31,A_32))) = k3_xboole_0(k1_relat_1(B_31),k4_xboole_0(k1_relat_1(B_31),A_32))
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_51])).

tff(c_12,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_12])).

tff(c_256,plain,
    ( k3_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_16])).

tff(c_292,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_256])).

tff(c_352,plain,
    ( k1_relat_1(k7_relat_1('#skF_2',k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_292])).

tff(c_354,plain,(
    k1_relat_1(k7_relat_1('#skF_2',k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_352])).

tff(c_357,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17,c_354])).

tff(c_359,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_357])).

tff(c_362,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15,c_359])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.38  
% 2.22/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.39  %$ v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.22/1.39  
% 2.22/1.39  %Foreground sorts:
% 2.22/1.39  
% 2.22/1.39  
% 2.22/1.39  %Background operators:
% 2.22/1.39  
% 2.22/1.39  
% 2.22/1.39  %Foreground operators:
% 2.22/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.22/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.39  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.22/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.39  
% 2.22/1.40  tff(f_46, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 2.22/1.40  tff(f_29, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.22/1.40  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 2.22/1.40  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 2.22/1.40  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.22/1.40  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.22/1.40  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.22/1.40  tff(c_4, plain, (![A_3, B_4]: (k6_subset_1(A_3, B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.40  tff(c_8, plain, (![B_8, A_7]: (k1_relat_1(k6_subset_1(B_8, k7_relat_1(B_8, A_7)))=k6_subset_1(k1_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.40  tff(c_15, plain, (![B_8, A_7]: (k1_relat_1(k4_xboole_0(B_8, k7_relat_1(B_8, A_7)))=k4_xboole_0(k1_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_8])).
% 2.22/1.40  tff(c_6, plain, (![B_6, A_5]: (k1_relat_1(k7_relat_1(B_6, k6_subset_1(k1_relat_1(B_6), A_5)))=k6_subset_1(k1_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.40  tff(c_17, plain, (![B_6, A_5]: (k1_relat_1(k7_relat_1(B_6, k4_xboole_0(k1_relat_1(B_6), A_5)))=k4_xboole_0(k1_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_6])).
% 2.22/1.40  tff(c_10, plain, (![B_10, A_9]: (k3_xboole_0(k1_relat_1(B_10), A_9)=k1_relat_1(k7_relat_1(B_10, A_9)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.22/1.40  tff(c_27, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.40  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.40  tff(c_51, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k3_xboole_0(A_17, k4_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_27, c_2])).
% 2.22/1.40  tff(c_250, plain, (![B_31, A_32]: (k4_xboole_0(k1_relat_1(B_31), k1_relat_1(k7_relat_1(B_31, A_32)))=k3_xboole_0(k1_relat_1(B_31), k4_xboole_0(k1_relat_1(B_31), A_32)) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_10, c_51])).
% 2.22/1.40  tff(c_12, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.22/1.40  tff(c_16, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_12])).
% 2.22/1.40  tff(c_256, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_250, c_16])).
% 2.22/1.40  tff(c_292, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_256])).
% 2.22/1.40  tff(c_352, plain, (k1_relat_1(k7_relat_1('#skF_2', k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_292])).
% 2.22/1.40  tff(c_354, plain, (k1_relat_1(k7_relat_1('#skF_2', k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_352])).
% 2.22/1.40  tff(c_357, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17, c_354])).
% 2.22/1.40  tff(c_359, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_357])).
% 2.22/1.40  tff(c_362, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15, c_359])).
% 2.22/1.40  tff(c_366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_362])).
% 2.22/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.40  
% 2.22/1.40  Inference rules
% 2.22/1.40  ----------------------
% 2.22/1.40  #Ref     : 0
% 2.22/1.40  #Sup     : 91
% 2.22/1.40  #Fact    : 0
% 2.22/1.40  #Define  : 0
% 2.22/1.40  #Split   : 0
% 2.22/1.40  #Chain   : 0
% 2.22/1.40  #Close   : 0
% 2.22/1.40  
% 2.22/1.40  Ordering : KBO
% 2.22/1.40  
% 2.22/1.40  Simplification rules
% 2.22/1.40  ----------------------
% 2.22/1.40  #Subsume      : 3
% 2.22/1.40  #Demod        : 33
% 2.22/1.40  #Tautology    : 30
% 2.22/1.40  #SimpNegUnit  : 0
% 2.22/1.40  #BackRed      : 0
% 2.22/1.40  
% 2.22/1.40  #Partial instantiations: 0
% 2.22/1.40  #Strategies tried      : 1
% 2.22/1.40  
% 2.22/1.40  Timing (in seconds)
% 2.22/1.40  ----------------------
% 2.22/1.40  Preprocessing        : 0.25
% 2.22/1.40  Parsing              : 0.13
% 2.22/1.40  CNF conversion       : 0.02
% 2.22/1.40  Main loop            : 0.25
% 2.22/1.40  Inferencing          : 0.10
% 2.22/1.40  Reduction            : 0.08
% 2.22/1.40  Demodulation         : 0.06
% 2.22/1.40  BG Simplification    : 0.02
% 2.22/1.40  Subsumption          : 0.04
% 2.22/1.40  Abstraction          : 0.02
% 2.22/1.40  MUC search           : 0.00
% 2.22/1.40  Cooper               : 0.00
% 2.22/1.40  Total                : 0.53
% 2.22/1.40  Index Insertion      : 0.00
% 2.22/1.40  Index Deletion       : 0.00
% 2.22/1.40  Index Matching       : 0.00
% 2.22/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
