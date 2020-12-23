%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:30 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   40 (  51 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  57 expanded)
%              Number of equality atoms :   26 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_55])).

tff(c_73,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_70])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [C_13,A_11,B_12] :
      ( k7_relat_1(C_13,k6_subset_1(A_11,B_12)) = k6_subset_1(C_13,k7_relat_1(C_13,B_12))
      | ~ r1_tarski(k1_relat_1(C_13),A_11)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_228,plain,(
    ! [C_33,A_34,B_35] :
      ( k7_relat_1(C_33,k4_xboole_0(A_34,B_35)) = k4_xboole_0(C_33,k7_relat_1(C_33,B_35))
      | ~ r1_tarski(k1_relat_1(C_33),A_34)
      | ~ v1_relat_1(C_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_16])).

tff(c_434,plain,(
    ! [C_44,B_45,B_46] :
      ( k7_relat_1(C_44,k4_xboole_0(B_45,B_46)) = k4_xboole_0(C_44,k7_relat_1(C_44,B_46))
      | ~ v1_relat_1(C_44)
      | k4_xboole_0(k1_relat_1(C_44),B_45) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_228])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k1_relat_1(k7_relat_1(B_10,k6_subset_1(k1_relat_1(B_10),A_9))) = k6_subset_1(k1_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_23,plain,(
    ! [B_10,A_9] :
      ( k1_relat_1(k7_relat_1(B_10,k4_xboole_0(k1_relat_1(B_10),A_9))) = k4_xboole_0(k1_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_14])).

tff(c_457,plain,(
    ! [C_44,B_46] :
      ( k1_relat_1(k4_xboole_0(C_44,k7_relat_1(C_44,B_46))) = k4_xboole_0(k1_relat_1(C_44),B_46)
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(C_44)
      | k4_xboole_0(k1_relat_1(C_44),k1_relat_1(C_44)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_23])).

tff(c_505,plain,(
    ! [C_47,B_48] :
      ( k1_relat_1(k4_xboole_0(C_47,k7_relat_1(C_47,B_48))) = k4_xboole_0(k1_relat_1(C_47),B_48)
      | ~ v1_relat_1(C_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_457])).

tff(c_18,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_21,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_18])).

tff(c_522,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_21])).

tff(c_536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.33  
% 2.51/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.34  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.51/1.34  
% 2.51/1.34  %Foreground sorts:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Background operators:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Foreground operators:
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.51/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.34  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.51/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.34  
% 2.51/1.35  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 2.51/1.35  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.51/1.35  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.51/1.35  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.51/1.35  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.51/1.35  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.51/1.35  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 2.51/1.35  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_relat_1)).
% 2.51/1.35  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.51/1.35  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.35  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.35  tff(c_55, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.35  tff(c_70, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_55])).
% 2.51/1.35  tff(c_73, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_70])).
% 2.51/1.35  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.35  tff(c_12, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.35  tff(c_16, plain, (![C_13, A_11, B_12]: (k7_relat_1(C_13, k6_subset_1(A_11, B_12))=k6_subset_1(C_13, k7_relat_1(C_13, B_12)) | ~r1_tarski(k1_relat_1(C_13), A_11) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.35  tff(c_228, plain, (![C_33, A_34, B_35]: (k7_relat_1(C_33, k4_xboole_0(A_34, B_35))=k4_xboole_0(C_33, k7_relat_1(C_33, B_35)) | ~r1_tarski(k1_relat_1(C_33), A_34) | ~v1_relat_1(C_33))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_16])).
% 2.51/1.35  tff(c_434, plain, (![C_44, B_45, B_46]: (k7_relat_1(C_44, k4_xboole_0(B_45, B_46))=k4_xboole_0(C_44, k7_relat_1(C_44, B_46)) | ~v1_relat_1(C_44) | k4_xboole_0(k1_relat_1(C_44), B_45)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_228])).
% 2.51/1.35  tff(c_14, plain, (![B_10, A_9]: (k1_relat_1(k7_relat_1(B_10, k6_subset_1(k1_relat_1(B_10), A_9)))=k6_subset_1(k1_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.35  tff(c_23, plain, (![B_10, A_9]: (k1_relat_1(k7_relat_1(B_10, k4_xboole_0(k1_relat_1(B_10), A_9)))=k4_xboole_0(k1_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_14])).
% 2.51/1.35  tff(c_457, plain, (![C_44, B_46]: (k1_relat_1(k4_xboole_0(C_44, k7_relat_1(C_44, B_46)))=k4_xboole_0(k1_relat_1(C_44), B_46) | ~v1_relat_1(C_44) | ~v1_relat_1(C_44) | k4_xboole_0(k1_relat_1(C_44), k1_relat_1(C_44))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_434, c_23])).
% 2.51/1.35  tff(c_505, plain, (![C_47, B_48]: (k1_relat_1(k4_xboole_0(C_47, k7_relat_1(C_47, B_48)))=k4_xboole_0(k1_relat_1(C_47), B_48) | ~v1_relat_1(C_47))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_457])).
% 2.51/1.35  tff(c_18, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.51/1.35  tff(c_21, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_18])).
% 2.51/1.35  tff(c_522, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_505, c_21])).
% 2.51/1.35  tff(c_536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_522])).
% 2.51/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.35  
% 2.51/1.35  Inference rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Ref     : 0
% 2.51/1.35  #Sup     : 135
% 2.51/1.35  #Fact    : 0
% 2.51/1.35  #Define  : 0
% 2.51/1.35  #Split   : 0
% 2.51/1.35  #Chain   : 0
% 2.51/1.35  #Close   : 0
% 2.51/1.35  
% 2.51/1.35  Ordering : KBO
% 2.51/1.35  
% 2.51/1.35  Simplification rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Subsume      : 6
% 2.51/1.35  #Demod        : 77
% 2.51/1.35  #Tautology    : 57
% 2.51/1.35  #SimpNegUnit  : 0
% 2.51/1.35  #BackRed      : 0
% 2.51/1.35  
% 2.51/1.35  #Partial instantiations: 0
% 2.51/1.35  #Strategies tried      : 1
% 2.51/1.35  
% 2.51/1.35  Timing (in seconds)
% 2.51/1.35  ----------------------
% 2.51/1.35  Preprocessing        : 0.29
% 2.51/1.35  Parsing              : 0.15
% 2.51/1.35  CNF conversion       : 0.02
% 2.51/1.35  Main loop            : 0.30
% 2.51/1.35  Inferencing          : 0.12
% 2.51/1.35  Reduction            : 0.10
% 2.51/1.35  Demodulation         : 0.08
% 2.51/1.35  BG Simplification    : 0.02
% 2.51/1.35  Subsumption          : 0.04
% 2.51/1.35  Abstraction          : 0.03
% 2.51/1.35  MUC search           : 0.00
% 2.51/1.35  Cooper               : 0.00
% 2.51/1.35  Total                : 0.61
% 2.51/1.35  Index Insertion      : 0.00
% 2.51/1.35  Index Deletion       : 0.00
% 2.51/1.35  Index Matching       : 0.00
% 2.51/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
