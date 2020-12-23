%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:45 EST 2020

% Result     : Theorem 24.29s
% Output     : CNFRefutation 24.38s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 155 expanded)
%              Number of leaves         :   25 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 217 expanded)
%              Number of equality atoms :   34 ( 107 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k4_xboole_0(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_24])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_59,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_79,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_79])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_138,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(k4_xboole_0(A_40,B_41),C_42) = k4_xboole_0(A_40,k2_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_289,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k2_xboole_0(B_54,k1_xboole_0)) = k4_xboole_0(A_53,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_138])).

tff(c_480,plain,(
    ! [A_60] : k4_xboole_0(A_60,k2_xboole_0('#skF_2','#skF_1')) = k4_xboole_0(A_60,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_289])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_xboole_0(k4_xboole_0(A_9,B_10),B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_156,plain,(
    ! [A_40,B_41,C_42] : r1_xboole_0(k4_xboole_0(A_40,k2_xboole_0(B_41,C_42)),C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_12])).

tff(c_500,plain,(
    ! [A_60] : r1_xboole_0(k4_xboole_0(A_60,'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_156])).

tff(c_40,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_40])).

tff(c_95,plain,(
    ! [B_33,A_34] :
      ( k7_relat_1(B_33,A_34) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_33),A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_105,plain,(
    ! [B_35] :
      ( k7_relat_1(B_35,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_43,c_95])).

tff(c_113,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_105])).

tff(c_172,plain,(
    ! [A_5,C_42] : k4_xboole_0(A_5,k2_xboole_0(k1_xboole_0,C_42)) = k4_xboole_0(A_5,C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_138])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k6_subset_1(B_16,k7_relat_1(B_16,A_15))) = k6_subset_1(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_29,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k4_xboole_0(B_16,k7_relat_1(B_16,A_15))) = k4_xboole_0(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_18])).

tff(c_255,plain,(
    ! [B_50,A_51] :
      ( k1_relat_1(k4_xboole_0(B_50,k7_relat_1(B_50,A_51))) = k4_xboole_0(k1_relat_1(B_50),A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_18])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2201,plain,(
    ! [B_134,A_135,A_136] :
      ( k7_relat_1(k4_xboole_0(B_134,k7_relat_1(B_134,A_135)),A_136) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(B_134),A_135),A_136)
      | ~ v1_relat_1(k4_xboole_0(B_134,k7_relat_1(B_134,A_135)))
      | ~ v1_relat_1(B_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_20])).

tff(c_2283,plain,(
    ! [B_16,A_15,A_135,A_136] :
      ( k7_relat_1(k4_xboole_0(k4_xboole_0(B_16,k7_relat_1(B_16,A_15)),k7_relat_1(k4_xboole_0(B_16,k7_relat_1(B_16,A_15)),A_135)),A_136) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k4_xboole_0(k1_relat_1(B_16),A_15),A_135),A_136)
      | ~ v1_relat_1(k4_xboole_0(k4_xboole_0(B_16,k7_relat_1(B_16,A_15)),k7_relat_1(k4_xboole_0(B_16,k7_relat_1(B_16,A_15)),A_135)))
      | ~ v1_relat_1(k4_xboole_0(B_16,k7_relat_1(B_16,A_15)))
      | ~ v1_relat_1(B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_2201])).

tff(c_32388,plain,(
    ! [B_493,A_494,A_495,A_496] :
      ( k7_relat_1(k4_xboole_0(B_493,k2_xboole_0(k7_relat_1(B_493,A_494),k7_relat_1(k4_xboole_0(B_493,k7_relat_1(B_493,A_494)),A_495))),A_496) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(B_493),k2_xboole_0(A_494,A_495)),A_496)
      | ~ v1_relat_1(k4_xboole_0(B_493,k2_xboole_0(k7_relat_1(B_493,A_494),k7_relat_1(k4_xboole_0(B_493,k7_relat_1(B_493,A_494)),A_495))))
      | ~ v1_relat_1(k4_xboole_0(B_493,k7_relat_1(B_493,A_494)))
      | ~ v1_relat_1(B_493) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_10,c_2283])).

tff(c_32451,plain,(
    ! [A_495,A_496] :
      ( k7_relat_1(k4_xboole_0('#skF_3',k2_xboole_0(k7_relat_1('#skF_3',k1_xboole_0),k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3',k1_xboole_0)),A_495))),A_496) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1('#skF_3'),k2_xboole_0(k1_xboole_0,A_495)),A_496)
      | ~ v1_relat_1(k4_xboole_0('#skF_3',k2_xboole_0(k7_relat_1('#skF_3',k1_xboole_0),k7_relat_1(k4_xboole_0('#skF_3',k1_xboole_0),A_495))))
      | ~ v1_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3',k1_xboole_0)))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_32388])).

tff(c_48112,plain,(
    ! [A_645,A_646] :
      ( k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3',A_645)),A_646) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1('#skF_3'),A_645),A_646)
      | ~ v1_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3',A_645))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_8,c_113,c_172,c_113,c_8,c_172,c_172,c_8,c_113,c_113,c_32451])).

tff(c_48704,plain,
    ( k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') = k1_xboole_0
    | ~ v1_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_500,c_48112])).

tff(c_48881,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_48704])).

tff(c_48893,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_48881])).

tff(c_48897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_48893])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:28:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.29/16.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.33/16.31  
% 24.33/16.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.33/16.31  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 24.33/16.31  
% 24.33/16.31  %Foreground sorts:
% 24.33/16.31  
% 24.33/16.31  
% 24.33/16.31  %Background operators:
% 24.33/16.31  
% 24.33/16.31  
% 24.33/16.31  %Foreground operators:
% 24.33/16.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.33/16.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 24.33/16.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 24.33/16.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.33/16.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.33/16.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 24.33/16.31  tff('#skF_2', type, '#skF_2': $i).
% 24.33/16.31  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 24.33/16.31  tff('#skF_3', type, '#skF_3': $i).
% 24.33/16.31  tff('#skF_1', type, '#skF_1': $i).
% 24.33/16.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.33/16.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 24.33/16.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.33/16.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.33/16.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 24.33/16.31  
% 24.38/16.33  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 24.38/16.33  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 24.38/16.33  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 24.38/16.33  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 24.38/16.33  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 24.38/16.33  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 24.38/16.33  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 24.38/16.33  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 24.38/16.33  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 24.38/16.33  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 24.38/16.33  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.38/16.33  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k4_xboole_0(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 24.38/16.33  tff(c_14, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 24.38/16.33  tff(c_24, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.38/16.33  tff(c_30, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_24])).
% 24.38/16.33  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.38/16.33  tff(c_59, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 24.38/16.33  tff(c_67, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_59])).
% 24.38/16.33  tff(c_79, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.38/16.33  tff(c_88, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_67, c_79])).
% 24.38/16.33  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.38/16.33  tff(c_138, plain, (![A_40, B_41, C_42]: (k4_xboole_0(k4_xboole_0(A_40, B_41), C_42)=k4_xboole_0(A_40, k2_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.38/16.33  tff(c_289, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k2_xboole_0(B_54, k1_xboole_0))=k4_xboole_0(A_53, B_54))), inference(superposition, [status(thm), theory('equality')], [c_8, c_138])).
% 24.38/16.33  tff(c_480, plain, (![A_60]: (k4_xboole_0(A_60, k2_xboole_0('#skF_2', '#skF_1'))=k4_xboole_0(A_60, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_289])).
% 24.38/16.33  tff(c_12, plain, (![A_9, B_10]: (r1_xboole_0(k4_xboole_0(A_9, B_10), B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.38/16.33  tff(c_156, plain, (![A_40, B_41, C_42]: (r1_xboole_0(k4_xboole_0(A_40, k2_xboole_0(B_41, C_42)), C_42))), inference(superposition, [status(thm), theory('equality')], [c_138, c_12])).
% 24.38/16.33  tff(c_500, plain, (![A_60]: (r1_xboole_0(k4_xboole_0(A_60, '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_480, c_156])).
% 24.38/16.33  tff(c_40, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.38/16.33  tff(c_43, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_40])).
% 24.38/16.33  tff(c_95, plain, (![B_33, A_34]: (k7_relat_1(B_33, A_34)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_33), A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 24.38/16.33  tff(c_105, plain, (![B_35]: (k7_relat_1(B_35, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_43, c_95])).
% 24.38/16.33  tff(c_113, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_105])).
% 24.38/16.33  tff(c_172, plain, (![A_5, C_42]: (k4_xboole_0(A_5, k2_xboole_0(k1_xboole_0, C_42))=k4_xboole_0(A_5, C_42))), inference(superposition, [status(thm), theory('equality')], [c_8, c_138])).
% 24.38/16.33  tff(c_10, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.38/16.33  tff(c_18, plain, (![B_16, A_15]: (k1_relat_1(k6_subset_1(B_16, k7_relat_1(B_16, A_15)))=k6_subset_1(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.38/16.33  tff(c_29, plain, (![B_16, A_15]: (k1_relat_1(k4_xboole_0(B_16, k7_relat_1(B_16, A_15)))=k4_xboole_0(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 24.38/16.33  tff(c_255, plain, (![B_50, A_51]: (k1_relat_1(k4_xboole_0(B_50, k7_relat_1(B_50, A_51)))=k4_xboole_0(k1_relat_1(B_50), A_51) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 24.38/16.33  tff(c_20, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 24.38/16.33  tff(c_2201, plain, (![B_134, A_135, A_136]: (k7_relat_1(k4_xboole_0(B_134, k7_relat_1(B_134, A_135)), A_136)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1(B_134), A_135), A_136) | ~v1_relat_1(k4_xboole_0(B_134, k7_relat_1(B_134, A_135))) | ~v1_relat_1(B_134))), inference(superposition, [status(thm), theory('equality')], [c_255, c_20])).
% 24.38/16.33  tff(c_2283, plain, (![B_16, A_15, A_135, A_136]: (k7_relat_1(k4_xboole_0(k4_xboole_0(B_16, k7_relat_1(B_16, A_15)), k7_relat_1(k4_xboole_0(B_16, k7_relat_1(B_16, A_15)), A_135)), A_136)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k4_xboole_0(k1_relat_1(B_16), A_15), A_135), A_136) | ~v1_relat_1(k4_xboole_0(k4_xboole_0(B_16, k7_relat_1(B_16, A_15)), k7_relat_1(k4_xboole_0(B_16, k7_relat_1(B_16, A_15)), A_135))) | ~v1_relat_1(k4_xboole_0(B_16, k7_relat_1(B_16, A_15))) | ~v1_relat_1(B_16))), inference(superposition, [status(thm), theory('equality')], [c_29, c_2201])).
% 24.38/16.33  tff(c_32388, plain, (![B_493, A_494, A_495, A_496]: (k7_relat_1(k4_xboole_0(B_493, k2_xboole_0(k7_relat_1(B_493, A_494), k7_relat_1(k4_xboole_0(B_493, k7_relat_1(B_493, A_494)), A_495))), A_496)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1(B_493), k2_xboole_0(A_494, A_495)), A_496) | ~v1_relat_1(k4_xboole_0(B_493, k2_xboole_0(k7_relat_1(B_493, A_494), k7_relat_1(k4_xboole_0(B_493, k7_relat_1(B_493, A_494)), A_495)))) | ~v1_relat_1(k4_xboole_0(B_493, k7_relat_1(B_493, A_494))) | ~v1_relat_1(B_493))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_10, c_2283])).
% 24.38/16.33  tff(c_32451, plain, (![A_495, A_496]: (k7_relat_1(k4_xboole_0('#skF_3', k2_xboole_0(k7_relat_1('#skF_3', k1_xboole_0), k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', k1_xboole_0)), A_495))), A_496)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1('#skF_3'), k2_xboole_0(k1_xboole_0, A_495)), A_496) | ~v1_relat_1(k4_xboole_0('#skF_3', k2_xboole_0(k7_relat_1('#skF_3', k1_xboole_0), k7_relat_1(k4_xboole_0('#skF_3', k1_xboole_0), A_495)))) | ~v1_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', k1_xboole_0))) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_32388])).
% 24.38/16.33  tff(c_48112, plain, (![A_645, A_646]: (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', A_645)), A_646)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1('#skF_3'), A_645), A_646) | ~v1_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', A_645))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_8, c_113, c_172, c_113, c_8, c_172, c_172, c_8, c_113, c_113, c_32451])).
% 24.38/16.33  tff(c_48704, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')=k1_xboole_0 | ~v1_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_500, c_48112])).
% 24.38/16.33  tff(c_48881, plain, (~v1_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_48704])).
% 24.38/16.33  tff(c_48893, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_48881])).
% 24.38/16.33  tff(c_48897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_48893])).
% 24.38/16.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.38/16.33  
% 24.38/16.33  Inference rules
% 24.38/16.33  ----------------------
% 24.38/16.33  #Ref     : 0
% 24.38/16.33  #Sup     : 12264
% 24.38/16.33  #Fact    : 0
% 24.38/16.33  #Define  : 0
% 24.38/16.33  #Split   : 1
% 24.38/16.33  #Chain   : 0
% 24.38/16.33  #Close   : 0
% 24.38/16.33  
% 24.38/16.33  Ordering : KBO
% 24.38/16.33  
% 24.38/16.33  Simplification rules
% 24.38/16.33  ----------------------
% 24.38/16.33  #Subsume      : 433
% 24.38/16.33  #Demod        : 15688
% 24.38/16.33  #Tautology    : 3935
% 24.38/16.33  #SimpNegUnit  : 1
% 24.38/16.33  #BackRed      : 6
% 24.38/16.33  
% 24.38/16.33  #Partial instantiations: 0
% 24.38/16.33  #Strategies tried      : 1
% 24.38/16.33  
% 24.38/16.33  Timing (in seconds)
% 24.38/16.33  ----------------------
% 24.38/16.33  Preprocessing        : 0.31
% 24.38/16.33  Parsing              : 0.17
% 24.38/16.33  CNF conversion       : 0.02
% 24.38/16.33  Main loop            : 15.22
% 24.38/16.33  Inferencing          : 1.40
% 24.38/16.33  Reduction            : 9.29
% 24.38/16.33  Demodulation         : 8.63
% 24.38/16.33  BG Simplification    : 0.18
% 24.38/16.33  Subsumption          : 3.86
% 24.38/16.33  Abstraction          : 0.23
% 24.38/16.34  MUC search           : 0.00
% 24.38/16.34  Cooper               : 0.00
% 24.38/16.34  Total                : 15.56
% 24.38/16.34  Index Insertion      : 0.00
% 24.38/16.34  Index Deletion       : 0.00
% 24.38/16.34  Index Matching       : 0.00
% 24.38/16.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
