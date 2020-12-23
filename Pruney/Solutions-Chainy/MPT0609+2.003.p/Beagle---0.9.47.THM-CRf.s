%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:31 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   48 (  70 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 (  94 expanded)
%              Number of equality atoms :   26 (  45 expanded)
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

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

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

tff(c_727,plain,(
    ! [C_67,A_68,B_69] :
      ( k7_relat_1(C_67,k4_xboole_0(A_68,B_69)) = k4_xboole_0(C_67,k7_relat_1(C_67,B_69))
      | ~ r1_tarski(k1_relat_1(C_67),A_68)
      | ~ v1_relat_1(C_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_20])).

tff(c_748,plain,(
    ! [C_70,B_71] :
      ( k7_relat_1(C_70,k4_xboole_0(k1_relat_1(C_70),B_71)) = k4_xboole_0(C_70,k7_relat_1(C_70,B_71))
      | ~ v1_relat_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_727])).

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

tff(c_760,plain,(
    ! [C_70,B_71] :
      ( k1_relat_1(k4_xboole_0(C_70,k7_relat_1(C_70,B_71))) = k4_xboole_0(k1_relat_1(C_70),B_71)
      | ~ v1_relat_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_32])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_19,A_18)),k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_279,plain,(
    ! [B_49,A_50] :
      ( k1_relat_1(k7_relat_1(B_49,A_50)) = A_50
      | ~ r1_tarski(A_50,k1_relat_1(B_49))
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_422,plain,(
    ! [B_60,A_61] :
      ( k1_relat_1(k7_relat_1(B_60,k1_relat_1(k7_relat_1(B_60,A_61)))) = k1_relat_1(k7_relat_1(B_60,A_61))
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_22,c_279])).

tff(c_213,plain,(
    ! [B_45,A_46] :
      ( k3_xboole_0(k1_relat_1(B_45),A_46) = k1_relat_1(k7_relat_1(B_45,A_46))
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_222,plain,(
    ! [B_45,A_46] :
      ( k5_xboole_0(k1_relat_1(B_45),k1_relat_1(k7_relat_1(B_45,A_46))) = k4_xboole_0(k1_relat_1(B_45),A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_8])).

tff(c_1480,plain,(
    ! [B_93,A_94] :
      ( k5_xboole_0(k1_relat_1(B_93),k1_relat_1(k7_relat_1(B_93,A_94))) = k4_xboole_0(k1_relat_1(B_93),k1_relat_1(k7_relat_1(B_93,A_94)))
      | ~ v1_relat_1(B_93)
      | ~ v1_relat_1(B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_222])).

tff(c_1769,plain,(
    ! [B_97,A_98] :
      ( k4_xboole_0(k1_relat_1(B_97),k1_relat_1(k7_relat_1(B_97,A_98))) = k4_xboole_0(k1_relat_1(B_97),A_98)
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1480,c_222])).

tff(c_28,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_33,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_28])).

tff(c_1796,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1769,c_33])).

tff(c_1856,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_30,c_1796])).

tff(c_1865,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_760,c_1856])).

tff(c_1869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:20:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.61  
% 3.47/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.61  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.47/1.61  
% 3.47/1.61  %Foreground sorts:
% 3.47/1.61  
% 3.47/1.61  
% 3.47/1.61  %Background operators:
% 3.47/1.61  
% 3.47/1.61  
% 3.47/1.61  %Foreground operators:
% 3.47/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.47/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.47/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.47/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.47/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.47/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.47/1.61  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.47/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.47/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.47/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.47/1.61  
% 3.47/1.62  tff(f_70, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 3.47/1.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.47/1.62  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.47/1.62  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 3.47/1.62  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_relat_1)).
% 3.47/1.62  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 3.47/1.62  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.47/1.62  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.47/1.62  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.47/1.62  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.47/1.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.47/1.62  tff(c_14, plain, (![A_9, B_10]: (k6_subset_1(A_9, B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.47/1.62  tff(c_20, plain, (![C_17, A_15, B_16]: (k7_relat_1(C_17, k6_subset_1(A_15, B_16))=k6_subset_1(C_17, k7_relat_1(C_17, B_16)) | ~r1_tarski(k1_relat_1(C_17), A_15) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.47/1.62  tff(c_727, plain, (![C_67, A_68, B_69]: (k7_relat_1(C_67, k4_xboole_0(A_68, B_69))=k4_xboole_0(C_67, k7_relat_1(C_67, B_69)) | ~r1_tarski(k1_relat_1(C_67), A_68) | ~v1_relat_1(C_67))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_20])).
% 3.47/1.62  tff(c_748, plain, (![C_70, B_71]: (k7_relat_1(C_70, k4_xboole_0(k1_relat_1(C_70), B_71))=k4_xboole_0(C_70, k7_relat_1(C_70, B_71)) | ~v1_relat_1(C_70))), inference(resolution, [status(thm)], [c_6, c_727])).
% 3.47/1.62  tff(c_18, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, k6_subset_1(k1_relat_1(B_14), A_13)))=k6_subset_1(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.47/1.62  tff(c_32, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, k4_xboole_0(k1_relat_1(B_14), A_13)))=k4_xboole_0(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 3.47/1.62  tff(c_760, plain, (![C_70, B_71]: (k1_relat_1(k4_xboole_0(C_70, k7_relat_1(C_70, B_71)))=k4_xboole_0(k1_relat_1(C_70), B_71) | ~v1_relat_1(C_70) | ~v1_relat_1(C_70))), inference(superposition, [status(thm), theory('equality')], [c_748, c_32])).
% 3.47/1.62  tff(c_22, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(k7_relat_1(B_19, A_18)), k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.47/1.62  tff(c_279, plain, (![B_49, A_50]: (k1_relat_1(k7_relat_1(B_49, A_50))=A_50 | ~r1_tarski(A_50, k1_relat_1(B_49)) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.47/1.62  tff(c_422, plain, (![B_60, A_61]: (k1_relat_1(k7_relat_1(B_60, k1_relat_1(k7_relat_1(B_60, A_61))))=k1_relat_1(k7_relat_1(B_60, A_61)) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_22, c_279])).
% 3.47/1.62  tff(c_213, plain, (![B_45, A_46]: (k3_xboole_0(k1_relat_1(B_45), A_46)=k1_relat_1(k7_relat_1(B_45, A_46)) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.47/1.62  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.47/1.62  tff(c_222, plain, (![B_45, A_46]: (k5_xboole_0(k1_relat_1(B_45), k1_relat_1(k7_relat_1(B_45, A_46)))=k4_xboole_0(k1_relat_1(B_45), A_46) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_213, c_8])).
% 3.47/1.62  tff(c_1480, plain, (![B_93, A_94]: (k5_xboole_0(k1_relat_1(B_93), k1_relat_1(k7_relat_1(B_93, A_94)))=k4_xboole_0(k1_relat_1(B_93), k1_relat_1(k7_relat_1(B_93, A_94))) | ~v1_relat_1(B_93) | ~v1_relat_1(B_93))), inference(superposition, [status(thm), theory('equality')], [c_422, c_222])).
% 3.47/1.62  tff(c_1769, plain, (![B_97, A_98]: (k4_xboole_0(k1_relat_1(B_97), k1_relat_1(k7_relat_1(B_97, A_98)))=k4_xboole_0(k1_relat_1(B_97), A_98) | ~v1_relat_1(B_97) | ~v1_relat_1(B_97) | ~v1_relat_1(B_97))), inference(superposition, [status(thm), theory('equality')], [c_1480, c_222])).
% 3.47/1.62  tff(c_28, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.47/1.62  tff(c_33, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_28])).
% 3.47/1.62  tff(c_1796, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1769, c_33])).
% 3.47/1.62  tff(c_1856, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_30, c_1796])).
% 3.47/1.62  tff(c_1865, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_760, c_1856])).
% 3.47/1.62  tff(c_1869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1865])).
% 3.47/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.62  
% 3.47/1.62  Inference rules
% 3.47/1.62  ----------------------
% 3.47/1.62  #Ref     : 0
% 3.47/1.62  #Sup     : 548
% 3.47/1.62  #Fact    : 0
% 3.47/1.62  #Define  : 0
% 3.47/1.62  #Split   : 0
% 3.47/1.62  #Chain   : 0
% 3.47/1.62  #Close   : 0
% 3.47/1.62  
% 3.47/1.62  Ordering : KBO
% 3.47/1.62  
% 3.47/1.62  Simplification rules
% 3.47/1.62  ----------------------
% 3.47/1.62  #Subsume      : 32
% 3.47/1.62  #Demod        : 25
% 3.47/1.62  #Tautology    : 96
% 3.47/1.62  #SimpNegUnit  : 0
% 3.47/1.62  #BackRed      : 0
% 3.47/1.62  
% 3.47/1.62  #Partial instantiations: 0
% 3.47/1.62  #Strategies tried      : 1
% 3.47/1.62  
% 3.47/1.62  Timing (in seconds)
% 3.47/1.62  ----------------------
% 3.81/1.62  Preprocessing        : 0.30
% 3.81/1.62  Parsing              : 0.16
% 3.81/1.62  CNF conversion       : 0.02
% 3.81/1.62  Main loop            : 0.55
% 3.81/1.62  Inferencing          : 0.20
% 3.81/1.62  Reduction            : 0.16
% 3.81/1.62  Demodulation         : 0.12
% 3.81/1.62  BG Simplification    : 0.04
% 3.81/1.62  Subsumption          : 0.11
% 3.81/1.62  Abstraction          : 0.04
% 3.81/1.62  MUC search           : 0.00
% 3.81/1.62  Cooper               : 0.00
% 3.81/1.62  Total                : 0.87
% 3.81/1.62  Index Insertion      : 0.00
% 3.81/1.62  Index Deletion       : 0.00
% 3.81/1.62  Index Matching       : 0.00
% 3.81/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
