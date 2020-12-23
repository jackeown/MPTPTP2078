%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:34 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   54 (  72 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 (  93 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_31,B_32] : k6_subset_1(A_31,B_32) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [C_37,A_35,B_36] :
      ( k7_relat_1(C_37,k6_subset_1(A_35,B_36)) = k6_subset_1(C_37,k7_relat_1(C_37,B_36))
      | ~ r1_tarski(k1_relat_1(C_37),A_35)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_735,plain,(
    ! [C_111,A_112,B_113] :
      ( k7_relat_1(C_111,k4_xboole_0(A_112,B_113)) = k4_xboole_0(C_111,k7_relat_1(C_111,B_113))
      | ~ r1_tarski(k1_relat_1(C_111),A_112)
      | ~ v1_relat_1(C_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_30])).

tff(c_753,plain,(
    ! [C_114,B_115] :
      ( k7_relat_1(C_114,k4_xboole_0(k1_relat_1(C_114),B_115)) = k4_xboole_0(C_114,k7_relat_1(C_114,B_115))
      | ~ v1_relat_1(C_114) ) ),
    inference(resolution,[status(thm)],[c_8,c_735])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_234,plain,(
    ! [B_80,A_81] :
      ( k1_relat_1(k7_relat_1(B_80,A_81)) = A_81
      | ~ r1_tarski(A_81,k1_relat_1(B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_255,plain,(
    ! [B_80,B_10] :
      ( k1_relat_1(k7_relat_1(B_80,k4_xboole_0(k1_relat_1(B_80),B_10))) = k4_xboole_0(k1_relat_1(B_80),B_10)
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_14,c_234])).

tff(c_774,plain,(
    ! [C_114,B_115] :
      ( k1_relat_1(k4_xboole_0(C_114,k7_relat_1(C_114,B_115))) = k4_xboole_0(k1_relat_1(C_114),B_115)
      | ~ v1_relat_1(C_114)
      | ~ v1_relat_1(C_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_255])).

tff(c_32,plain,(
    ! [B_39,A_38] :
      ( k3_xboole_0(k1_relat_1(B_39),A_38) = k1_relat_1(k7_relat_1(B_39,A_38))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_295,plain,(
    ! [B_95,B_96] :
      ( k1_relat_1(k7_relat_1(B_95,k3_xboole_0(k1_relat_1(B_95),B_96))) = k3_xboole_0(k1_relat_1(B_95),B_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_12,c_234])).

tff(c_137,plain,(
    ! [B_68,A_69] :
      ( k3_xboole_0(k1_relat_1(B_68),A_69) = k1_relat_1(k7_relat_1(B_68,A_69))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_146,plain,(
    ! [B_68,A_69] :
      ( k5_xboole_0(k1_relat_1(B_68),k1_relat_1(k7_relat_1(B_68,A_69))) = k4_xboole_0(k1_relat_1(B_68),A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_10])).

tff(c_307,plain,(
    ! [B_95,B_96] :
      ( k5_xboole_0(k1_relat_1(B_95),k3_xboole_0(k1_relat_1(B_95),B_96)) = k4_xboole_0(k1_relat_1(B_95),k3_xboole_0(k1_relat_1(B_95),B_96))
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_146])).

tff(c_678,plain,(
    ! [B_109,B_110] :
      ( k4_xboole_0(k1_relat_1(B_109),k3_xboole_0(k1_relat_1(B_109),B_110)) = k4_xboole_0(k1_relat_1(B_109),B_110)
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_307])).

tff(c_1531,plain,(
    ! [B_132,A_133] :
      ( k4_xboole_0(k1_relat_1(B_132),k1_relat_1(k7_relat_1(B_132,A_133))) = k4_xboole_0(k1_relat_1(B_132),A_133)
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_678])).

tff(c_38,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_41,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_38])).

tff(c_1546,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_41])).

tff(c_1612,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_40,c_1546])).

tff(c_1624,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_1612])).

tff(c_1628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.88  
% 3.61/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.88  %$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.61/1.88  
% 3.61/1.88  %Foreground sorts:
% 3.61/1.88  
% 3.61/1.88  
% 3.61/1.88  %Background operators:
% 3.61/1.88  
% 3.61/1.88  
% 3.61/1.88  %Foreground operators:
% 3.61/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.61/1.88  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.61/1.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.61/1.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.61/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.61/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.61/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.61/1.88  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.88  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.61/1.88  tff('#skF_1', type, '#skF_1': $i).
% 3.61/1.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.61/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.61/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.61/1.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.61/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.61/1.88  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.61/1.88  
% 3.61/1.89  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 3.61/1.89  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.61/1.89  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.61/1.89  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 3.61/1.89  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.61/1.89  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.61/1.89  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.61/1.89  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.61/1.89  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.61/1.89  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.61/1.89  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.61/1.89  tff(c_26, plain, (![A_31, B_32]: (k6_subset_1(A_31, B_32)=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.61/1.89  tff(c_30, plain, (![C_37, A_35, B_36]: (k7_relat_1(C_37, k6_subset_1(A_35, B_36))=k6_subset_1(C_37, k7_relat_1(C_37, B_36)) | ~r1_tarski(k1_relat_1(C_37), A_35) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.61/1.89  tff(c_735, plain, (![C_111, A_112, B_113]: (k7_relat_1(C_111, k4_xboole_0(A_112, B_113))=k4_xboole_0(C_111, k7_relat_1(C_111, B_113)) | ~r1_tarski(k1_relat_1(C_111), A_112) | ~v1_relat_1(C_111))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_30])).
% 3.61/1.89  tff(c_753, plain, (![C_114, B_115]: (k7_relat_1(C_114, k4_xboole_0(k1_relat_1(C_114), B_115))=k4_xboole_0(C_114, k7_relat_1(C_114, B_115)) | ~v1_relat_1(C_114))), inference(resolution, [status(thm)], [c_8, c_735])).
% 3.61/1.89  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.61/1.89  tff(c_234, plain, (![B_80, A_81]: (k1_relat_1(k7_relat_1(B_80, A_81))=A_81 | ~r1_tarski(A_81, k1_relat_1(B_80)) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.61/1.89  tff(c_255, plain, (![B_80, B_10]: (k1_relat_1(k7_relat_1(B_80, k4_xboole_0(k1_relat_1(B_80), B_10)))=k4_xboole_0(k1_relat_1(B_80), B_10) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_14, c_234])).
% 3.61/1.89  tff(c_774, plain, (![C_114, B_115]: (k1_relat_1(k4_xboole_0(C_114, k7_relat_1(C_114, B_115)))=k4_xboole_0(k1_relat_1(C_114), B_115) | ~v1_relat_1(C_114) | ~v1_relat_1(C_114))), inference(superposition, [status(thm), theory('equality')], [c_753, c_255])).
% 3.61/1.89  tff(c_32, plain, (![B_39, A_38]: (k3_xboole_0(k1_relat_1(B_39), A_38)=k1_relat_1(k7_relat_1(B_39, A_38)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.61/1.89  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.61/1.89  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.61/1.89  tff(c_295, plain, (![B_95, B_96]: (k1_relat_1(k7_relat_1(B_95, k3_xboole_0(k1_relat_1(B_95), B_96)))=k3_xboole_0(k1_relat_1(B_95), B_96) | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_12, c_234])).
% 3.61/1.89  tff(c_137, plain, (![B_68, A_69]: (k3_xboole_0(k1_relat_1(B_68), A_69)=k1_relat_1(k7_relat_1(B_68, A_69)) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.61/1.89  tff(c_146, plain, (![B_68, A_69]: (k5_xboole_0(k1_relat_1(B_68), k1_relat_1(k7_relat_1(B_68, A_69)))=k4_xboole_0(k1_relat_1(B_68), A_69) | ~v1_relat_1(B_68))), inference(superposition, [status(thm), theory('equality')], [c_137, c_10])).
% 3.61/1.89  tff(c_307, plain, (![B_95, B_96]: (k5_xboole_0(k1_relat_1(B_95), k3_xboole_0(k1_relat_1(B_95), B_96))=k4_xboole_0(k1_relat_1(B_95), k3_xboole_0(k1_relat_1(B_95), B_96)) | ~v1_relat_1(B_95) | ~v1_relat_1(B_95))), inference(superposition, [status(thm), theory('equality')], [c_295, c_146])).
% 3.61/1.89  tff(c_678, plain, (![B_109, B_110]: (k4_xboole_0(k1_relat_1(B_109), k3_xboole_0(k1_relat_1(B_109), B_110))=k4_xboole_0(k1_relat_1(B_109), B_110) | ~v1_relat_1(B_109) | ~v1_relat_1(B_109))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_307])).
% 3.61/1.89  tff(c_1531, plain, (![B_132, A_133]: (k4_xboole_0(k1_relat_1(B_132), k1_relat_1(k7_relat_1(B_132, A_133)))=k4_xboole_0(k1_relat_1(B_132), A_133) | ~v1_relat_1(B_132) | ~v1_relat_1(B_132) | ~v1_relat_1(B_132))), inference(superposition, [status(thm), theory('equality')], [c_32, c_678])).
% 3.61/1.89  tff(c_38, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.61/1.89  tff(c_41, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_38])).
% 3.61/1.89  tff(c_1546, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1531, c_41])).
% 3.61/1.89  tff(c_1612, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_40, c_1546])).
% 3.61/1.89  tff(c_1624, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_774, c_1612])).
% 3.61/1.89  tff(c_1628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1624])).
% 3.61/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.89  
% 3.61/1.89  Inference rules
% 3.61/1.89  ----------------------
% 3.61/1.89  #Ref     : 0
% 3.61/1.89  #Sup     : 462
% 3.61/1.89  #Fact    : 0
% 3.61/1.89  #Define  : 0
% 3.61/1.89  #Split   : 0
% 3.61/1.89  #Chain   : 0
% 3.61/1.89  #Close   : 0
% 3.61/1.89  
% 3.61/1.89  Ordering : KBO
% 3.61/1.89  
% 3.61/1.89  Simplification rules
% 3.61/1.89  ----------------------
% 3.61/1.89  #Subsume      : 30
% 3.61/1.89  #Demod        : 49
% 3.61/1.89  #Tautology    : 93
% 3.61/1.89  #SimpNegUnit  : 0
% 3.61/1.89  #BackRed      : 0
% 3.61/1.89  
% 3.61/1.89  #Partial instantiations: 0
% 3.61/1.89  #Strategies tried      : 1
% 3.61/1.89  
% 3.61/1.89  Timing (in seconds)
% 3.61/1.89  ----------------------
% 3.61/1.89  Preprocessing        : 0.50
% 3.61/1.89  Parsing              : 0.26
% 3.61/1.89  CNF conversion       : 0.03
% 3.61/1.89  Main loop            : 0.51
% 3.61/1.89  Inferencing          : 0.19
% 3.61/1.89  Reduction            : 0.15
% 3.61/1.89  Demodulation         : 0.11
% 3.61/1.89  BG Simplification    : 0.05
% 3.61/1.89  Subsumption          : 0.11
% 3.61/1.89  Abstraction          : 0.04
% 3.61/1.89  MUC search           : 0.00
% 3.61/1.89  Cooper               : 0.00
% 3.61/1.89  Total                : 1.04
% 3.61/1.90  Index Insertion      : 0.00
% 3.61/1.90  Index Deletion       : 0.00
% 3.61/1.90  Index Matching       : 0.00
% 3.61/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
