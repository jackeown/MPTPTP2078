%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:34 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   55 (  75 expanded)
%              Number of leaves         :   30 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 (  94 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_76,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_34,B_35] : k6_subset_1(A_34,B_35) = k4_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [C_42,A_40,B_41] :
      ( k7_relat_1(C_42,k6_subset_1(A_40,B_41)) = k6_subset_1(C_42,k7_relat_1(C_42,B_41))
      | ~ r1_tarski(k1_relat_1(C_42),A_40)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_445,plain,(
    ! [C_100,A_101,B_102] :
      ( k7_relat_1(C_100,k4_xboole_0(A_101,B_102)) = k4_xboole_0(C_100,k7_relat_1(C_100,B_102))
      | ~ r1_tarski(k1_relat_1(C_100),A_101)
      | ~ v1_relat_1(C_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_30])).

tff(c_549,plain,(
    ! [C_105,B_106] :
      ( k7_relat_1(C_105,k4_xboole_0(k1_relat_1(C_105),B_106)) = k4_xboole_0(C_105,k7_relat_1(C_105,B_106))
      | ~ v1_relat_1(C_105) ) ),
    inference(resolution,[status(thm)],[c_6,c_445])).

tff(c_28,plain,(
    ! [B_39,A_38] :
      ( k1_relat_1(k7_relat_1(B_39,k6_subset_1(k1_relat_1(B_39),A_38))) = k6_subset_1(k1_relat_1(B_39),A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_41,plain,(
    ! [B_39,A_38] :
      ( k1_relat_1(k7_relat_1(B_39,k4_xboole_0(k1_relat_1(B_39),A_38))) = k4_xboole_0(k1_relat_1(B_39),A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_28])).

tff(c_564,plain,(
    ! [C_105,B_106] :
      ( k1_relat_1(k4_xboole_0(C_105,k7_relat_1(C_105,B_106))) = k4_xboole_0(k1_relat_1(C_105),B_106)
      | ~ v1_relat_1(C_105)
      | ~ v1_relat_1(C_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_41])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [B_44,A_43] :
      ( k3_xboole_0(k1_relat_1(B_44),A_43) = k1_relat_1(k7_relat_1(B_44,A_43))
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_123,plain,(
    ! [B_69,A_70] :
      ( k1_relat_1(k7_relat_1(B_69,A_70)) = A_70
      | ~ r1_tarski(A_70,k1_relat_1(B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_267,plain,(
    ! [B_93,B_94] :
      ( k1_relat_1(k7_relat_1(B_93,k3_xboole_0(k1_relat_1(B_93),B_94))) = k3_xboole_0(k1_relat_1(B_93),B_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_10,c_123])).

tff(c_685,plain,(
    ! [B_118,A_119] :
      ( k1_relat_1(k7_relat_1(B_118,k1_relat_1(k7_relat_1(B_118,A_119)))) = k3_xboole_0(k1_relat_1(B_118),A_119)
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_267])).

tff(c_101,plain,(
    ! [B_65,A_66] :
      ( k3_xboole_0(k1_relat_1(B_65),A_66) = k1_relat_1(k7_relat_1(B_65,A_66))
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_110,plain,(
    ! [B_65,A_66] :
      ( k5_xboole_0(k1_relat_1(B_65),k1_relat_1(k7_relat_1(B_65,A_66))) = k4_xboole_0(k1_relat_1(B_65),A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_8])).

tff(c_732,plain,(
    ! [B_118,A_119] :
      ( k5_xboole_0(k1_relat_1(B_118),k3_xboole_0(k1_relat_1(B_118),A_119)) = k4_xboole_0(k1_relat_1(B_118),k1_relat_1(k7_relat_1(B_118,A_119)))
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_110])).

tff(c_1168,plain,(
    ! [B_131,A_132] :
      ( k4_xboole_0(k1_relat_1(B_131),k1_relat_1(k7_relat_1(B_131,A_132))) = k4_xboole_0(k1_relat_1(B_131),A_132)
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_732])).

tff(c_36,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_39,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_36])).

tff(c_1189,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1168,c_39])).

tff(c_1237,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_38,c_1189])).

tff(c_1245,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_1237])).

tff(c_1249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.56  
% 3.53/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.57  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.53/1.57  
% 3.53/1.57  %Foreground sorts:
% 3.53/1.57  
% 3.53/1.57  
% 3.53/1.57  %Background operators:
% 3.53/1.57  
% 3.53/1.57  
% 3.53/1.57  %Foreground operators:
% 3.53/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.53/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.53/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.53/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.53/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.53/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.57  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.53/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.53/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.53/1.57  
% 3.53/1.58  tff(f_76, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 3.53/1.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.53/1.58  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.53/1.58  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 3.53/1.58  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 3.53/1.58  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.53/1.58  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.53/1.58  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.53/1.58  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 3.53/1.58  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.53/1.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.58  tff(c_24, plain, (![A_34, B_35]: (k6_subset_1(A_34, B_35)=k4_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.53/1.58  tff(c_30, plain, (![C_42, A_40, B_41]: (k7_relat_1(C_42, k6_subset_1(A_40, B_41))=k6_subset_1(C_42, k7_relat_1(C_42, B_41)) | ~r1_tarski(k1_relat_1(C_42), A_40) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.53/1.58  tff(c_445, plain, (![C_100, A_101, B_102]: (k7_relat_1(C_100, k4_xboole_0(A_101, B_102))=k4_xboole_0(C_100, k7_relat_1(C_100, B_102)) | ~r1_tarski(k1_relat_1(C_100), A_101) | ~v1_relat_1(C_100))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_30])).
% 3.53/1.58  tff(c_549, plain, (![C_105, B_106]: (k7_relat_1(C_105, k4_xboole_0(k1_relat_1(C_105), B_106))=k4_xboole_0(C_105, k7_relat_1(C_105, B_106)) | ~v1_relat_1(C_105))), inference(resolution, [status(thm)], [c_6, c_445])).
% 3.53/1.58  tff(c_28, plain, (![B_39, A_38]: (k1_relat_1(k7_relat_1(B_39, k6_subset_1(k1_relat_1(B_39), A_38)))=k6_subset_1(k1_relat_1(B_39), A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.53/1.58  tff(c_41, plain, (![B_39, A_38]: (k1_relat_1(k7_relat_1(B_39, k4_xboole_0(k1_relat_1(B_39), A_38)))=k4_xboole_0(k1_relat_1(B_39), A_38) | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_28])).
% 3.53/1.58  tff(c_564, plain, (![C_105, B_106]: (k1_relat_1(k4_xboole_0(C_105, k7_relat_1(C_105, B_106)))=k4_xboole_0(k1_relat_1(C_105), B_106) | ~v1_relat_1(C_105) | ~v1_relat_1(C_105))), inference(superposition, [status(thm), theory('equality')], [c_549, c_41])).
% 3.53/1.58  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.53/1.58  tff(c_32, plain, (![B_44, A_43]: (k3_xboole_0(k1_relat_1(B_44), A_43)=k1_relat_1(k7_relat_1(B_44, A_43)) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.53/1.58  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.53/1.58  tff(c_123, plain, (![B_69, A_70]: (k1_relat_1(k7_relat_1(B_69, A_70))=A_70 | ~r1_tarski(A_70, k1_relat_1(B_69)) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.53/1.58  tff(c_267, plain, (![B_93, B_94]: (k1_relat_1(k7_relat_1(B_93, k3_xboole_0(k1_relat_1(B_93), B_94)))=k3_xboole_0(k1_relat_1(B_93), B_94) | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_10, c_123])).
% 3.53/1.58  tff(c_685, plain, (![B_118, A_119]: (k1_relat_1(k7_relat_1(B_118, k1_relat_1(k7_relat_1(B_118, A_119))))=k3_xboole_0(k1_relat_1(B_118), A_119) | ~v1_relat_1(B_118) | ~v1_relat_1(B_118))), inference(superposition, [status(thm), theory('equality')], [c_32, c_267])).
% 3.53/1.58  tff(c_101, plain, (![B_65, A_66]: (k3_xboole_0(k1_relat_1(B_65), A_66)=k1_relat_1(k7_relat_1(B_65, A_66)) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.53/1.58  tff(c_110, plain, (![B_65, A_66]: (k5_xboole_0(k1_relat_1(B_65), k1_relat_1(k7_relat_1(B_65, A_66)))=k4_xboole_0(k1_relat_1(B_65), A_66) | ~v1_relat_1(B_65))), inference(superposition, [status(thm), theory('equality')], [c_101, c_8])).
% 3.53/1.58  tff(c_732, plain, (![B_118, A_119]: (k5_xboole_0(k1_relat_1(B_118), k3_xboole_0(k1_relat_1(B_118), A_119))=k4_xboole_0(k1_relat_1(B_118), k1_relat_1(k7_relat_1(B_118, A_119))) | ~v1_relat_1(B_118) | ~v1_relat_1(B_118) | ~v1_relat_1(B_118))), inference(superposition, [status(thm), theory('equality')], [c_685, c_110])).
% 3.53/1.58  tff(c_1168, plain, (![B_131, A_132]: (k4_xboole_0(k1_relat_1(B_131), k1_relat_1(k7_relat_1(B_131, A_132)))=k4_xboole_0(k1_relat_1(B_131), A_132) | ~v1_relat_1(B_131) | ~v1_relat_1(B_131) | ~v1_relat_1(B_131))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_732])).
% 3.53/1.58  tff(c_36, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.53/1.58  tff(c_39, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_36])).
% 3.53/1.58  tff(c_1189, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1168, c_39])).
% 3.53/1.58  tff(c_1237, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_38, c_1189])).
% 3.53/1.58  tff(c_1245, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_564, c_1237])).
% 3.53/1.58  tff(c_1249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1245])).
% 3.53/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.58  
% 3.53/1.58  Inference rules
% 3.53/1.58  ----------------------
% 3.53/1.58  #Ref     : 0
% 3.53/1.58  #Sup     : 357
% 3.53/1.58  #Fact    : 0
% 3.53/1.58  #Define  : 0
% 3.53/1.58  #Split   : 0
% 3.53/1.58  #Chain   : 0
% 3.53/1.58  #Close   : 0
% 3.53/1.58  
% 3.53/1.58  Ordering : KBO
% 3.53/1.58  
% 3.53/1.58  Simplification rules
% 3.53/1.58  ----------------------
% 3.53/1.58  #Subsume      : 19
% 3.53/1.58  #Demod        : 21
% 3.53/1.58  #Tautology    : 64
% 3.53/1.58  #SimpNegUnit  : 0
% 3.53/1.58  #BackRed      : 0
% 3.53/1.58  
% 3.53/1.58  #Partial instantiations: 0
% 3.53/1.58  #Strategies tried      : 1
% 3.53/1.58  
% 3.53/1.58  Timing (in seconds)
% 3.53/1.58  ----------------------
% 3.53/1.58  Preprocessing        : 0.34
% 3.53/1.58  Parsing              : 0.18
% 3.53/1.58  CNF conversion       : 0.02
% 3.53/1.58  Main loop            : 0.47
% 3.53/1.58  Inferencing          : 0.18
% 3.53/1.58  Reduction            : 0.13
% 3.53/1.58  Demodulation         : 0.10
% 3.53/1.58  BG Simplification    : 0.04
% 3.53/1.58  Subsumption          : 0.09
% 3.53/1.58  Abstraction          : 0.04
% 3.53/1.58  MUC search           : 0.00
% 3.53/1.58  Cooper               : 0.00
% 3.53/1.58  Total                : 0.83
% 3.53/1.58  Index Insertion      : 0.00
% 3.53/1.58  Index Deletion       : 0.00
% 3.53/1.58  Index Matching       : 0.00
% 3.53/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
