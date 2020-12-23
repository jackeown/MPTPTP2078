%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:34 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   55 (  73 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 (  94 expanded)
%              Number of equality atoms :   26 (  41 expanded)
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

tff(f_74,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_36,B_37] : k6_subset_1(A_36,B_37) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [C_42,A_40,B_41] :
      ( k7_relat_1(C_42,k6_subset_1(A_40,B_41)) = k6_subset_1(C_42,k7_relat_1(C_42,B_41))
      | ~ r1_tarski(k1_relat_1(C_42),A_40)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_396,plain,(
    ! [C_100,A_101,B_102] :
      ( k7_relat_1(C_100,k4_xboole_0(A_101,B_102)) = k4_xboole_0(C_100,k7_relat_1(C_100,B_102))
      | ~ r1_tarski(k1_relat_1(C_100),A_101)
      | ~ v1_relat_1(C_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_30])).

tff(c_412,plain,(
    ! [C_103,B_104] :
      ( k7_relat_1(C_103,k4_xboole_0(k1_relat_1(C_103),B_104)) = k4_xboole_0(C_103,k7_relat_1(C_103,B_104))
      | ~ v1_relat_1(C_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_396])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [B_77,A_78] :
      ( k1_relat_1(k7_relat_1(B_77,A_78)) = A_78
      | ~ r1_tarski(A_78,k1_relat_1(B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_154,plain,(
    ! [B_77,B_8] :
      ( k1_relat_1(k7_relat_1(B_77,k4_xboole_0(k1_relat_1(B_77),B_8))) = k4_xboole_0(k1_relat_1(B_77),B_8)
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_12,c_136])).

tff(c_424,plain,(
    ! [C_103,B_104] :
      ( k1_relat_1(k4_xboole_0(C_103,k7_relat_1(C_103,B_104))) = k4_xboole_0(k1_relat_1(C_103),B_104)
      | ~ v1_relat_1(C_103)
      | ~ v1_relat_1(C_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_154])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [B_44,A_43] :
      ( k3_xboole_0(k1_relat_1(B_44),A_43) = k1_relat_1(k7_relat_1(B_44,A_43))
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_257,plain,(
    ! [B_95,B_96] :
      ( k1_relat_1(k7_relat_1(B_95,k3_xboole_0(k1_relat_1(B_95),B_96))) = k3_xboole_0(k1_relat_1(B_95),B_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_10,c_136])).

tff(c_664,plain,(
    ! [B_120,A_121] :
      ( k1_relat_1(k7_relat_1(B_120,k1_relat_1(k7_relat_1(B_120,A_121)))) = k3_xboole_0(k1_relat_1(B_120),A_121)
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_257])).

tff(c_105,plain,(
    ! [B_69,A_70] :
      ( k3_xboole_0(k1_relat_1(B_69),A_70) = k1_relat_1(k7_relat_1(B_69,A_70))
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_114,plain,(
    ! [B_69,A_70] :
      ( k5_xboole_0(k1_relat_1(B_69),k1_relat_1(k7_relat_1(B_69,A_70))) = k4_xboole_0(k1_relat_1(B_69),A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_8])).

tff(c_711,plain,(
    ! [B_120,A_121] :
      ( k5_xboole_0(k1_relat_1(B_120),k3_xboole_0(k1_relat_1(B_120),A_121)) = k4_xboole_0(k1_relat_1(B_120),k1_relat_1(k7_relat_1(B_120,A_121)))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_114])).

tff(c_933,plain,(
    ! [B_128,A_129] :
      ( k4_xboole_0(k1_relat_1(B_128),k1_relat_1(k7_relat_1(B_128,A_129))) = k4_xboole_0(k1_relat_1(B_128),A_129)
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_711])).

tff(c_36,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_39,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_36])).

tff(c_948,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_933,c_39])).

tff(c_993,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_38,c_948])).

tff(c_1002,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_993])).

tff(c_1006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1002])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.50  
% 2.96/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.50  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.96/1.50  
% 2.96/1.50  %Foreground sorts:
% 2.96/1.50  
% 2.96/1.50  
% 2.96/1.50  %Background operators:
% 2.96/1.50  
% 2.96/1.50  
% 2.96/1.50  %Foreground operators:
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.96/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.96/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.96/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.96/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.96/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.96/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.96/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.50  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.96/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.96/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.96/1.50  
% 2.96/1.51  tff(f_74, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 2.96/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.96/1.51  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.96/1.51  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 2.96/1.51  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.96/1.51  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.96/1.51  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.96/1.51  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.96/1.51  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.96/1.51  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.96/1.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.51  tff(c_26, plain, (![A_36, B_37]: (k6_subset_1(A_36, B_37)=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.96/1.51  tff(c_30, plain, (![C_42, A_40, B_41]: (k7_relat_1(C_42, k6_subset_1(A_40, B_41))=k6_subset_1(C_42, k7_relat_1(C_42, B_41)) | ~r1_tarski(k1_relat_1(C_42), A_40) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.96/1.51  tff(c_396, plain, (![C_100, A_101, B_102]: (k7_relat_1(C_100, k4_xboole_0(A_101, B_102))=k4_xboole_0(C_100, k7_relat_1(C_100, B_102)) | ~r1_tarski(k1_relat_1(C_100), A_101) | ~v1_relat_1(C_100))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_30])).
% 2.96/1.51  tff(c_412, plain, (![C_103, B_104]: (k7_relat_1(C_103, k4_xboole_0(k1_relat_1(C_103), B_104))=k4_xboole_0(C_103, k7_relat_1(C_103, B_104)) | ~v1_relat_1(C_103))), inference(resolution, [status(thm)], [c_6, c_396])).
% 2.96/1.51  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.51  tff(c_136, plain, (![B_77, A_78]: (k1_relat_1(k7_relat_1(B_77, A_78))=A_78 | ~r1_tarski(A_78, k1_relat_1(B_77)) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.96/1.51  tff(c_154, plain, (![B_77, B_8]: (k1_relat_1(k7_relat_1(B_77, k4_xboole_0(k1_relat_1(B_77), B_8)))=k4_xboole_0(k1_relat_1(B_77), B_8) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_12, c_136])).
% 2.96/1.51  tff(c_424, plain, (![C_103, B_104]: (k1_relat_1(k4_xboole_0(C_103, k7_relat_1(C_103, B_104)))=k4_xboole_0(k1_relat_1(C_103), B_104) | ~v1_relat_1(C_103) | ~v1_relat_1(C_103))), inference(superposition, [status(thm), theory('equality')], [c_412, c_154])).
% 2.96/1.51  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.51  tff(c_32, plain, (![B_44, A_43]: (k3_xboole_0(k1_relat_1(B_44), A_43)=k1_relat_1(k7_relat_1(B_44, A_43)) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.96/1.51  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.51  tff(c_257, plain, (![B_95, B_96]: (k1_relat_1(k7_relat_1(B_95, k3_xboole_0(k1_relat_1(B_95), B_96)))=k3_xboole_0(k1_relat_1(B_95), B_96) | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_10, c_136])).
% 2.96/1.51  tff(c_664, plain, (![B_120, A_121]: (k1_relat_1(k7_relat_1(B_120, k1_relat_1(k7_relat_1(B_120, A_121))))=k3_xboole_0(k1_relat_1(B_120), A_121) | ~v1_relat_1(B_120) | ~v1_relat_1(B_120))), inference(superposition, [status(thm), theory('equality')], [c_32, c_257])).
% 2.96/1.51  tff(c_105, plain, (![B_69, A_70]: (k3_xboole_0(k1_relat_1(B_69), A_70)=k1_relat_1(k7_relat_1(B_69, A_70)) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.96/1.51  tff(c_114, plain, (![B_69, A_70]: (k5_xboole_0(k1_relat_1(B_69), k1_relat_1(k7_relat_1(B_69, A_70)))=k4_xboole_0(k1_relat_1(B_69), A_70) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_105, c_8])).
% 2.96/1.51  tff(c_711, plain, (![B_120, A_121]: (k5_xboole_0(k1_relat_1(B_120), k3_xboole_0(k1_relat_1(B_120), A_121))=k4_xboole_0(k1_relat_1(B_120), k1_relat_1(k7_relat_1(B_120, A_121))) | ~v1_relat_1(B_120) | ~v1_relat_1(B_120) | ~v1_relat_1(B_120))), inference(superposition, [status(thm), theory('equality')], [c_664, c_114])).
% 2.96/1.51  tff(c_933, plain, (![B_128, A_129]: (k4_xboole_0(k1_relat_1(B_128), k1_relat_1(k7_relat_1(B_128, A_129)))=k4_xboole_0(k1_relat_1(B_128), A_129) | ~v1_relat_1(B_128) | ~v1_relat_1(B_128) | ~v1_relat_1(B_128))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_711])).
% 2.96/1.51  tff(c_36, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.96/1.51  tff(c_39, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_36])).
% 2.96/1.51  tff(c_948, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_933, c_39])).
% 2.96/1.51  tff(c_993, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_38, c_948])).
% 2.96/1.51  tff(c_1002, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_424, c_993])).
% 2.96/1.51  tff(c_1006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1002])).
% 2.96/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.51  
% 2.96/1.51  Inference rules
% 2.96/1.51  ----------------------
% 2.96/1.51  #Ref     : 0
% 2.96/1.51  #Sup     : 279
% 2.96/1.51  #Fact    : 0
% 2.96/1.51  #Define  : 0
% 2.96/1.51  #Split   : 0
% 2.96/1.51  #Chain   : 0
% 2.96/1.51  #Close   : 0
% 2.96/1.51  
% 2.96/1.51  Ordering : KBO
% 2.96/1.51  
% 2.96/1.51  Simplification rules
% 2.96/1.51  ----------------------
% 2.96/1.51  #Subsume      : 15
% 2.96/1.51  #Demod        : 23
% 2.96/1.51  #Tautology    : 66
% 2.96/1.51  #SimpNegUnit  : 0
% 2.96/1.51  #BackRed      : 0
% 2.96/1.51  
% 2.96/1.51  #Partial instantiations: 0
% 2.96/1.51  #Strategies tried      : 1
% 2.96/1.51  
% 2.96/1.51  Timing (in seconds)
% 2.96/1.51  ----------------------
% 2.96/1.52  Preprocessing        : 0.33
% 2.96/1.52  Parsing              : 0.18
% 2.96/1.52  CNF conversion       : 0.02
% 2.96/1.52  Main loop            : 0.38
% 2.96/1.52  Inferencing          : 0.15
% 2.96/1.52  Reduction            : 0.11
% 2.96/1.52  Demodulation         : 0.08
% 2.96/1.52  BG Simplification    : 0.03
% 2.96/1.52  Subsumption          : 0.07
% 2.96/1.52  Abstraction          : 0.03
% 2.96/1.52  MUC search           : 0.00
% 2.96/1.52  Cooper               : 0.00
% 2.96/1.52  Total                : 0.73
% 2.96/1.52  Index Insertion      : 0.00
% 2.96/1.52  Index Deletion       : 0.00
% 2.96/1.52  Index Matching       : 0.00
% 2.96/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
