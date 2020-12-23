%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:32 EST 2020

% Result     : Theorem 8.85s
% Output     : CNFRefutation 8.85s
% Verified   : 
% Statistics : Number of formulae       :   57 (  71 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 (  73 expanded)
%              Number of equality atoms :   30 (  43 expanded)
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

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_38,B_39] : k6_subset_1(A_38,B_39) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [C_46,A_44,B_45] :
      ( k7_relat_1(C_46,k6_subset_1(A_44,B_45)) = k6_subset_1(C_46,k7_relat_1(C_46,B_45))
      | ~ r1_tarski(k1_relat_1(C_46),A_44)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1141,plain,(
    ! [C_114,A_115,B_116] :
      ( k7_relat_1(C_114,k4_xboole_0(A_115,B_116)) = k4_xboole_0(C_114,k7_relat_1(C_114,B_116))
      | ~ r1_tarski(k1_relat_1(C_114),A_115)
      | ~ v1_relat_1(C_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_34])).

tff(c_2578,plain,(
    ! [C_149,B_150] :
      ( k7_relat_1(C_149,k4_xboole_0(k1_relat_1(C_149),B_150)) = k4_xboole_0(C_149,k7_relat_1(C_149,B_150))
      | ~ v1_relat_1(C_149) ) ),
    inference(resolution,[status(thm)],[c_8,c_1141])).

tff(c_32,plain,(
    ! [B_43,A_42] :
      ( k1_relat_1(k7_relat_1(B_43,k6_subset_1(k1_relat_1(B_43),A_42))) = k6_subset_1(k1_relat_1(B_43),A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_43,plain,(
    ! [B_43,A_42] :
      ( k1_relat_1(k7_relat_1(B_43,k4_xboole_0(k1_relat_1(B_43),A_42))) = k4_xboole_0(k1_relat_1(B_43),A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_32])).

tff(c_2590,plain,(
    ! [C_149,B_150] :
      ( k1_relat_1(k4_xboole_0(C_149,k7_relat_1(C_149,B_150))) = k4_xboole_0(k1_relat_1(C_149),B_150)
      | ~ v1_relat_1(C_149)
      | ~ v1_relat_1(C_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2578,c_43])).

tff(c_36,plain,(
    ! [B_48,A_47] :
      ( k3_xboole_0(k1_relat_1(B_48),A_47) = k1_relat_1(k7_relat_1(B_48,A_47))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_102,plain,(
    ! [A_7,B_8] : k3_xboole_0(k3_xboole_0(A_7,B_8),A_7) = k3_xboole_0(A_7,B_8) ),
    inference(resolution,[status(thm)],[c_12,c_95])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_153,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_254,plain,(
    ! [B_75,A_76] : k5_xboole_0(B_75,k3_xboole_0(A_76,B_75)) = k4_xboole_0(B_75,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_153])).

tff(c_267,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_254])).

tff(c_496,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_267])).

tff(c_9513,plain,(
    ! [B_241,A_242] :
      ( k4_xboole_0(k1_relat_1(B_241),k1_relat_1(k7_relat_1(B_241,A_242))) = k4_xboole_0(k1_relat_1(B_241),A_242)
      | ~ v1_relat_1(B_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_496])).

tff(c_38,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_41,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_38])).

tff(c_9553,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9513,c_41])).

tff(c_9615,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_9553])).

tff(c_9623,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2590,c_9615])).

tff(c_9627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_9623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:17:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.85/3.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.85/3.22  
% 8.85/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.85/3.22  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.85/3.22  
% 8.85/3.22  %Foreground sorts:
% 8.85/3.22  
% 8.85/3.22  
% 8.85/3.22  %Background operators:
% 8.85/3.22  
% 8.85/3.22  
% 8.85/3.22  %Foreground operators:
% 8.85/3.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.85/3.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.85/3.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.85/3.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.85/3.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.85/3.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.85/3.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.85/3.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.85/3.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.85/3.22  tff('#skF_2', type, '#skF_2': $i).
% 8.85/3.22  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 8.85/3.22  tff('#skF_1', type, '#skF_1': $i).
% 8.85/3.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.85/3.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.85/3.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.85/3.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.85/3.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.85/3.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.85/3.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.85/3.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.85/3.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.85/3.22  
% 8.85/3.23  tff(f_76, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 8.85/3.23  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.85/3.23  tff(f_55, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 8.85/3.23  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 8.85/3.23  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 8.85/3.23  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 8.85/3.23  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.85/3.23  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.85/3.23  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.85/3.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.85/3.23  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.85/3.23  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.85/3.23  tff(c_28, plain, (![A_38, B_39]: (k6_subset_1(A_38, B_39)=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.85/3.23  tff(c_34, plain, (![C_46, A_44, B_45]: (k7_relat_1(C_46, k6_subset_1(A_44, B_45))=k6_subset_1(C_46, k7_relat_1(C_46, B_45)) | ~r1_tarski(k1_relat_1(C_46), A_44) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.85/3.23  tff(c_1141, plain, (![C_114, A_115, B_116]: (k7_relat_1(C_114, k4_xboole_0(A_115, B_116))=k4_xboole_0(C_114, k7_relat_1(C_114, B_116)) | ~r1_tarski(k1_relat_1(C_114), A_115) | ~v1_relat_1(C_114))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_34])).
% 8.85/3.23  tff(c_2578, plain, (![C_149, B_150]: (k7_relat_1(C_149, k4_xboole_0(k1_relat_1(C_149), B_150))=k4_xboole_0(C_149, k7_relat_1(C_149, B_150)) | ~v1_relat_1(C_149))), inference(resolution, [status(thm)], [c_8, c_1141])).
% 8.85/3.23  tff(c_32, plain, (![B_43, A_42]: (k1_relat_1(k7_relat_1(B_43, k6_subset_1(k1_relat_1(B_43), A_42)))=k6_subset_1(k1_relat_1(B_43), A_42) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.85/3.23  tff(c_43, plain, (![B_43, A_42]: (k1_relat_1(k7_relat_1(B_43, k4_xboole_0(k1_relat_1(B_43), A_42)))=k4_xboole_0(k1_relat_1(B_43), A_42) | ~v1_relat_1(B_43))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_32])).
% 8.85/3.23  tff(c_2590, plain, (![C_149, B_150]: (k1_relat_1(k4_xboole_0(C_149, k7_relat_1(C_149, B_150)))=k4_xboole_0(k1_relat_1(C_149), B_150) | ~v1_relat_1(C_149) | ~v1_relat_1(C_149))), inference(superposition, [status(thm), theory('equality')], [c_2578, c_43])).
% 8.85/3.23  tff(c_36, plain, (![B_48, A_47]: (k3_xboole_0(k1_relat_1(B_48), A_47)=k1_relat_1(k7_relat_1(B_48, A_47)) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.85/3.23  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.85/3.23  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.85/3.23  tff(c_95, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.85/3.23  tff(c_102, plain, (![A_7, B_8]: (k3_xboole_0(k3_xboole_0(A_7, B_8), A_7)=k3_xboole_0(A_7, B_8))), inference(resolution, [status(thm)], [c_12, c_95])).
% 8.85/3.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.85/3.23  tff(c_153, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.85/3.23  tff(c_254, plain, (![B_75, A_76]: (k5_xboole_0(B_75, k3_xboole_0(A_76, B_75))=k4_xboole_0(B_75, A_76))), inference(superposition, [status(thm), theory('equality')], [c_2, c_153])).
% 8.85/3.23  tff(c_267, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, k3_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_254])).
% 8.85/3.23  tff(c_496, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_267])).
% 8.85/3.23  tff(c_9513, plain, (![B_241, A_242]: (k4_xboole_0(k1_relat_1(B_241), k1_relat_1(k7_relat_1(B_241, A_242)))=k4_xboole_0(k1_relat_1(B_241), A_242) | ~v1_relat_1(B_241))), inference(superposition, [status(thm), theory('equality')], [c_36, c_496])).
% 8.85/3.23  tff(c_38, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.85/3.23  tff(c_41, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_38])).
% 8.85/3.23  tff(c_9553, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9513, c_41])).
% 8.85/3.23  tff(c_9615, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_9553])).
% 8.85/3.23  tff(c_9623, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2590, c_9615])).
% 8.85/3.23  tff(c_9627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_9623])).
% 8.85/3.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.85/3.23  
% 8.85/3.23  Inference rules
% 8.85/3.23  ----------------------
% 8.85/3.23  #Ref     : 0
% 8.85/3.23  #Sup     : 2507
% 8.85/3.23  #Fact    : 0
% 8.85/3.23  #Define  : 0
% 8.85/3.23  #Split   : 0
% 8.85/3.23  #Chain   : 0
% 8.85/3.23  #Close   : 0
% 8.85/3.23  
% 8.85/3.23  Ordering : KBO
% 8.85/3.23  
% 8.85/3.23  Simplification rules
% 8.85/3.23  ----------------------
% 8.85/3.23  #Subsume      : 518
% 8.85/3.23  #Demod        : 3266
% 8.85/3.23  #Tautology    : 978
% 8.85/3.23  #SimpNegUnit  : 0
% 8.85/3.23  #BackRed      : 0
% 8.85/3.23  
% 8.85/3.23  #Partial instantiations: 0
% 8.85/3.23  #Strategies tried      : 1
% 8.85/3.23  
% 8.85/3.23  Timing (in seconds)
% 8.85/3.23  ----------------------
% 8.85/3.23  Preprocessing        : 0.32
% 8.85/3.23  Parsing              : 0.17
% 8.85/3.23  CNF conversion       : 0.02
% 8.85/3.23  Main loop            : 2.13
% 8.85/3.23  Inferencing          : 0.51
% 8.85/3.23  Reduction            : 1.13
% 8.85/3.23  Demodulation         : 0.99
% 8.85/3.24  BG Simplification    : 0.08
% 8.85/3.24  Subsumption          : 0.32
% 8.85/3.24  Abstraction          : 0.13
% 8.85/3.24  MUC search           : 0.00
% 8.85/3.24  Cooper               : 0.00
% 8.85/3.24  Total                : 2.49
% 8.85/3.24  Index Insertion      : 0.00
% 8.85/3.24  Index Deletion       : 0.00
% 8.85/3.24  Index Matching       : 0.00
% 8.85/3.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
