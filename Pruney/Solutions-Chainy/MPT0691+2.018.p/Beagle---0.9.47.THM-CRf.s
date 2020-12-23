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
% DateTime   : Thu Dec  3 10:04:41 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 135 expanded)
%              Number of leaves         :   30 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :   75 ( 182 expanded)
%              Number of equality atoms :   35 (  90 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_96,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | k4_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_103,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_96,c_26])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_256,plain,(
    ! [B_48,A_49] :
      ( k3_xboole_0(k1_relat_1(B_48),A_49) = k1_relat_1(k7_relat_1(B_48,A_49))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    ! [B_35,A_36] : k1_setfam_1(k2_tarski(B_35,A_36)) = k3_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_72])).

tff(c_14,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    ! [B_35,A_36] : k3_xboole_0(B_35,A_36) = k3_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_14])).

tff(c_325,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,k1_relat_1(B_54)) = k1_relat_1(k7_relat_1(B_54,A_53))
      | ~ v1_relat_1(B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_124])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_105,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_105])).

tff(c_347,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_113])).

tff(c_368,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_347])).

tff(c_268,plain,(
    ! [A_49,B_48] :
      ( k3_xboole_0(A_49,k1_relat_1(B_48)) = k1_relat_1(k7_relat_1(B_48,A_49))
      | ~ v1_relat_1(B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_124])).

tff(c_375,plain,(
    ! [A_49] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_49)) = k3_xboole_0(A_49,'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_268])).

tff(c_383,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_386,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_383])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_386])).

tff(c_392,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_203,plain,(
    ! [B_42,A_43] :
      ( k2_relat_1(k7_relat_1(B_42,A_43)) = k9_relat_1(B_42,A_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_16] :
      ( k10_relat_1(A_16,k2_relat_1(A_16)) = k1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_839,plain,(
    ! [B_79,A_80] :
      ( k10_relat_1(k7_relat_1(B_79,A_80),k9_relat_1(B_79,A_80)) = k1_relat_1(k7_relat_1(B_79,A_80))
      | ~ v1_relat_1(k7_relat_1(B_79,A_80))
      | ~ v1_relat_1(B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_20])).

tff(c_285,plain,(
    ! [A_50,C_51,B_52] :
      ( k3_xboole_0(A_50,k10_relat_1(C_51,B_52)) = k10_relat_1(k7_relat_1(C_51,A_50),B_52)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_298,plain,(
    ! [A_50,C_51,B_52] :
      ( k5_xboole_0(A_50,k10_relat_1(k7_relat_1(C_51,A_50),B_52)) = k4_xboole_0(A_50,k10_relat_1(C_51,B_52))
      | ~ v1_relat_1(C_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_6])).

tff(c_2088,plain,(
    ! [A_116,B_117] :
      ( k5_xboole_0(A_116,k1_relat_1(k7_relat_1(B_117,A_116))) = k4_xboole_0(A_116,k10_relat_1(B_117,k9_relat_1(B_117,A_116)))
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1(k7_relat_1(B_117,A_116))
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_298])).

tff(c_2149,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_2088])).

tff(c_2155,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_392,c_30,c_10,c_2149])).

tff(c_2157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_2155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.68  
% 3.72/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.68  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.72/1.68  
% 3.72/1.68  %Foreground sorts:
% 3.72/1.68  
% 3.72/1.68  
% 3.72/1.68  %Background operators:
% 3.72/1.68  
% 3.72/1.68  
% 3.72/1.68  %Foreground operators:
% 3.72/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.72/1.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.72/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.72/1.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.72/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.72/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.72/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.72/1.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.72/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.72/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.68  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.72/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.72/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.72/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.72/1.68  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.72/1.68  
% 3.72/1.69  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.72/1.69  tff(f_68, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 3.72/1.69  tff(f_45, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.72/1.69  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.72/1.69  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.72/1.69  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.72/1.69  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.72/1.69  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.72/1.69  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.72/1.69  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.72/1.69  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.72/1.69  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.72/1.69  tff(c_96, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | k4_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.72/1.69  tff(c_26, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.72/1.69  tff(c_103, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_96, c_26])).
% 3.72/1.69  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.72/1.69  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.72/1.69  tff(c_256, plain, (![B_48, A_49]: (k3_xboole_0(k1_relat_1(B_48), A_49)=k1_relat_1(k7_relat_1(B_48, A_49)) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.72/1.69  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.72/1.69  tff(c_72, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.72/1.69  tff(c_118, plain, (![B_35, A_36]: (k1_setfam_1(k2_tarski(B_35, A_36))=k3_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_12, c_72])).
% 3.72/1.69  tff(c_14, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.72/1.69  tff(c_124, plain, (![B_35, A_36]: (k3_xboole_0(B_35, A_36)=k3_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_118, c_14])).
% 3.72/1.69  tff(c_325, plain, (![A_53, B_54]: (k3_xboole_0(A_53, k1_relat_1(B_54))=k1_relat_1(k7_relat_1(B_54, A_53)) | ~v1_relat_1(B_54))), inference(superposition, [status(thm), theory('equality')], [c_256, c_124])).
% 3.72/1.69  tff(c_28, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.72/1.69  tff(c_105, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=A_33 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.72/1.69  tff(c_113, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_105])).
% 3.72/1.69  tff(c_347, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_325, c_113])).
% 3.72/1.69  tff(c_368, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_347])).
% 3.72/1.69  tff(c_268, plain, (![A_49, B_48]: (k3_xboole_0(A_49, k1_relat_1(B_48))=k1_relat_1(k7_relat_1(B_48, A_49)) | ~v1_relat_1(B_48))), inference(superposition, [status(thm), theory('equality')], [c_256, c_124])).
% 3.72/1.69  tff(c_375, plain, (![A_49]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_49))=k3_xboole_0(A_49, '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_368, c_268])).
% 3.72/1.69  tff(c_383, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_375])).
% 3.72/1.69  tff(c_386, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_383])).
% 3.72/1.69  tff(c_390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_386])).
% 3.72/1.69  tff(c_392, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_375])).
% 3.72/1.69  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.72/1.69  tff(c_203, plain, (![B_42, A_43]: (k2_relat_1(k7_relat_1(B_42, A_43))=k9_relat_1(B_42, A_43) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.72/1.69  tff(c_20, plain, (![A_16]: (k10_relat_1(A_16, k2_relat_1(A_16))=k1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.72/1.69  tff(c_839, plain, (![B_79, A_80]: (k10_relat_1(k7_relat_1(B_79, A_80), k9_relat_1(B_79, A_80))=k1_relat_1(k7_relat_1(B_79, A_80)) | ~v1_relat_1(k7_relat_1(B_79, A_80)) | ~v1_relat_1(B_79))), inference(superposition, [status(thm), theory('equality')], [c_203, c_20])).
% 3.72/1.69  tff(c_285, plain, (![A_50, C_51, B_52]: (k3_xboole_0(A_50, k10_relat_1(C_51, B_52))=k10_relat_1(k7_relat_1(C_51, A_50), B_52) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.72/1.69  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.72/1.69  tff(c_298, plain, (![A_50, C_51, B_52]: (k5_xboole_0(A_50, k10_relat_1(k7_relat_1(C_51, A_50), B_52))=k4_xboole_0(A_50, k10_relat_1(C_51, B_52)) | ~v1_relat_1(C_51))), inference(superposition, [status(thm), theory('equality')], [c_285, c_6])).
% 3.72/1.69  tff(c_2088, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k1_relat_1(k7_relat_1(B_117, A_116)))=k4_xboole_0(A_116, k10_relat_1(B_117, k9_relat_1(B_117, A_116))) | ~v1_relat_1(B_117) | ~v1_relat_1(k7_relat_1(B_117, A_116)) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_839, c_298])).
% 3.72/1.69  tff(c_2149, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_368, c_2088])).
% 3.72/1.69  tff(c_2155, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_392, c_30, c_10, c_2149])).
% 3.72/1.69  tff(c_2157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_2155])).
% 3.72/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.69  
% 3.72/1.69  Inference rules
% 3.72/1.69  ----------------------
% 3.72/1.69  #Ref     : 0
% 3.72/1.69  #Sup     : 544
% 3.72/1.69  #Fact    : 0
% 3.72/1.69  #Define  : 0
% 3.72/1.69  #Split   : 2
% 3.72/1.69  #Chain   : 0
% 3.72/1.69  #Close   : 0
% 3.72/1.69  
% 3.72/1.69  Ordering : KBO
% 3.72/1.69  
% 3.72/1.69  Simplification rules
% 3.72/1.69  ----------------------
% 3.72/1.69  #Subsume      : 94
% 3.72/1.69  #Demod        : 197
% 3.72/1.69  #Tautology    : 193
% 3.72/1.69  #SimpNegUnit  : 1
% 3.72/1.69  #BackRed      : 1
% 3.72/1.69  
% 3.72/1.69  #Partial instantiations: 0
% 3.72/1.69  #Strategies tried      : 1
% 3.72/1.69  
% 3.72/1.69  Timing (in seconds)
% 3.72/1.69  ----------------------
% 3.72/1.69  Preprocessing        : 0.29
% 3.72/1.69  Parsing              : 0.16
% 3.72/1.69  CNF conversion       : 0.02
% 3.72/1.69  Main loop            : 0.61
% 3.72/1.69  Inferencing          : 0.24
% 3.72/1.69  Reduction            : 0.20
% 3.72/1.69  Demodulation         : 0.16
% 3.72/1.70  BG Simplification    : 0.03
% 3.72/1.70  Subsumption          : 0.10
% 3.72/1.70  Abstraction          : 0.04
% 3.72/1.70  MUC search           : 0.00
% 3.72/1.70  Cooper               : 0.00
% 3.72/1.70  Total                : 0.92
% 3.72/1.70  Index Insertion      : 0.00
% 3.72/1.70  Index Deletion       : 0.00
% 3.72/1.70  Index Matching       : 0.00
% 3.72/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
