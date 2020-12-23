%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:44 EST 2020

% Result     : Theorem 4.49s
% Output     : CNFRefutation 4.49s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 631 expanded)
%              Number of leaves         :   26 ( 220 expanded)
%              Depth                    :   21
%              Number of atoms          :   99 (1017 expanded)
%              Number of equality atoms :   40 ( 497 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_147,plain,(
    ! [B_38,A_39] :
      ( k7_relat_1(B_38,A_39) = B_38
      | ~ r1_tarski(k1_relat_1(B_38),A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_150,plain,(
    ! [A_15,A_39] :
      ( k7_relat_1(k6_relat_1(A_15),A_39) = k6_relat_1(A_15)
      | ~ r1_tarski(A_15,A_39)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_147])).

tff(c_152,plain,(
    ! [A_15,A_39] :
      ( k7_relat_1(k6_relat_1(A_15),A_39) = k6_relat_1(A_15)
      | ~ r1_tarski(A_15,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_150])).

tff(c_167,plain,(
    ! [B_42,A_43] :
      ( k3_xboole_0(k1_relat_1(B_42),A_43) = k1_relat_1(k7_relat_1(B_42,A_43))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_196,plain,(
    ! [A_15,A_43] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_15),A_43)) = k3_xboole_0(A_15,A_43)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_167])).

tff(c_201,plain,(
    ! [A_44,A_45] : k1_relat_1(k7_relat_1(k6_relat_1(A_44),A_45)) = k3_xboole_0(A_44,A_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_196])).

tff(c_219,plain,(
    ! [A_15,A_39] :
      ( k3_xboole_0(A_15,A_39) = k1_relat_1(k6_relat_1(A_15))
      | ~ r1_tarski(A_15,A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_201])).

tff(c_268,plain,(
    ! [A_49,A_50] :
      ( k3_xboole_0(A_49,A_50) = A_49
      | ~ r1_tarski(A_49,A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_219])).

tff(c_280,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_268])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_287,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_4])).

tff(c_222,plain,(
    ! [A_15,A_39] :
      ( k3_xboole_0(A_15,A_39) = A_15
      | ~ r1_tarski(A_15,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_219])).

tff(c_295,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_287,c_222])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [B_28,A_29] : k3_xboole_0(B_28,A_29) = k3_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [B_28,A_29] : r1_tarski(k3_xboole_0(B_28,A_29),A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_4])).

tff(c_351,plain,(
    ! [B_56,A_57] : k3_xboole_0(k3_xboole_0(B_56,A_57),A_57) = k3_xboole_0(B_56,A_57) ),
    inference(resolution,[status(thm)],[c_66,c_268])).

tff(c_1013,plain,(
    ! [B_74,A_75] : k3_xboole_0(k3_xboole_0(B_74,A_75),B_74) = k3_xboole_0(A_75,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_351])).

tff(c_1111,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_1013])).

tff(c_1157,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_1111])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( k3_xboole_0(k1_relat_1(B_17),A_16) = k1_relat_1(k7_relat_1(B_17,A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1195,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1157,c_20])).

tff(c_1230,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1195])).

tff(c_182,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_42,A_43)),k1_relat_1(B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_4])).

tff(c_1246,plain,(
    ! [A_43] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_43)),'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_182])).

tff(c_1287,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1246])).

tff(c_1290,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_1287])).

tff(c_1294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1290])).

tff(c_1296,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1246])).

tff(c_10,plain,(
    ! [A_8] :
      ( k9_relat_1(A_8,k1_relat_1(A_8)) = k2_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1258,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_10])).

tff(c_1768,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_1258])).

tff(c_12,plain,(
    ! [A_9,C_13,B_12] :
      ( k9_relat_1(k7_relat_1(A_9,C_13),B_12) = k9_relat_1(A_9,B_12)
      | ~ r1_tarski(B_12,C_13)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1772,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1768,c_12])).

tff(c_1779,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_287,c_1772])).

tff(c_14,plain,(
    ! [A_14] :
      ( k10_relat_1(A_14,k2_relat_1(A_14)) = k1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1787,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1779,c_14])).

tff(c_1791,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_1230,c_1787])).

tff(c_223,plain,(
    ! [A_46,C_47,B_48] :
      ( k3_xboole_0(A_46,k10_relat_1(C_47,B_48)) = k10_relat_1(k7_relat_1(C_47,A_46),B_48)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3798,plain,(
    ! [C_123,A_124,B_125] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_123,A_124),B_125),k10_relat_1(C_123,B_125))
      | ~ v1_relat_1(C_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_66])).

tff(c_3830,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1791,c_3798])).

tff(c_3856,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3830])).

tff(c_3858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_3856])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:45:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.49/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.90  
% 4.49/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.90  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.49/1.90  
% 4.49/1.90  %Foreground sorts:
% 4.49/1.90  
% 4.49/1.90  
% 4.49/1.90  %Background operators:
% 4.49/1.90  
% 4.49/1.90  
% 4.49/1.90  %Foreground operators:
% 4.49/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.49/1.90  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.49/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.49/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.49/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.49/1.90  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.49/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.49/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.49/1.90  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.49/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.49/1.90  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.49/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.49/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.49/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.49/1.90  
% 4.49/1.92  tff(f_75, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 4.49/1.92  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.49/1.92  tff(f_54, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.49/1.92  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 4.49/1.92  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 4.49/1.92  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 4.49/1.92  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.49/1.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.49/1.92  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 4.49/1.92  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 4.49/1.92  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.49/1.92  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 4.49/1.92  tff(c_26, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.49/1.92  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.49/1.92  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.49/1.92  tff(c_28, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.49/1.92  tff(c_16, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.49/1.92  tff(c_6, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.49/1.92  tff(c_147, plain, (![B_38, A_39]: (k7_relat_1(B_38, A_39)=B_38 | ~r1_tarski(k1_relat_1(B_38), A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.49/1.92  tff(c_150, plain, (![A_15, A_39]: (k7_relat_1(k6_relat_1(A_15), A_39)=k6_relat_1(A_15) | ~r1_tarski(A_15, A_39) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_147])).
% 4.49/1.92  tff(c_152, plain, (![A_15, A_39]: (k7_relat_1(k6_relat_1(A_15), A_39)=k6_relat_1(A_15) | ~r1_tarski(A_15, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_150])).
% 4.49/1.92  tff(c_167, plain, (![B_42, A_43]: (k3_xboole_0(k1_relat_1(B_42), A_43)=k1_relat_1(k7_relat_1(B_42, A_43)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.49/1.92  tff(c_196, plain, (![A_15, A_43]: (k1_relat_1(k7_relat_1(k6_relat_1(A_15), A_43))=k3_xboole_0(A_15, A_43) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_167])).
% 4.49/1.92  tff(c_201, plain, (![A_44, A_45]: (k1_relat_1(k7_relat_1(k6_relat_1(A_44), A_45))=k3_xboole_0(A_44, A_45))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_196])).
% 4.49/1.92  tff(c_219, plain, (![A_15, A_39]: (k3_xboole_0(A_15, A_39)=k1_relat_1(k6_relat_1(A_15)) | ~r1_tarski(A_15, A_39))), inference(superposition, [status(thm), theory('equality')], [c_152, c_201])).
% 4.49/1.92  tff(c_268, plain, (![A_49, A_50]: (k3_xboole_0(A_49, A_50)=A_49 | ~r1_tarski(A_49, A_50))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_219])).
% 4.49/1.92  tff(c_280, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_268])).
% 4.49/1.92  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.49/1.92  tff(c_287, plain, (r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_280, c_4])).
% 4.49/1.92  tff(c_222, plain, (![A_15, A_39]: (k3_xboole_0(A_15, A_39)=A_15 | ~r1_tarski(A_15, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_219])).
% 4.49/1.92  tff(c_295, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_287, c_222])).
% 4.49/1.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.49/1.92  tff(c_51, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.49/1.92  tff(c_66, plain, (![B_28, A_29]: (r1_tarski(k3_xboole_0(B_28, A_29), A_29))), inference(superposition, [status(thm), theory('equality')], [c_51, c_4])).
% 4.49/1.92  tff(c_351, plain, (![B_56, A_57]: (k3_xboole_0(k3_xboole_0(B_56, A_57), A_57)=k3_xboole_0(B_56, A_57))), inference(resolution, [status(thm)], [c_66, c_268])).
% 4.49/1.92  tff(c_1013, plain, (![B_74, A_75]: (k3_xboole_0(k3_xboole_0(B_74, A_75), B_74)=k3_xboole_0(A_75, B_74))), inference(superposition, [status(thm), theory('equality')], [c_2, c_351])).
% 4.49/1.92  tff(c_1111, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_280, c_1013])).
% 4.49/1.92  tff(c_1157, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_295, c_1111])).
% 4.49/1.92  tff(c_20, plain, (![B_17, A_16]: (k3_xboole_0(k1_relat_1(B_17), A_16)=k1_relat_1(k7_relat_1(B_17, A_16)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.49/1.92  tff(c_1195, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1157, c_20])).
% 4.49/1.92  tff(c_1230, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1195])).
% 4.49/1.92  tff(c_182, plain, (![B_42, A_43]: (r1_tarski(k1_relat_1(k7_relat_1(B_42, A_43)), k1_relat_1(B_42)) | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_167, c_4])).
% 4.49/1.92  tff(c_1246, plain, (![A_43]: (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_43)), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1230, c_182])).
% 4.49/1.92  tff(c_1287, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1246])).
% 4.49/1.92  tff(c_1290, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_1287])).
% 4.49/1.92  tff(c_1294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1290])).
% 4.49/1.92  tff(c_1296, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_1246])).
% 4.49/1.92  tff(c_10, plain, (![A_8]: (k9_relat_1(A_8, k1_relat_1(A_8))=k2_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.49/1.92  tff(c_1258, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1230, c_10])).
% 4.49/1.92  tff(c_1768, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_1258])).
% 4.49/1.92  tff(c_12, plain, (![A_9, C_13, B_12]: (k9_relat_1(k7_relat_1(A_9, C_13), B_12)=k9_relat_1(A_9, B_12) | ~r1_tarski(B_12, C_13) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.49/1.92  tff(c_1772, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1768, c_12])).
% 4.49/1.92  tff(c_1779, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_287, c_1772])).
% 4.49/1.92  tff(c_14, plain, (![A_14]: (k10_relat_1(A_14, k2_relat_1(A_14))=k1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.49/1.92  tff(c_1787, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1779, c_14])).
% 4.49/1.92  tff(c_1791, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_1230, c_1787])).
% 4.49/1.92  tff(c_223, plain, (![A_46, C_47, B_48]: (k3_xboole_0(A_46, k10_relat_1(C_47, B_48))=k10_relat_1(k7_relat_1(C_47, A_46), B_48) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.49/1.92  tff(c_3798, plain, (![C_123, A_124, B_125]: (r1_tarski(k10_relat_1(k7_relat_1(C_123, A_124), B_125), k10_relat_1(C_123, B_125)) | ~v1_relat_1(C_123))), inference(superposition, [status(thm), theory('equality')], [c_223, c_66])).
% 4.49/1.92  tff(c_3830, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1791, c_3798])).
% 4.49/1.92  tff(c_3856, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3830])).
% 4.49/1.92  tff(c_3858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_3856])).
% 4.49/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.92  
% 4.49/1.92  Inference rules
% 4.49/1.92  ----------------------
% 4.49/1.92  #Ref     : 0
% 4.49/1.92  #Sup     : 945
% 4.49/1.92  #Fact    : 0
% 4.49/1.92  #Define  : 0
% 4.49/1.92  #Split   : 3
% 4.49/1.92  #Chain   : 0
% 4.49/1.92  #Close   : 0
% 4.49/1.92  
% 4.49/1.92  Ordering : KBO
% 4.49/1.92  
% 4.49/1.92  Simplification rules
% 4.49/1.92  ----------------------
% 4.49/1.92  #Subsume      : 120
% 4.49/1.92  #Demod        : 1047
% 4.49/1.92  #Tautology    : 532
% 4.49/1.92  #SimpNegUnit  : 1
% 4.49/1.92  #BackRed      : 1
% 4.49/1.92  
% 4.49/1.92  #Partial instantiations: 0
% 4.49/1.92  #Strategies tried      : 1
% 4.49/1.92  
% 4.49/1.92  Timing (in seconds)
% 4.49/1.92  ----------------------
% 4.49/1.92  Preprocessing        : 0.29
% 4.49/1.92  Parsing              : 0.15
% 4.49/1.92  CNF conversion       : 0.02
% 4.49/1.92  Main loop            : 0.76
% 4.49/1.92  Inferencing          : 0.23
% 4.49/1.92  Reduction            : 0.35
% 4.49/1.92  Demodulation         : 0.29
% 4.49/1.92  BG Simplification    : 0.03
% 4.49/1.92  Subsumption          : 0.11
% 4.49/1.92  Abstraction          : 0.05
% 4.49/1.92  MUC search           : 0.00
% 4.49/1.92  Cooper               : 0.00
% 4.49/1.92  Total                : 1.08
% 4.49/1.92  Index Insertion      : 0.00
% 4.49/1.92  Index Deletion       : 0.00
% 4.49/1.92  Index Matching       : 0.00
% 4.49/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
