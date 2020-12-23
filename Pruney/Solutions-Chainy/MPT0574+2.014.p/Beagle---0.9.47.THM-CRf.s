%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:52 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   74 (  98 expanded)
%              Number of leaves         :   33 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :   66 (  96 expanded)
%              Number of equality atoms :   44 (  64 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_140,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_232,plain,(
    ! [A_51,B_52] : k1_setfam_1(k2_tarski(A_51,B_52)) = k3_xboole_0(B_52,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_140])).

tff(c_28,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_270,plain,(
    ! [B_55,A_56] : k3_xboole_0(B_55,A_56) = k3_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_28])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ r1_tarski(A_35,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,(
    ! [B_6] : k3_xboole_0(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_286,plain,(
    ! [B_55] : k3_xboole_0(B_55,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_80])).

tff(c_18,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_383,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_392,plain,(
    ! [B_55] : k5_xboole_0(B_55,k1_xboole_0) = k4_xboole_0(B_55,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_383])).

tff(c_437,plain,(
    ! [B_62] : k4_xboole_0(B_62,k1_xboole_0) = B_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_392])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_447,plain,(
    ! [B_62] : k4_xboole_0(B_62,B_62) = k3_xboole_0(B_62,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_16])).

tff(c_457,plain,(
    ! [B_62] : k4_xboole_0(B_62,B_62) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_447])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_410,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_383])).

tff(c_533,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_410])).

tff(c_34,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_155,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_172,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_155])).

tff(c_404,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_383])).

tff(c_534,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_404])).

tff(c_560,plain,(
    ! [A_67,B_68] : k2_xboole_0(A_67,k4_xboole_0(B_68,A_67)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_575,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_560])).

tff(c_592,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_575])).

tff(c_217,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_661,plain,(
    ! [A_73,B_74] : k3_tarski(k2_tarski(A_73,B_74)) = k2_xboole_0(B_74,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_217])).

tff(c_26,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_684,plain,(
    ! [B_75,A_76] : k2_xboole_0(B_75,A_76) = k2_xboole_0(A_76,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_26])).

tff(c_752,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_592,c_684])).

tff(c_635,plain,(
    ! [C_70,A_71,B_72] :
      ( k2_xboole_0(k10_relat_1(C_70,A_71),k10_relat_1(C_70,B_72)) = k10_relat_1(C_70,k2_xboole_0(A_71,B_72))
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1918,plain,(
    ! [C_104,A_105,B_106] :
      ( r1_tarski(k10_relat_1(C_104,A_105),k10_relat_1(C_104,k2_xboole_0(A_105,B_106)))
      | ~ v1_relat_1(C_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_20])).

tff(c_2756,plain,(
    ! [C_123] :
      ( r1_tarski(k10_relat_1(C_123,'#skF_1'),k10_relat_1(C_123,'#skF_2'))
      | ~ v1_relat_1(C_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_1918])).

tff(c_32,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2762,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2756,c_32])).

tff(c_2767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2762])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.61  
% 3.39/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.61  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.39/1.61  
% 3.39/1.61  %Foreground sorts:
% 3.39/1.61  
% 3.39/1.61  
% 3.39/1.61  %Background operators:
% 3.39/1.61  
% 3.39/1.61  
% 3.39/1.61  %Foreground operators:
% 3.39/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.39/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.39/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.39/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.39/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.39/1.61  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.39/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.39/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.39/1.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.39/1.61  
% 3.39/1.63  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 3.39/1.63  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.39/1.63  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.39/1.63  tff(f_57, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.39/1.63  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.39/1.63  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.39/1.63  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.39/1.63  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.39/1.63  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.39/1.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.39/1.63  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.39/1.63  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.39/1.63  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.39/1.63  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 3.39/1.63  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.39/1.63  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.39/1.63  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.39/1.63  tff(c_22, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.39/1.63  tff(c_140, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.39/1.63  tff(c_232, plain, (![A_51, B_52]: (k1_setfam_1(k2_tarski(A_51, B_52))=k3_xboole_0(B_52, A_51))), inference(superposition, [status(thm), theory('equality')], [c_22, c_140])).
% 3.39/1.63  tff(c_28, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.39/1.63  tff(c_270, plain, (![B_55, A_56]: (k3_xboole_0(B_55, A_56)=k3_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_232, c_28])).
% 3.39/1.63  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.63  tff(c_69, plain, (![A_35]: (k1_xboole_0=A_35 | ~r1_tarski(A_35, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.39/1.63  tff(c_80, plain, (![B_6]: (k3_xboole_0(k1_xboole_0, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_69])).
% 3.39/1.63  tff(c_286, plain, (![B_55]: (k3_xboole_0(B_55, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_270, c_80])).
% 3.39/1.63  tff(c_18, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.39/1.63  tff(c_383, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.63  tff(c_392, plain, (![B_55]: (k5_xboole_0(B_55, k1_xboole_0)=k4_xboole_0(B_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_286, c_383])).
% 3.39/1.63  tff(c_437, plain, (![B_62]: (k4_xboole_0(B_62, k1_xboole_0)=B_62)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_392])).
% 3.39/1.63  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.39/1.63  tff(c_447, plain, (![B_62]: (k4_xboole_0(B_62, B_62)=k3_xboole_0(B_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_437, c_16])).
% 3.39/1.63  tff(c_457, plain, (![B_62]: (k4_xboole_0(B_62, B_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_447])).
% 3.39/1.63  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.39/1.63  tff(c_410, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_383])).
% 3.39/1.63  tff(c_533, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_457, c_410])).
% 3.39/1.63  tff(c_34, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.39/1.63  tff(c_155, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.39/1.63  tff(c_172, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_34, c_155])).
% 3.39/1.63  tff(c_404, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_172, c_383])).
% 3.39/1.63  tff(c_534, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_533, c_404])).
% 3.39/1.63  tff(c_560, plain, (![A_67, B_68]: (k2_xboole_0(A_67, k4_xboole_0(B_68, A_67))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.39/1.63  tff(c_575, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_534, c_560])).
% 3.39/1.63  tff(c_592, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_575])).
% 3.39/1.63  tff(c_217, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.39/1.63  tff(c_661, plain, (![A_73, B_74]: (k3_tarski(k2_tarski(A_73, B_74))=k2_xboole_0(B_74, A_73))), inference(superposition, [status(thm), theory('equality')], [c_22, c_217])).
% 3.39/1.63  tff(c_26, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.39/1.63  tff(c_684, plain, (![B_75, A_76]: (k2_xboole_0(B_75, A_76)=k2_xboole_0(A_76, B_75))), inference(superposition, [status(thm), theory('equality')], [c_661, c_26])).
% 3.39/1.63  tff(c_752, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_592, c_684])).
% 3.39/1.63  tff(c_635, plain, (![C_70, A_71, B_72]: (k2_xboole_0(k10_relat_1(C_70, A_71), k10_relat_1(C_70, B_72))=k10_relat_1(C_70, k2_xboole_0(A_71, B_72)) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.63  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.39/1.63  tff(c_1918, plain, (![C_104, A_105, B_106]: (r1_tarski(k10_relat_1(C_104, A_105), k10_relat_1(C_104, k2_xboole_0(A_105, B_106))) | ~v1_relat_1(C_104))), inference(superposition, [status(thm), theory('equality')], [c_635, c_20])).
% 3.39/1.63  tff(c_2756, plain, (![C_123]: (r1_tarski(k10_relat_1(C_123, '#skF_1'), k10_relat_1(C_123, '#skF_2')) | ~v1_relat_1(C_123))), inference(superposition, [status(thm), theory('equality')], [c_752, c_1918])).
% 3.39/1.63  tff(c_32, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.39/1.63  tff(c_2762, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2756, c_32])).
% 3.39/1.63  tff(c_2767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2762])).
% 3.39/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.63  
% 3.39/1.63  Inference rules
% 3.39/1.63  ----------------------
% 3.39/1.63  #Ref     : 0
% 3.39/1.63  #Sup     : 683
% 3.39/1.63  #Fact    : 0
% 3.39/1.63  #Define  : 0
% 3.39/1.63  #Split   : 0
% 3.39/1.63  #Chain   : 0
% 3.39/1.63  #Close   : 0
% 3.39/1.63  
% 3.39/1.63  Ordering : KBO
% 3.39/1.63  
% 3.39/1.63  Simplification rules
% 3.39/1.63  ----------------------
% 3.39/1.63  #Subsume      : 3
% 3.39/1.63  #Demod        : 591
% 3.39/1.63  #Tautology    : 552
% 3.39/1.63  #SimpNegUnit  : 0
% 3.39/1.63  #BackRed      : 2
% 3.39/1.63  
% 3.39/1.63  #Partial instantiations: 0
% 3.39/1.63  #Strategies tried      : 1
% 3.39/1.63  
% 3.39/1.63  Timing (in seconds)
% 3.39/1.63  ----------------------
% 3.39/1.63  Preprocessing        : 0.31
% 3.39/1.63  Parsing              : 0.17
% 3.39/1.63  CNF conversion       : 0.02
% 3.39/1.63  Main loop            : 0.51
% 3.39/1.63  Inferencing          : 0.17
% 3.39/1.63  Reduction            : 0.22
% 3.39/1.63  Demodulation         : 0.18
% 3.39/1.63  BG Simplification    : 0.02
% 3.39/1.63  Subsumption          : 0.07
% 3.39/1.63  Abstraction          : 0.03
% 3.39/1.63  MUC search           : 0.00
% 3.39/1.63  Cooper               : 0.00
% 3.39/1.63  Total                : 0.85
% 3.39/1.63  Index Insertion      : 0.00
% 3.39/1.63  Index Deletion       : 0.00
% 3.39/1.63  Index Matching       : 0.00
% 3.39/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
