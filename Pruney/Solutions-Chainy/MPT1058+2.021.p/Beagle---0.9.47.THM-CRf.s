%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:24 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   55 (  64 expanded)
%              Number of leaves         :   31 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  70 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_32,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_279,plain,(
    ! [A_74,C_75,B_76] :
      ( k3_xboole_0(A_74,k10_relat_1(C_75,B_76)) = k10_relat_1(k7_relat_1(C_75,A_74),B_76)
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    ! [A_32] : k1_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_37] : v1_relat_1(k6_relat_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_222,plain,(
    ! [B_64,A_65] :
      ( k7_relat_1(B_64,A_65) = B_64
      | ~ r1_tarski(k1_relat_1(B_64),A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_228,plain,(
    ! [A_32,A_65] :
      ( k7_relat_1(k6_relat_1(A_32),A_65) = k6_relat_1(A_32)
      | ~ r1_tarski(A_32,A_65)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_222])).

tff(c_240,plain,(
    ! [A_70,A_71] :
      ( k7_relat_1(k6_relat_1(A_70),A_71) = k6_relat_1(A_70)
      | ~ r1_tarski(A_70,A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_228])).

tff(c_182,plain,(
    ! [B_60,A_61] :
      ( k3_xboole_0(k1_relat_1(B_60),A_61) = k1_relat_1(k7_relat_1(B_60,A_61))
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_205,plain,(
    ! [A_32,A_61] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_32),A_61)) = k3_xboole_0(A_32,A_61)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_182])).

tff(c_209,plain,(
    ! [A_32,A_61] : k1_relat_1(k7_relat_1(k6_relat_1(A_32),A_61)) = k3_xboole_0(A_32,A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_205])).

tff(c_246,plain,(
    ! [A_70,A_71] :
      ( k3_xboole_0(A_70,A_71) = k1_relat_1(k6_relat_1(A_70))
      | ~ r1_tarski(A_70,A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_209])).

tff(c_253,plain,(
    ! [A_72,A_73] :
      ( k3_xboole_0(A_72,A_73) = A_72
      | ~ r1_tarski(A_72,A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_246])).

tff(c_257,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_253])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_101,plain,(
    ! [A_51,B_52] : k1_setfam_1(k2_tarski(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_116,plain,(
    ! [B_53,A_54] : k1_setfam_1(k2_tarski(B_53,A_54)) = k3_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_101])).

tff(c_16,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [B_53,A_54] : k3_xboole_0(B_53,A_54) = k3_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_16])).

tff(c_261,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_122])).

tff(c_285,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_261])).

tff(c_316,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_285])).

tff(c_318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_316])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.23  
% 2.14/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.23  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.14/1.23  
% 2.14/1.23  %Foreground sorts:
% 2.14/1.23  
% 2.14/1.23  
% 2.14/1.23  %Background operators:
% 2.14/1.23  
% 2.14/1.23  
% 2.14/1.23  %Foreground operators:
% 2.14/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.14/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.14/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.14/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.14/1.23  
% 2.24/1.25  tff(f_73, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 2.24/1.25  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 2.24/1.25  tff(f_45, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.24/1.25  tff(f_59, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.24/1.25  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.24/1.25  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.24/1.25  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.24/1.25  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.24/1.25  tff(c_32, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.24/1.25  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.24/1.25  tff(c_279, plain, (![A_74, C_75, B_76]: (k3_xboole_0(A_74, k10_relat_1(C_75, B_76))=k10_relat_1(k7_relat_1(C_75, A_74), B_76) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.24/1.25  tff(c_34, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.24/1.25  tff(c_18, plain, (![A_32]: (k1_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.24/1.25  tff(c_26, plain, (![A_37]: (v1_relat_1(k6_relat_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.25  tff(c_222, plain, (![B_64, A_65]: (k7_relat_1(B_64, A_65)=B_64 | ~r1_tarski(k1_relat_1(B_64), A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.25  tff(c_228, plain, (![A_32, A_65]: (k7_relat_1(k6_relat_1(A_32), A_65)=k6_relat_1(A_32) | ~r1_tarski(A_32, A_65) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_222])).
% 2.24/1.25  tff(c_240, plain, (![A_70, A_71]: (k7_relat_1(k6_relat_1(A_70), A_71)=k6_relat_1(A_70) | ~r1_tarski(A_70, A_71))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_228])).
% 2.24/1.25  tff(c_182, plain, (![B_60, A_61]: (k3_xboole_0(k1_relat_1(B_60), A_61)=k1_relat_1(k7_relat_1(B_60, A_61)) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.24/1.25  tff(c_205, plain, (![A_32, A_61]: (k1_relat_1(k7_relat_1(k6_relat_1(A_32), A_61))=k3_xboole_0(A_32, A_61) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_182])).
% 2.24/1.25  tff(c_209, plain, (![A_32, A_61]: (k1_relat_1(k7_relat_1(k6_relat_1(A_32), A_61))=k3_xboole_0(A_32, A_61))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_205])).
% 2.24/1.25  tff(c_246, plain, (![A_70, A_71]: (k3_xboole_0(A_70, A_71)=k1_relat_1(k6_relat_1(A_70)) | ~r1_tarski(A_70, A_71))), inference(superposition, [status(thm), theory('equality')], [c_240, c_209])).
% 2.24/1.25  tff(c_253, plain, (![A_72, A_73]: (k3_xboole_0(A_72, A_73)=A_72 | ~r1_tarski(A_72, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_246])).
% 2.24/1.25  tff(c_257, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_253])).
% 2.24/1.25  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.25  tff(c_101, plain, (![A_51, B_52]: (k1_setfam_1(k2_tarski(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.25  tff(c_116, plain, (![B_53, A_54]: (k1_setfam_1(k2_tarski(B_53, A_54))=k3_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_2, c_101])).
% 2.24/1.25  tff(c_16, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.25  tff(c_122, plain, (![B_53, A_54]: (k3_xboole_0(B_53, A_54)=k3_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_116, c_16])).
% 2.24/1.25  tff(c_261, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_257, c_122])).
% 2.24/1.25  tff(c_285, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_279, c_261])).
% 2.24/1.25  tff(c_316, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_285])).
% 2.24/1.25  tff(c_318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_316])).
% 2.24/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.25  
% 2.24/1.25  Inference rules
% 2.24/1.25  ----------------------
% 2.24/1.25  #Ref     : 0
% 2.24/1.25  #Sup     : 70
% 2.24/1.25  #Fact    : 0
% 2.24/1.25  #Define  : 0
% 2.24/1.25  #Split   : 0
% 2.24/1.25  #Chain   : 0
% 2.24/1.25  #Close   : 0
% 2.24/1.25  
% 2.24/1.25  Ordering : KBO
% 2.24/1.25  
% 2.24/1.25  Simplification rules
% 2.24/1.25  ----------------------
% 2.24/1.25  #Subsume      : 1
% 2.24/1.25  #Demod        : 8
% 2.24/1.25  #Tautology    : 45
% 2.24/1.25  #SimpNegUnit  : 1
% 2.24/1.25  #BackRed      : 0
% 2.24/1.25  
% 2.24/1.25  #Partial instantiations: 0
% 2.24/1.25  #Strategies tried      : 1
% 2.24/1.25  
% 2.24/1.25  Timing (in seconds)
% 2.24/1.25  ----------------------
% 2.24/1.25  Preprocessing        : 0.32
% 2.24/1.25  Parsing              : 0.18
% 2.24/1.25  CNF conversion       : 0.02
% 2.24/1.25  Main loop            : 0.17
% 2.24/1.25  Inferencing          : 0.07
% 2.24/1.25  Reduction            : 0.06
% 2.24/1.25  Demodulation         : 0.05
% 2.24/1.25  BG Simplification    : 0.01
% 2.24/1.25  Subsumption          : 0.02
% 2.24/1.25  Abstraction          : 0.01
% 2.24/1.25  MUC search           : 0.00
% 2.24/1.25  Cooper               : 0.00
% 2.24/1.25  Total                : 0.52
% 2.24/1.25  Index Insertion      : 0.00
% 2.24/1.25  Index Deletion       : 0.00
% 2.24/1.25  Index Matching       : 0.00
% 2.24/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
