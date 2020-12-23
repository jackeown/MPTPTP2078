%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:24 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   54 (  63 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 (  72 expanded)
%              Number of equality atoms :   30 (  39 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_71,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_32,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_408,plain,(
    ! [A_65,B_66] :
      ( k5_relat_1(k6_relat_1(A_65),B_66) = k7_relat_1(B_66,A_65)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [B_25,A_24] : k5_relat_1(k6_relat_1(B_25),k6_relat_1(A_24)) = k6_relat_1(k3_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_415,plain,(
    ! [A_24,A_65] :
      ( k7_relat_1(k6_relat_1(A_24),A_65) = k6_relat_1(k3_xboole_0(A_24,A_65))
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_30])).

tff(c_424,plain,(
    ! [A_24,A_65] : k7_relat_1(k6_relat_1(A_24),A_65) = k6_relat_1(k3_xboole_0(A_24,A_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_415])).

tff(c_486,plain,(
    ! [B_73,A_74] :
      ( k7_relat_1(B_73,A_74) = B_73
      | ~ r1_tarski(k1_relat_1(B_73),A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_504,plain,(
    ! [A_12,A_74] :
      ( k7_relat_1(k6_relat_1(A_12),A_74) = k6_relat_1(A_12)
      | ~ r1_tarski(A_12,A_74)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_486])).

tff(c_1129,plain,(
    ! [A_113,A_114] :
      ( k6_relat_1(k3_xboole_0(A_113,A_114)) = k6_relat_1(A_113)
      | ~ r1_tarski(A_113,A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_424,c_504])).

tff(c_1150,plain,(
    ! [A_113,A_114] :
      ( k3_xboole_0(A_113,A_114) = k1_relat_1(k6_relat_1(A_113))
      | ~ r1_tarski(A_113,A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1129,c_12])).

tff(c_1186,plain,(
    ! [A_115,A_116] :
      ( k3_xboole_0(A_115,A_116) = A_115
      | ~ r1_tarski(A_115,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1150])).

tff(c_1268,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1186])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_133,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_175,plain,(
    ! [B_46,A_47] : k1_setfam_1(k2_tarski(B_46,A_47)) = k3_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_133])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_181,plain,(
    ! [B_46,A_47] : k3_xboole_0(B_46,A_47) = k3_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_10])).

tff(c_1422,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1268,c_181])).

tff(c_28,plain,(
    ! [A_21,C_23,B_22] :
      ( k3_xboole_0(A_21,k10_relat_1(C_23,B_22)) = k10_relat_1(k7_relat_1(C_23,A_21),B_22)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1778,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1422,c_28])).

tff(c_1806,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1778])).

tff(c_1808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1806])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:36:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.57  
% 2.98/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.57  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.98/1.57  
% 2.98/1.57  %Foreground sorts:
% 2.98/1.57  
% 2.98/1.57  
% 2.98/1.57  %Background operators:
% 2.98/1.57  
% 2.98/1.57  
% 2.98/1.57  %Foreground operators:
% 2.98/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.98/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.98/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.98/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.98/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.57  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.57  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.57  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.98/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.98/1.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.98/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.98/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.98/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.98/1.57  
% 2.98/1.58  tff(f_81, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 2.98/1.58  tff(f_43, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.98/1.58  tff(f_65, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.98/1.58  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.98/1.58  tff(f_71, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.98/1.58  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.98/1.58  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.98/1.58  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.98/1.58  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.98/1.58  tff(c_32, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.98/1.58  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.98/1.58  tff(c_34, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.98/1.58  tff(c_12, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.98/1.58  tff(c_24, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.98/1.58  tff(c_408, plain, (![A_65, B_66]: (k5_relat_1(k6_relat_1(A_65), B_66)=k7_relat_1(B_66, A_65) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.98/1.58  tff(c_30, plain, (![B_25, A_24]: (k5_relat_1(k6_relat_1(B_25), k6_relat_1(A_24))=k6_relat_1(k3_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.98/1.58  tff(c_415, plain, (![A_24, A_65]: (k7_relat_1(k6_relat_1(A_24), A_65)=k6_relat_1(k3_xboole_0(A_24, A_65)) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_408, c_30])).
% 2.98/1.58  tff(c_424, plain, (![A_24, A_65]: (k7_relat_1(k6_relat_1(A_24), A_65)=k6_relat_1(k3_xboole_0(A_24, A_65)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_415])).
% 2.98/1.58  tff(c_486, plain, (![B_73, A_74]: (k7_relat_1(B_73, A_74)=B_73 | ~r1_tarski(k1_relat_1(B_73), A_74) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.98/1.58  tff(c_504, plain, (![A_12, A_74]: (k7_relat_1(k6_relat_1(A_12), A_74)=k6_relat_1(A_12) | ~r1_tarski(A_12, A_74) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_486])).
% 2.98/1.58  tff(c_1129, plain, (![A_113, A_114]: (k6_relat_1(k3_xboole_0(A_113, A_114))=k6_relat_1(A_113) | ~r1_tarski(A_113, A_114))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_424, c_504])).
% 2.98/1.58  tff(c_1150, plain, (![A_113, A_114]: (k3_xboole_0(A_113, A_114)=k1_relat_1(k6_relat_1(A_113)) | ~r1_tarski(A_113, A_114))), inference(superposition, [status(thm), theory('equality')], [c_1129, c_12])).
% 2.98/1.58  tff(c_1186, plain, (![A_115, A_116]: (k3_xboole_0(A_115, A_116)=A_115 | ~r1_tarski(A_115, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1150])).
% 2.98/1.58  tff(c_1268, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_1186])).
% 2.98/1.58  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.98/1.58  tff(c_133, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.58  tff(c_175, plain, (![B_46, A_47]: (k1_setfam_1(k2_tarski(B_46, A_47))=k3_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_6, c_133])).
% 2.98/1.58  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.58  tff(c_181, plain, (![B_46, A_47]: (k3_xboole_0(B_46, A_47)=k3_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_175, c_10])).
% 2.98/1.58  tff(c_1422, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1268, c_181])).
% 2.98/1.58  tff(c_28, plain, (![A_21, C_23, B_22]: (k3_xboole_0(A_21, k10_relat_1(C_23, B_22))=k10_relat_1(k7_relat_1(C_23, A_21), B_22) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.98/1.58  tff(c_1778, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1422, c_28])).
% 2.98/1.58  tff(c_1806, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1778])).
% 2.98/1.58  tff(c_1808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1806])).
% 2.98/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.58  
% 2.98/1.58  Inference rules
% 2.98/1.58  ----------------------
% 2.98/1.58  #Ref     : 0
% 2.98/1.58  #Sup     : 434
% 2.98/1.58  #Fact    : 0
% 2.98/1.58  #Define  : 0
% 2.98/1.58  #Split   : 0
% 2.98/1.58  #Chain   : 0
% 2.98/1.58  #Close   : 0
% 2.98/1.58  
% 2.98/1.58  Ordering : KBO
% 2.98/1.58  
% 2.98/1.58  Simplification rules
% 2.98/1.58  ----------------------
% 2.98/1.58  #Subsume      : 12
% 2.98/1.58  #Demod        : 239
% 2.98/1.58  #Tautology    : 264
% 2.98/1.58  #SimpNegUnit  : 1
% 2.98/1.58  #BackRed      : 0
% 2.98/1.58  
% 2.98/1.58  #Partial instantiations: 0
% 2.98/1.58  #Strategies tried      : 1
% 2.98/1.58  
% 2.98/1.58  Timing (in seconds)
% 2.98/1.58  ----------------------
% 3.23/1.58  Preprocessing        : 0.31
% 3.23/1.58  Parsing              : 0.18
% 3.23/1.58  CNF conversion       : 0.02
% 3.23/1.58  Main loop            : 0.45
% 3.23/1.58  Inferencing          : 0.16
% 3.23/1.58  Reduction            : 0.17
% 3.23/1.58  Demodulation         : 0.14
% 3.23/1.58  BG Simplification    : 0.02
% 3.23/1.58  Subsumption          : 0.07
% 3.23/1.58  Abstraction          : 0.03
% 3.23/1.58  MUC search           : 0.00
% 3.23/1.58  Cooper               : 0.00
% 3.23/1.58  Total                : 0.79
% 3.23/1.58  Index Insertion      : 0.00
% 3.23/1.58  Index Deletion       : 0.00
% 3.23/1.58  Index Matching       : 0.00
% 3.23/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
