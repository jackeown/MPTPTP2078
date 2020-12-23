%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:25 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :   55 (  61 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 (  70 expanded)
%              Number of equality atoms :   26 (  30 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_24,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_78,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,(
    ! [B_40,A_41] : k1_setfam_1(k2_tarski(B_40,A_41)) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_78])).

tff(c_20,plain,(
    ! [A_21,B_22] : k1_setfam_1(k2_tarski(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_113,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_20])).

tff(c_10,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_205,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(A_50,C_51)
      | ~ r1_tarski(B_52,C_51)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_358,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,'#skF_2')
      | ~ r1_tarski(A_65,k10_relat_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_26,c_205])).

tff(c_384,plain,(
    ! [B_8] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),B_8),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_358])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_tarski(A_1,k3_xboole_0(B_2,C_3))
      | ~ r1_tarski(A_1,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_164,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1519,plain,(
    ! [A_112,B_113] :
      ( k4_xboole_0(A_112,B_113) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_112,B_113),k3_xboole_0(A_112,B_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_8])).

tff(c_1544,plain,(
    ! [B_2,C_3] :
      ( k4_xboole_0(B_2,C_3) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(B_2,C_3),C_3)
      | ~ r1_tarski(k4_xboole_0(B_2,C_3),B_2) ) ),
    inference(resolution,[status(thm)],[c_2,c_1519])).

tff(c_2145,plain,(
    ! [B_143,C_144] :
      ( k4_xboole_0(B_143,C_144) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(B_143,C_144),C_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1544])).

tff(c_2208,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_384,c_2145])).

tff(c_12,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2243,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),k1_xboole_0) = k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2208,c_12])).

tff(c_2263,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_10,c_2243])).

tff(c_22,plain,(
    ! [A_23,C_25,B_24] :
      ( k3_xboole_0(A_23,k10_relat_1(C_25,B_24)) = k10_relat_1(k7_relat_1(C_25,A_23),B_24)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2949,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2263,c_22])).

tff(c_2980,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2949])).

tff(c_2982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_2980])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.02/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.74  
% 4.02/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.74  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.02/1.74  
% 4.02/1.74  %Foreground sorts:
% 4.02/1.74  
% 4.02/1.74  
% 4.02/1.74  %Background operators:
% 4.02/1.74  
% 4.02/1.74  
% 4.02/1.74  %Foreground operators:
% 4.02/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.02/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.02/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.02/1.74  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.02/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.02/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.02/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.02/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.02/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.02/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.02/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.02/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.02/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.02/1.74  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.02/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.02/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.02/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.02/1.74  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.02/1.74  
% 4.02/1.75  tff(f_69, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 4.02/1.75  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.02/1.75  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.02/1.75  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.02/1.75  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.02/1.75  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.02/1.75  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.02/1.75  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.02/1.75  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 4.02/1.75  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 4.02/1.75  tff(c_24, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.02/1.75  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.02/1.75  tff(c_14, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.02/1.75  tff(c_78, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.02/1.75  tff(c_107, plain, (![B_40, A_41]: (k1_setfam_1(k2_tarski(B_40, A_41))=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_14, c_78])).
% 4.02/1.75  tff(c_20, plain, (![A_21, B_22]: (k1_setfam_1(k2_tarski(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.02/1.75  tff(c_113, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_107, c_20])).
% 4.02/1.75  tff(c_10, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.02/1.75  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.02/1.75  tff(c_26, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.02/1.75  tff(c_205, plain, (![A_50, C_51, B_52]: (r1_tarski(A_50, C_51) | ~r1_tarski(B_52, C_51) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.02/1.75  tff(c_358, plain, (![A_65]: (r1_tarski(A_65, '#skF_2') | ~r1_tarski(A_65, k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_26, c_205])).
% 4.02/1.75  tff(c_384, plain, (![B_8]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), B_8), '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_358])).
% 4.02/1.75  tff(c_2, plain, (![A_1, B_2, C_3]: (r1_tarski(A_1, k3_xboole_0(B_2, C_3)) | ~r1_tarski(A_1, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.02/1.75  tff(c_164, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.02/1.75  tff(c_8, plain, (![A_9, B_10]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k4_xboole_0(B_10, A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.02/1.75  tff(c_1519, plain, (![A_112, B_113]: (k4_xboole_0(A_112, B_113)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_112, B_113), k3_xboole_0(A_112, B_113)))), inference(superposition, [status(thm), theory('equality')], [c_164, c_8])).
% 4.02/1.75  tff(c_1544, plain, (![B_2, C_3]: (k4_xboole_0(B_2, C_3)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(B_2, C_3), C_3) | ~r1_tarski(k4_xboole_0(B_2, C_3), B_2))), inference(resolution, [status(thm)], [c_2, c_1519])).
% 4.02/1.75  tff(c_2145, plain, (![B_143, C_144]: (k4_xboole_0(B_143, C_144)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(B_143, C_144), C_144))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1544])).
% 4.02/1.75  tff(c_2208, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_384, c_2145])).
% 4.02/1.75  tff(c_12, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.02/1.75  tff(c_2243, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), k1_xboole_0)=k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2208, c_12])).
% 4.02/1.75  tff(c_2263, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_10, c_2243])).
% 4.02/1.75  tff(c_22, plain, (![A_23, C_25, B_24]: (k3_xboole_0(A_23, k10_relat_1(C_25, B_24))=k10_relat_1(k7_relat_1(C_25, A_23), B_24) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.02/1.75  tff(c_2949, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2263, c_22])).
% 4.02/1.75  tff(c_2980, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2949])).
% 4.02/1.75  tff(c_2982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_2980])).
% 4.02/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.75  
% 4.02/1.75  Inference rules
% 4.02/1.75  ----------------------
% 4.02/1.75  #Ref     : 0
% 4.02/1.75  #Sup     : 700
% 4.02/1.75  #Fact    : 0
% 4.02/1.75  #Define  : 0
% 4.02/1.75  #Split   : 0
% 4.02/1.75  #Chain   : 0
% 4.02/1.75  #Close   : 0
% 4.02/1.75  
% 4.02/1.75  Ordering : KBO
% 4.02/1.75  
% 4.02/1.75  Simplification rules
% 4.02/1.75  ----------------------
% 4.02/1.75  #Subsume      : 45
% 4.02/1.75  #Demod        : 486
% 4.02/1.75  #Tautology    : 423
% 4.02/1.75  #SimpNegUnit  : 1
% 4.02/1.75  #BackRed      : 4
% 4.02/1.75  
% 4.02/1.75  #Partial instantiations: 0
% 4.02/1.75  #Strategies tried      : 1
% 4.02/1.75  
% 4.02/1.75  Timing (in seconds)
% 4.02/1.75  ----------------------
% 4.02/1.76  Preprocessing        : 0.30
% 4.02/1.76  Parsing              : 0.16
% 4.02/1.76  CNF conversion       : 0.02
% 4.02/1.76  Main loop            : 0.69
% 4.02/1.76  Inferencing          : 0.22
% 4.02/1.76  Reduction            : 0.29
% 4.02/1.76  Demodulation         : 0.24
% 4.02/1.76  BG Simplification    : 0.02
% 4.02/1.76  Subsumption          : 0.11
% 4.02/1.76  Abstraction          : 0.03
% 4.02/1.76  MUC search           : 0.00
% 4.02/1.76  Cooper               : 0.00
% 4.02/1.76  Total                : 1.02
% 4.02/1.76  Index Insertion      : 0.00
% 4.02/1.76  Index Deletion       : 0.00
% 4.02/1.76  Index Matching       : 0.00
% 4.02/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
