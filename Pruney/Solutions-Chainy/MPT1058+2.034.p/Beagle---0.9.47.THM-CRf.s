%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:26 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :   49 (  54 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 (  64 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_22,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_140,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_196,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,'#skF_2')
      | ~ r1_tarski(A_47,k10_relat_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_24,c_140])).

tff(c_217,plain,(
    ! [B_10] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),B_10),'#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_196])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,k3_xboole_0(B_4,C_5))
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(B_12,A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1646,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_109,B_110),k3_xboole_0(A_109,B_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_10])).

tff(c_1671,plain,(
    ! [B_4,C_5] :
      ( k4_xboole_0(B_4,C_5) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(B_4,C_5),C_5)
      | ~ r1_tarski(k4_xboole_0(B_4,C_5),B_4) ) ),
    inference(resolution,[status(thm)],[c_4,c_1646])).

tff(c_2176,plain,(
    ! [B_129,C_130] :
      ( k4_xboole_0(B_129,C_130) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(B_129,C_130),C_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1671])).

tff(c_2235,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_217,c_2176])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2361,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),k1_xboole_0) = k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2235,c_14])).

tff(c_2382,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12,c_2361])).

tff(c_20,plain,(
    ! [A_20,C_22,B_21] :
      ( k3_xboole_0(A_20,k10_relat_1(C_22,B_21)) = k10_relat_1(k7_relat_1(C_22,A_20),B_21)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2923,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2382,c_20])).

tff(c_2949,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2923])).

tff(c_2951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_2949])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:03:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.71  
% 4.07/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.71  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.07/1.71  
% 4.07/1.71  %Foreground sorts:
% 4.07/1.71  
% 4.07/1.71  
% 4.07/1.71  %Background operators:
% 4.07/1.71  
% 4.07/1.71  
% 4.07/1.71  %Foreground operators:
% 4.07/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.07/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.07/1.71  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.07/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.07/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.07/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.07/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.07/1.71  tff('#skF_2', type, '#skF_2': $i).
% 4.07/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.07/1.71  tff('#skF_1', type, '#skF_1': $i).
% 4.07/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/1.71  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.07/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.07/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.07/1.71  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.07/1.71  
% 4.07/1.72  tff(f_67, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 4.07/1.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.07/1.72  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.07/1.72  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.07/1.72  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.07/1.72  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.07/1.72  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.07/1.72  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 4.07/1.72  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 4.07/1.72  tff(c_22, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.07/1.72  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.07/1.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.07/1.72  tff(c_12, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.07/1.72  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.07/1.72  tff(c_24, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.07/1.72  tff(c_140, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.07/1.72  tff(c_196, plain, (![A_47]: (r1_tarski(A_47, '#skF_2') | ~r1_tarski(A_47, k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_24, c_140])).
% 4.07/1.72  tff(c_217, plain, (![B_10]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), B_10), '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_196])).
% 4.07/1.72  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, k3_xboole_0(B_4, C_5)) | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.07/1.72  tff(c_99, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.07/1.72  tff(c_10, plain, (![A_11, B_12]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k4_xboole_0(B_12, A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.07/1.72  tff(c_1646, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_109, B_110), k3_xboole_0(A_109, B_110)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_10])).
% 4.07/1.72  tff(c_1671, plain, (![B_4, C_5]: (k4_xboole_0(B_4, C_5)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(B_4, C_5), C_5) | ~r1_tarski(k4_xboole_0(B_4, C_5), B_4))), inference(resolution, [status(thm)], [c_4, c_1646])).
% 4.07/1.72  tff(c_2176, plain, (![B_129, C_130]: (k4_xboole_0(B_129, C_130)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(B_129, C_130), C_130))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1671])).
% 4.07/1.72  tff(c_2235, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_217, c_2176])).
% 4.07/1.72  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.07/1.72  tff(c_2361, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), k1_xboole_0)=k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2235, c_14])).
% 4.07/1.72  tff(c_2382, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12, c_2361])).
% 4.07/1.72  tff(c_20, plain, (![A_20, C_22, B_21]: (k3_xboole_0(A_20, k10_relat_1(C_22, B_21))=k10_relat_1(k7_relat_1(C_22, A_20), B_21) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.07/1.72  tff(c_2923, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2382, c_20])).
% 4.07/1.72  tff(c_2949, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2923])).
% 4.07/1.72  tff(c_2951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_2949])).
% 4.07/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.72  
% 4.07/1.72  Inference rules
% 4.07/1.72  ----------------------
% 4.07/1.72  #Ref     : 0
% 4.07/1.72  #Sup     : 684
% 4.07/1.72  #Fact    : 0
% 4.07/1.72  #Define  : 0
% 4.07/1.72  #Split   : 0
% 4.07/1.72  #Chain   : 0
% 4.07/1.72  #Close   : 0
% 4.07/1.72  
% 4.07/1.72  Ordering : KBO
% 4.07/1.72  
% 4.07/1.72  Simplification rules
% 4.07/1.72  ----------------------
% 4.07/1.72  #Subsume      : 51
% 4.07/1.72  #Demod        : 455
% 4.07/1.72  #Tautology    : 393
% 4.07/1.72  #SimpNegUnit  : 1
% 4.07/1.72  #BackRed      : 2
% 4.07/1.72  
% 4.07/1.72  #Partial instantiations: 0
% 4.07/1.72  #Strategies tried      : 1
% 4.07/1.72  
% 4.07/1.72  Timing (in seconds)
% 4.07/1.72  ----------------------
% 4.07/1.73  Preprocessing        : 0.30
% 4.07/1.73  Parsing              : 0.16
% 4.07/1.73  CNF conversion       : 0.02
% 4.07/1.73  Main loop            : 0.65
% 4.07/1.73  Inferencing          : 0.22
% 4.07/1.73  Reduction            : 0.27
% 4.07/1.73  Demodulation         : 0.21
% 4.07/1.73  BG Simplification    : 0.02
% 4.07/1.73  Subsumption          : 0.10
% 4.07/1.73  Abstraction          : 0.03
% 4.07/1.73  MUC search           : 0.00
% 4.07/1.73  Cooper               : 0.00
% 4.07/1.73  Total                : 0.99
% 4.07/1.73  Index Insertion      : 0.00
% 4.07/1.73  Index Deletion       : 0.00
% 4.07/1.73  Index Matching       : 0.00
% 4.07/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
