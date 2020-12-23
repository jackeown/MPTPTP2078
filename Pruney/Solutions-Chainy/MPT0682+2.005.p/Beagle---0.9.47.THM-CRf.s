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
% DateTime   : Thu Dec  3 10:04:29 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  54 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => k9_relat_1(k8_relat_1(A,C),B) = k3_xboole_0(A,k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k8_relat_1(A_5,B_6))
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k7_relat_1(A_3,B_4))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_9,C_11,B_10] :
      ( k8_relat_1(A_9,k7_relat_1(C_11,B_10)) = k7_relat_1(k8_relat_1(A_9,C_11),B_10)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    ! [B_22,A_23] :
      ( k3_xboole_0(k2_relat_1(B_22),A_23) = k2_relat_1(k8_relat_1(A_23,B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_222,plain,(
    ! [A_34,B_35,A_36] :
      ( k2_relat_1(k8_relat_1(A_34,k7_relat_1(B_35,A_36))) = k3_xboole_0(k9_relat_1(B_35,A_36),A_34)
      | ~ v1_relat_1(k7_relat_1(B_35,A_36))
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_63])).

tff(c_308,plain,(
    ! [A_40,C_41,B_42] :
      ( k2_relat_1(k7_relat_1(k8_relat_1(A_40,C_41),B_42)) = k3_xboole_0(k9_relat_1(C_41,B_42),A_40)
      | ~ v1_relat_1(k7_relat_1(C_41,B_42))
      | ~ v1_relat_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_222])).

tff(c_586,plain,(
    ! [A_60,C_61,A_62] :
      ( k9_relat_1(k8_relat_1(A_60,C_61),A_62) = k3_xboole_0(k9_relat_1(C_61,A_62),A_60)
      | ~ v1_relat_1(k7_relat_1(C_61,A_62))
      | ~ v1_relat_1(C_61)
      | ~ v1_relat_1(C_61)
      | ~ v1_relat_1(k8_relat_1(A_60,C_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_308])).

tff(c_596,plain,(
    ! [A_63,A_64,B_65] :
      ( k9_relat_1(k8_relat_1(A_63,A_64),B_65) = k3_xboole_0(k9_relat_1(A_64,B_65),A_63)
      | ~ v1_relat_1(k8_relat_1(A_63,A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(resolution,[status(thm)],[c_4,c_586])).

tff(c_602,plain,(
    ! [A_66,B_67,B_68] :
      ( k9_relat_1(k8_relat_1(A_66,B_67),B_68) = k3_xboole_0(k9_relat_1(B_67,B_68),A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_6,c_596])).

tff(c_14,plain,(
    k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_608,plain,
    ( k3_xboole_0(k9_relat_1('#skF_3','#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_14])).

tff(c_618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2,c_608])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.37  
% 2.52/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.37  %$ v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.52/1.37  
% 2.52/1.37  %Foreground sorts:
% 2.52/1.37  
% 2.52/1.37  
% 2.52/1.37  %Background operators:
% 2.52/1.37  
% 2.52/1.37  
% 2.52/1.37  %Foreground operators:
% 2.52/1.37  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.52/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.52/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.52/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.52/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.52/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.52/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.52/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.52/1.37  
% 2.81/1.38  tff(f_54, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(k8_relat_1(A, C), B) = k3_xboole_0(A, k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_funct_1)).
% 2.81/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.81/1.38  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.81/1.38  tff(f_31, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.81/1.38  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.81/1.38  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 2.81/1.38  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 2.81/1.38  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.38  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k8_relat_1(A_5, B_6)) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.38  tff(c_4, plain, (![A_3, B_4]: (v1_relat_1(k7_relat_1(A_3, B_4)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.38  tff(c_12, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.81/1.38  tff(c_10, plain, (![A_9, C_11, B_10]: (k8_relat_1(A_9, k7_relat_1(C_11, B_10))=k7_relat_1(k8_relat_1(A_9, C_11), B_10) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.38  tff(c_63, plain, (![B_22, A_23]: (k3_xboole_0(k2_relat_1(B_22), A_23)=k2_relat_1(k8_relat_1(A_23, B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.38  tff(c_222, plain, (![A_34, B_35, A_36]: (k2_relat_1(k8_relat_1(A_34, k7_relat_1(B_35, A_36)))=k3_xboole_0(k9_relat_1(B_35, A_36), A_34) | ~v1_relat_1(k7_relat_1(B_35, A_36)) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_12, c_63])).
% 2.81/1.38  tff(c_308, plain, (![A_40, C_41, B_42]: (k2_relat_1(k7_relat_1(k8_relat_1(A_40, C_41), B_42))=k3_xboole_0(k9_relat_1(C_41, B_42), A_40) | ~v1_relat_1(k7_relat_1(C_41, B_42)) | ~v1_relat_1(C_41) | ~v1_relat_1(C_41))), inference(superposition, [status(thm), theory('equality')], [c_10, c_222])).
% 2.81/1.38  tff(c_586, plain, (![A_60, C_61, A_62]: (k9_relat_1(k8_relat_1(A_60, C_61), A_62)=k3_xboole_0(k9_relat_1(C_61, A_62), A_60) | ~v1_relat_1(k7_relat_1(C_61, A_62)) | ~v1_relat_1(C_61) | ~v1_relat_1(C_61) | ~v1_relat_1(k8_relat_1(A_60, C_61)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_308])).
% 2.81/1.38  tff(c_596, plain, (![A_63, A_64, B_65]: (k9_relat_1(k8_relat_1(A_63, A_64), B_65)=k3_xboole_0(k9_relat_1(A_64, B_65), A_63) | ~v1_relat_1(k8_relat_1(A_63, A_64)) | ~v1_relat_1(A_64))), inference(resolution, [status(thm)], [c_4, c_586])).
% 2.81/1.38  tff(c_602, plain, (![A_66, B_67, B_68]: (k9_relat_1(k8_relat_1(A_66, B_67), B_68)=k3_xboole_0(k9_relat_1(B_67, B_68), A_66) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_6, c_596])).
% 2.81/1.38  tff(c_14, plain, (k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.38  tff(c_608, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_602, c_14])).
% 2.81/1.38  tff(c_618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_2, c_608])).
% 2.81/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.38  
% 2.81/1.38  Inference rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Ref     : 0
% 2.81/1.38  #Sup     : 167
% 2.81/1.38  #Fact    : 0
% 2.81/1.38  #Define  : 0
% 2.81/1.38  #Split   : 0
% 2.81/1.38  #Chain   : 0
% 2.81/1.38  #Close   : 0
% 2.81/1.38  
% 2.81/1.38  Ordering : KBO
% 2.81/1.38  
% 2.81/1.38  Simplification rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Subsume      : 20
% 2.81/1.38  #Demod        : 2
% 2.81/1.38  #Tautology    : 39
% 2.81/1.38  #SimpNegUnit  : 0
% 2.81/1.38  #BackRed      : 0
% 2.81/1.38  
% 2.81/1.38  #Partial instantiations: 0
% 2.81/1.38  #Strategies tried      : 1
% 2.81/1.38  
% 2.81/1.38  Timing (in seconds)
% 2.81/1.38  ----------------------
% 2.81/1.38  Preprocessing        : 0.28
% 2.81/1.38  Parsing              : 0.16
% 2.81/1.38  CNF conversion       : 0.02
% 2.81/1.38  Main loop            : 0.33
% 2.81/1.38  Inferencing          : 0.14
% 2.81/1.38  Reduction            : 0.09
% 2.81/1.38  Demodulation         : 0.07
% 2.81/1.38  BG Simplification    : 0.03
% 2.81/1.38  Subsumption          : 0.06
% 2.81/1.39  Abstraction          : 0.02
% 2.81/1.39  MUC search           : 0.00
% 2.81/1.39  Cooper               : 0.00
% 2.81/1.39  Total                : 0.64
% 2.81/1.39  Index Insertion      : 0.00
% 2.81/1.39  Index Deletion       : 0.00
% 2.81/1.39  Index Matching       : 0.00
% 2.81/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
