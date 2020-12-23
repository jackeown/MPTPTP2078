%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:32 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  86 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_20,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [A_23] :
      ( k10_relat_1(A_23,k2_relat_1(A_23)) = k1_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [A_6] :
      ( k10_relat_1(k6_relat_1(A_6),A_6) = k1_relat_1(k6_relat_1(A_6))
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_65])).

tff(c_78,plain,(
    ! [A_6] : k10_relat_1(k6_relat_1(A_6),A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_8,c_74])).

tff(c_88,plain,(
    ! [B_25,A_26] :
      ( k7_relat_1(B_25,A_26) = B_25
      | ~ r1_tarski(k1_relat_1(B_25),A_26)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_6,A_26] :
      ( k7_relat_1(k6_relat_1(A_6),A_26) = k6_relat_1(A_6)
      | ~ r1_tarski(A_6,A_26)
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_88])).

tff(c_93,plain,(
    ! [A_6,A_26] :
      ( k7_relat_1(k6_relat_1(A_6),A_26) = k6_relat_1(A_6)
      | ~ r1_tarski(A_6,A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_91])).

tff(c_6,plain,(
    ! [A_5] :
      ( k10_relat_1(A_5,k2_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_103,plain,(
    ! [A_29,C_30,B_31] :
      ( k3_xboole_0(A_29,k10_relat_1(C_30,B_31)) = k10_relat_1(k7_relat_1(C_30,A_29),B_31)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_120,plain,(
    ! [A_32,A_33] :
      ( k10_relat_1(k7_relat_1(A_32,A_33),k2_relat_1(A_32)) = k3_xboole_0(A_33,k1_relat_1(A_32))
      | ~ v1_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_103])).

tff(c_132,plain,(
    ! [A_26,A_6] :
      ( k3_xboole_0(A_26,k1_relat_1(k6_relat_1(A_6))) = k10_relat_1(k6_relat_1(A_6),k2_relat_1(k6_relat_1(A_6)))
      | ~ v1_relat_1(k6_relat_1(A_6))
      | ~ v1_relat_1(k6_relat_1(A_6))
      | ~ r1_tarski(A_6,A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_120])).

tff(c_142,plain,(
    ! [A_34,A_35] :
      ( k3_xboole_0(A_34,A_35) = A_35
      | ~ r1_tarski(A_35,A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_78,c_8,c_10,c_132])).

tff(c_146,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_142])).

tff(c_18,plain,(
    ! [A_10,C_12,B_11] :
      ( k3_xboole_0(A_10,k10_relat_1(C_12,B_11)) = k10_relat_1(k7_relat_1(C_12,A_10),B_11)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_150,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_18])).

tff(c_157,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_150])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.16  
% 1.81/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.17  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.81/1.17  
% 1.81/1.17  %Foreground sorts:
% 1.81/1.17  
% 1.81/1.17  
% 1.81/1.17  %Background operators:
% 1.81/1.17  
% 1.81/1.17  
% 1.81/1.17  %Foreground operators:
% 1.81/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.81/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.81/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.17  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.81/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.81/1.17  
% 1.92/1.18  tff(f_61, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 1.92/1.18  tff(f_47, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.92/1.18  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.92/1.18  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 1.92/1.18  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.92/1.18  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 1.92/1.18  tff(c_20, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.18  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.18  tff(c_22, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.18  tff(c_14, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.18  tff(c_8, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.18  tff(c_10, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.18  tff(c_65, plain, (![A_23]: (k10_relat_1(A_23, k2_relat_1(A_23))=k1_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.18  tff(c_74, plain, (![A_6]: (k10_relat_1(k6_relat_1(A_6), A_6)=k1_relat_1(k6_relat_1(A_6)) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_65])).
% 1.92/1.18  tff(c_78, plain, (![A_6]: (k10_relat_1(k6_relat_1(A_6), A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_8, c_74])).
% 1.92/1.18  tff(c_88, plain, (![B_25, A_26]: (k7_relat_1(B_25, A_26)=B_25 | ~r1_tarski(k1_relat_1(B_25), A_26) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.18  tff(c_91, plain, (![A_6, A_26]: (k7_relat_1(k6_relat_1(A_6), A_26)=k6_relat_1(A_6) | ~r1_tarski(A_6, A_26) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_88])).
% 1.92/1.18  tff(c_93, plain, (![A_6, A_26]: (k7_relat_1(k6_relat_1(A_6), A_26)=k6_relat_1(A_6) | ~r1_tarski(A_6, A_26))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_91])).
% 1.92/1.18  tff(c_6, plain, (![A_5]: (k10_relat_1(A_5, k2_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.18  tff(c_103, plain, (![A_29, C_30, B_31]: (k3_xboole_0(A_29, k10_relat_1(C_30, B_31))=k10_relat_1(k7_relat_1(C_30, A_29), B_31) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.18  tff(c_120, plain, (![A_32, A_33]: (k10_relat_1(k7_relat_1(A_32, A_33), k2_relat_1(A_32))=k3_xboole_0(A_33, k1_relat_1(A_32)) | ~v1_relat_1(A_32) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_6, c_103])).
% 1.92/1.18  tff(c_132, plain, (![A_26, A_6]: (k3_xboole_0(A_26, k1_relat_1(k6_relat_1(A_6)))=k10_relat_1(k6_relat_1(A_6), k2_relat_1(k6_relat_1(A_6))) | ~v1_relat_1(k6_relat_1(A_6)) | ~v1_relat_1(k6_relat_1(A_6)) | ~r1_tarski(A_6, A_26))), inference(superposition, [status(thm), theory('equality')], [c_93, c_120])).
% 1.92/1.18  tff(c_142, plain, (![A_34, A_35]: (k3_xboole_0(A_34, A_35)=A_35 | ~r1_tarski(A_35, A_34))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_78, c_8, c_10, c_132])).
% 1.92/1.18  tff(c_146, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_142])).
% 1.92/1.18  tff(c_18, plain, (![A_10, C_12, B_11]: (k3_xboole_0(A_10, k10_relat_1(C_12, B_11))=k10_relat_1(k7_relat_1(C_12, A_10), B_11) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.18  tff(c_150, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_146, c_18])).
% 1.92/1.18  tff(c_157, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_150])).
% 1.92/1.18  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_157])).
% 1.92/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.18  
% 1.92/1.18  Inference rules
% 1.92/1.18  ----------------------
% 1.92/1.18  #Ref     : 0
% 1.92/1.18  #Sup     : 30
% 1.92/1.18  #Fact    : 0
% 1.92/1.18  #Define  : 0
% 1.92/1.18  #Split   : 0
% 1.92/1.18  #Chain   : 0
% 1.92/1.18  #Close   : 0
% 1.92/1.18  
% 1.92/1.18  Ordering : KBO
% 1.92/1.18  
% 1.92/1.18  Simplification rules
% 1.92/1.18  ----------------------
% 1.92/1.18  #Subsume      : 0
% 1.92/1.18  #Demod        : 13
% 1.92/1.18  #Tautology    : 19
% 1.92/1.18  #SimpNegUnit  : 1
% 1.92/1.18  #BackRed      : 0
% 1.92/1.18  
% 1.92/1.18  #Partial instantiations: 0
% 1.92/1.18  #Strategies tried      : 1
% 1.92/1.18  
% 1.92/1.18  Timing (in seconds)
% 1.92/1.18  ----------------------
% 1.92/1.18  Preprocessing        : 0.29
% 1.92/1.18  Parsing              : 0.16
% 1.92/1.18  CNF conversion       : 0.02
% 1.92/1.18  Main loop            : 0.12
% 1.92/1.18  Inferencing          : 0.05
% 1.92/1.18  Reduction            : 0.04
% 1.92/1.18  Demodulation         : 0.03
% 1.92/1.18  BG Simplification    : 0.01
% 1.92/1.18  Subsumption          : 0.01
% 1.92/1.18  Abstraction          : 0.01
% 1.92/1.18  MUC search           : 0.00
% 1.92/1.18  Cooper               : 0.00
% 1.92/1.18  Total                : 0.44
% 1.92/1.18  Index Insertion      : 0.00
% 1.92/1.18  Index Deletion       : 0.00
% 1.92/1.18  Index Matching       : 0.00
% 1.92/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
