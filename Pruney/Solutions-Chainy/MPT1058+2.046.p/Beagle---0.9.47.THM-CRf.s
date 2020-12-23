%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:28 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   47 (  71 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_40,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_116,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_226,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(k3_xboole_0(A_57,C_58),k3_xboole_0(B_59,C_58))
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_243,plain,(
    ! [B_2,B_59] :
      ( r1_tarski(B_2,k3_xboole_0(B_59,B_2))
      | ~ r1_tarski(B_2,B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_226])).

tff(c_118,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_129,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_118])).

tff(c_734,plain,(
    ! [A_87,B_88,C_89] : r1_tarski(k2_xboole_0(k3_xboole_0(A_87,B_88),k3_xboole_0(A_87,C_89)),k2_xboole_0(B_88,C_89)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_770,plain,(
    ! [A_87,B_88] : r1_tarski(k3_xboole_0(A_87,B_88),k2_xboole_0(B_88,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_734])).

tff(c_794,plain,(
    ! [A_90,B_91] : r1_tarski(k3_xboole_0(A_90,B_91),B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_770])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1823,plain,(
    ! [A_117,B_118] :
      ( k3_xboole_0(A_117,B_118) = B_118
      | ~ r1_tarski(B_118,k3_xboole_0(A_117,B_118)) ) ),
    inference(resolution,[status(thm)],[c_794,c_2])).

tff(c_1868,plain,(
    ! [B_119,B_120] :
      ( k3_xboole_0(B_119,B_120) = B_120
      | ~ r1_tarski(B_120,B_119) ) ),
    inference(resolution,[status(thm)],[c_243,c_1823])).

tff(c_1939,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1868])).

tff(c_36,plain,(
    ! [A_26,C_28,B_27] :
      ( k3_xboole_0(A_26,k10_relat_1(C_28,B_27)) = k10_relat_1(k7_relat_1(C_28,A_26),B_27)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1958,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1939,c_36])).

tff(c_2003,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1958])).

tff(c_2005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.99  
% 4.14/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.99  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.14/1.99  
% 4.14/1.99  %Foreground sorts:
% 4.14/1.99  
% 4.14/1.99  
% 4.14/1.99  %Background operators:
% 4.14/1.99  
% 4.14/1.99  
% 4.14/1.99  %Foreground operators:
% 4.14/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.14/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.14/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.14/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.14/1.99  tff('#skF_2', type, '#skF_2': $i).
% 4.14/1.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.14/1.99  tff('#skF_3', type, '#skF_3': $i).
% 4.14/1.99  tff('#skF_1', type, '#skF_1': $i).
% 4.14/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.99  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.14/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.14/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.14/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.14/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.14/1.99  
% 4.14/2.01  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 4.14/2.01  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.14/2.01  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.14/2.01  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_xboole_1)).
% 4.14/2.01  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.14/2.01  tff(f_47, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 4.14/2.01  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 4.14/2.01  tff(c_40, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.14/2.01  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.14/2.01  tff(c_42, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.14/2.01  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.14/2.01  tff(c_105, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.14/2.01  tff(c_116, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_105])).
% 4.14/2.01  tff(c_226, plain, (![A_57, C_58, B_59]: (r1_tarski(k3_xboole_0(A_57, C_58), k3_xboole_0(B_59, C_58)) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.14/2.01  tff(c_243, plain, (![B_2, B_59]: (r1_tarski(B_2, k3_xboole_0(B_59, B_2)) | ~r1_tarski(B_2, B_59))), inference(superposition, [status(thm), theory('equality')], [c_116, c_226])).
% 4.14/2.01  tff(c_118, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.14/2.01  tff(c_129, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_118])).
% 4.14/2.01  tff(c_734, plain, (![A_87, B_88, C_89]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_87, B_88), k3_xboole_0(A_87, C_89)), k2_xboole_0(B_88, C_89)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.14/2.01  tff(c_770, plain, (![A_87, B_88]: (r1_tarski(k3_xboole_0(A_87, B_88), k2_xboole_0(B_88, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_734])).
% 4.14/2.01  tff(c_794, plain, (![A_90, B_91]: (r1_tarski(k3_xboole_0(A_90, B_91), B_91))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_770])).
% 4.14/2.01  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.14/2.01  tff(c_1823, plain, (![A_117, B_118]: (k3_xboole_0(A_117, B_118)=B_118 | ~r1_tarski(B_118, k3_xboole_0(A_117, B_118)))), inference(resolution, [status(thm)], [c_794, c_2])).
% 4.14/2.01  tff(c_1868, plain, (![B_119, B_120]: (k3_xboole_0(B_119, B_120)=B_120 | ~r1_tarski(B_120, B_119))), inference(resolution, [status(thm)], [c_243, c_1823])).
% 4.14/2.01  tff(c_1939, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_1868])).
% 4.14/2.01  tff(c_36, plain, (![A_26, C_28, B_27]: (k3_xboole_0(A_26, k10_relat_1(C_28, B_27))=k10_relat_1(k7_relat_1(C_28, A_26), B_27) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.14/2.01  tff(c_1958, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1939, c_36])).
% 4.14/2.01  tff(c_2003, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1958])).
% 4.14/2.01  tff(c_2005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_2003])).
% 4.14/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/2.01  
% 4.14/2.01  Inference rules
% 4.14/2.01  ----------------------
% 4.14/2.01  #Ref     : 0
% 4.14/2.01  #Sup     : 479
% 4.14/2.01  #Fact    : 0
% 4.14/2.01  #Define  : 0
% 4.14/2.01  #Split   : 1
% 4.14/2.01  #Chain   : 0
% 4.14/2.01  #Close   : 0
% 4.14/2.01  
% 4.14/2.01  Ordering : KBO
% 4.14/2.01  
% 4.14/2.01  Simplification rules
% 4.14/2.01  ----------------------
% 4.14/2.01  #Subsume      : 25
% 4.14/2.01  #Demod        : 353
% 4.14/2.01  #Tautology    : 277
% 4.14/2.01  #SimpNegUnit  : 2
% 4.14/2.01  #BackRed      : 3
% 4.14/2.01  
% 4.14/2.01  #Partial instantiations: 0
% 4.14/2.01  #Strategies tried      : 1
% 4.14/2.01  
% 4.14/2.01  Timing (in seconds)
% 4.14/2.01  ----------------------
% 4.14/2.01  Preprocessing        : 0.51
% 4.14/2.01  Parsing              : 0.27
% 4.14/2.01  CNF conversion       : 0.03
% 4.14/2.01  Main loop            : 0.66
% 4.14/2.01  Inferencing          : 0.22
% 4.14/2.01  Reduction            : 0.23
% 4.14/2.01  Demodulation         : 0.18
% 4.14/2.01  BG Simplification    : 0.03
% 4.14/2.01  Subsumption          : 0.13
% 4.14/2.01  Abstraction          : 0.04
% 4.14/2.01  MUC search           : 0.00
% 4.14/2.01  Cooper               : 0.00
% 4.14/2.01  Total                : 1.21
% 4.14/2.01  Index Insertion      : 0.00
% 4.14/2.01  Index Deletion       : 0.00
% 4.14/2.01  Index Matching       : 0.00
% 4.14/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
