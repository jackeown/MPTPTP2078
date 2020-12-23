%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:14 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   42 (  47 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 (  75 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [B_26,A_27] :
      ( k5_relat_1(B_26,k6_relat_1(A_27)) = k8_relat_1(A_27,B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k5_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [A_27,B_26] :
      ( v1_relat_1(k8_relat_1(A_27,B_26))
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_4])).

tff(c_71,plain,(
    ! [A_27,B_26] :
      ( v1_relat_1(k8_relat_1(A_27,B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_16,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k5_relat_1(B_8,k6_relat_1(A_7)) = k8_relat_1(A_7,B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_105,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_35,B_36)),k2_relat_1(B_36))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_115,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_7,B_8)),k2_relat_1(k6_relat_1(A_7)))
      | ~ v1_relat_1(k6_relat_1(A_7))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_105])).

tff(c_126,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_37,B_38)),A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16,c_115])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_43,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(A_20,C_21)
      | ~ r1_tarski(B_22,C_21)
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_20] :
      ( r1_tarski(A_20,'#skF_2')
      | ~ r1_tarski(A_20,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_74,plain,(
    ! [A_30,B_31] :
      ( k8_relat_1(A_30,B_31) = B_31
      | ~ r1_tarski(k2_relat_1(B_31),A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_82,plain,(
    ! [B_31] :
      ( k8_relat_1('#skF_2',B_31) = B_31
      | ~ v1_relat_1(B_31)
      | ~ r1_tarski(k2_relat_1(B_31),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_74])).

tff(c_632,plain,(
    ! [B_75] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_75)) = k8_relat_1('#skF_1',B_75)
      | ~ v1_relat_1(k8_relat_1('#skF_1',B_75))
      | ~ v1_relat_1(B_75) ) ),
    inference(resolution,[status(thm)],[c_126,c_82])).

tff(c_652,plain,(
    ! [B_76] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_76)) = k8_relat_1('#skF_1',B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_71,c_632])).

tff(c_18,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_679,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_18])).

tff(c_700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:47:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.42  
% 2.51/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.42  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.51/1.42  
% 2.51/1.42  %Foreground sorts:
% 2.51/1.42  
% 2.51/1.42  
% 2.51/1.42  %Background operators:
% 2.51/1.42  
% 2.51/1.42  
% 2.51/1.42  %Foreground operators:
% 2.51/1.42  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.51/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.51/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.51/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.42  
% 2.51/1.43  tff(f_67, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 2.51/1.43  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.51/1.43  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.51/1.43  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.51/1.43  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.51/1.43  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.51/1.43  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.51/1.43  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.51/1.43  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.51/1.43  tff(c_6, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.51/1.43  tff(c_59, plain, (![B_26, A_27]: (k5_relat_1(B_26, k6_relat_1(A_27))=k8_relat_1(A_27, B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.51/1.43  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k5_relat_1(A_4, B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.43  tff(c_65, plain, (![A_27, B_26]: (v1_relat_1(k8_relat_1(A_27, B_26)) | ~v1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(B_26) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_59, c_4])).
% 2.51/1.43  tff(c_71, plain, (![A_27, B_26]: (v1_relat_1(k8_relat_1(A_27, B_26)) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_65])).
% 2.51/1.43  tff(c_16, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.43  tff(c_8, plain, (![B_8, A_7]: (k5_relat_1(B_8, k6_relat_1(A_7))=k8_relat_1(A_7, B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.51/1.43  tff(c_105, plain, (![A_35, B_36]: (r1_tarski(k2_relat_1(k5_relat_1(A_35, B_36)), k2_relat_1(B_36)) | ~v1_relat_1(B_36) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.43  tff(c_115, plain, (![A_7, B_8]: (r1_tarski(k2_relat_1(k8_relat_1(A_7, B_8)), k2_relat_1(k6_relat_1(A_7))) | ~v1_relat_1(k6_relat_1(A_7)) | ~v1_relat_1(B_8) | ~v1_relat_1(B_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_105])).
% 2.51/1.43  tff(c_126, plain, (![A_37, B_38]: (r1_tarski(k2_relat_1(k8_relat_1(A_37, B_38)), A_37) | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16, c_115])).
% 2.51/1.43  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.51/1.43  tff(c_43, plain, (![A_20, C_21, B_22]: (r1_tarski(A_20, C_21) | ~r1_tarski(B_22, C_21) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.43  tff(c_46, plain, (![A_20]: (r1_tarski(A_20, '#skF_2') | ~r1_tarski(A_20, '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_43])).
% 2.51/1.43  tff(c_74, plain, (![A_30, B_31]: (k8_relat_1(A_30, B_31)=B_31 | ~r1_tarski(k2_relat_1(B_31), A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.51/1.43  tff(c_82, plain, (![B_31]: (k8_relat_1('#skF_2', B_31)=B_31 | ~v1_relat_1(B_31) | ~r1_tarski(k2_relat_1(B_31), '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_74])).
% 2.51/1.43  tff(c_632, plain, (![B_75]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_75))=k8_relat_1('#skF_1', B_75) | ~v1_relat_1(k8_relat_1('#skF_1', B_75)) | ~v1_relat_1(B_75))), inference(resolution, [status(thm)], [c_126, c_82])).
% 2.51/1.43  tff(c_652, plain, (![B_76]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_76))=k8_relat_1('#skF_1', B_76) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_71, c_632])).
% 2.51/1.43  tff(c_18, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.51/1.43  tff(c_679, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_652, c_18])).
% 2.51/1.43  tff(c_700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_679])).
% 2.51/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.43  
% 2.51/1.43  Inference rules
% 2.51/1.43  ----------------------
% 2.51/1.43  #Ref     : 0
% 2.51/1.43  #Sup     : 157
% 2.51/1.43  #Fact    : 0
% 2.51/1.43  #Define  : 0
% 2.51/1.43  #Split   : 0
% 2.51/1.43  #Chain   : 0
% 2.51/1.43  #Close   : 0
% 2.51/1.43  
% 2.51/1.43  Ordering : KBO
% 2.51/1.43  
% 2.51/1.43  Simplification rules
% 2.51/1.43  ----------------------
% 2.51/1.43  #Subsume      : 31
% 2.51/1.43  #Demod        : 52
% 2.51/1.43  #Tautology    : 42
% 2.51/1.43  #SimpNegUnit  : 0
% 2.51/1.43  #BackRed      : 0
% 2.51/1.43  
% 2.51/1.43  #Partial instantiations: 0
% 2.51/1.43  #Strategies tried      : 1
% 2.51/1.43  
% 2.51/1.43  Timing (in seconds)
% 2.51/1.43  ----------------------
% 2.51/1.44  Preprocessing        : 0.29
% 2.51/1.44  Parsing              : 0.17
% 2.51/1.44  CNF conversion       : 0.02
% 2.51/1.44  Main loop            : 0.33
% 2.51/1.44  Inferencing          : 0.14
% 2.51/1.44  Reduction            : 0.09
% 2.51/1.44  Demodulation         : 0.06
% 2.51/1.44  BG Simplification    : 0.02
% 2.51/1.44  Subsumption          : 0.07
% 2.51/1.44  Abstraction          : 0.02
% 2.51/1.44  MUC search           : 0.00
% 2.51/1.44  Cooper               : 0.00
% 2.51/1.44  Total                : 0.65
% 2.51/1.44  Index Insertion      : 0.00
% 2.51/1.44  Index Deletion       : 0.00
% 2.51/1.44  Index Matching       : 0.00
% 2.51/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
