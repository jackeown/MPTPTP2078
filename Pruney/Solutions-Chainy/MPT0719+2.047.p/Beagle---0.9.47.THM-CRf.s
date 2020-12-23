%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:49 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  50 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 (  74 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_48,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_42,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_42])).

tff(c_28,plain,(
    ! [A_22] : v1_funct_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_28])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_162,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_3'(A_57,B_58),k1_relat_1(B_58))
      | v5_funct_1(B_58,A_57)
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_11] :
      ( k10_relat_1(A_11,k2_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_107,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden(k4_tarski(A_46,'#skF_2'(A_46,B_47,C_48)),C_48)
      | ~ r2_hidden(A_46,k10_relat_1(C_48,B_47))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [C_49,A_50,B_51] :
      ( ~ v1_xboole_0(C_49)
      | ~ r2_hidden(A_50,k10_relat_1(C_49,B_51))
      | ~ v1_relat_1(C_49) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_133,plain,(
    ! [A_11,A_50] :
      ( ~ v1_xboole_0(A_11)
      | ~ r2_hidden(A_50,k1_relat_1(A_11))
      | ~ v1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_122])).

tff(c_278,plain,(
    ! [B_87,A_88] :
      ( ~ v1_xboole_0(B_87)
      | v5_funct_1(B_87,A_88)
      | ~ v1_funct_1(B_87)
      | ~ v1_relat_1(B_87)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_162,c_133])).

tff(c_30,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_281,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_278,c_30])).

tff(c_285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_44,c_38,c_6,c_281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.27  
% 2.22/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.27  %$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.22/1.27  
% 2.22/1.27  %Foreground sorts:
% 2.22/1.27  
% 2.22/1.27  
% 2.22/1.27  %Background operators:
% 2.22/1.27  
% 2.22/1.27  
% 2.22/1.27  %Foreground operators:
% 2.22/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.22/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.22/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.22/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.22/1.27  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.22/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.22/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.22/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.22/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.22/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.27  
% 2.22/1.28  tff(f_75, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.22/1.28  tff(f_48, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.22/1.28  tff(f_68, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.22/1.28  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.22/1.28  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.22/1.28  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.22/1.28  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.22/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.22/1.28  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.22/1.28  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.22/1.28  tff(c_18, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.22/1.28  tff(c_42, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.22/1.28  tff(c_44, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_42])).
% 2.22/1.28  tff(c_28, plain, (![A_22]: (v1_funct_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.22/1.28  tff(c_38, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_28])).
% 2.22/1.28  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.28  tff(c_162, plain, (![A_57, B_58]: (r2_hidden('#skF_3'(A_57, B_58), k1_relat_1(B_58)) | v5_funct_1(B_58, A_57) | ~v1_funct_1(B_58) | ~v1_relat_1(B_58) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.22/1.28  tff(c_16, plain, (![A_11]: (k10_relat_1(A_11, k2_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.28  tff(c_107, plain, (![A_46, B_47, C_48]: (r2_hidden(k4_tarski(A_46, '#skF_2'(A_46, B_47, C_48)), C_48) | ~r2_hidden(A_46, k10_relat_1(C_48, B_47)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.28  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.28  tff(c_122, plain, (![C_49, A_50, B_51]: (~v1_xboole_0(C_49) | ~r2_hidden(A_50, k10_relat_1(C_49, B_51)) | ~v1_relat_1(C_49))), inference(resolution, [status(thm)], [c_107, c_2])).
% 2.22/1.28  tff(c_133, plain, (![A_11, A_50]: (~v1_xboole_0(A_11) | ~r2_hidden(A_50, k1_relat_1(A_11)) | ~v1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_16, c_122])).
% 2.22/1.28  tff(c_278, plain, (![B_87, A_88]: (~v1_xboole_0(B_87) | v5_funct_1(B_87, A_88) | ~v1_funct_1(B_87) | ~v1_relat_1(B_87) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(resolution, [status(thm)], [c_162, c_133])).
% 2.22/1.28  tff(c_30, plain, (~v5_funct_1(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.22/1.28  tff(c_281, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_278, c_30])).
% 2.22/1.28  tff(c_285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_44, c_38, c_6, c_281])).
% 2.22/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.28  
% 2.22/1.28  Inference rules
% 2.22/1.28  ----------------------
% 2.22/1.28  #Ref     : 0
% 2.22/1.28  #Sup     : 55
% 2.22/1.28  #Fact    : 0
% 2.22/1.28  #Define  : 0
% 2.22/1.28  #Split   : 0
% 2.22/1.28  #Chain   : 0
% 2.22/1.28  #Close   : 0
% 2.22/1.28  
% 2.22/1.28  Ordering : KBO
% 2.22/1.28  
% 2.22/1.28  Simplification rules
% 2.22/1.28  ----------------------
% 2.22/1.28  #Subsume      : 6
% 2.22/1.28  #Demod        : 5
% 2.22/1.28  #Tautology    : 5
% 2.22/1.28  #SimpNegUnit  : 0
% 2.22/1.28  #BackRed      : 0
% 2.22/1.28  
% 2.22/1.28  #Partial instantiations: 0
% 2.22/1.28  #Strategies tried      : 1
% 2.22/1.28  
% 2.22/1.28  Timing (in seconds)
% 2.22/1.28  ----------------------
% 2.22/1.29  Preprocessing        : 0.29
% 2.22/1.29  Parsing              : 0.16
% 2.22/1.29  CNF conversion       : 0.02
% 2.22/1.29  Main loop            : 0.24
% 2.22/1.29  Inferencing          : 0.10
% 2.22/1.29  Reduction            : 0.06
% 2.22/1.29  Demodulation         : 0.04
% 2.22/1.29  BG Simplification    : 0.01
% 2.22/1.29  Subsumption          : 0.05
% 2.22/1.29  Abstraction          : 0.01
% 2.22/1.29  MUC search           : 0.00
% 2.22/1.29  Cooper               : 0.00
% 2.22/1.29  Total                : 0.55
% 2.22/1.29  Index Insertion      : 0.00
% 2.22/1.29  Index Deletion       : 0.00
% 2.22/1.29  Index Matching       : 0.00
% 2.22/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
