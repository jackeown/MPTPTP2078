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
% DateTime   : Thu Dec  3 10:05:49 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  66 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_35,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_52,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_22,plain,(
    ! [A_15] : v1_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_22])).

tff(c_10,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53,plain,(
    ! [A_21,B_22] :
      ( r2_hidden('#skF_2'(A_21,B_22),k1_relat_1(B_22))
      | v5_funct_1(B_22,A_21)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_59,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_2'(A_21,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_21)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_63,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_2'(A_23,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_59])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_71,plain,(
    ! [A_26] :
      ( v5_funct_1(k1_xboole_0,A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_24,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_74,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_24])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:10:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.22  
% 1.85/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.22  %$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.85/1.22  
% 1.85/1.22  %Foreground sorts:
% 1.85/1.22  
% 1.85/1.22  
% 1.85/1.22  %Background operators:
% 1.85/1.22  
% 1.85/1.22  
% 1.85/1.22  %Foreground operators:
% 1.85/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.85/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.22  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.85/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.85/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.85/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.85/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.85/1.22  
% 1.98/1.23  tff(f_63, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.98/1.23  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.98/1.23  tff(f_36, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.98/1.23  tff(f_56, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.98/1.23  tff(f_35, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.98/1.23  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.98/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.98/1.23  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.98/1.23  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.98/1.23  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.98/1.23  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.98/1.23  tff(c_44, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.23  tff(c_46, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_44])).
% 1.98/1.23  tff(c_22, plain, (![A_15]: (v1_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.23  tff(c_40, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_22])).
% 1.98/1.23  tff(c_10, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.98/1.23  tff(c_53, plain, (![A_21, B_22]: (r2_hidden('#skF_2'(A_21, B_22), k1_relat_1(B_22)) | v5_funct_1(B_22, A_21) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.98/1.23  tff(c_59, plain, (![A_21]: (r2_hidden('#skF_2'(A_21, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_21) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(superposition, [status(thm), theory('equality')], [c_10, c_53])).
% 1.98/1.23  tff(c_63, plain, (![A_23]: (r2_hidden('#skF_2'(A_23, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_59])).
% 1.98/1.23  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.23  tff(c_66, plain, (![A_23]: (~v1_xboole_0(k1_xboole_0) | v5_funct_1(k1_xboole_0, A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(resolution, [status(thm)], [c_63, c_2])).
% 1.98/1.23  tff(c_71, plain, (![A_26]: (v5_funct_1(k1_xboole_0, A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_66])).
% 1.98/1.23  tff(c_24, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.98/1.23  tff(c_74, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_24])).
% 1.98/1.23  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_74])).
% 1.98/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  Inference rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Ref     : 0
% 1.98/1.23  #Sup     : 13
% 1.98/1.23  #Fact    : 0
% 1.98/1.23  #Define  : 0
% 1.98/1.23  #Split   : 0
% 1.98/1.23  #Chain   : 0
% 1.98/1.23  #Close   : 0
% 1.98/1.23  
% 1.98/1.23  Ordering : KBO
% 1.98/1.23  
% 1.98/1.23  Simplification rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Subsume      : 1
% 1.98/1.23  #Demod        : 5
% 1.98/1.23  #Tautology    : 7
% 1.98/1.23  #SimpNegUnit  : 0
% 1.98/1.23  #BackRed      : 0
% 1.98/1.23  
% 1.98/1.23  #Partial instantiations: 0
% 1.98/1.23  #Strategies tried      : 1
% 1.98/1.23  
% 1.98/1.23  Timing (in seconds)
% 1.98/1.23  ----------------------
% 1.98/1.24  Preprocessing        : 0.28
% 1.98/1.24  Parsing              : 0.16
% 1.98/1.24  CNF conversion       : 0.02
% 1.98/1.24  Main loop            : 0.13
% 1.98/1.24  Inferencing          : 0.06
% 1.98/1.24  Reduction            : 0.04
% 1.98/1.24  Demodulation         : 0.03
% 1.98/1.24  BG Simplification    : 0.01
% 1.98/1.24  Subsumption          : 0.01
% 1.98/1.24  Abstraction          : 0.00
% 1.98/1.24  MUC search           : 0.00
% 1.98/1.24  Cooper               : 0.00
% 1.98/1.24  Total                : 0.44
% 1.98/1.24  Index Insertion      : 0.00
% 1.98/1.24  Index Deletion       : 0.00
% 1.98/1.24  Index Matching       : 0.00
% 1.98/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
