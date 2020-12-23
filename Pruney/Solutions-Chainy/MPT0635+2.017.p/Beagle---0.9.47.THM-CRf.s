%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:22 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   40 (  49 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  81 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_34,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_59,plain,(
    ! [D_19,B_20,A_21] :
      ( r2_hidden(D_19,B_20)
      | ~ r2_hidden(D_19,k3_xboole_0(A_21,B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_63,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_30,plain,(
    ! [B_14,A_13] :
      ( k1_funct_1(k6_relat_1(B_14),A_13) = A_13
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [A_8] : v1_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_167,plain,(
    ! [B_43,C_44,A_45] :
      ( k1_funct_1(k5_relat_1(B_43,C_44),A_45) = k1_funct_1(C_44,k1_funct_1(B_43,A_45))
      | ~ r2_hidden(A_45,k1_relat_1(B_43))
      | ~ v1_funct_1(C_44)
      | ~ v1_relat_1(C_44)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_189,plain,(
    ! [A_7,C_44,A_45] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_7),C_44),A_45) = k1_funct_1(C_44,k1_funct_1(k6_relat_1(A_7),A_45))
      | ~ r2_hidden(A_45,A_7)
      | ~ v1_funct_1(C_44)
      | ~ v1_relat_1(C_44)
      | ~ v1_funct_1(k6_relat_1(A_7))
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_167])).

tff(c_404,plain,(
    ! [A_69,C_70,A_71] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_69),C_70),A_71) = k1_funct_1(C_70,k1_funct_1(k6_relat_1(A_69),A_71))
      | ~ r2_hidden(A_71,A_69)
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_189])).

tff(c_32,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_410,plain,
    ( k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_32])).

tff(c_416,plain,(
    k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_63,c_410])).

tff(c_420,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_416])).

tff(c_424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:19:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.46  
% 2.57/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.47  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.57/1.47  
% 2.57/1.47  %Foreground sorts:
% 2.57/1.47  
% 2.57/1.47  
% 2.57/1.47  %Background operators:
% 2.57/1.47  
% 2.57/1.47  
% 2.57/1.47  %Foreground operators:
% 2.57/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.57/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.57/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.57/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.57/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.57/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.57/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.47  
% 2.57/1.48  tff(f_68, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 2.57/1.48  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.57/1.48  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_1)).
% 2.57/1.48  tff(f_42, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.57/1.48  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.57/1.48  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 2.57/1.48  tff(c_34, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.57/1.48  tff(c_59, plain, (![D_19, B_20, A_21]: (r2_hidden(D_19, B_20) | ~r2_hidden(D_19, k3_xboole_0(A_21, B_20)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.57/1.48  tff(c_63, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_59])).
% 2.57/1.48  tff(c_30, plain, (![B_14, A_13]: (k1_funct_1(k6_relat_1(B_14), A_13)=A_13 | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.57/1.48  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.57/1.48  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.57/1.48  tff(c_24, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.57/1.48  tff(c_26, plain, (![A_8]: (v1_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.57/1.48  tff(c_20, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.57/1.48  tff(c_167, plain, (![B_43, C_44, A_45]: (k1_funct_1(k5_relat_1(B_43, C_44), A_45)=k1_funct_1(C_44, k1_funct_1(B_43, A_45)) | ~r2_hidden(A_45, k1_relat_1(B_43)) | ~v1_funct_1(C_44) | ~v1_relat_1(C_44) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.48  tff(c_189, plain, (![A_7, C_44, A_45]: (k1_funct_1(k5_relat_1(k6_relat_1(A_7), C_44), A_45)=k1_funct_1(C_44, k1_funct_1(k6_relat_1(A_7), A_45)) | ~r2_hidden(A_45, A_7) | ~v1_funct_1(C_44) | ~v1_relat_1(C_44) | ~v1_funct_1(k6_relat_1(A_7)) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_167])).
% 2.57/1.48  tff(c_404, plain, (![A_69, C_70, A_71]: (k1_funct_1(k5_relat_1(k6_relat_1(A_69), C_70), A_71)=k1_funct_1(C_70, k1_funct_1(k6_relat_1(A_69), A_71)) | ~r2_hidden(A_71, A_69) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_189])).
% 2.57/1.48  tff(c_32, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.57/1.48  tff(c_410, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_404, c_32])).
% 2.57/1.48  tff(c_416, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_63, c_410])).
% 2.57/1.48  tff(c_420, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_416])).
% 2.57/1.48  tff(c_424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_420])).
% 2.57/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.48  
% 2.57/1.48  Inference rules
% 2.57/1.48  ----------------------
% 2.57/1.48  #Ref     : 0
% 2.57/1.48  #Sup     : 81
% 2.57/1.48  #Fact    : 0
% 2.57/1.48  #Define  : 0
% 2.57/1.48  #Split   : 0
% 2.57/1.48  #Chain   : 0
% 2.57/1.48  #Close   : 0
% 2.57/1.48  
% 2.57/1.48  Ordering : KBO
% 2.57/1.48  
% 2.57/1.48  Simplification rules
% 2.57/1.48  ----------------------
% 2.57/1.48  #Subsume      : 13
% 2.57/1.48  #Demod        : 34
% 2.57/1.48  #Tautology    : 19
% 2.57/1.48  #SimpNegUnit  : 0
% 2.57/1.48  #BackRed      : 0
% 2.57/1.48  
% 2.57/1.48  #Partial instantiations: 0
% 2.57/1.48  #Strategies tried      : 1
% 2.57/1.48  
% 2.57/1.48  Timing (in seconds)
% 2.57/1.48  ----------------------
% 2.57/1.48  Preprocessing        : 0.41
% 2.57/1.48  Parsing              : 0.23
% 2.57/1.48  CNF conversion       : 0.03
% 2.57/1.48  Main loop            : 0.29
% 2.57/1.48  Inferencing          : 0.12
% 2.57/1.48  Reduction            : 0.07
% 2.57/1.48  Demodulation         : 0.05
% 2.57/1.48  BG Simplification    : 0.02
% 2.57/1.48  Subsumption          : 0.06
% 2.57/1.48  Abstraction          : 0.02
% 2.57/1.48  MUC search           : 0.00
% 2.57/1.48  Cooper               : 0.00
% 2.57/1.48  Total                : 0.73
% 2.57/1.48  Index Insertion      : 0.00
% 2.57/1.48  Index Deletion       : 0.00
% 2.57/1.48  Index Matching       : 0.00
% 2.57/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
