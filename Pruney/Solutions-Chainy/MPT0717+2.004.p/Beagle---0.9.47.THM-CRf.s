%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:41 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  71 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A)
          & v1_funct_1(B) )
       => ! [C] :
            ( r2_hidden(C,k1_relat_1(B))
           => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_78,plain,(
    ! [B_34,A_35] :
      ( r2_hidden(k1_funct_1(B_34,A_35),k2_relat_1(B_34))
      | ~ r2_hidden(A_35,k1_relat_1(B_34))
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,(
    ! [B_22,A_23] :
      ( r1_tarski(k2_relat_1(B_22),A_23)
      | ~ v5_relat_1(B_22,A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [B_29,A_30] :
      ( k3_xboole_0(k2_relat_1(B_29),A_30) = k2_relat_1(B_29)
      | ~ v5_relat_1(B_29,A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_40,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [D_6,A_30,B_29] :
      ( r2_hidden(D_6,A_30)
      | ~ r2_hidden(D_6,k2_relat_1(B_29))
      | ~ v5_relat_1(B_29,A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_4])).

tff(c_223,plain,(
    ! [B_54,A_55,A_56] :
      ( r2_hidden(k1_funct_1(B_54,A_55),A_56)
      | ~ v5_relat_1(B_54,A_56)
      | ~ r2_hidden(A_55,k1_relat_1(B_54))
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_78,c_71])).

tff(c_28,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_237,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_223,c_28])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_34,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.21  
% 2.02/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.21  %$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.02/1.21  
% 2.02/1.21  %Foreground sorts:
% 2.02/1.21  
% 2.02/1.21  
% 2.02/1.21  %Background operators:
% 2.02/1.21  
% 2.02/1.21  
% 2.02/1.21  %Foreground operators:
% 2.02/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.02/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.21  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.02/1.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.02/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.21  
% 2.13/1.22  tff(f_64, negated_conjecture, ~(![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.13/1.22  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.13/1.22  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.13/1.22  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.13/1.22  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.13/1.22  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.13/1.22  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.13/1.22  tff(c_30, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.13/1.22  tff(c_34, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.13/1.22  tff(c_78, plain, (![B_34, A_35]: (r2_hidden(k1_funct_1(B_34, A_35), k2_relat_1(B_34)) | ~r2_hidden(A_35, k1_relat_1(B_34)) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.13/1.22  tff(c_40, plain, (![B_22, A_23]: (r1_tarski(k2_relat_1(B_22), A_23) | ~v5_relat_1(B_22, A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.13/1.22  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.13/1.22  tff(c_59, plain, (![B_29, A_30]: (k3_xboole_0(k2_relat_1(B_29), A_30)=k2_relat_1(B_29) | ~v5_relat_1(B_29, A_30) | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_40, c_20])).
% 2.13/1.22  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.13/1.22  tff(c_71, plain, (![D_6, A_30, B_29]: (r2_hidden(D_6, A_30) | ~r2_hidden(D_6, k2_relat_1(B_29)) | ~v5_relat_1(B_29, A_30) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_59, c_4])).
% 2.13/1.22  tff(c_223, plain, (![B_54, A_55, A_56]: (r2_hidden(k1_funct_1(B_54, A_55), A_56) | ~v5_relat_1(B_54, A_56) | ~r2_hidden(A_55, k1_relat_1(B_54)) | ~v1_funct_1(B_54) | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_78, c_71])).
% 2.13/1.22  tff(c_28, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.13/1.22  tff(c_237, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_223, c_28])).
% 2.13/1.22  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_34, c_237])).
% 2.13/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.22  
% 2.13/1.22  Inference rules
% 2.13/1.22  ----------------------
% 2.13/1.22  #Ref     : 0
% 2.13/1.22  #Sup     : 43
% 2.13/1.22  #Fact    : 0
% 2.13/1.22  #Define  : 0
% 2.13/1.22  #Split   : 0
% 2.13/1.22  #Chain   : 0
% 2.13/1.22  #Close   : 0
% 2.13/1.22  
% 2.13/1.22  Ordering : KBO
% 2.13/1.22  
% 2.13/1.22  Simplification rules
% 2.13/1.22  ----------------------
% 2.13/1.22  #Subsume      : 3
% 2.13/1.22  #Demod        : 4
% 2.13/1.22  #Tautology    : 7
% 2.13/1.22  #SimpNegUnit  : 0
% 2.13/1.22  #BackRed      : 0
% 2.13/1.22  
% 2.13/1.22  #Partial instantiations: 0
% 2.13/1.22  #Strategies tried      : 1
% 2.13/1.22  
% 2.13/1.22  Timing (in seconds)
% 2.13/1.22  ----------------------
% 2.13/1.22  Preprocessing        : 0.28
% 2.13/1.23  Parsing              : 0.15
% 2.13/1.23  CNF conversion       : 0.02
% 2.13/1.23  Main loop            : 0.20
% 2.13/1.23  Inferencing          : 0.08
% 2.13/1.23  Reduction            : 0.04
% 2.13/1.23  Demodulation         : 0.03
% 2.13/1.23  BG Simplification    : 0.02
% 2.13/1.23  Subsumption          : 0.05
% 2.13/1.23  Abstraction          : 0.01
% 2.13/1.23  MUC search           : 0.00
% 2.13/1.23  Cooper               : 0.00
% 2.13/1.23  Total                : 0.50
% 2.13/1.23  Index Insertion      : 0.00
% 2.13/1.23  Index Deletion       : 0.00
% 2.13/1.23  Index Matching       : 0.00
% 2.13/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
