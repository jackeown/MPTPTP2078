%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:26 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   48 (  78 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_45,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_45])).

tff(c_390,plain,(
    ! [C_37,A_38,B_39] :
      ( k3_xboole_0(k9_relat_1(C_37,A_38),k9_relat_1(C_37,B_39)) = k9_relat_1(C_37,k3_xboole_0(A_38,B_39))
      | ~ v2_funct_1(C_37)
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k3_xboole_0(A_18,B_19) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_64,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_20])).

tff(c_403,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_64])).

tff(c_414,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_49,c_403])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_236,plain,(
    ! [B_30,A_31] :
      ( k9_relat_1(B_30,A_31) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_30),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_515,plain,(
    ! [B_44,B_45] :
      ( k9_relat_1(B_44,B_45) = k1_xboole_0
      | ~ v1_relat_1(B_44)
      | k3_xboole_0(k1_relat_1(B_44),B_45) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_236])).

tff(c_525,plain,(
    ! [B_46] :
      ( k9_relat_1(B_46,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_515])).

tff(c_528,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_525])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_414,c_528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:02:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.29  
% 2.01/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.30  %$ r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.01/1.30  
% 2.01/1.30  %Foreground sorts:
% 2.01/1.30  
% 2.01/1.30  
% 2.01/1.30  %Background operators:
% 2.01/1.30  
% 2.01/1.30  
% 2.01/1.30  %Foreground operators:
% 2.01/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.01/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.01/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.01/1.30  
% 2.30/1.31  tff(f_62, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_funct_1)).
% 2.30/1.31  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.30/1.31  tff(f_51, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 2.30/1.31  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.30/1.31  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.30/1.31  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.30/1.31  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.30/1.31  tff(c_22, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.30/1.31  tff(c_24, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.30/1.31  tff(c_45, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.31  tff(c_49, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_45])).
% 2.30/1.31  tff(c_390, plain, (![C_37, A_38, B_39]: (k3_xboole_0(k9_relat_1(C_37, A_38), k9_relat_1(C_37, B_39))=k9_relat_1(C_37, k3_xboole_0(A_38, B_39)) | ~v2_funct_1(C_37) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.30/1.31  tff(c_54, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k3_xboole_0(A_18, B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.31  tff(c_20, plain, (~r1_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.30/1.31  tff(c_64, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_20])).
% 2.30/1.31  tff(c_403, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_390, c_64])).
% 2.30/1.31  tff(c_414, plain, (k9_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_49, c_403])).
% 2.30/1.31  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.31  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.31  tff(c_236, plain, (![B_30, A_31]: (k9_relat_1(B_30, A_31)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_30), A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.30/1.31  tff(c_515, plain, (![B_44, B_45]: (k9_relat_1(B_44, B_45)=k1_xboole_0 | ~v1_relat_1(B_44) | k3_xboole_0(k1_relat_1(B_44), B_45)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_236])).
% 2.30/1.31  tff(c_525, plain, (![B_46]: (k9_relat_1(B_46, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_6, c_515])).
% 2.30/1.31  tff(c_528, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_525])).
% 2.30/1.31  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_414, c_528])).
% 2.30/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.31  
% 2.30/1.31  Inference rules
% 2.30/1.31  ----------------------
% 2.30/1.31  #Ref     : 0
% 2.30/1.31  #Sup     : 119
% 2.30/1.31  #Fact    : 0
% 2.30/1.31  #Define  : 0
% 2.30/1.31  #Split   : 0
% 2.30/1.31  #Chain   : 0
% 2.30/1.31  #Close   : 0
% 2.30/1.31  
% 2.30/1.31  Ordering : KBO
% 2.30/1.31  
% 2.30/1.31  Simplification rules
% 2.30/1.31  ----------------------
% 2.30/1.31  #Subsume      : 1
% 2.30/1.31  #Demod        : 88
% 2.30/1.31  #Tautology    : 88
% 2.30/1.31  #SimpNegUnit  : 1
% 2.30/1.31  #BackRed      : 4
% 2.30/1.31  
% 2.30/1.31  #Partial instantiations: 0
% 2.30/1.31  #Strategies tried      : 1
% 2.30/1.31  
% 2.30/1.31  Timing (in seconds)
% 2.30/1.31  ----------------------
% 2.30/1.31  Preprocessing        : 0.26
% 2.30/1.31  Parsing              : 0.14
% 2.30/1.31  CNF conversion       : 0.02
% 2.30/1.31  Main loop            : 0.28
% 2.30/1.31  Inferencing          : 0.12
% 2.30/1.31  Reduction            : 0.09
% 2.30/1.31  Demodulation         : 0.07
% 2.30/1.31  BG Simplification    : 0.01
% 2.30/1.31  Subsumption          : 0.04
% 2.30/1.31  Abstraction          : 0.01
% 2.30/1.31  MUC search           : 0.00
% 2.30/1.31  Cooper               : 0.00
% 2.30/1.31  Total                : 0.57
% 2.30/1.31  Index Insertion      : 0.00
% 2.30/1.31  Index Deletion       : 0.00
% 2.30/1.31  Index Matching       : 0.00
% 2.30/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
