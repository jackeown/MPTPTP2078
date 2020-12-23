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
% DateTime   : Thu Dec  3 10:04:26 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   46 (  80 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_51,plain,(
    ! [A_17] :
      ( k7_relat_1(A_17,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_51])).

tff(c_217,plain,(
    ! [B_33,A_34] :
      ( k2_relat_1(k7_relat_1(B_33,A_34)) = k9_relat_1(B_33,A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_226,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_217])).

tff(c_230,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_20,c_226])).

tff(c_30,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_82,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_82])).

tff(c_297,plain,(
    ! [C_37,A_38,B_39] :
      ( k3_xboole_0(k9_relat_1(C_37,A_38),k9_relat_1(C_37,B_39)) = k9_relat_1(C_37,k3_xboole_0(A_38,B_39))
      | ~ v2_funct_1(C_37)
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_92,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_104,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_26])).

tff(c_307,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_104])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_230,c_91,c_307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.28  
% 2.21/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.28  %$ r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.21/1.28  
% 2.21/1.28  %Foreground sorts:
% 2.21/1.28  
% 2.21/1.28  
% 2.21/1.28  %Background operators:
% 2.21/1.28  
% 2.21/1.28  
% 2.21/1.28  %Foreground operators:
% 2.21/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.21/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.21/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.21/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.28  
% 2.21/1.29  tff(f_69, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_funct_1)).
% 2.21/1.29  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.21/1.29  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 2.21/1.29  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.21/1.29  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.21/1.29  tff(f_58, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 2.21/1.29  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.29  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.29  tff(c_28, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.29  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.21/1.29  tff(c_51, plain, (![A_17]: (k7_relat_1(A_17, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.29  tff(c_55, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_51])).
% 2.21/1.29  tff(c_217, plain, (![B_33, A_34]: (k2_relat_1(k7_relat_1(B_33, A_34))=k9_relat_1(B_33, A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.29  tff(c_226, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_55, c_217])).
% 2.21/1.29  tff(c_230, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_20, c_226])).
% 2.21/1.29  tff(c_30, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.29  tff(c_82, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.29  tff(c_91, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_82])).
% 2.21/1.29  tff(c_297, plain, (![C_37, A_38, B_39]: (k3_xboole_0(k9_relat_1(C_37, A_38), k9_relat_1(C_37, B_39))=k9_relat_1(C_37, k3_xboole_0(A_38, B_39)) | ~v2_funct_1(C_37) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.21/1.29  tff(c_92, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.29  tff(c_26, plain, (~r1_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.29  tff(c_104, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_92, c_26])).
% 2.21/1.29  tff(c_307, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_297, c_104])).
% 2.21/1.29  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_230, c_91, c_307])).
% 2.21/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.29  
% 2.21/1.29  Inference rules
% 2.21/1.29  ----------------------
% 2.21/1.29  #Ref     : 0
% 2.21/1.29  #Sup     : 74
% 2.21/1.29  #Fact    : 0
% 2.21/1.29  #Define  : 0
% 2.21/1.29  #Split   : 0
% 2.21/1.29  #Chain   : 0
% 2.21/1.29  #Close   : 0
% 2.21/1.29  
% 2.21/1.29  Ordering : KBO
% 2.21/1.29  
% 2.21/1.29  Simplification rules
% 2.21/1.29  ----------------------
% 2.21/1.29  #Subsume      : 1
% 2.21/1.29  #Demod        : 25
% 2.21/1.29  #Tautology    : 52
% 2.21/1.29  #SimpNegUnit  : 0
% 2.21/1.29  #BackRed      : 0
% 2.21/1.29  
% 2.21/1.29  #Partial instantiations: 0
% 2.21/1.29  #Strategies tried      : 1
% 2.21/1.29  
% 2.21/1.29  Timing (in seconds)
% 2.21/1.29  ----------------------
% 2.21/1.29  Preprocessing        : 0.30
% 2.21/1.29  Parsing              : 0.17
% 2.21/1.29  CNF conversion       : 0.02
% 2.21/1.30  Main loop            : 0.20
% 2.21/1.30  Inferencing          : 0.09
% 2.21/1.30  Reduction            : 0.06
% 2.21/1.30  Demodulation         : 0.04
% 2.21/1.30  BG Simplification    : 0.01
% 2.21/1.30  Subsumption          : 0.03
% 2.21/1.30  Abstraction          : 0.01
% 2.21/1.30  MUC search           : 0.00
% 2.21/1.30  Cooper               : 0.00
% 2.21/1.30  Total                : 0.53
% 2.21/1.30  Index Insertion      : 0.00
% 2.21/1.30  Index Deletion       : 0.00
% 2.21/1.30  Index Matching       : 0.00
% 2.21/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
