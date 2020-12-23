%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:27 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   35 (  42 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    4
%              Number of atoms          :   42 (  70 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [B_15,A_16] :
      ( k9_relat_1(B_15,A_16) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_15),A_16)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [B_17] :
      ( k9_relat_1(B_17,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_17) ) ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_68,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_24])).

tff(c_82,plain,(
    ! [C_20,A_21,B_22] :
      ( k3_xboole_0(k9_relat_1(C_20,A_21),k9_relat_1(C_20,B_22)) = k9_relat_1(C_20,k3_xboole_0(A_21,B_22))
      | ~ v2_funct_1(C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_52,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_14])).

tff(c_88,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_52])).

tff(c_101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_68,c_31,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:24:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.10  
% 1.69/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.10  %$ r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.69/1.10  
% 1.69/1.10  %Foreground sorts:
% 1.69/1.10  
% 1.69/1.10  
% 1.69/1.10  %Background operators:
% 1.69/1.10  
% 1.69/1.10  
% 1.69/1.10  %Foreground operators:
% 1.69/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.69/1.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.69/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.69/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.69/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.69/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.69/1.10  
% 1.69/1.11  tff(f_56, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_funct_1)).
% 1.69/1.11  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.69/1.11  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 1.69/1.11  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.69/1.11  tff(f_45, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 1.69/1.11  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.69/1.11  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.69/1.11  tff(c_16, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.69/1.11  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.11  tff(c_53, plain, (![B_15, A_16]: (k9_relat_1(B_15, A_16)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_15), A_16) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.69/1.11  tff(c_64, plain, (![B_17]: (k9_relat_1(B_17, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_17))), inference(resolution, [status(thm)], [c_6, c_53])).
% 1.69/1.11  tff(c_68, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_64])).
% 1.69/1.11  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.69/1.11  tff(c_24, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.11  tff(c_31, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_24])).
% 1.69/1.11  tff(c_82, plain, (![C_20, A_21, B_22]: (k3_xboole_0(k9_relat_1(C_20, A_21), k9_relat_1(C_20, B_22))=k9_relat_1(C_20, k3_xboole_0(A_21, B_22)) | ~v2_funct_1(C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.69/1.11  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.11  tff(c_14, plain, (~r1_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.69/1.11  tff(c_52, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_14])).
% 1.69/1.11  tff(c_88, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_82, c_52])).
% 1.69/1.11  tff(c_101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_68, c_31, c_88])).
% 1.69/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.11  
% 1.69/1.11  Inference rules
% 1.69/1.11  ----------------------
% 1.69/1.11  #Ref     : 0
% 1.69/1.11  #Sup     : 20
% 1.69/1.11  #Fact    : 0
% 1.69/1.11  #Define  : 0
% 1.69/1.11  #Split   : 0
% 1.69/1.11  #Chain   : 0
% 1.69/1.11  #Close   : 0
% 1.69/1.11  
% 1.69/1.11  Ordering : KBO
% 1.69/1.11  
% 1.69/1.11  Simplification rules
% 1.69/1.11  ----------------------
% 1.69/1.11  #Subsume      : 0
% 1.69/1.11  #Demod        : 5
% 1.69/1.11  #Tautology    : 9
% 1.69/1.11  #SimpNegUnit  : 0
% 1.69/1.11  #BackRed      : 0
% 1.69/1.11  
% 1.69/1.11  #Partial instantiations: 0
% 1.69/1.11  #Strategies tried      : 1
% 1.69/1.11  
% 1.69/1.11  Timing (in seconds)
% 1.69/1.11  ----------------------
% 1.69/1.12  Preprocessing        : 0.26
% 1.69/1.12  Parsing              : 0.15
% 1.69/1.12  CNF conversion       : 0.02
% 1.69/1.12  Main loop            : 0.11
% 1.69/1.12  Inferencing          : 0.05
% 1.69/1.12  Reduction            : 0.03
% 1.69/1.12  Demodulation         : 0.02
% 1.69/1.12  BG Simplification    : 0.01
% 1.69/1.12  Subsumption          : 0.02
% 1.69/1.12  Abstraction          : 0.01
% 1.69/1.12  MUC search           : 0.00
% 1.69/1.12  Cooper               : 0.00
% 1.69/1.12  Total                : 0.39
% 1.69/1.12  Index Insertion      : 0.00
% 1.69/1.12  Index Deletion       : 0.00
% 1.69/1.12  Index Matching       : 0.00
% 1.69/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
