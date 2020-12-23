%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:24 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   18 (  21 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    3
%              Number of atoms          :   20 (  32 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v1_finset_1(A)
         => v1_finset_1(k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_finset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k9_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_finset_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_11,plain,(
    ! [A_3,B_4] :
      ( v1_finset_1(k9_relat_1(A_3,B_4))
      | ~ v1_finset_1(B_4)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ~ v1_finset_1(k9_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,
    ( ~ v1_finset_1('#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_11,c_4])).

tff(c_18,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_6,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 20:41:02 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.03  
% 1.51/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.05  %$ v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > #nlpp > #skF_2 > #skF_1
% 1.51/1.05  
% 1.51/1.05  %Foreground sorts:
% 1.51/1.05  
% 1.51/1.05  
% 1.51/1.05  %Background operators:
% 1.51/1.05  
% 1.51/1.05  
% 1.51/1.05  %Foreground operators:
% 1.51/1.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.51/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.51/1.05  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.51/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.51/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.05  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.51/1.05  
% 1.51/1.05  tff(f_42, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_finset_1(A) => v1_finset_1(k9_relat_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_finset_1)).
% 1.51/1.05  tff(f_33, axiom, (![A, B]: (((v1_relat_1(A) & v1_funct_1(A)) & v1_finset_1(B)) => v1_finset_1(k9_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_finset_1)).
% 1.51/1.05  tff(c_10, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.51/1.05  tff(c_8, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.51/1.05  tff(c_6, plain, (v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.51/1.05  tff(c_11, plain, (![A_3, B_4]: (v1_finset_1(k9_relat_1(A_3, B_4)) | ~v1_finset_1(B_4) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.51/1.05  tff(c_4, plain, (~v1_finset_1(k9_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.51/1.05  tff(c_14, plain, (~v1_finset_1('#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_11, c_4])).
% 1.51/1.05  tff(c_18, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_6, c_14])).
% 1.51/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.05  
% 1.51/1.05  Inference rules
% 1.51/1.05  ----------------------
% 1.51/1.05  #Ref     : 0
% 1.51/1.05  #Sup     : 1
% 1.51/1.05  #Fact    : 0
% 1.51/1.05  #Define  : 0
% 1.51/1.05  #Split   : 0
% 1.51/1.05  #Chain   : 0
% 1.51/1.05  #Close   : 0
% 1.51/1.05  
% 1.51/1.05  Ordering : KBO
% 1.51/1.05  
% 1.51/1.05  Simplification rules
% 1.51/1.05  ----------------------
% 1.51/1.05  #Subsume      : 0
% 1.51/1.05  #Demod        : 3
% 1.51/1.05  #Tautology    : 0
% 1.51/1.05  #SimpNegUnit  : 0
% 1.51/1.05  #BackRed      : 0
% 1.51/1.05  
% 1.51/1.05  #Partial instantiations: 0
% 1.51/1.05  #Strategies tried      : 1
% 1.51/1.05  
% 1.51/1.05  Timing (in seconds)
% 1.51/1.05  ----------------------
% 1.51/1.06  Preprocessing        : 0.24
% 1.51/1.06  Parsing              : 0.14
% 1.51/1.06  CNF conversion       : 0.01
% 1.51/1.06  Main loop            : 0.06
% 1.51/1.06  Inferencing          : 0.03
% 1.51/1.06  Reduction            : 0.02
% 1.51/1.06  Demodulation         : 0.01
% 1.51/1.06  BG Simplification    : 0.01
% 1.51/1.06  Subsumption          : 0.01
% 1.51/1.06  Abstraction          : 0.00
% 1.51/1.06  MUC search           : 0.00
% 1.51/1.06  Cooper               : 0.00
% 1.51/1.06  Total                : 0.34
% 1.51/1.06  Index Insertion      : 0.00
% 1.51/1.06  Index Deletion       : 0.00
% 1.51/1.06  Index Matching       : 0.00
% 1.51/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
