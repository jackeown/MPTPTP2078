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

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   39 (  52 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 145 expanded)
%              Number of equality atoms :    2 (  11 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_relat_1,type,(
    v2_relat_1: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v5_funct_1(A,B)
                & k1_relat_1(A) = k1_relat_1(B) )
             => v2_relat_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_relat_1(A)
      <=> ! [B] :
            ~ ( r2_hidden(B,k1_relat_1(A))
              & v1_xboole_0(k1_funct_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).

tff(f_59,axiom,(
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

tff(c_18,plain,(
    ~ v2_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    v5_funct_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    k1_relat_1('#skF_5') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_41,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_2'(A_23),k1_relat_1(A_23))
      | v2_relat_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,
    ( r2_hidden('#skF_2'('#skF_5'),k1_relat_1('#skF_4'))
    | v2_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_41])).

tff(c_50,plain,
    ( r2_hidden('#skF_2'('#skF_5'),k1_relat_1('#skF_4'))
    | v2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_47])).

tff(c_51,plain,(
    r2_hidden('#skF_2'('#skF_5'),k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_50])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(k1_funct_1(A_5,'#skF_2'(A_5)))
      | v2_relat_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_125,plain,(
    ! [B_38,C_39,A_40] :
      ( r2_hidden(k1_funct_1(B_38,C_39),k1_funct_1(A_40,C_39))
      | ~ r2_hidden(C_39,k1_relat_1(B_38))
      | ~ v5_funct_1(B_38,A_40)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_41,C_42,B_43] :
      ( ~ v1_xboole_0(k1_funct_1(A_41,C_42))
      | ~ r2_hidden(C_42,k1_relat_1(B_43))
      | ~ v5_funct_1(B_43,A_41)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_139,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden('#skF_2'(A_44),k1_relat_1(B_45))
      | ~ v5_funct_1(B_45,A_44)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45)
      | v2_relat_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_8,c_135])).

tff(c_142,plain,
    ( ~ v5_funct_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | v2_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_51,c_139])).

tff(c_151,plain,(
    v2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_30,c_28,c_22,c_142])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  %$ v5_funct_1 > r2_hidden > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 1.98/1.21  
% 1.98/1.21  %Foreground sorts:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Background operators:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Foreground operators:
% 1.98/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.21  tff(v2_relat_1, type, v2_relat_1: $i > $o).
% 1.98/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.98/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.98/1.21  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.98/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.21  
% 1.98/1.22  tff(f_75, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v5_funct_1(A, B) & (k1_relat_1(A) = k1_relat_1(B))) => v2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_funct_1)).
% 1.98/1.22  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_relat_1(A) <=> (![B]: ~(r2_hidden(B, k1_relat_1(A)) & v1_xboole_0(k1_funct_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_funct_1)).
% 1.98/1.22  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.98/1.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.98/1.22  tff(c_18, plain, (~v2_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.22  tff(c_26, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.22  tff(c_24, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.22  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.22  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.22  tff(c_22, plain, (v5_funct_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.22  tff(c_20, plain, (k1_relat_1('#skF_5')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.98/1.22  tff(c_41, plain, (![A_23]: (r2_hidden('#skF_2'(A_23), k1_relat_1(A_23)) | v2_relat_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.98/1.22  tff(c_47, plain, (r2_hidden('#skF_2'('#skF_5'), k1_relat_1('#skF_4')) | v2_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_20, c_41])).
% 1.98/1.22  tff(c_50, plain, (r2_hidden('#skF_2'('#skF_5'), k1_relat_1('#skF_4')) | v2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_47])).
% 1.98/1.22  tff(c_51, plain, (r2_hidden('#skF_2'('#skF_5'), k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_18, c_50])).
% 1.98/1.22  tff(c_8, plain, (![A_5]: (v1_xboole_0(k1_funct_1(A_5, '#skF_2'(A_5))) | v2_relat_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.98/1.22  tff(c_125, plain, (![B_38, C_39, A_40]: (r2_hidden(k1_funct_1(B_38, C_39), k1_funct_1(A_40, C_39)) | ~r2_hidden(C_39, k1_relat_1(B_38)) | ~v5_funct_1(B_38, A_40) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.98/1.22  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.22  tff(c_135, plain, (![A_41, C_42, B_43]: (~v1_xboole_0(k1_funct_1(A_41, C_42)) | ~r2_hidden(C_42, k1_relat_1(B_43)) | ~v5_funct_1(B_43, A_41) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_125, c_2])).
% 1.98/1.22  tff(c_139, plain, (![A_44, B_45]: (~r2_hidden('#skF_2'(A_44), k1_relat_1(B_45)) | ~v5_funct_1(B_45, A_44) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45) | v2_relat_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_8, c_135])).
% 1.98/1.22  tff(c_142, plain, (~v5_funct_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v2_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_51, c_139])).
% 1.98/1.22  tff(c_151, plain, (v2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_30, c_28, c_22, c_142])).
% 1.98/1.22  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_151])).
% 1.98/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  Inference rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Ref     : 0
% 1.98/1.22  #Sup     : 24
% 1.98/1.22  #Fact    : 0
% 1.98/1.22  #Define  : 0
% 1.98/1.22  #Split   : 1
% 1.98/1.22  #Chain   : 0
% 1.98/1.22  #Close   : 0
% 1.98/1.22  
% 1.98/1.22  Ordering : KBO
% 1.98/1.22  
% 1.98/1.22  Simplification rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Subsume      : 6
% 1.98/1.22  #Demod        : 22
% 1.98/1.22  #Tautology    : 5
% 1.98/1.22  #SimpNegUnit  : 4
% 1.98/1.22  #BackRed      : 0
% 1.98/1.22  
% 1.98/1.22  #Partial instantiations: 0
% 1.98/1.22  #Strategies tried      : 1
% 1.98/1.22  
% 1.98/1.22  Timing (in seconds)
% 1.98/1.22  ----------------------
% 1.98/1.22  Preprocessing        : 0.29
% 1.98/1.22  Parsing              : 0.16
% 1.98/1.22  CNF conversion       : 0.02
% 1.98/1.22  Main loop            : 0.17
% 1.98/1.22  Inferencing          : 0.07
% 1.98/1.22  Reduction            : 0.05
% 1.98/1.22  Demodulation         : 0.03
% 1.98/1.22  BG Simplification    : 0.01
% 1.98/1.22  Subsumption          : 0.03
% 1.98/1.22  Abstraction          : 0.01
% 1.98/1.22  MUC search           : 0.00
% 1.98/1.22  Cooper               : 0.00
% 1.98/1.22  Total                : 0.49
% 1.98/1.22  Index Insertion      : 0.00
% 1.98/1.23  Index Deletion       : 0.00
% 1.98/1.23  Index Matching       : 0.00
% 1.98/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
