%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:27 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  57 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 103 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_31,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_31])).

tff(c_51,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ r1_xboole_0(A_26,B_27)
      | ~ r2_hidden(C_28,k3_xboole_0(A_26,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62,plain,(
    ! [C_28] :
      ( ~ r1_xboole_0('#skF_3','#skF_4')
      | ~ r2_hidden(C_28,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_51])).

tff(c_67,plain,(
    ! [C_29] : ~ r2_hidden(C_29,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_62])).

tff(c_76,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_67])).

tff(c_390,plain,(
    ! [B_54,A_55] :
      ( k9_relat_1(B_54,A_55) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_54),A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_406,plain,(
    ! [B_56] :
      ( k9_relat_1(B_56,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_76,c_390])).

tff(c_410,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_406])).

tff(c_504,plain,(
    ! [C_66,A_67,B_68] :
      ( k3_xboole_0(k9_relat_1(C_66,A_67),k9_relat_1(C_66,B_68)) = k9_relat_1(C_66,k3_xboole_0(A_67,B_68))
      | ~ v2_funct_1(C_66)
      | ~ v1_funct_1(C_66)
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_47,plain,(
    k3_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_22])).

tff(c_528,plain,
    ( k9_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_47])).

tff(c_541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_410,c_35,c_528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.35  
% 2.21/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.35  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.21/1.35  
% 2.21/1.35  %Foreground sorts:
% 2.21/1.35  
% 2.21/1.35  
% 2.21/1.35  %Background operators:
% 2.21/1.35  
% 2.21/1.35  
% 2.21/1.35  %Foreground operators:
% 2.21/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.21/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.21/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.35  
% 2.21/1.36  tff(f_86, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_funct_1)).
% 2.21/1.36  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.21/1.36  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.21/1.36  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.21/1.36  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.21/1.36  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 2.21/1.36  tff(c_30, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.36  tff(c_28, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.36  tff(c_24, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.36  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.36  tff(c_26, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.36  tff(c_31, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.36  tff(c_35, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_31])).
% 2.21/1.36  tff(c_51, plain, (![A_26, B_27, C_28]: (~r1_xboole_0(A_26, B_27) | ~r2_hidden(C_28, k3_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.21/1.36  tff(c_62, plain, (![C_28]: (~r1_xboole_0('#skF_3', '#skF_4') | ~r2_hidden(C_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_35, c_51])).
% 2.21/1.36  tff(c_67, plain, (![C_29]: (~r2_hidden(C_29, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_62])).
% 2.21/1.36  tff(c_76, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_67])).
% 2.21/1.36  tff(c_390, plain, (![B_54, A_55]: (k9_relat_1(B_54, A_55)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_54), A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.36  tff(c_406, plain, (![B_56]: (k9_relat_1(B_56, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_76, c_390])).
% 2.21/1.36  tff(c_410, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_406])).
% 2.21/1.36  tff(c_504, plain, (![C_66, A_67, B_68]: (k3_xboole_0(k9_relat_1(C_66, A_67), k9_relat_1(C_66, B_68))=k9_relat_1(C_66, k3_xboole_0(A_67, B_68)) | ~v2_funct_1(C_66) | ~v1_funct_1(C_66) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.21/1.36  tff(c_40, plain, (![A_20, B_21]: (r1_xboole_0(A_20, B_21) | k3_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.36  tff(c_22, plain, (~r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.36  tff(c_47, plain, (k3_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_22])).
% 2.21/1.36  tff(c_528, plain, (k9_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0 | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_504, c_47])).
% 2.21/1.36  tff(c_541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_410, c_35, c_528])).
% 2.21/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.36  
% 2.21/1.36  Inference rules
% 2.21/1.36  ----------------------
% 2.21/1.36  #Ref     : 0
% 2.21/1.36  #Sup     : 120
% 2.21/1.36  #Fact    : 0
% 2.21/1.36  #Define  : 0
% 2.21/1.36  #Split   : 0
% 2.21/1.36  #Chain   : 0
% 2.21/1.36  #Close   : 0
% 2.21/1.36  
% 2.21/1.36  Ordering : KBO
% 2.21/1.36  
% 2.21/1.36  Simplification rules
% 2.21/1.36  ----------------------
% 2.21/1.36  #Subsume      : 15
% 2.21/1.36  #Demod        : 60
% 2.21/1.36  #Tautology    : 68
% 2.21/1.36  #SimpNegUnit  : 7
% 2.21/1.36  #BackRed      : 0
% 2.21/1.36  
% 2.21/1.36  #Partial instantiations: 0
% 2.21/1.36  #Strategies tried      : 1
% 2.21/1.36  
% 2.21/1.36  Timing (in seconds)
% 2.21/1.36  ----------------------
% 2.21/1.36  Preprocessing        : 0.29
% 2.21/1.36  Parsing              : 0.17
% 2.21/1.36  CNF conversion       : 0.02
% 2.21/1.36  Main loop            : 0.25
% 2.21/1.36  Inferencing          : 0.10
% 2.21/1.36  Reduction            : 0.07
% 2.21/1.36  Demodulation         : 0.05
% 2.21/1.36  BG Simplification    : 0.01
% 2.21/1.36  Subsumption          : 0.05
% 2.21/1.36  Abstraction          : 0.01
% 2.21/1.37  MUC search           : 0.00
% 2.21/1.37  Cooper               : 0.00
% 2.21/1.37  Total                : 0.57
% 2.21/1.37  Index Insertion      : 0.00
% 2.21/1.37  Index Deletion       : 0.00
% 2.21/1.37  Index Matching       : 0.00
% 2.21/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
