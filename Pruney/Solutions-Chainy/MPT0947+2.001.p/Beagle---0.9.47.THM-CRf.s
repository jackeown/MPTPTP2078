%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:35 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   34 (  45 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 107 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > v3_ordinal1 > v1_relat_1 > #nlpp > k1_wellord2 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ! [C] :
                ( v3_ordinal1(C)
               => ( ( r4_wellord1(A,k1_wellord2(B))
                    & r4_wellord1(A,k1_wellord2(C)) )
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_wellord2)).

tff(f_50,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( ( r4_wellord1(A,B)
                  & r4_wellord1(B,C) )
               => r4_wellord1(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).

tff(f_59,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(c_10,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_11] : v1_relat_1(k1_wellord2(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    r4_wellord1('#skF_1',k1_wellord2('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [B_20,A_21] :
      ( r4_wellord1(B_20,A_21)
      | ~ r4_wellord1(A_21,B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,
    ( r4_wellord1(k1_wellord2('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k1_wellord2('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_22])).

tff(c_32,plain,(
    r4_wellord1(k1_wellord2('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6,c_26])).

tff(c_16,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    r4_wellord1('#skF_1',k1_wellord2('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ! [A_24,C_25,B_26] :
      ( r4_wellord1(A_24,C_25)
      | ~ r4_wellord1(B_26,C_25)
      | ~ r4_wellord1(A_24,B_26)
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    ! [A_24] :
      ( r4_wellord1(A_24,k1_wellord2('#skF_3'))
      | ~ r4_wellord1(A_24,'#skF_1')
      | ~ v1_relat_1(k1_wellord2('#skF_3'))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_24) ) ),
    inference(resolution,[status(thm)],[c_12,c_44])).

tff(c_65,plain,(
    ! [A_27] :
      ( r4_wellord1(A_27,k1_wellord2('#skF_3'))
      | ~ r4_wellord1(A_27,'#skF_1')
      | ~ v1_relat_1(A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6,c_50])).

tff(c_8,plain,(
    ! [B_14,A_12] :
      ( B_14 = A_12
      | ~ r4_wellord1(k1_wellord2(A_12),k1_wellord2(B_14))
      | ~ v3_ordinal1(B_14)
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,(
    ! [A_12] :
      ( A_12 = '#skF_3'
      | ~ v3_ordinal1('#skF_3')
      | ~ v3_ordinal1(A_12)
      | ~ r4_wellord1(k1_wellord2(A_12),'#skF_1')
      | ~ v1_relat_1(k1_wellord2(A_12)) ) ),
    inference(resolution,[status(thm)],[c_65,c_8])).

tff(c_83,plain,(
    ! [A_28] :
      ( A_28 = '#skF_3'
      | ~ v3_ordinal1(A_28)
      | ~ r4_wellord1(k1_wellord2(A_28),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16,c_71])).

tff(c_86,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_83])).

tff(c_92,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_86])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.12  %$ r4_wellord1 > v3_ordinal1 > v1_relat_1 > #nlpp > k1_wellord2 > #skF_2 > #skF_3 > #skF_1
% 1.67/1.12  
% 1.67/1.12  %Foreground sorts:
% 1.67/1.12  
% 1.67/1.12  
% 1.67/1.12  %Background operators:
% 1.67/1.12  
% 1.67/1.12  
% 1.67/1.12  %Foreground operators:
% 1.67/1.12  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.12  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.67/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.12  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.12  
% 1.67/1.13  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r4_wellord1(A, k1_wellord2(B)) & r4_wellord1(A, k1_wellord2(C))) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_wellord2)).
% 1.67/1.13  tff(f_50, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.67/1.13  tff(f_34, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 1.67/1.13  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r4_wellord1(A, B) & r4_wellord1(B, C)) => r4_wellord1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_wellord1)).
% 1.67/1.13  tff(f_59, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 1.67/1.13  tff(c_10, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.67/1.13  tff(c_18, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.67/1.13  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.67/1.13  tff(c_6, plain, (![A_11]: (v1_relat_1(k1_wellord2(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.67/1.13  tff(c_14, plain, (r4_wellord1('#skF_1', k1_wellord2('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.67/1.13  tff(c_22, plain, (![B_20, A_21]: (r4_wellord1(B_20, A_21) | ~r4_wellord1(A_21, B_20) | ~v1_relat_1(B_20) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.67/1.13  tff(c_26, plain, (r4_wellord1(k1_wellord2('#skF_2'), '#skF_1') | ~v1_relat_1(k1_wellord2('#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_22])).
% 1.67/1.13  tff(c_32, plain, (r4_wellord1(k1_wellord2('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6, c_26])).
% 1.67/1.13  tff(c_16, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.67/1.13  tff(c_12, plain, (r4_wellord1('#skF_1', k1_wellord2('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.67/1.13  tff(c_44, plain, (![A_24, C_25, B_26]: (r4_wellord1(A_24, C_25) | ~r4_wellord1(B_26, C_25) | ~r4_wellord1(A_24, B_26) | ~v1_relat_1(C_25) | ~v1_relat_1(B_26) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.13  tff(c_50, plain, (![A_24]: (r4_wellord1(A_24, k1_wellord2('#skF_3')) | ~r4_wellord1(A_24, '#skF_1') | ~v1_relat_1(k1_wellord2('#skF_3')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_24))), inference(resolution, [status(thm)], [c_12, c_44])).
% 1.67/1.13  tff(c_65, plain, (![A_27]: (r4_wellord1(A_27, k1_wellord2('#skF_3')) | ~r4_wellord1(A_27, '#skF_1') | ~v1_relat_1(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6, c_50])).
% 1.67/1.13  tff(c_8, plain, (![B_14, A_12]: (B_14=A_12 | ~r4_wellord1(k1_wellord2(A_12), k1_wellord2(B_14)) | ~v3_ordinal1(B_14) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.67/1.13  tff(c_71, plain, (![A_12]: (A_12='#skF_3' | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(A_12) | ~r4_wellord1(k1_wellord2(A_12), '#skF_1') | ~v1_relat_1(k1_wellord2(A_12)))), inference(resolution, [status(thm)], [c_65, c_8])).
% 1.67/1.13  tff(c_83, plain, (![A_28]: (A_28='#skF_3' | ~v3_ordinal1(A_28) | ~r4_wellord1(k1_wellord2(A_28), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16, c_71])).
% 1.67/1.13  tff(c_86, plain, ('#skF_2'='#skF_3' | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_83])).
% 1.67/1.13  tff(c_92, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_86])).
% 1.67/1.13  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_92])).
% 1.67/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  Inference rules
% 1.67/1.13  ----------------------
% 1.67/1.13  #Ref     : 0
% 1.67/1.13  #Sup     : 13
% 1.67/1.13  #Fact    : 0
% 1.67/1.13  #Define  : 0
% 1.67/1.13  #Split   : 0
% 1.67/1.13  #Chain   : 0
% 1.67/1.13  #Close   : 0
% 1.67/1.13  
% 1.67/1.13  Ordering : KBO
% 1.67/1.13  
% 1.67/1.13  Simplification rules
% 1.67/1.13  ----------------------
% 1.67/1.13  #Subsume      : 0
% 1.67/1.13  #Demod        : 23
% 1.67/1.13  #Tautology    : 2
% 1.67/1.13  #SimpNegUnit  : 1
% 1.67/1.13  #BackRed      : 0
% 1.67/1.13  
% 1.67/1.13  #Partial instantiations: 0
% 1.67/1.13  #Strategies tried      : 1
% 1.67/1.13  
% 1.67/1.13  Timing (in seconds)
% 1.67/1.13  ----------------------
% 1.67/1.14  Preprocessing        : 0.27
% 1.67/1.14  Parsing              : 0.14
% 1.67/1.14  CNF conversion       : 0.02
% 1.67/1.14  Main loop            : 0.11
% 1.67/1.14  Inferencing          : 0.04
% 1.67/1.14  Reduction            : 0.04
% 1.67/1.14  Demodulation         : 0.03
% 1.67/1.14  BG Simplification    : 0.01
% 1.67/1.14  Subsumption          : 0.02
% 1.67/1.14  Abstraction          : 0.00
% 1.67/1.14  MUC search           : 0.00
% 1.67/1.14  Cooper               : 0.00
% 1.67/1.14  Total                : 0.40
% 1.67/1.14  Index Insertion      : 0.00
% 1.67/1.14  Index Deletion       : 0.00
% 1.67/1.14  Index Matching       : 0.00
% 1.67/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
