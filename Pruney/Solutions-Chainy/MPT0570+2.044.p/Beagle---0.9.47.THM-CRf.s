%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:47 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 (  82 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden('#skF_1'(A_2,B_3),B_3)
      | r1_xboole_0(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( r2_hidden('#skF_1'(A_2,B_3),A_2)
      | r1_xboole_0(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_33,plain,(
    ! [B_23,A_24] :
      ( r1_xboole_0(k2_relat_1(B_23),A_24)
      | k10_relat_1(B_23,A_24) != k1_xboole_0
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_2,B_3,C_6] :
      ( ~ r1_xboole_0(A_2,B_3)
      | ~ r2_hidden(C_6,B_3)
      | ~ r2_hidden(C_6,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_45,plain,(
    ! [C_25,A_26,B_27] :
      ( ~ r2_hidden(C_25,A_26)
      | ~ r2_hidden(C_25,k2_relat_1(B_27))
      | k10_relat_1(B_27,A_26) != k1_xboole_0
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_33,c_4])).

tff(c_65,plain,(
    ! [A_35,B_36,B_37] :
      ( ~ r2_hidden('#skF_1'(A_35,B_36),k2_relat_1(B_37))
      | k10_relat_1(B_37,A_35) != k1_xboole_0
      | ~ v1_relat_1(B_37)
      | r1_xboole_0(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_8,c_45])).

tff(c_76,plain,(
    ! [B_38,A_39] :
      ( k10_relat_1(B_38,A_39) != k1_xboole_0
      | ~ v1_relat_1(B_38)
      | r1_xboole_0(A_39,k2_relat_1(B_38)) ) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_xboole_0(B_8,A_7)
      | ~ r1_tarski(B_8,A_7)
      | v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [A_42,B_43] :
      ( ~ r1_tarski(A_42,k2_relat_1(B_43))
      | v1_xboole_0(A_42)
      | k10_relat_1(B_43,A_42) != k1_xboole_0
      | ~ v1_relat_1(B_43) ) ),
    inference(resolution,[status(thm)],[c_76,c_10])).

tff(c_93,plain,
    ( v1_xboole_0('#skF_2')
    | k10_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_90])).

tff(c_96,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_93])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:20:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.14  
% 1.79/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.14  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.79/1.14  
% 1.79/1.14  %Foreground sorts:
% 1.79/1.14  
% 1.79/1.14  
% 1.79/1.14  %Background operators:
% 1.79/1.14  
% 1.79/1.14  
% 1.79/1.14  %Foreground operators:
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.79/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.79/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.79/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.79/1.14  
% 1.79/1.15  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 1.79/1.15  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.79/1.15  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 1.79/1.15  tff(f_55, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.79/1.15  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.79/1.15  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.79/1.15  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.79/1.15  tff(c_16, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.79/1.15  tff(c_18, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.79/1.15  tff(c_6, plain, (![A_2, B_3]: (r2_hidden('#skF_1'(A_2, B_3), B_3) | r1_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.79/1.15  tff(c_8, plain, (![A_2, B_3]: (r2_hidden('#skF_1'(A_2, B_3), A_2) | r1_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.79/1.15  tff(c_33, plain, (![B_23, A_24]: (r1_xboole_0(k2_relat_1(B_23), A_24) | k10_relat_1(B_23, A_24)!=k1_xboole_0 | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.79/1.15  tff(c_4, plain, (![A_2, B_3, C_6]: (~r1_xboole_0(A_2, B_3) | ~r2_hidden(C_6, B_3) | ~r2_hidden(C_6, A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.79/1.15  tff(c_45, plain, (![C_25, A_26, B_27]: (~r2_hidden(C_25, A_26) | ~r2_hidden(C_25, k2_relat_1(B_27)) | k10_relat_1(B_27, A_26)!=k1_xboole_0 | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_33, c_4])).
% 1.79/1.15  tff(c_65, plain, (![A_35, B_36, B_37]: (~r2_hidden('#skF_1'(A_35, B_36), k2_relat_1(B_37)) | k10_relat_1(B_37, A_35)!=k1_xboole_0 | ~v1_relat_1(B_37) | r1_xboole_0(A_35, B_36))), inference(resolution, [status(thm)], [c_8, c_45])).
% 1.79/1.15  tff(c_76, plain, (![B_38, A_39]: (k10_relat_1(B_38, A_39)!=k1_xboole_0 | ~v1_relat_1(B_38) | r1_xboole_0(A_39, k2_relat_1(B_38)))), inference(resolution, [status(thm)], [c_6, c_65])).
% 1.79/1.15  tff(c_10, plain, (![B_8, A_7]: (~r1_xboole_0(B_8, A_7) | ~r1_tarski(B_8, A_7) | v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.79/1.15  tff(c_90, plain, (![A_42, B_43]: (~r1_tarski(A_42, k2_relat_1(B_43)) | v1_xboole_0(A_42) | k10_relat_1(B_43, A_42)!=k1_xboole_0 | ~v1_relat_1(B_43))), inference(resolution, [status(thm)], [c_76, c_10])).
% 1.79/1.15  tff(c_93, plain, (v1_xboole_0('#skF_2') | k10_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_90])).
% 1.79/1.15  tff(c_96, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_93])).
% 1.79/1.15  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.15  tff(c_99, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_96, c_2])).
% 1.79/1.15  tff(c_103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_99])).
% 1.79/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  Inference rules
% 1.79/1.15  ----------------------
% 1.79/1.15  #Ref     : 0
% 1.79/1.15  #Sup     : 16
% 1.79/1.15  #Fact    : 0
% 1.79/1.15  #Define  : 0
% 1.79/1.15  #Split   : 0
% 1.79/1.15  #Chain   : 0
% 1.79/1.15  #Close   : 0
% 1.79/1.15  
% 1.79/1.15  Ordering : KBO
% 1.79/1.15  
% 1.79/1.15  Simplification rules
% 1.79/1.15  ----------------------
% 1.79/1.15  #Subsume      : 1
% 1.79/1.15  #Demod        : 2
% 1.79/1.15  #Tautology    : 3
% 1.79/1.15  #SimpNegUnit  : 1
% 1.79/1.15  #BackRed      : 0
% 1.79/1.15  
% 1.79/1.15  #Partial instantiations: 0
% 1.79/1.15  #Strategies tried      : 1
% 1.79/1.15  
% 1.79/1.15  Timing (in seconds)
% 1.79/1.15  ----------------------
% 1.79/1.16  Preprocessing        : 0.26
% 1.79/1.16  Parsing              : 0.14
% 1.79/1.16  CNF conversion       : 0.02
% 1.79/1.16  Main loop            : 0.13
% 1.79/1.16  Inferencing          : 0.06
% 1.79/1.16  Reduction            : 0.03
% 1.79/1.16  Demodulation         : 0.02
% 1.79/1.16  BG Simplification    : 0.01
% 1.79/1.16  Subsumption          : 0.03
% 1.79/1.16  Abstraction          : 0.00
% 1.79/1.16  MUC search           : 0.00
% 1.79/1.16  Cooper               : 0.00
% 1.79/1.16  Total                : 0.42
% 1.79/1.16  Index Insertion      : 0.00
% 1.79/1.16  Index Deletion       : 0.00
% 1.79/1.16  Index Matching       : 0.00
% 1.79/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
