%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:52 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  67 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    k9_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_103,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(k1_relat_1(B_32),A_33)
      | k9_relat_1(B_32,A_33) != k1_xboole_0
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),k3_xboole_0(A_4,B_5))
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_73,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,k3_xboole_0(A_22,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_91,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r1_xboole_0(A_27,B_28)
      | ~ r2_hidden(C_29,k3_xboole_0(B_28,A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_73])).

tff(c_101,plain,(
    ! [B_5,A_4] :
      ( ~ r1_xboole_0(B_5,A_4)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_131,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(A_38,k1_relat_1(B_39))
      | k9_relat_1(B_39,A_38) != k1_xboole_0
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_103,c_101])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( ~ r1_xboole_0(B_10,A_9)
      | ~ r1_tarski(B_10,A_9)
      | v1_xboole_0(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_144,plain,(
    ! [A_40,B_41] :
      ( ~ r1_tarski(A_40,k1_relat_1(B_41))
      | v1_xboole_0(A_40)
      | k9_relat_1(B_41,A_40) != k1_xboole_0
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_131,c_10])).

tff(c_147,plain,
    ( v1_xboole_0('#skF_2')
    | k9_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_144])).

tff(c_150,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_147])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_153,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_150,c_4])).

tff(c_157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:16:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.15  
% 1.84/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.16  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.84/1.16  
% 1.84/1.16  %Foreground sorts:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Background operators:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Foreground operators:
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.84/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.84/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.84/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.84/1.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.84/1.16  
% 1.84/1.17  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 1.84/1.17  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 1.84/1.17  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.84/1.17  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.84/1.17  tff(f_53, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.84/1.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.84/1.17  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.84/1.17  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.84/1.17  tff(c_18, plain, (k9_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.84/1.17  tff(c_20, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.84/1.17  tff(c_103, plain, (![B_32, A_33]: (r1_xboole_0(k1_relat_1(B_32), A_33) | k9_relat_1(B_32, A_33)!=k1_xboole_0 | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.84/1.17  tff(c_6, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), k3_xboole_0(A_4, B_5)) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.84/1.17  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.84/1.17  tff(c_73, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, k3_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.84/1.17  tff(c_91, plain, (![A_27, B_28, C_29]: (~r1_xboole_0(A_27, B_28) | ~r2_hidden(C_29, k3_xboole_0(B_28, A_27)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_73])).
% 1.84/1.17  tff(c_101, plain, (![B_5, A_4]: (~r1_xboole_0(B_5, A_4) | r1_xboole_0(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_91])).
% 1.84/1.17  tff(c_131, plain, (![A_38, B_39]: (r1_xboole_0(A_38, k1_relat_1(B_39)) | k9_relat_1(B_39, A_38)!=k1_xboole_0 | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_103, c_101])).
% 1.84/1.17  tff(c_10, plain, (![B_10, A_9]: (~r1_xboole_0(B_10, A_9) | ~r1_tarski(B_10, A_9) | v1_xboole_0(B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.17  tff(c_144, plain, (![A_40, B_41]: (~r1_tarski(A_40, k1_relat_1(B_41)) | v1_xboole_0(A_40) | k9_relat_1(B_41, A_40)!=k1_xboole_0 | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_131, c_10])).
% 1.84/1.17  tff(c_147, plain, (v1_xboole_0('#skF_2') | k9_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_144])).
% 1.84/1.17  tff(c_150, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_147])).
% 1.84/1.17  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.17  tff(c_153, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_150, c_4])).
% 1.84/1.17  tff(c_157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_153])).
% 1.84/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.17  
% 1.84/1.17  Inference rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Ref     : 0
% 1.84/1.17  #Sup     : 32
% 1.84/1.17  #Fact    : 0
% 1.84/1.17  #Define  : 0
% 1.84/1.17  #Split   : 0
% 1.84/1.17  #Chain   : 0
% 1.84/1.17  #Close   : 0
% 1.84/1.17  
% 1.84/1.17  Ordering : KBO
% 1.84/1.17  
% 1.84/1.17  Simplification rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Subsume      : 8
% 1.84/1.17  #Demod        : 2
% 1.84/1.17  #Tautology    : 15
% 1.84/1.17  #SimpNegUnit  : 1
% 1.84/1.17  #BackRed      : 0
% 1.84/1.17  
% 1.84/1.17  #Partial instantiations: 0
% 1.84/1.17  #Strategies tried      : 1
% 1.84/1.17  
% 1.84/1.17  Timing (in seconds)
% 1.84/1.17  ----------------------
% 1.84/1.17  Preprocessing        : 0.27
% 1.84/1.17  Parsing              : 0.15
% 1.84/1.17  CNF conversion       : 0.02
% 1.84/1.17  Main loop            : 0.13
% 1.84/1.17  Inferencing          : 0.05
% 1.84/1.17  Reduction            : 0.04
% 1.84/1.17  Demodulation         : 0.03
% 1.84/1.17  BG Simplification    : 0.01
% 1.84/1.17  Subsumption          : 0.02
% 1.84/1.17  Abstraction          : 0.01
% 1.84/1.17  MUC search           : 0.00
% 1.84/1.17  Cooper               : 0.00
% 1.84/1.17  Total                : 0.43
% 1.84/1.17  Index Insertion      : 0.00
% 1.84/1.17  Index Deletion       : 0.00
% 1.84/1.17  Index Matching       : 0.00
% 1.84/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
