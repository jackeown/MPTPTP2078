%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:12 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   34 (  40 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  68 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(c_30,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_35,plain,(
    ! [D_13,B_14,A_15] :
      ( r2_hidden(D_13,B_14)
      | ~ r2_hidden(D_13,k3_xboole_0(A_15,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_39,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_35])).

tff(c_34,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [D_16,A_17,B_18] :
      ( r2_hidden(D_16,A_17)
      | ~ r2_hidden(D_16,k3_xboole_0(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_30,c_40])).

tff(c_20,plain,(
    ! [A_7,C_9,B_8] :
      ( r2_hidden(A_7,k1_relat_1(k7_relat_1(C_9,B_8)))
      | ~ r2_hidden(A_7,k1_relat_1(C_9))
      | ~ r2_hidden(A_7,B_8)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_210,plain,(
    ! [C_44,B_45,A_46] :
      ( k1_funct_1(k7_relat_1(C_44,B_45),A_46) = k1_funct_1(C_44,A_46)
      | ~ r2_hidden(A_46,k1_relat_1(k7_relat_1(C_44,B_45)))
      | ~ v1_funct_1(C_44)
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_574,plain,(
    ! [C_74,B_75,A_76] :
      ( k1_funct_1(k7_relat_1(C_74,B_75),A_76) = k1_funct_1(C_74,A_76)
      | ~ v1_funct_1(C_74)
      | ~ r2_hidden(A_76,k1_relat_1(C_74))
      | ~ r2_hidden(A_76,B_75)
      | ~ v1_relat_1(C_74) ) ),
    inference(resolution,[status(thm)],[c_20,c_210])).

tff(c_614,plain,(
    ! [B_75] :
      ( k1_funct_1(k7_relat_1('#skF_5',B_75),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden('#skF_3',B_75)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_574])).

tff(c_631,plain,(
    ! [B_77] :
      ( k1_funct_1(k7_relat_1('#skF_5',B_77),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
      | ~ r2_hidden('#skF_3',B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_614])).

tff(c_28,plain,(
    k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_637,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_28])).

tff(c_645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_637])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:16:24 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.40  
% 2.65/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.40  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.65/1.40  
% 2.65/1.40  %Foreground sorts:
% 2.65/1.40  
% 2.65/1.40  
% 2.65/1.40  %Background operators:
% 2.65/1.40  
% 2.65/1.40  
% 2.65/1.40  %Foreground operators:
% 2.65/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.65/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.65/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.65/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.65/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.40  
% 2.65/1.41  tff(f_59, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_funct_1)).
% 2.65/1.41  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.65/1.41  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 2.65/1.41  tff(f_50, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 2.65/1.41  tff(c_30, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.65/1.41  tff(c_35, plain, (![D_13, B_14, A_15]: (r2_hidden(D_13, B_14) | ~r2_hidden(D_13, k3_xboole_0(A_15, B_14)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.65/1.41  tff(c_39, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_35])).
% 2.65/1.41  tff(c_34, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.65/1.41  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.65/1.41  tff(c_40, plain, (![D_16, A_17, B_18]: (r2_hidden(D_16, A_17) | ~r2_hidden(D_16, k3_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.65/1.41  tff(c_44, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_40])).
% 2.65/1.41  tff(c_20, plain, (![A_7, C_9, B_8]: (r2_hidden(A_7, k1_relat_1(k7_relat_1(C_9, B_8))) | ~r2_hidden(A_7, k1_relat_1(C_9)) | ~r2_hidden(A_7, B_8) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.65/1.41  tff(c_210, plain, (![C_44, B_45, A_46]: (k1_funct_1(k7_relat_1(C_44, B_45), A_46)=k1_funct_1(C_44, A_46) | ~r2_hidden(A_46, k1_relat_1(k7_relat_1(C_44, B_45))) | ~v1_funct_1(C_44) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.65/1.41  tff(c_574, plain, (![C_74, B_75, A_76]: (k1_funct_1(k7_relat_1(C_74, B_75), A_76)=k1_funct_1(C_74, A_76) | ~v1_funct_1(C_74) | ~r2_hidden(A_76, k1_relat_1(C_74)) | ~r2_hidden(A_76, B_75) | ~v1_relat_1(C_74))), inference(resolution, [status(thm)], [c_20, c_210])).
% 2.65/1.41  tff(c_614, plain, (![B_75]: (k1_funct_1(k7_relat_1('#skF_5', B_75), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~r2_hidden('#skF_3', B_75) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_574])).
% 2.65/1.41  tff(c_631, plain, (![B_77]: (k1_funct_1(k7_relat_1('#skF_5', B_77), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', B_77))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_614])).
% 2.65/1.41  tff(c_28, plain, (k1_funct_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.65/1.41  tff(c_637, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_631, c_28])).
% 2.65/1.41  tff(c_645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_637])).
% 2.65/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.41  
% 2.65/1.41  Inference rules
% 2.65/1.41  ----------------------
% 2.65/1.41  #Ref     : 0
% 2.65/1.41  #Sup     : 127
% 2.65/1.41  #Fact    : 0
% 2.65/1.41  #Define  : 0
% 2.65/1.41  #Split   : 0
% 2.65/1.41  #Chain   : 0
% 2.65/1.41  #Close   : 0
% 2.65/1.41  
% 2.65/1.41  Ordering : KBO
% 2.65/1.41  
% 2.65/1.41  Simplification rules
% 2.65/1.41  ----------------------
% 2.65/1.41  #Subsume      : 14
% 2.65/1.41  #Demod        : 32
% 2.65/1.41  #Tautology    : 15
% 2.65/1.41  #SimpNegUnit  : 0
% 2.65/1.41  #BackRed      : 0
% 2.65/1.41  
% 2.65/1.41  #Partial instantiations: 0
% 2.65/1.41  #Strategies tried      : 1
% 2.65/1.41  
% 2.65/1.41  Timing (in seconds)
% 2.65/1.41  ----------------------
% 2.65/1.42  Preprocessing        : 0.29
% 2.65/1.42  Parsing              : 0.15
% 2.65/1.42  CNF conversion       : 0.02
% 2.65/1.42  Main loop            : 0.37
% 2.65/1.42  Inferencing          : 0.14
% 2.65/1.42  Reduction            : 0.08
% 2.65/1.42  Demodulation         : 0.06
% 2.65/1.42  BG Simplification    : 0.02
% 2.65/1.42  Subsumption          : 0.09
% 2.65/1.42  Abstraction          : 0.03
% 2.65/1.42  MUC search           : 0.00
% 2.65/1.42  Cooper               : 0.00
% 2.65/1.42  Total                : 0.68
% 2.65/1.42  Index Insertion      : 0.00
% 2.65/1.42  Index Deletion       : 0.00
% 2.65/1.42  Index Matching       : 0.00
% 2.65/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
