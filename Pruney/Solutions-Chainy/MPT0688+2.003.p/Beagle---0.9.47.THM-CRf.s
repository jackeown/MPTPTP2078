%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:38 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   45 (  51 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  74 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( ! [C] :
              ~ ( r2_hidden(C,A)
                & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
         => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(k1_tarski(A_23),B_24)
      | r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_145,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_2'(A_60,B_61),k3_xboole_0(A_60,B_61))
      | r1_xboole_0(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r1_xboole_0(A_42,B_43)
      | ~ r2_hidden(C_44,k3_xboole_0(A_42,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_101,plain,(
    ! [A_1,B_2,C_44] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_44,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_163,plain,(
    ! [B_62,A_63] :
      ( ~ r1_xboole_0(B_62,A_63)
      | r1_xboole_0(A_63,B_62) ) ),
    inference(resolution,[status(thm)],[c_145,c_101])).

tff(c_166,plain,(
    ! [B_24,A_23] :
      ( r1_xboole_0(B_24,k1_tarski(A_23))
      | r2_hidden(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_22,c_163])).

tff(c_171,plain,(
    ! [B_66,A_67] :
      ( k10_relat_1(B_66,A_67) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_66),A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_274,plain,(
    ! [B_89,A_90] :
      ( k10_relat_1(B_89,k1_tarski(A_90)) = k1_xboole_0
      | ~ v1_relat_1(B_89)
      | r2_hidden(A_90,k2_relat_1(B_89)) ) ),
    inference(resolution,[status(thm)],[c_166,c_171])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_434,plain,(
    ! [A_119,B_120] :
      ( r1_tarski(A_119,k2_relat_1(B_120))
      | k10_relat_1(B_120,k1_tarski('#skF_1'(A_119,k2_relat_1(B_120)))) = k1_xboole_0
      | ~ v1_relat_1(B_120) ) ),
    inference(resolution,[status(thm)],[c_274,c_6])).

tff(c_30,plain,(
    ! [C_28] :
      ( k10_relat_1('#skF_4',k1_tarski(C_28)) != k1_xboole_0
      | ~ r2_hidden(C_28,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_441,plain,(
    ! [A_119] :
      ( ~ r2_hidden('#skF_1'(A_119,k2_relat_1('#skF_4')),'#skF_3')
      | r1_tarski(A_119,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_30])).

tff(c_450,plain,(
    ! [A_121] :
      ( ~ r2_hidden('#skF_1'(A_121,k2_relat_1('#skF_4')),'#skF_3')
      | r1_tarski(A_121,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_441])).

tff(c_458,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_450])).

tff(c_463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.28  
% 2.17/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.17/1.28  
% 2.17/1.28  %Foreground sorts:
% 2.17/1.28  
% 2.17/1.28  
% 2.17/1.28  %Background operators:
% 2.17/1.28  
% 2.17/1.28  
% 2.17/1.28  %Foreground operators:
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.17/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.17/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.28  
% 2.17/1.29  tff(f_78, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_funct_1)).
% 2.17/1.29  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.17/1.29  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.17/1.29  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.17/1.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.17/1.29  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.17/1.29  tff(c_28, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.17/1.29  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.29  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.17/1.29  tff(c_22, plain, (![A_23, B_24]: (r1_xboole_0(k1_tarski(A_23), B_24) | r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.29  tff(c_145, plain, (![A_60, B_61]: (r2_hidden('#skF_2'(A_60, B_61), k3_xboole_0(A_60, B_61)) | r1_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.17/1.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.29  tff(c_94, plain, (![A_42, B_43, C_44]: (~r1_xboole_0(A_42, B_43) | ~r2_hidden(C_44, k3_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.17/1.29  tff(c_101, plain, (![A_1, B_2, C_44]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_44, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_94])).
% 2.17/1.29  tff(c_163, plain, (![B_62, A_63]: (~r1_xboole_0(B_62, A_63) | r1_xboole_0(A_63, B_62))), inference(resolution, [status(thm)], [c_145, c_101])).
% 2.17/1.29  tff(c_166, plain, (![B_24, A_23]: (r1_xboole_0(B_24, k1_tarski(A_23)) | r2_hidden(A_23, B_24))), inference(resolution, [status(thm)], [c_22, c_163])).
% 2.17/1.29  tff(c_171, plain, (![B_66, A_67]: (k10_relat_1(B_66, A_67)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_66), A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.17/1.29  tff(c_274, plain, (![B_89, A_90]: (k10_relat_1(B_89, k1_tarski(A_90))=k1_xboole_0 | ~v1_relat_1(B_89) | r2_hidden(A_90, k2_relat_1(B_89)))), inference(resolution, [status(thm)], [c_166, c_171])).
% 2.17/1.29  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.29  tff(c_434, plain, (![A_119, B_120]: (r1_tarski(A_119, k2_relat_1(B_120)) | k10_relat_1(B_120, k1_tarski('#skF_1'(A_119, k2_relat_1(B_120))))=k1_xboole_0 | ~v1_relat_1(B_120))), inference(resolution, [status(thm)], [c_274, c_6])).
% 2.17/1.29  tff(c_30, plain, (![C_28]: (k10_relat_1('#skF_4', k1_tarski(C_28))!=k1_xboole_0 | ~r2_hidden(C_28, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.17/1.29  tff(c_441, plain, (![A_119]: (~r2_hidden('#skF_1'(A_119, k2_relat_1('#skF_4')), '#skF_3') | r1_tarski(A_119, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_434, c_30])).
% 2.17/1.29  tff(c_450, plain, (![A_121]: (~r2_hidden('#skF_1'(A_121, k2_relat_1('#skF_4')), '#skF_3') | r1_tarski(A_121, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_441])).
% 2.17/1.29  tff(c_458, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_450])).
% 2.17/1.29  tff(c_463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_458])).
% 2.17/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  Inference rules
% 2.17/1.29  ----------------------
% 2.17/1.29  #Ref     : 0
% 2.17/1.29  #Sup     : 103
% 2.17/1.29  #Fact    : 0
% 2.17/1.29  #Define  : 0
% 2.17/1.29  #Split   : 0
% 2.17/1.29  #Chain   : 0
% 2.17/1.29  #Close   : 0
% 2.17/1.29  
% 2.17/1.29  Ordering : KBO
% 2.17/1.29  
% 2.17/1.29  Simplification rules
% 2.17/1.29  ----------------------
% 2.17/1.29  #Subsume      : 48
% 2.17/1.29  #Demod        : 1
% 2.17/1.29  #Tautology    : 28
% 2.17/1.29  #SimpNegUnit  : 1
% 2.17/1.29  #BackRed      : 0
% 2.17/1.29  
% 2.17/1.29  #Partial instantiations: 0
% 2.17/1.29  #Strategies tried      : 1
% 2.17/1.29  
% 2.17/1.29  Timing (in seconds)
% 2.17/1.29  ----------------------
% 2.17/1.29  Preprocessing        : 0.29
% 2.17/1.29  Parsing              : 0.16
% 2.17/1.29  CNF conversion       : 0.02
% 2.17/1.29  Main loop            : 0.25
% 2.17/1.29  Inferencing          : 0.10
% 2.17/1.29  Reduction            : 0.07
% 2.17/1.29  Demodulation         : 0.05
% 2.17/1.29  BG Simplification    : 0.01
% 2.17/1.29  Subsumption          : 0.05
% 2.17/1.29  Abstraction          : 0.01
% 2.17/1.29  MUC search           : 0.00
% 2.17/1.29  Cooper               : 0.00
% 2.17/1.29  Total                : 0.56
% 2.17/1.29  Index Insertion      : 0.00
% 2.17/1.29  Index Deletion       : 0.00
% 2.17/1.29  Index Matching       : 0.00
% 2.17/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
