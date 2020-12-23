%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:34 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   44 (  65 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  96 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_10,plain,(
    ! [B_5] : r1_tarski(k1_xboole_0,k1_tarski(B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,k1_relat_1(B_12))
      | k11_relat_1(B_12,A_11) = k1_xboole_0
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_92,plain,(
    ! [B_30,A_31] :
      ( k1_tarski(k1_funct_1(B_30,A_31)) = k11_relat_1(B_30,A_31)
      | ~ r2_hidden(A_31,k1_relat_1(B_30))
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_97,plain,(
    ! [B_32,A_33] :
      ( k1_tarski(k1_funct_1(B_32,A_33)) = k11_relat_1(B_32,A_33)
      | ~ v1_funct_1(B_32)
      | k11_relat_1(B_32,A_33) = k1_xboole_0
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_16,c_92])).

tff(c_8,plain,(
    ! [B_5] : r1_tarski(k1_tarski(B_5),k1_tarski(B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_153,plain,(
    ! [B_38,A_39] :
      ( r1_tarski(k11_relat_1(B_38,A_39),k1_tarski(k1_funct_1(B_38,A_39)))
      | ~ v1_funct_1(B_38)
      | k11_relat_1(B_38,A_39) = k1_xboole_0
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_8])).

tff(c_12,plain,(
    ! [A_6,B_8] :
      ( k9_relat_1(A_6,k1_tarski(B_8)) = k11_relat_1(A_6,B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_80,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_78])).

tff(c_83,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_80])).

tff(c_85,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_83])).

tff(c_156,plain,
    ( ~ v1_funct_1('#skF_2')
    | k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_153,c_85])).

tff(c_165,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_156])).

tff(c_179,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_85])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.30  
% 2.06/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.30  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.06/1.30  
% 2.06/1.30  %Foreground sorts:
% 2.06/1.30  
% 2.06/1.30  
% 2.06/1.30  %Background operators:
% 2.06/1.30  
% 2.06/1.30  
% 2.06/1.30  %Foreground operators:
% 2.06/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.06/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.30  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.06/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.06/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.30  
% 2.06/1.31  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.06/1.31  tff(f_66, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 2.06/1.31  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.06/1.31  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 2.06/1.31  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.06/1.31  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.06/1.31  tff(c_10, plain, (![B_5]: (r1_tarski(k1_xboole_0, k1_tarski(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.31  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.06/1.31  tff(c_24, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.06/1.31  tff(c_16, plain, (![A_11, B_12]: (r2_hidden(A_11, k1_relat_1(B_12)) | k11_relat_1(B_12, A_11)=k1_xboole_0 | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.06/1.31  tff(c_92, plain, (![B_30, A_31]: (k1_tarski(k1_funct_1(B_30, A_31))=k11_relat_1(B_30, A_31) | ~r2_hidden(A_31, k1_relat_1(B_30)) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.06/1.31  tff(c_97, plain, (![B_32, A_33]: (k1_tarski(k1_funct_1(B_32, A_33))=k11_relat_1(B_32, A_33) | ~v1_funct_1(B_32) | k11_relat_1(B_32, A_33)=k1_xboole_0 | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_16, c_92])).
% 2.06/1.31  tff(c_8, plain, (![B_5]: (r1_tarski(k1_tarski(B_5), k1_tarski(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.31  tff(c_153, plain, (![B_38, A_39]: (r1_tarski(k11_relat_1(B_38, A_39), k1_tarski(k1_funct_1(B_38, A_39))) | ~v1_funct_1(B_38) | k11_relat_1(B_38, A_39)=k1_xboole_0 | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_97, c_8])).
% 2.06/1.31  tff(c_12, plain, (![A_6, B_8]: (k9_relat_1(A_6, k1_tarski(B_8))=k11_relat_1(A_6, B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.06/1.31  tff(c_14, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.31  tff(c_22, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.06/1.31  tff(c_78, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_22])).
% 2.06/1.31  tff(c_80, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_78])).
% 2.06/1.31  tff(c_83, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12, c_80])).
% 2.06/1.31  tff(c_85, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_83])).
% 2.06/1.31  tff(c_156, plain, (~v1_funct_1('#skF_2') | k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_153, c_85])).
% 2.06/1.31  tff(c_165, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_156])).
% 2.06/1.31  tff(c_179, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_85])).
% 2.06/1.31  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_179])).
% 2.06/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.31  
% 2.06/1.31  Inference rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Ref     : 0
% 2.06/1.31  #Sup     : 32
% 2.06/1.31  #Fact    : 0
% 2.06/1.31  #Define  : 0
% 2.06/1.31  #Split   : 3
% 2.06/1.31  #Chain   : 0
% 2.06/1.31  #Close   : 0
% 2.06/1.31  
% 2.06/1.31  Ordering : KBO
% 2.06/1.31  
% 2.06/1.31  Simplification rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Subsume      : 3
% 2.06/1.31  #Demod        : 18
% 2.06/1.31  #Tautology    : 15
% 2.06/1.31  #SimpNegUnit  : 0
% 2.06/1.31  #BackRed      : 4
% 2.06/1.31  
% 2.06/1.31  #Partial instantiations: 0
% 2.06/1.31  #Strategies tried      : 1
% 2.06/1.31  
% 2.06/1.31  Timing (in seconds)
% 2.06/1.31  ----------------------
% 2.06/1.31  Preprocessing        : 0.32
% 2.06/1.31  Parsing              : 0.17
% 2.06/1.31  CNF conversion       : 0.02
% 2.06/1.31  Main loop            : 0.16
% 2.06/1.31  Inferencing          : 0.06
% 2.06/1.31  Reduction            : 0.05
% 2.06/1.31  Demodulation         : 0.04
% 2.06/1.31  BG Simplification    : 0.01
% 2.06/1.31  Subsumption          : 0.03
% 2.06/1.31  Abstraction          : 0.01
% 2.06/1.31  MUC search           : 0.00
% 2.06/1.31  Cooper               : 0.00
% 2.06/1.31  Total                : 0.51
% 2.06/1.31  Index Insertion      : 0.00
% 2.06/1.31  Index Deletion       : 0.00
% 2.06/1.31  Index Matching       : 0.00
% 2.06/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
