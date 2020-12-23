%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:34 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   47 (  68 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  98 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [A_25,B_26] :
      ( ~ r2_hidden('#skF_1'(A_25,B_26),B_26)
      | r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,k1_relat_1(B_16))
      | k11_relat_1(B_16,A_15) = k1_xboole_0
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_135,plain,(
    ! [B_47,A_48] :
      ( k1_tarski(k1_funct_1(B_47,A_48)) = k11_relat_1(B_47,A_48)
      | ~ r2_hidden(A_48,k1_relat_1(B_47))
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_194,plain,(
    ! [B_60,A_61] :
      ( k1_tarski(k1_funct_1(B_60,A_61)) = k11_relat_1(B_60,A_61)
      | ~ v1_funct_1(B_60)
      | k11_relat_1(B_60,A_61) = k1_xboole_0
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_18,c_135])).

tff(c_14,plain,(
    ! [A_10,B_12] :
      ( k9_relat_1(A_10,k1_tarski(B_12)) = k11_relat_1(A_10,B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_69,plain,(
    ! [B_33,A_34] :
      ( k2_relat_1(k7_relat_1(B_33,A_34)) = k9_relat_1(B_33,A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_3',k1_tarski('#skF_2'))),k1_tarski(k1_funct_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_75,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k1_tarski('#skF_2')),k1_tarski(k1_funct_1('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_24])).

tff(c_81,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k1_tarski('#skF_2')),k1_tarski(k1_funct_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_75])).

tff(c_85,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_3','#skF_2'),k1_tarski(k1_funct_1('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_81])).

tff(c_87,plain,(
    ~ r1_tarski(k11_relat_1('#skF_3','#skF_2'),k1_tarski(k1_funct_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_85])).

tff(c_200,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_3','#skF_2'),k11_relat_1('#skF_3','#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | k11_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_87])).

tff(c_215,plain,(
    k11_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_54,c_200])).

tff(c_221,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_87])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.89/1.21  
% 1.89/1.21  %Foreground sorts:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Background operators:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Foreground operators:
% 1.89/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.89/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.89/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.21  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 1.89/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.89/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.21  
% 1.89/1.22  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.89/1.22  tff(f_69, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 1.89/1.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.89/1.22  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 1.89/1.22  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 1.89/1.22  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 1.89/1.22  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.89/1.22  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.89/1.22  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.89/1.22  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.89/1.22  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.22  tff(c_49, plain, (![A_25, B_26]: (~r2_hidden('#skF_1'(A_25, B_26), B_26) | r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.22  tff(c_54, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_49])).
% 1.89/1.22  tff(c_18, plain, (![A_15, B_16]: (r2_hidden(A_15, k1_relat_1(B_16)) | k11_relat_1(B_16, A_15)=k1_xboole_0 | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.89/1.22  tff(c_135, plain, (![B_47, A_48]: (k1_tarski(k1_funct_1(B_47, A_48))=k11_relat_1(B_47, A_48) | ~r2_hidden(A_48, k1_relat_1(B_47)) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.89/1.22  tff(c_194, plain, (![B_60, A_61]: (k1_tarski(k1_funct_1(B_60, A_61))=k11_relat_1(B_60, A_61) | ~v1_funct_1(B_60) | k11_relat_1(B_60, A_61)=k1_xboole_0 | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_18, c_135])).
% 1.89/1.22  tff(c_14, plain, (![A_10, B_12]: (k9_relat_1(A_10, k1_tarski(B_12))=k11_relat_1(A_10, B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.89/1.22  tff(c_69, plain, (![B_33, A_34]: (k2_relat_1(k7_relat_1(B_33, A_34))=k9_relat_1(B_33, A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.89/1.22  tff(c_24, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_3', k1_tarski('#skF_2'))), k1_tarski(k1_funct_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.89/1.22  tff(c_75, plain, (~r1_tarski(k9_relat_1('#skF_3', k1_tarski('#skF_2')), k1_tarski(k1_funct_1('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_69, c_24])).
% 1.89/1.22  tff(c_81, plain, (~r1_tarski(k9_relat_1('#skF_3', k1_tarski('#skF_2')), k1_tarski(k1_funct_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_75])).
% 1.89/1.22  tff(c_85, plain, (~r1_tarski(k11_relat_1('#skF_3', '#skF_2'), k1_tarski(k1_funct_1('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_81])).
% 1.89/1.22  tff(c_87, plain, (~r1_tarski(k11_relat_1('#skF_3', '#skF_2'), k1_tarski(k1_funct_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_85])).
% 1.89/1.22  tff(c_200, plain, (~r1_tarski(k11_relat_1('#skF_3', '#skF_2'), k11_relat_1('#skF_3', '#skF_2')) | ~v1_funct_1('#skF_3') | k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_194, c_87])).
% 1.89/1.22  tff(c_215, plain, (k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_54, c_200])).
% 1.89/1.22  tff(c_221, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_87])).
% 1.89/1.22  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_221])).
% 1.89/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  Inference rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Ref     : 0
% 1.89/1.22  #Sup     : 40
% 1.89/1.22  #Fact    : 0
% 1.89/1.22  #Define  : 0
% 1.89/1.22  #Split   : 0
% 1.89/1.22  #Chain   : 0
% 1.89/1.22  #Close   : 0
% 1.89/1.22  
% 1.89/1.22  Ordering : KBO
% 1.89/1.22  
% 1.89/1.22  Simplification rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Subsume      : 5
% 1.89/1.22  #Demod        : 14
% 1.89/1.22  #Tautology    : 17
% 1.89/1.22  #SimpNegUnit  : 0
% 1.89/1.22  #BackRed      : 1
% 1.89/1.22  
% 1.89/1.22  #Partial instantiations: 0
% 1.89/1.22  #Strategies tried      : 1
% 1.89/1.22  
% 1.89/1.22  Timing (in seconds)
% 1.89/1.22  ----------------------
% 1.89/1.22  Preprocessing        : 0.28
% 1.89/1.22  Parsing              : 0.15
% 1.89/1.22  CNF conversion       : 0.02
% 1.89/1.22  Main loop            : 0.16
% 1.89/1.22  Inferencing          : 0.07
% 1.89/1.22  Reduction            : 0.05
% 1.89/1.22  Demodulation         : 0.03
% 1.89/1.22  BG Simplification    : 0.01
% 1.89/1.22  Subsumption          : 0.03
% 1.89/1.23  Abstraction          : 0.01
% 1.89/1.23  MUC search           : 0.00
% 1.89/1.23  Cooper               : 0.00
% 1.89/1.23  Total                : 0.47
% 1.89/1.23  Index Insertion      : 0.00
% 1.89/1.23  Index Deletion       : 0.00
% 1.89/1.23  Index Matching       : 0.00
% 1.89/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
