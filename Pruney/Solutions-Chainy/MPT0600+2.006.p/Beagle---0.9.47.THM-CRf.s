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
% DateTime   : Thu Dec  3 10:02:14 EST 2020

% Result     : Theorem 8.58s
% Output     : CNFRefutation 8.58s
% Verified   : 
% Statistics : Number of formulae       :   63 (  95 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 163 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_1 > #skF_3 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_86,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_94,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8')
    | r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_134,plain,(
    r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_72,plain,(
    ! [A_32,B_34] :
      ( k9_relat_1(A_32,k1_tarski(B_34)) = k11_relat_1(A_32,B_34)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_88,plain,
    ( ~ r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6'))
    | ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_169,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_88])).

tff(c_293,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_hidden('#skF_5'(A_112,B_113,C_114),B_113)
      | ~ r2_hidden(A_112,k9_relat_1(C_114,B_113))
      | ~ v1_relat_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_147,plain,(
    ! [D_87,B_88,A_89] :
      ( D_87 = B_88
      | D_87 = A_89
      | ~ r2_hidden(D_87,k2_tarski(A_89,B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_156,plain,(
    ! [D_87,A_7] :
      ( D_87 = A_7
      | D_87 = A_7
      | ~ r2_hidden(D_87,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_147])).

tff(c_623,plain,(
    ! [A_203,A_204,C_205] :
      ( '#skF_5'(A_203,k1_tarski(A_204),C_205) = A_204
      | ~ r2_hidden(A_203,k9_relat_1(C_205,k1_tarski(A_204)))
      | ~ v1_relat_1(C_205) ) ),
    inference(resolution,[status(thm)],[c_293,c_156])).

tff(c_637,plain,(
    ! [A_206,B_207,A_208] :
      ( '#skF_5'(A_206,k1_tarski(B_207),A_208) = B_207
      | ~ r2_hidden(A_206,k11_relat_1(A_208,B_207))
      | ~ v1_relat_1(A_208)
      | ~ v1_relat_1(A_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_623])).

tff(c_648,plain,
    ( '#skF_5'('#skF_7',k1_tarski('#skF_6'),'#skF_8') = '#skF_6'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_134,c_637])).

tff(c_653,plain,(
    '#skF_5'('#skF_7',k1_tarski('#skF_6'),'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_648])).

tff(c_78,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden(k4_tarski('#skF_5'(A_35,B_36,C_37),A_35),C_37)
      | ~ r2_hidden(A_35,k9_relat_1(C_37,B_36))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_657,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8')
    | ~ r2_hidden('#skF_7',k9_relat_1('#skF_8',k1_tarski('#skF_6')))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_78])).

tff(c_667,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8')
    | ~ r2_hidden('#skF_7',k9_relat_1('#skF_8',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_657])).

tff(c_668,plain,(
    ~ r2_hidden('#skF_7',k9_relat_1('#skF_8',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_667])).

tff(c_676,plain,
    ( ~ r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_668])).

tff(c_679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_134,c_676])).

tff(c_681,plain,(
    ~ r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_680,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_717,plain,(
    ! [A_241,C_242,B_243] :
      ( r2_hidden(A_241,k1_relat_1(C_242))
      | ~ r2_hidden(k4_tarski(A_241,B_243),C_242)
      | ~ v1_relat_1(C_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_736,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_680,c_717])).

tff(c_763,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_736])).

tff(c_104,plain,(
    ! [D_45,B_46] : r2_hidden(D_45,k2_tarski(D_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_107,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_104])).

tff(c_3754,plain,(
    ! [A_10907,C_10908,B_10909,D_10910] :
      ( r2_hidden(A_10907,k9_relat_1(C_10908,B_10909))
      | ~ r2_hidden(D_10910,B_10909)
      | ~ r2_hidden(k4_tarski(D_10910,A_10907),C_10908)
      | ~ r2_hidden(D_10910,k1_relat_1(C_10908))
      | ~ v1_relat_1(C_10908) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5283,plain,(
    ! [A_16073,C_16074,A_16075] :
      ( r2_hidden(A_16073,k9_relat_1(C_16074,k1_tarski(A_16075)))
      | ~ r2_hidden(k4_tarski(A_16075,A_16073),C_16074)
      | ~ r2_hidden(A_16075,k1_relat_1(C_16074))
      | ~ v1_relat_1(C_16074) ) ),
    inference(resolution,[status(thm)],[c_107,c_3754])).

tff(c_11018,plain,(
    ! [A_26204,A_26205,B_26206] :
      ( r2_hidden(A_26204,k11_relat_1(A_26205,B_26206))
      | ~ r2_hidden(k4_tarski(B_26206,A_26204),A_26205)
      | ~ r2_hidden(B_26206,k1_relat_1(A_26205))
      | ~ v1_relat_1(A_26205)
      | ~ v1_relat_1(A_26205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_5283])).

tff(c_11241,plain,
    ( r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6'))
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_680,c_11018])).

tff(c_11324,plain,(
    r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_763,c_11241])).

tff(c_11326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_681,c_11324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.58/2.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.58/2.84  
% 8.58/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.58/2.85  %$ r2_hidden > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_1 > #skF_3 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_4
% 8.58/2.85  
% 8.58/2.85  %Foreground sorts:
% 8.58/2.85  
% 8.58/2.85  
% 8.58/2.85  %Background operators:
% 8.58/2.85  
% 8.58/2.85  
% 8.58/2.85  %Foreground operators:
% 8.58/2.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.58/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.58/2.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.58/2.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.58/2.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.58/2.85  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.58/2.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.58/2.85  tff('#skF_7', type, '#skF_7': $i).
% 8.58/2.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.58/2.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.58/2.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.58/2.85  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 8.58/2.85  tff('#skF_6', type, '#skF_6': $i).
% 8.58/2.85  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.58/2.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.58/2.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.58/2.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.58/2.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.58/2.85  tff('#skF_8', type, '#skF_8': $i).
% 8.58/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.58/2.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.58/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.58/2.85  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.58/2.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.58/2.85  
% 8.58/2.86  tff(f_99, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 8.58/2.86  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 8.58/2.86  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 8.58/2.86  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.58/2.86  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 8.58/2.86  tff(f_92, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 8.58/2.86  tff(c_86, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.58/2.86  tff(c_94, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8') | r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.58/2.86  tff(c_134, plain, (r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6'))), inference(splitLeft, [status(thm)], [c_94])).
% 8.58/2.86  tff(c_72, plain, (![A_32, B_34]: (k9_relat_1(A_32, k1_tarski(B_34))=k11_relat_1(A_32, B_34) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.58/2.86  tff(c_88, plain, (~r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6')) | ~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.58/2.86  tff(c_169, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_88])).
% 8.58/2.86  tff(c_293, plain, (![A_112, B_113, C_114]: (r2_hidden('#skF_5'(A_112, B_113, C_114), B_113) | ~r2_hidden(A_112, k9_relat_1(C_114, B_113)) | ~v1_relat_1(C_114))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.58/2.86  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.58/2.86  tff(c_147, plain, (![D_87, B_88, A_89]: (D_87=B_88 | D_87=A_89 | ~r2_hidden(D_87, k2_tarski(A_89, B_88)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.58/2.86  tff(c_156, plain, (![D_87, A_7]: (D_87=A_7 | D_87=A_7 | ~r2_hidden(D_87, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_147])).
% 8.58/2.86  tff(c_623, plain, (![A_203, A_204, C_205]: ('#skF_5'(A_203, k1_tarski(A_204), C_205)=A_204 | ~r2_hidden(A_203, k9_relat_1(C_205, k1_tarski(A_204))) | ~v1_relat_1(C_205))), inference(resolution, [status(thm)], [c_293, c_156])).
% 8.58/2.86  tff(c_637, plain, (![A_206, B_207, A_208]: ('#skF_5'(A_206, k1_tarski(B_207), A_208)=B_207 | ~r2_hidden(A_206, k11_relat_1(A_208, B_207)) | ~v1_relat_1(A_208) | ~v1_relat_1(A_208))), inference(superposition, [status(thm), theory('equality')], [c_72, c_623])).
% 8.58/2.86  tff(c_648, plain, ('#skF_5'('#skF_7', k1_tarski('#skF_6'), '#skF_8')='#skF_6' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_134, c_637])).
% 8.58/2.86  tff(c_653, plain, ('#skF_5'('#skF_7', k1_tarski('#skF_6'), '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_648])).
% 8.58/2.86  tff(c_78, plain, (![A_35, B_36, C_37]: (r2_hidden(k4_tarski('#skF_5'(A_35, B_36, C_37), A_35), C_37) | ~r2_hidden(A_35, k9_relat_1(C_37, B_36)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.58/2.86  tff(c_657, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8') | ~r2_hidden('#skF_7', k9_relat_1('#skF_8', k1_tarski('#skF_6'))) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_653, c_78])).
% 8.58/2.86  tff(c_667, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8') | ~r2_hidden('#skF_7', k9_relat_1('#skF_8', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_657])).
% 8.58/2.86  tff(c_668, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_8', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_169, c_667])).
% 8.58/2.86  tff(c_676, plain, (~r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_72, c_668])).
% 8.58/2.86  tff(c_679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_134, c_676])).
% 8.58/2.86  tff(c_681, plain, (~r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6'))), inference(splitRight, [status(thm)], [c_94])).
% 8.58/2.86  tff(c_680, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_94])).
% 8.58/2.86  tff(c_717, plain, (![A_241, C_242, B_243]: (r2_hidden(A_241, k1_relat_1(C_242)) | ~r2_hidden(k4_tarski(A_241, B_243), C_242) | ~v1_relat_1(C_242))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.58/2.86  tff(c_736, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_680, c_717])).
% 8.58/2.86  tff(c_763, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_736])).
% 8.58/2.86  tff(c_104, plain, (![D_45, B_46]: (r2_hidden(D_45, k2_tarski(D_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.58/2.86  tff(c_107, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_104])).
% 8.58/2.86  tff(c_3754, plain, (![A_10907, C_10908, B_10909, D_10910]: (r2_hidden(A_10907, k9_relat_1(C_10908, B_10909)) | ~r2_hidden(D_10910, B_10909) | ~r2_hidden(k4_tarski(D_10910, A_10907), C_10908) | ~r2_hidden(D_10910, k1_relat_1(C_10908)) | ~v1_relat_1(C_10908))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.58/2.86  tff(c_5283, plain, (![A_16073, C_16074, A_16075]: (r2_hidden(A_16073, k9_relat_1(C_16074, k1_tarski(A_16075))) | ~r2_hidden(k4_tarski(A_16075, A_16073), C_16074) | ~r2_hidden(A_16075, k1_relat_1(C_16074)) | ~v1_relat_1(C_16074))), inference(resolution, [status(thm)], [c_107, c_3754])).
% 8.58/2.86  tff(c_11018, plain, (![A_26204, A_26205, B_26206]: (r2_hidden(A_26204, k11_relat_1(A_26205, B_26206)) | ~r2_hidden(k4_tarski(B_26206, A_26204), A_26205) | ~r2_hidden(B_26206, k1_relat_1(A_26205)) | ~v1_relat_1(A_26205) | ~v1_relat_1(A_26205))), inference(superposition, [status(thm), theory('equality')], [c_72, c_5283])).
% 8.58/2.86  tff(c_11241, plain, (r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6')) | ~r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_680, c_11018])).
% 8.58/2.86  tff(c_11324, plain, (r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_763, c_11241])).
% 8.58/2.86  tff(c_11326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_681, c_11324])).
% 8.58/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.58/2.86  
% 8.58/2.86  Inference rules
% 8.58/2.86  ----------------------
% 8.58/2.86  #Ref     : 0
% 8.58/2.86  #Sup     : 1774
% 8.58/2.86  #Fact    : 30
% 8.58/2.86  #Define  : 0
% 8.58/2.86  #Split   : 6
% 8.58/2.86  #Chain   : 0
% 8.58/2.86  #Close   : 0
% 8.58/2.86  
% 8.58/2.86  Ordering : KBO
% 8.58/2.86  
% 8.58/2.86  Simplification rules
% 8.58/2.86  ----------------------
% 8.58/2.86  #Subsume      : 358
% 8.58/2.86  #Demod        : 197
% 8.58/2.86  #Tautology    : 336
% 8.58/2.86  #SimpNegUnit  : 2
% 8.58/2.86  #BackRed      : 0
% 8.58/2.86  
% 8.58/2.86  #Partial instantiations: 8804
% 8.58/2.86  #Strategies tried      : 1
% 8.58/2.86  
% 8.58/2.86  Timing (in seconds)
% 8.58/2.86  ----------------------
% 8.58/2.86  Preprocessing        : 0.34
% 8.58/2.86  Parsing              : 0.16
% 8.58/2.86  CNF conversion       : 0.03
% 8.58/2.86  Main loop            : 1.72
% 8.58/2.86  Inferencing          : 0.78
% 8.58/2.86  Reduction            : 0.43
% 8.58/2.86  Demodulation         : 0.32
% 8.58/2.86  BG Simplification    : 0.08
% 8.58/2.86  Subsumption          : 0.31
% 8.58/2.86  Abstraction          : 0.12
% 8.58/2.86  MUC search           : 0.00
% 8.58/2.86  Cooper               : 0.00
% 8.58/2.86  Total                : 2.09
% 8.58/2.86  Index Insertion      : 0.00
% 8.58/2.86  Index Deletion       : 0.00
% 8.58/2.86  Index Matching       : 0.00
% 8.58/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
