%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:13 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :   62 (  93 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 163 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_70,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_78,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8')
    | r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_101,plain,(
    r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_56,plain,(
    ! [A_21,B_23] :
      ( k9_relat_1(A_21,k1_tarski(B_23)) = k11_relat_1(A_21,B_23)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,
    ( ~ r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6'))
    | ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_173,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_72])).

tff(c_293,plain,(
    ! [A_84,B_85,C_86] :
      ( r2_hidden('#skF_5'(A_84,B_85,C_86),B_85)
      | ~ r2_hidden(A_84,k9_relat_1(C_86,B_85))
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_112,plain,(
    ! [D_57,B_58,A_59] :
      ( D_57 = B_58
      | D_57 = A_59
      | ~ r2_hidden(D_57,k2_tarski(A_59,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_115,plain,(
    ! [D_57,A_7] :
      ( D_57 = A_7
      | D_57 = A_7
      | ~ r2_hidden(D_57,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_112])).

tff(c_381,plain,(
    ! [A_107,A_108,C_109] :
      ( '#skF_5'(A_107,k1_tarski(A_108),C_109) = A_108
      | ~ r2_hidden(A_107,k9_relat_1(C_109,k1_tarski(A_108)))
      | ~ v1_relat_1(C_109) ) ),
    inference(resolution,[status(thm)],[c_293,c_115])).

tff(c_509,plain,(
    ! [A_131,B_132,A_133] :
      ( '#skF_5'(A_131,k1_tarski(B_132),A_133) = B_132
      | ~ r2_hidden(A_131,k11_relat_1(A_133,B_132))
      | ~ v1_relat_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_381])).

tff(c_520,plain,
    ( '#skF_5'('#skF_7',k1_tarski('#skF_6'),'#skF_8') = '#skF_6'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_101,c_509])).

tff(c_525,plain,(
    '#skF_5'('#skF_7',k1_tarski('#skF_6'),'#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_520])).

tff(c_62,plain,(
    ! [A_24,B_25,C_26] :
      ( r2_hidden(k4_tarski('#skF_5'(A_24,B_25,C_26),A_24),C_26)
      | ~ r2_hidden(A_24,k9_relat_1(C_26,B_25))
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_529,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8')
    | ~ r2_hidden('#skF_7',k9_relat_1('#skF_8',k1_tarski('#skF_6')))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_62])).

tff(c_539,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8')
    | ~ r2_hidden('#skF_7',k9_relat_1('#skF_8',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_529])).

tff(c_540,plain,(
    ~ r2_hidden('#skF_7',k9_relat_1('#skF_8',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_539])).

tff(c_548,plain,
    ( ~ r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_540])).

tff(c_551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_101,c_548])).

tff(c_553,plain,(
    ~ r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_552,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_632,plain,(
    ! [A_159,C_160,B_161] :
      ( r2_hidden(A_159,k1_relat_1(C_160))
      | ~ r2_hidden(k4_tarski(A_159,B_161),C_160)
      | ~ v1_relat_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_651,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_552,c_632])).

tff(c_682,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_651])).

tff(c_81,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87,plain,(
    ! [A_37] : r2_hidden(A_37,k1_tarski(A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_4])).

tff(c_979,plain,(
    ! [A_220,C_221,B_222,D_223] :
      ( r2_hidden(A_220,k9_relat_1(C_221,B_222))
      | ~ r2_hidden(D_223,B_222)
      | ~ r2_hidden(k4_tarski(D_223,A_220),C_221)
      | ~ r2_hidden(D_223,k1_relat_1(C_221))
      | ~ v1_relat_1(C_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2576,plain,(
    ! [A_4453,C_4454,A_4455] :
      ( r2_hidden(A_4453,k9_relat_1(C_4454,k1_tarski(A_4455)))
      | ~ r2_hidden(k4_tarski(A_4455,A_4453),C_4454)
      | ~ r2_hidden(A_4455,k1_relat_1(C_4454))
      | ~ v1_relat_1(C_4454) ) ),
    inference(resolution,[status(thm)],[c_87,c_979])).

tff(c_10284,plain,(
    ! [A_17491,A_17492,B_17493] :
      ( r2_hidden(A_17491,k11_relat_1(A_17492,B_17493))
      | ~ r2_hidden(k4_tarski(B_17493,A_17491),A_17492)
      | ~ r2_hidden(B_17493,k1_relat_1(A_17492))
      | ~ v1_relat_1(A_17492)
      | ~ v1_relat_1(A_17492) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2576])).

tff(c_10467,plain,
    ( r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6'))
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_552,c_10284])).

tff(c_10544,plain,(
    r2_hidden('#skF_7',k11_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_682,c_10467])).

tff(c_10546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_553,c_10544])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:27:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.67/2.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/2.62  
% 7.67/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/2.62  %$ r2_hidden > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_8
% 7.67/2.62  
% 7.67/2.62  %Foreground sorts:
% 7.67/2.62  
% 7.67/2.62  
% 7.67/2.62  %Background operators:
% 7.67/2.62  
% 7.67/2.62  
% 7.67/2.62  %Foreground operators:
% 7.67/2.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.67/2.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.67/2.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.67/2.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.67/2.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.67/2.62  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 7.67/2.62  tff('#skF_7', type, '#skF_7': $i).
% 7.67/2.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.67/2.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.67/2.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.67/2.62  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 7.67/2.62  tff('#skF_6', type, '#skF_6': $i).
% 7.67/2.62  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.67/2.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.67/2.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.67/2.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.67/2.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 7.67/2.62  tff('#skF_8', type, '#skF_8': $i).
% 7.67/2.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.67/2.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.67/2.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.67/2.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.67/2.62  
% 7.67/2.63  tff(f_89, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 7.67/2.63  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 7.67/2.63  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 7.67/2.63  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.67/2.63  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 7.67/2.63  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 7.67/2.63  tff(c_70, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.67/2.63  tff(c_78, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8') | r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.67/2.63  tff(c_101, plain, (r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6'))), inference(splitLeft, [status(thm)], [c_78])).
% 7.67/2.63  tff(c_56, plain, (![A_21, B_23]: (k9_relat_1(A_21, k1_tarski(B_23))=k11_relat_1(A_21, B_23) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.67/2.63  tff(c_72, plain, (~r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6')) | ~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.67/2.63  tff(c_173, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_72])).
% 7.67/2.63  tff(c_293, plain, (![A_84, B_85, C_86]: (r2_hidden('#skF_5'(A_84, B_85, C_86), B_85) | ~r2_hidden(A_84, k9_relat_1(C_86, B_85)) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.67/2.63  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.67/2.63  tff(c_112, plain, (![D_57, B_58, A_59]: (D_57=B_58 | D_57=A_59 | ~r2_hidden(D_57, k2_tarski(A_59, B_58)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.67/2.63  tff(c_115, plain, (![D_57, A_7]: (D_57=A_7 | D_57=A_7 | ~r2_hidden(D_57, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_112])).
% 7.67/2.63  tff(c_381, plain, (![A_107, A_108, C_109]: ('#skF_5'(A_107, k1_tarski(A_108), C_109)=A_108 | ~r2_hidden(A_107, k9_relat_1(C_109, k1_tarski(A_108))) | ~v1_relat_1(C_109))), inference(resolution, [status(thm)], [c_293, c_115])).
% 7.67/2.63  tff(c_509, plain, (![A_131, B_132, A_133]: ('#skF_5'(A_131, k1_tarski(B_132), A_133)=B_132 | ~r2_hidden(A_131, k11_relat_1(A_133, B_132)) | ~v1_relat_1(A_133) | ~v1_relat_1(A_133))), inference(superposition, [status(thm), theory('equality')], [c_56, c_381])).
% 7.67/2.63  tff(c_520, plain, ('#skF_5'('#skF_7', k1_tarski('#skF_6'), '#skF_8')='#skF_6' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_101, c_509])).
% 7.67/2.63  tff(c_525, plain, ('#skF_5'('#skF_7', k1_tarski('#skF_6'), '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_520])).
% 7.67/2.63  tff(c_62, plain, (![A_24, B_25, C_26]: (r2_hidden(k4_tarski('#skF_5'(A_24, B_25, C_26), A_24), C_26) | ~r2_hidden(A_24, k9_relat_1(C_26, B_25)) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.67/2.63  tff(c_529, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8') | ~r2_hidden('#skF_7', k9_relat_1('#skF_8', k1_tarski('#skF_6'))) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_525, c_62])).
% 7.67/2.63  tff(c_539, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8') | ~r2_hidden('#skF_7', k9_relat_1('#skF_8', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_529])).
% 7.67/2.63  tff(c_540, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_8', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_173, c_539])).
% 7.67/2.63  tff(c_548, plain, (~r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_56, c_540])).
% 7.67/2.63  tff(c_551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_101, c_548])).
% 7.67/2.63  tff(c_553, plain, (~r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6'))), inference(splitRight, [status(thm)], [c_78])).
% 7.67/2.63  tff(c_552, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 7.67/2.63  tff(c_632, plain, (![A_159, C_160, B_161]: (r2_hidden(A_159, k1_relat_1(C_160)) | ~r2_hidden(k4_tarski(A_159, B_161), C_160) | ~v1_relat_1(C_160))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.67/2.63  tff(c_651, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_552, c_632])).
% 7.67/2.63  tff(c_682, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_651])).
% 7.67/2.63  tff(c_81, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.67/2.63  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.67/2.63  tff(c_87, plain, (![A_37]: (r2_hidden(A_37, k1_tarski(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_81, c_4])).
% 7.67/2.63  tff(c_979, plain, (![A_220, C_221, B_222, D_223]: (r2_hidden(A_220, k9_relat_1(C_221, B_222)) | ~r2_hidden(D_223, B_222) | ~r2_hidden(k4_tarski(D_223, A_220), C_221) | ~r2_hidden(D_223, k1_relat_1(C_221)) | ~v1_relat_1(C_221))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.67/2.63  tff(c_2576, plain, (![A_4453, C_4454, A_4455]: (r2_hidden(A_4453, k9_relat_1(C_4454, k1_tarski(A_4455))) | ~r2_hidden(k4_tarski(A_4455, A_4453), C_4454) | ~r2_hidden(A_4455, k1_relat_1(C_4454)) | ~v1_relat_1(C_4454))), inference(resolution, [status(thm)], [c_87, c_979])).
% 7.67/2.63  tff(c_10284, plain, (![A_17491, A_17492, B_17493]: (r2_hidden(A_17491, k11_relat_1(A_17492, B_17493)) | ~r2_hidden(k4_tarski(B_17493, A_17491), A_17492) | ~r2_hidden(B_17493, k1_relat_1(A_17492)) | ~v1_relat_1(A_17492) | ~v1_relat_1(A_17492))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2576])).
% 7.67/2.63  tff(c_10467, plain, (r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6')) | ~r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_552, c_10284])).
% 7.67/2.63  tff(c_10544, plain, (r2_hidden('#skF_7', k11_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_682, c_10467])).
% 7.67/2.63  tff(c_10546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_553, c_10544])).
% 7.67/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/2.63  
% 7.67/2.63  Inference rules
% 7.67/2.63  ----------------------
% 7.67/2.63  #Ref     : 0
% 7.67/2.63  #Sup     : 1641
% 7.67/2.63  #Fact    : 30
% 7.67/2.63  #Define  : 0
% 7.67/2.63  #Split   : 6
% 7.67/2.63  #Chain   : 0
% 7.67/2.63  #Close   : 0
% 7.67/2.63  
% 7.67/2.63  Ordering : KBO
% 7.67/2.63  
% 7.67/2.63  Simplification rules
% 7.67/2.63  ----------------------
% 7.67/2.63  #Subsume      : 371
% 7.67/2.63  #Demod        : 203
% 7.67/2.63  #Tautology    : 336
% 7.67/2.63  #SimpNegUnit  : 2
% 7.67/2.63  #BackRed      : 0
% 7.67/2.63  
% 7.67/2.63  #Partial instantiations: 7540
% 7.67/2.63  #Strategies tried      : 1
% 7.67/2.63  
% 7.67/2.63  Timing (in seconds)
% 7.67/2.63  ----------------------
% 7.67/2.63  Preprocessing        : 0.33
% 7.67/2.63  Parsing              : 0.16
% 7.67/2.63  CNF conversion       : 0.03
% 7.67/2.63  Main loop            : 1.55
% 7.67/2.63  Inferencing          : 0.73
% 7.67/2.63  Reduction            : 0.36
% 7.67/2.63  Demodulation         : 0.26
% 7.67/2.63  BG Simplification    : 0.07
% 7.67/2.63  Subsumption          : 0.27
% 7.67/2.63  Abstraction          : 0.09
% 7.67/2.63  MUC search           : 0.00
% 7.67/2.63  Cooper               : 0.00
% 7.67/2.63  Total                : 1.90
% 7.67/2.63  Index Insertion      : 0.00
% 7.67/2.63  Index Deletion       : 0.00
% 7.67/2.63  Index Matching       : 0.00
% 7.67/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
