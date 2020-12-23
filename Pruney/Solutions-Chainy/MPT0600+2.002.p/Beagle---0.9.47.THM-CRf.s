%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:13 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 152 expanded)
%              Number of leaves         :   27 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  106 ( 303 expanded)
%              Number of equality atoms :   20 (  63 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_7 > #skF_8 > #skF_3

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
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_65,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(c_58,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10')
    | r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_107,plain,(
    r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_50,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [A_50,B_52] :
      ( k9_relat_1(A_50,k1_tarski(B_52)) = k11_relat_1(A_50,B_52)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8'))
    | ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_108,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_109,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden('#skF_7'(A_72,B_73,C_74),B_73)
      | ~ r2_hidden(A_72,k9_relat_1(C_74,B_73))
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_87,plain,(
    ! [D_67,B_68,A_69] :
      ( D_67 = B_68
      | D_67 = A_69
      | ~ r2_hidden(D_67,k2_tarski(A_69,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_96,plain,(
    ! [D_67,A_7] :
      ( D_67 = A_7
      | D_67 = A_7
      | ~ r2_hidden(D_67,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_87])).

tff(c_121,plain,(
    ! [A_78,A_79,C_80] :
      ( '#skF_7'(A_78,k1_tarski(A_79),C_80) = A_79
      | ~ r2_hidden(A_78,k9_relat_1(C_80,k1_tarski(A_79)))
      | ~ v1_relat_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_109,c_96])).

tff(c_353,plain,(
    ! [A_117,B_118,A_119] :
      ( '#skF_7'(A_117,k1_tarski(B_118),A_119) = B_118
      | ~ r2_hidden(A_117,k11_relat_1(A_119,B_118))
      | ~ v1_relat_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_121])).

tff(c_367,plain,
    ( '#skF_7'('#skF_9',k1_tarski('#skF_8'),'#skF_10') = '#skF_8'
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_107,c_353])).

tff(c_373,plain,(
    '#skF_7'('#skF_9',k1_tarski('#skF_8'),'#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_367])).

tff(c_46,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden(k4_tarski('#skF_7'(A_53,B_54,C_55),A_53),C_55)
      | ~ r2_hidden(A_53,k9_relat_1(C_55,B_54))
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_377,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10')
    | ~ r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8')))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_46])).

tff(c_387,plain,
    ( r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10')
    | ~ r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_377])).

tff(c_388,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_387])).

tff(c_399,plain,
    ( ~ r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_388])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_107,c_399])).

tff(c_406,plain,(
    ~ r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_406])).

tff(c_411,plain,(
    ~ r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_410,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_68,plain,(
    ! [D_60,B_61] : r2_hidden(D_60,k2_tarski(D_60,B_61)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_68])).

tff(c_451,plain,(
    ! [D_132,A_133,B_134,E_135] :
      ( r2_hidden(D_132,k9_relat_1(A_133,B_134))
      | ~ r2_hidden(E_135,B_134)
      | ~ r2_hidden(k4_tarski(E_135,D_132),A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_471,plain,(
    ! [D_132,A_133,A_7] :
      ( r2_hidden(D_132,k9_relat_1(A_133,k1_tarski(A_7)))
      | ~ r2_hidden(k4_tarski(A_7,D_132),A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(resolution,[status(thm)],[c_71,c_451])).

tff(c_473,plain,(
    ! [D_136,A_137,A_138] :
      ( r2_hidden(D_136,k9_relat_1(A_137,k1_tarski(A_138)))
      | ~ r2_hidden(k4_tarski(A_138,D_136),A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(resolution,[status(thm)],[c_71,c_451])).

tff(c_414,plain,(
    ! [A_120,B_121,C_122] :
      ( r2_hidden('#skF_7'(A_120,B_121,C_122),B_121)
      | ~ r2_hidden(A_120,k9_relat_1(C_122,B_121))
      | ~ v1_relat_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_423,plain,(
    ! [A_120,A_7,C_122] :
      ( '#skF_7'(A_120,k1_tarski(A_7),C_122) = A_7
      | ~ r2_hidden(A_120,k9_relat_1(C_122,k1_tarski(A_7)))
      | ~ v1_relat_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_414,c_96])).

tff(c_484,plain,(
    ! [D_139,A_140,A_141] :
      ( '#skF_7'(D_139,k1_tarski(A_140),A_141) = A_140
      | ~ r2_hidden(k4_tarski(A_140,D_139),A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_473,c_423])).

tff(c_494,plain,
    ( '#skF_7'('#skF_9',k1_tarski('#skF_8'),'#skF_10') = '#skF_8'
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_410,c_484])).

tff(c_511,plain,(
    '#skF_7'('#skF_9',k1_tarski('#skF_8'),'#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_494])).

tff(c_48,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden('#skF_7'(A_53,B_54,C_55),k1_relat_1(C_55))
      | ~ r2_hidden(A_53,k9_relat_1(C_55,B_54))
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_521,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_10'))
    | ~ r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8')))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_48])).

tff(c_530,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_10'))
    | ~ r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_521])).

tff(c_534,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_530])).

tff(c_537,plain,
    ( ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_471,c_534])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_410,c_537])).

tff(c_546,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_10',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_530])).

tff(c_563,plain,
    ( r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_546])).

tff(c_569,plain,(
    r2_hidden('#skF_9',k11_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_563])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.35  
% 2.68/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.36  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_7 > #skF_8 > #skF_3
% 2.68/1.36  
% 2.68/1.36  %Foreground sorts:
% 2.68/1.36  
% 2.68/1.36  
% 2.68/1.36  %Background operators:
% 2.68/1.36  
% 2.68/1.36  
% 2.68/1.36  %Foreground operators:
% 2.68/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.68/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.68/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.68/1.36  tff('#skF_10', type, '#skF_10': $i).
% 2.68/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.36  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.68/1.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.68/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.68/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.68/1.36  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.68/1.36  tff('#skF_9', type, '#skF_9': $i).
% 2.68/1.36  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.68/1.36  tff('#skF_8', type, '#skF_8': $i).
% 2.68/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.68/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.68/1.36  
% 2.68/1.37  tff(f_72, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.68/1.37  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.68/1.37  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.68/1.37  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.68/1.37  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.68/1.37  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 2.68/1.37  tff(c_58, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10') | r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.68/1.37  tff(c_107, plain, (r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8'))), inference(splitLeft, [status(thm)], [c_58])).
% 2.68/1.37  tff(c_50, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.68/1.37  tff(c_40, plain, (![A_50, B_52]: (k9_relat_1(A_50, k1_tarski(B_52))=k11_relat_1(A_50, B_52) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.68/1.37  tff(c_52, plain, (~r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8')) | ~r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.68/1.37  tff(c_108, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10')), inference(splitLeft, [status(thm)], [c_52])).
% 2.68/1.37  tff(c_109, plain, (![A_72, B_73, C_74]: (r2_hidden('#skF_7'(A_72, B_73, C_74), B_73) | ~r2_hidden(A_72, k9_relat_1(C_74, B_73)) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.37  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.68/1.37  tff(c_87, plain, (![D_67, B_68, A_69]: (D_67=B_68 | D_67=A_69 | ~r2_hidden(D_67, k2_tarski(A_69, B_68)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.68/1.37  tff(c_96, plain, (![D_67, A_7]: (D_67=A_7 | D_67=A_7 | ~r2_hidden(D_67, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_87])).
% 2.68/1.37  tff(c_121, plain, (![A_78, A_79, C_80]: ('#skF_7'(A_78, k1_tarski(A_79), C_80)=A_79 | ~r2_hidden(A_78, k9_relat_1(C_80, k1_tarski(A_79))) | ~v1_relat_1(C_80))), inference(resolution, [status(thm)], [c_109, c_96])).
% 2.68/1.37  tff(c_353, plain, (![A_117, B_118, A_119]: ('#skF_7'(A_117, k1_tarski(B_118), A_119)=B_118 | ~r2_hidden(A_117, k11_relat_1(A_119, B_118)) | ~v1_relat_1(A_119) | ~v1_relat_1(A_119))), inference(superposition, [status(thm), theory('equality')], [c_40, c_121])).
% 2.68/1.37  tff(c_367, plain, ('#skF_7'('#skF_9', k1_tarski('#skF_8'), '#skF_10')='#skF_8' | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_107, c_353])).
% 2.68/1.37  tff(c_373, plain, ('#skF_7'('#skF_9', k1_tarski('#skF_8'), '#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_367])).
% 2.68/1.37  tff(c_46, plain, (![A_53, B_54, C_55]: (r2_hidden(k4_tarski('#skF_7'(A_53, B_54, C_55), A_53), C_55) | ~r2_hidden(A_53, k9_relat_1(C_55, B_54)) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.37  tff(c_377, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10') | ~r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8'))) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_373, c_46])).
% 2.68/1.37  tff(c_387, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10') | ~r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_377])).
% 2.68/1.37  tff(c_388, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_108, c_387])).
% 2.68/1.37  tff(c_399, plain, (~r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_40, c_388])).
% 2.68/1.37  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_107, c_399])).
% 2.68/1.37  tff(c_406, plain, (~r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_52])).
% 2.68/1.37  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_406])).
% 2.68/1.37  tff(c_411, plain, (~r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_58])).
% 2.68/1.37  tff(c_410, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10')), inference(splitRight, [status(thm)], [c_58])).
% 2.68/1.37  tff(c_68, plain, (![D_60, B_61]: (r2_hidden(D_60, k2_tarski(D_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.68/1.37  tff(c_71, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_68])).
% 2.68/1.37  tff(c_451, plain, (![D_132, A_133, B_134, E_135]: (r2_hidden(D_132, k9_relat_1(A_133, B_134)) | ~r2_hidden(E_135, B_134) | ~r2_hidden(k4_tarski(E_135, D_132), A_133) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.37  tff(c_471, plain, (![D_132, A_133, A_7]: (r2_hidden(D_132, k9_relat_1(A_133, k1_tarski(A_7))) | ~r2_hidden(k4_tarski(A_7, D_132), A_133) | ~v1_relat_1(A_133))), inference(resolution, [status(thm)], [c_71, c_451])).
% 2.68/1.37  tff(c_473, plain, (![D_136, A_137, A_138]: (r2_hidden(D_136, k9_relat_1(A_137, k1_tarski(A_138))) | ~r2_hidden(k4_tarski(A_138, D_136), A_137) | ~v1_relat_1(A_137))), inference(resolution, [status(thm)], [c_71, c_451])).
% 2.68/1.37  tff(c_414, plain, (![A_120, B_121, C_122]: (r2_hidden('#skF_7'(A_120, B_121, C_122), B_121) | ~r2_hidden(A_120, k9_relat_1(C_122, B_121)) | ~v1_relat_1(C_122))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.37  tff(c_423, plain, (![A_120, A_7, C_122]: ('#skF_7'(A_120, k1_tarski(A_7), C_122)=A_7 | ~r2_hidden(A_120, k9_relat_1(C_122, k1_tarski(A_7))) | ~v1_relat_1(C_122))), inference(resolution, [status(thm)], [c_414, c_96])).
% 2.68/1.37  tff(c_484, plain, (![D_139, A_140, A_141]: ('#skF_7'(D_139, k1_tarski(A_140), A_141)=A_140 | ~r2_hidden(k4_tarski(A_140, D_139), A_141) | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_473, c_423])).
% 2.68/1.37  tff(c_494, plain, ('#skF_7'('#skF_9', k1_tarski('#skF_8'), '#skF_10')='#skF_8' | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_410, c_484])).
% 2.68/1.37  tff(c_511, plain, ('#skF_7'('#skF_9', k1_tarski('#skF_8'), '#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_494])).
% 2.68/1.37  tff(c_48, plain, (![A_53, B_54, C_55]: (r2_hidden('#skF_7'(A_53, B_54, C_55), k1_relat_1(C_55)) | ~r2_hidden(A_53, k9_relat_1(C_55, B_54)) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.68/1.37  tff(c_521, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_10')) | ~r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8'))) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_511, c_48])).
% 2.68/1.37  tff(c_530, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_10')) | ~r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_521])).
% 2.68/1.37  tff(c_534, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_530])).
% 2.68/1.37  tff(c_537, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_471, c_534])).
% 2.68/1.37  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_410, c_537])).
% 2.68/1.37  tff(c_546, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_10', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_530])).
% 2.68/1.37  tff(c_563, plain, (r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_40, c_546])).
% 2.68/1.37  tff(c_569, plain, (r2_hidden('#skF_9', k11_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_563])).
% 2.68/1.37  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_411, c_569])).
% 2.68/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.37  
% 2.68/1.37  Inference rules
% 2.68/1.37  ----------------------
% 2.68/1.37  #Ref     : 0
% 2.68/1.37  #Sup     : 110
% 2.68/1.37  #Fact    : 0
% 2.68/1.37  #Define  : 0
% 2.68/1.37  #Split   : 3
% 2.68/1.37  #Chain   : 0
% 2.68/1.37  #Close   : 0
% 2.68/1.37  
% 2.68/1.37  Ordering : KBO
% 2.68/1.37  
% 2.68/1.37  Simplification rules
% 2.68/1.37  ----------------------
% 2.68/1.37  #Subsume      : 6
% 2.68/1.37  #Demod        : 24
% 2.68/1.37  #Tautology    : 22
% 2.68/1.37  #SimpNegUnit  : 2
% 2.68/1.37  #BackRed      : 0
% 2.68/1.37  
% 2.68/1.37  #Partial instantiations: 0
% 2.68/1.37  #Strategies tried      : 1
% 2.68/1.37  
% 2.68/1.37  Timing (in seconds)
% 2.68/1.37  ----------------------
% 2.68/1.38  Preprocessing        : 0.31
% 2.68/1.38  Parsing              : 0.16
% 2.68/1.38  CNF conversion       : 0.03
% 2.68/1.38  Main loop            : 0.30
% 2.68/1.38  Inferencing          : 0.11
% 2.68/1.38  Reduction            : 0.08
% 2.68/1.38  Demodulation         : 0.06
% 2.68/1.38  BG Simplification    : 0.02
% 2.68/1.38  Subsumption          : 0.06
% 2.68/1.38  Abstraction          : 0.02
% 2.68/1.38  MUC search           : 0.00
% 2.68/1.38  Cooper               : 0.00
% 2.68/1.38  Total                : 0.65
% 2.68/1.38  Index Insertion      : 0.00
% 2.68/1.38  Index Deletion       : 0.00
% 2.68/1.38  Index Matching       : 0.00
% 2.68/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
