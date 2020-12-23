%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:03 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.08s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 164 expanded)
%              Number of leaves         :   24 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  140 ( 592 expanded)
%              Number of equality atoms :   35 ( 173 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_36,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_48,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_42,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_22,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_12,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_865,plain,(
    ! [A_62] :
      ( k5_relat_1(k2_funct_1(A_62),A_62) = k6_relat_1(k2_relat_1(A_62))
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_8,plain,(
    ! [A_7,B_9] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_7,B_9)),k1_relat_1(A_7))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_871,plain,(
    ! [A_62] :
      ( r1_tarski(k1_relat_1(k6_relat_1(k2_relat_1(A_62))),k1_relat_1(k2_funct_1(A_62)))
      | ~ v1_relat_1(A_62)
      | ~ v1_relat_1(k2_funct_1(A_62))
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_865,c_8])).

tff(c_1912,plain,(
    ! [A_83] :
      ( r1_tarski(k2_relat_1(A_83),k1_relat_1(k2_funct_1(A_83)))
      | ~ v1_relat_1(A_83)
      | ~ v1_relat_1(k2_funct_1(A_83))
      | ~ v2_funct_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_871])).

tff(c_1951,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_1')))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1912])).

tff(c_1961,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_1')))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_42,c_50,c_1951])).

tff(c_1964,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1961])).

tff(c_1967,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1964])).

tff(c_1971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1967])).

tff(c_1973,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1961])).

tff(c_38,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_195,plain,(
    ! [A_38] :
      ( k2_relat_1(k2_funct_1(A_38)) = k1_relat_1(A_38)
      | ~ v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k6_relat_1(k2_relat_1(A_20))) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2147,plain,(
    ! [A_85] :
      ( k5_relat_1(k2_funct_1(A_85),k6_relat_1(k1_relat_1(A_85))) = k2_funct_1(A_85)
      | ~ v1_relat_1(k2_funct_1(A_85))
      | ~ v2_funct_1(A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_18])).

tff(c_2174,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2147])).

tff(c_2189,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_42,c_1973,c_2174])).

tff(c_32,plain,(
    ! [A_24] :
      ( k5_relat_1(k2_funct_1(A_24),A_24) = k6_relat_1(k2_relat_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1046,plain,(
    ! [A_67,B_68,C_69] :
      ( k5_relat_1(k5_relat_1(A_67,B_68),C_69) = k5_relat_1(A_67,k5_relat_1(B_68,C_69))
      | ~ v1_relat_1(C_69)
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7166,plain,(
    ! [A_149,C_150] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_149)),C_150) = k5_relat_1(k2_funct_1(A_149),k5_relat_1(A_149,C_150))
      | ~ v1_relat_1(C_150)
      | ~ v1_relat_1(A_149)
      | ~ v1_relat_1(k2_funct_1(A_149))
      | ~ v2_funct_1(A_149)
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1046])).

tff(c_7487,plain,(
    ! [C_150] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_150) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_150))
      | ~ v1_relat_1(C_150)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_7166])).

tff(c_7731,plain,(
    ! [C_151] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_151) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_151))
      | ~ v1_relat_1(C_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_42,c_1973,c_50,c_7487])).

tff(c_30,plain,(
    ! [A_23] :
      ( k1_relat_1(k2_funct_1(A_23)) = k2_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1972,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1961])).

tff(c_16,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = B_19
      | ~ r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2024,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_1'))),'#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1972,c_16])).

tff(c_2030,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_1'))),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2024])).

tff(c_2052,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')),'#skF_2') = '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2030])).

tff(c_2066,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_42,c_40,c_2052])).

tff(c_7827,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7731,c_2066])).

tff(c_7980,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2189,c_7827])).

tff(c_7982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_7980])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:30:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.08/2.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.08/2.43  
% 7.08/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.08/2.43  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 7.08/2.43  
% 7.08/2.43  %Foreground sorts:
% 7.08/2.43  
% 7.08/2.43  
% 7.08/2.43  %Background operators:
% 7.08/2.43  
% 7.08/2.43  
% 7.08/2.43  %Foreground operators:
% 7.08/2.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.08/2.43  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.08/2.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.08/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.08/2.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.08/2.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.08/2.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.08/2.43  tff('#skF_2', type, '#skF_2': $i).
% 7.08/2.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.08/2.43  tff('#skF_1', type, '#skF_1': $i).
% 7.08/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.08/2.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.08/2.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.08/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.08/2.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.08/2.43  
% 7.08/2.44  tff(f_123, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 7.08/2.44  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.08/2.44  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.08/2.44  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 7.08/2.44  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 7.08/2.44  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.08/2.44  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 7.08/2.44  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 7.08/2.44  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 7.08/2.44  tff(c_36, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.08/2.44  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.08/2.44  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.08/2.44  tff(c_48, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.08/2.44  tff(c_42, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.08/2.44  tff(c_22, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.08/2.44  tff(c_40, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.08/2.44  tff(c_12, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.08/2.44  tff(c_865, plain, (![A_62]: (k5_relat_1(k2_funct_1(A_62), A_62)=k6_relat_1(k2_relat_1(A_62)) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.08/2.44  tff(c_8, plain, (![A_7, B_9]: (r1_tarski(k1_relat_1(k5_relat_1(A_7, B_9)), k1_relat_1(A_7)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.08/2.44  tff(c_871, plain, (![A_62]: (r1_tarski(k1_relat_1(k6_relat_1(k2_relat_1(A_62))), k1_relat_1(k2_funct_1(A_62))) | ~v1_relat_1(A_62) | ~v1_relat_1(k2_funct_1(A_62)) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(superposition, [status(thm), theory('equality')], [c_865, c_8])).
% 7.08/2.44  tff(c_1912, plain, (![A_83]: (r1_tarski(k2_relat_1(A_83), k1_relat_1(k2_funct_1(A_83))) | ~v1_relat_1(A_83) | ~v1_relat_1(k2_funct_1(A_83)) | ~v2_funct_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_871])).
% 7.08/2.44  tff(c_1951, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_1'))) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_1912])).
% 7.08/2.44  tff(c_1961, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_1'))) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_42, c_50, c_1951])).
% 7.08/2.44  tff(c_1964, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1961])).
% 7.08/2.44  tff(c_1967, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1964])).
% 7.08/2.44  tff(c_1971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1967])).
% 7.08/2.44  tff(c_1973, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1961])).
% 7.08/2.44  tff(c_38, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.08/2.44  tff(c_195, plain, (![A_38]: (k2_relat_1(k2_funct_1(A_38))=k1_relat_1(A_38) | ~v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.08/2.44  tff(c_18, plain, (![A_20]: (k5_relat_1(A_20, k6_relat_1(k2_relat_1(A_20)))=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.08/2.44  tff(c_2147, plain, (![A_85]: (k5_relat_1(k2_funct_1(A_85), k6_relat_1(k1_relat_1(A_85)))=k2_funct_1(A_85) | ~v1_relat_1(k2_funct_1(A_85)) | ~v2_funct_1(A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_195, c_18])).
% 7.08/2.44  tff(c_2174, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2147])).
% 7.08/2.44  tff(c_2189, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_42, c_1973, c_2174])).
% 7.08/2.44  tff(c_32, plain, (![A_24]: (k5_relat_1(k2_funct_1(A_24), A_24)=k6_relat_1(k2_relat_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.08/2.44  tff(c_1046, plain, (![A_67, B_68, C_69]: (k5_relat_1(k5_relat_1(A_67, B_68), C_69)=k5_relat_1(A_67, k5_relat_1(B_68, C_69)) | ~v1_relat_1(C_69) | ~v1_relat_1(B_68) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.08/2.44  tff(c_7166, plain, (![A_149, C_150]: (k5_relat_1(k6_relat_1(k2_relat_1(A_149)), C_150)=k5_relat_1(k2_funct_1(A_149), k5_relat_1(A_149, C_150)) | ~v1_relat_1(C_150) | ~v1_relat_1(A_149) | ~v1_relat_1(k2_funct_1(A_149)) | ~v2_funct_1(A_149) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1046])).
% 7.08/2.44  tff(c_7487, plain, (![C_150]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_150)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_150)) | ~v1_relat_1(C_150) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_7166])).
% 7.08/2.44  tff(c_7731, plain, (![C_151]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_151)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_151)) | ~v1_relat_1(C_151))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_42, c_1973, c_50, c_7487])).
% 7.08/2.44  tff(c_30, plain, (![A_23]: (k1_relat_1(k2_funct_1(A_23))=k2_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.08/2.44  tff(c_1972, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_1')))), inference(splitRight, [status(thm)], [c_1961])).
% 7.08/2.44  tff(c_16, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=B_19 | ~r1_tarski(k1_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.08/2.44  tff(c_2024, plain, (k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_1'))), '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1972, c_16])).
% 7.08/2.44  tff(c_2030, plain, (k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_1'))), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2024])).
% 7.08/2.44  tff(c_2052, plain, (k5_relat_1(k6_relat_1(k2_relat_1('#skF_1')), '#skF_2')='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_2030])).
% 7.08/2.44  tff(c_2066, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_42, c_40, c_2052])).
% 7.08/2.44  tff(c_7827, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7731, c_2066])).
% 7.08/2.44  tff(c_7980, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2189, c_7827])).
% 7.08/2.44  tff(c_7982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_7980])).
% 7.08/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.08/2.44  
% 7.08/2.44  Inference rules
% 7.08/2.44  ----------------------
% 7.08/2.44  #Ref     : 0
% 7.08/2.44  #Sup     : 1662
% 7.08/2.44  #Fact    : 0
% 7.08/2.44  #Define  : 0
% 7.08/2.44  #Split   : 5
% 7.08/2.44  #Chain   : 0
% 7.08/2.44  #Close   : 0
% 7.08/2.44  
% 7.08/2.44  Ordering : KBO
% 7.08/2.44  
% 7.08/2.44  Simplification rules
% 7.08/2.44  ----------------------
% 7.08/2.44  #Subsume      : 210
% 7.08/2.44  #Demod        : 3416
% 7.08/2.44  #Tautology    : 725
% 7.08/2.44  #SimpNegUnit  : 1
% 7.08/2.44  #BackRed      : 1
% 7.08/2.44  
% 7.08/2.44  #Partial instantiations: 0
% 7.08/2.44  #Strategies tried      : 1
% 7.08/2.44  
% 7.08/2.44  Timing (in seconds)
% 7.08/2.44  ----------------------
% 7.08/2.45  Preprocessing        : 0.31
% 7.08/2.45  Parsing              : 0.17
% 7.08/2.45  CNF conversion       : 0.02
% 7.08/2.45  Main loop            : 1.38
% 7.08/2.45  Inferencing          : 0.43
% 7.08/2.45  Reduction            : 0.56
% 7.08/2.45  Demodulation         : 0.44
% 7.08/2.45  BG Simplification    : 0.05
% 7.08/2.45  Subsumption          : 0.27
% 7.08/2.45  Abstraction          : 0.07
% 7.08/2.45  MUC search           : 0.00
% 7.08/2.45  Cooper               : 0.00
% 7.08/2.45  Total                : 1.72
% 7.08/2.45  Index Insertion      : 0.00
% 7.08/2.45  Index Deletion       : 0.00
% 7.08/2.45  Index Matching       : 0.00
% 7.08/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
