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
% DateTime   : Thu Dec  3 10:03:42 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 117 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  133 ( 359 expanded)
%              Number of equality atoms :   33 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( ? [B] :
              ( v1_relat_1(B)
              & v1_funct_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
         => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(c_30,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_91,plain,(
    ! [A_26] :
      ( '#skF_2'(A_26) != '#skF_1'(A_26)
      | v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_94,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_30])).

tff(c_97,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_94])).

tff(c_36,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_funct_1(A_1,'#skF_2'(A_1)) = k1_funct_1(A_1,'#skF_1'(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_320,plain,(
    ! [B_42,C_43,A_44] :
      ( k1_funct_1(k5_relat_1(B_42,C_43),A_44) = k1_funct_1(C_43,k1_funct_1(B_42,A_44))
      | ~ r2_hidden(A_44,k1_relat_1(B_42))
      | ~ v1_funct_1(C_43)
      | ~ v1_relat_1(C_43)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_392,plain,(
    ! [A_50,C_51] :
      ( k1_funct_1(k5_relat_1(A_50,C_51),'#skF_2'(A_50)) = k1_funct_1(C_51,k1_funct_1(A_50,'#skF_2'(A_50)))
      | ~ v1_funct_1(C_51)
      | ~ v1_relat_1(C_51)
      | v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(resolution,[status(thm)],[c_8,c_320])).

tff(c_122,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_2'(A_29),k1_relat_1(A_29))
      | v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    k6_relat_1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14,plain,(
    ! [A_8] : v1_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_14,C_18] :
      ( k1_funct_1(k6_relat_1(A_14),C_18) = C_18
      | ~ r2_hidden(C_18,A_14)
      | ~ v1_funct_1(k6_relat_1(A_14))
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ! [A_14,C_18] :
      ( k1_funct_1(k6_relat_1(A_14),C_18) = C_18
      | ~ r2_hidden(C_18,A_14)
      | ~ v1_funct_1(k6_relat_1(A_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_26])).

tff(c_79,plain,(
    ! [A_24,C_25] :
      ( k1_funct_1(k6_relat_1(A_24),C_25) = C_25
      | ~ r2_hidden(C_25,A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_44])).

tff(c_88,plain,(
    ! [C_25] :
      ( k1_funct_1(k5_relat_1('#skF_4','#skF_5'),C_25) = C_25
      | ~ r2_hidden(C_25,k1_relat_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_79])).

tff(c_126,plain,
    ( k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_2'('#skF_4')) = '#skF_2'('#skF_4')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_88])).

tff(c_135,plain,
    ( k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_2'('#skF_4')) = '#skF_2'('#skF_4')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_126])).

tff(c_136,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_2'('#skF_4')) = '#skF_2'('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_135])).

tff(c_413,plain,
    ( k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_2'('#skF_4'))) = '#skF_2'('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_136])).

tff(c_439,plain,
    ( k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_2'('#skF_4'))) = '#skF_2'('#skF_4')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_413])).

tff(c_440,plain,(
    k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_2'('#skF_4'))) = '#skF_2'('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_439])).

tff(c_459,plain,
    ( k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_1'('#skF_4'))) = '#skF_2'('#skF_4')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_440])).

tff(c_467,plain,
    ( k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_1'('#skF_4'))) = '#skF_2'('#skF_4')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_459])).

tff(c_468,plain,(
    k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_1'('#skF_4'))) = '#skF_2'('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_467])).

tff(c_10,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_482,plain,(
    ! [A_52,C_53] :
      ( k1_funct_1(k5_relat_1(A_52,C_53),'#skF_1'(A_52)) = k1_funct_1(C_53,k1_funct_1(A_52,'#skF_1'(A_52)))
      | ~ v1_funct_1(C_53)
      | ~ v1_relat_1(C_53)
      | v2_funct_1(A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(resolution,[status(thm)],[c_10,c_320])).

tff(c_99,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),k1_relat_1(A_28))
      | v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_103,plain,
    ( k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_1'('#skF_4')) = '#skF_1'('#skF_4')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_88])).

tff(c_112,plain,
    ( k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_1'('#skF_4')) = '#skF_1'('#skF_4')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_103])).

tff(c_113,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_1'('#skF_4')) = '#skF_1'('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_112])).

tff(c_503,plain,
    ( k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_1'('#skF_4'))) = '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_113])).

tff(c_529,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_468,c_503])).

tff(c_531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_97,c_529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:21:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.44  
% 2.62/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.44  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 2.62/1.44  
% 2.62/1.44  %Foreground sorts:
% 2.62/1.44  
% 2.62/1.44  
% 2.62/1.44  %Background operators:
% 2.62/1.44  
% 2.62/1.44  
% 2.62/1.44  %Foreground operators:
% 2.62/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.44  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.62/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.62/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.62/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.62/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.62/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.62/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.62/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.62/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.44  
% 2.97/1.46  tff(f_88, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 2.97/1.46  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 2.97/1.46  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 2.97/1.46  tff(f_44, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.97/1.46  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.97/1.46  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.97/1.46  tff(c_30, plain, (~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.97/1.46  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.97/1.46  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.97/1.46  tff(c_91, plain, (![A_26]: ('#skF_2'(A_26)!='#skF_1'(A_26) | v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.97/1.46  tff(c_94, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_91, c_30])).
% 2.97/1.46  tff(c_97, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_94])).
% 2.97/1.46  tff(c_36, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.97/1.46  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.97/1.46  tff(c_6, plain, (![A_1]: (k1_funct_1(A_1, '#skF_2'(A_1))=k1_funct_1(A_1, '#skF_1'(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.97/1.46  tff(c_8, plain, (![A_1]: (r2_hidden('#skF_2'(A_1), k1_relat_1(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.97/1.46  tff(c_320, plain, (![B_42, C_43, A_44]: (k1_funct_1(k5_relat_1(B_42, C_43), A_44)=k1_funct_1(C_43, k1_funct_1(B_42, A_44)) | ~r2_hidden(A_44, k1_relat_1(B_42)) | ~v1_funct_1(C_43) | ~v1_relat_1(C_43) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.97/1.46  tff(c_392, plain, (![A_50, C_51]: (k1_funct_1(k5_relat_1(A_50, C_51), '#skF_2'(A_50))=k1_funct_1(C_51, k1_funct_1(A_50, '#skF_2'(A_50))) | ~v1_funct_1(C_51) | ~v1_relat_1(C_51) | v2_funct_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(resolution, [status(thm)], [c_8, c_320])).
% 2.97/1.46  tff(c_122, plain, (![A_29]: (r2_hidden('#skF_2'(A_29), k1_relat_1(A_29)) | v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.97/1.46  tff(c_32, plain, (k6_relat_1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.97/1.46  tff(c_14, plain, (![A_8]: (v1_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.97/1.46  tff(c_16, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.97/1.46  tff(c_26, plain, (![A_14, C_18]: (k1_funct_1(k6_relat_1(A_14), C_18)=C_18 | ~r2_hidden(C_18, A_14) | ~v1_funct_1(k6_relat_1(A_14)) | ~v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.97/1.46  tff(c_44, plain, (![A_14, C_18]: (k1_funct_1(k6_relat_1(A_14), C_18)=C_18 | ~r2_hidden(C_18, A_14) | ~v1_funct_1(k6_relat_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_26])).
% 2.97/1.46  tff(c_79, plain, (![A_24, C_25]: (k1_funct_1(k6_relat_1(A_24), C_25)=C_25 | ~r2_hidden(C_25, A_24))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_44])).
% 2.97/1.46  tff(c_88, plain, (![C_25]: (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), C_25)=C_25 | ~r2_hidden(C_25, k1_relat_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_79])).
% 2.97/1.46  tff(c_126, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_2'('#skF_4'))='#skF_2'('#skF_4') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_122, c_88])).
% 2.97/1.46  tff(c_135, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_2'('#skF_4'))='#skF_2'('#skF_4') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_126])).
% 2.97/1.46  tff(c_136, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_2'('#skF_4'))='#skF_2'('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_135])).
% 2.97/1.46  tff(c_413, plain, (k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_2'('#skF_4')))='#skF_2'('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_392, c_136])).
% 2.97/1.46  tff(c_439, plain, (k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_2'('#skF_4')))='#skF_2'('#skF_4') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_413])).
% 2.97/1.46  tff(c_440, plain, (k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_2'('#skF_4')))='#skF_2'('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_439])).
% 2.97/1.46  tff(c_459, plain, (k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_1'('#skF_4')))='#skF_2'('#skF_4') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6, c_440])).
% 2.97/1.46  tff(c_467, plain, (k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_1'('#skF_4')))='#skF_2'('#skF_4') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_459])).
% 2.97/1.46  tff(c_468, plain, (k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_1'('#skF_4')))='#skF_2'('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_467])).
% 2.97/1.46  tff(c_10, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), k1_relat_1(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.97/1.46  tff(c_482, plain, (![A_52, C_53]: (k1_funct_1(k5_relat_1(A_52, C_53), '#skF_1'(A_52))=k1_funct_1(C_53, k1_funct_1(A_52, '#skF_1'(A_52))) | ~v1_funct_1(C_53) | ~v1_relat_1(C_53) | v2_funct_1(A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(resolution, [status(thm)], [c_10, c_320])).
% 2.97/1.46  tff(c_99, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), k1_relat_1(A_28)) | v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.97/1.46  tff(c_103, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_1'('#skF_4'))='#skF_1'('#skF_4') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_99, c_88])).
% 2.97/1.46  tff(c_112, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_1'('#skF_4'))='#skF_1'('#skF_4') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_103])).
% 2.97/1.46  tff(c_113, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_1'('#skF_4'))='#skF_1'('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_112])).
% 2.97/1.46  tff(c_503, plain, (k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_1'('#skF_4')))='#skF_1'('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_482, c_113])).
% 2.97/1.46  tff(c_529, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_468, c_503])).
% 2.97/1.46  tff(c_531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_97, c_529])).
% 2.97/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.46  
% 2.97/1.46  Inference rules
% 2.97/1.46  ----------------------
% 2.97/1.46  #Ref     : 3
% 2.97/1.46  #Sup     : 109
% 2.97/1.46  #Fact    : 0
% 2.97/1.46  #Define  : 0
% 2.97/1.46  #Split   : 1
% 2.97/1.46  #Chain   : 0
% 2.97/1.46  #Close   : 0
% 2.97/1.46  
% 2.97/1.46  Ordering : KBO
% 2.97/1.46  
% 2.97/1.46  Simplification rules
% 2.97/1.46  ----------------------
% 2.97/1.46  #Subsume      : 7
% 2.97/1.46  #Demod        : 186
% 2.97/1.46  #Tautology    : 61
% 2.97/1.46  #SimpNegUnit  : 9
% 2.97/1.46  #BackRed      : 7
% 2.97/1.46  
% 2.97/1.46  #Partial instantiations: 0
% 2.97/1.46  #Strategies tried      : 1
% 2.97/1.46  
% 2.97/1.46  Timing (in seconds)
% 2.97/1.46  ----------------------
% 2.97/1.46  Preprocessing        : 0.32
% 2.97/1.46  Parsing              : 0.17
% 2.97/1.46  CNF conversion       : 0.02
% 2.97/1.46  Main loop            : 0.34
% 2.97/1.46  Inferencing          : 0.12
% 2.97/1.46  Reduction            : 0.12
% 2.97/1.46  Demodulation         : 0.09
% 2.97/1.46  BG Simplification    : 0.02
% 2.97/1.46  Subsumption          : 0.06
% 2.97/1.46  Abstraction          : 0.02
% 2.97/1.46  MUC search           : 0.00
% 2.97/1.46  Cooper               : 0.00
% 2.97/1.46  Total                : 0.70
% 2.97/1.46  Index Insertion      : 0.00
% 2.97/1.46  Index Deletion       : 0.00
% 2.97/1.46  Index Matching       : 0.00
% 2.97/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
