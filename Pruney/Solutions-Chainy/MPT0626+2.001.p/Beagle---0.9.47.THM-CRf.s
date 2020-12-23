%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:16 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 118 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  122 ( 359 expanded)
%              Number of equality atoms :    7 (  18 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
            <=> ( r2_hidden(A,k1_relat_1(C))
                & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7','#skF_6')))
    | r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_47,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7','#skF_6')))
    | r2_hidden(k1_funct_1('#skF_7','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_57,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),k1_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_57,c_36])).

tff(c_20,plain,(
    ! [A_43,B_45] :
      ( k10_relat_1(A_43,k1_relat_1(B_45)) = k1_relat_1(k5_relat_1(A_43,B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_46,C_48] :
      ( r2_hidden(k4_tarski(A_46,k1_funct_1(C_48,A_46)),C_48)
      | ~ r2_hidden(A_46,k1_relat_1(C_48))
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_62,plain,(
    ! [D_58,A_59,B_60,E_61] :
      ( r2_hidden(D_58,k10_relat_1(A_59,B_60))
      | ~ r2_hidden(E_61,B_60)
      | ~ r2_hidden(k4_tarski(D_58,E_61),A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,(
    ! [D_68,A_69] :
      ( r2_hidden(D_68,k10_relat_1(A_69,k1_relat_1('#skF_6')))
      | ~ r2_hidden(k4_tarski(D_68,k1_funct_1('#skF_7','#skF_5')),A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_57,c_62])).

tff(c_120,plain,
    ( r2_hidden('#skF_5',k10_relat_1('#skF_7',k1_relat_1('#skF_6')))
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_116])).

tff(c_131,plain,(
    r2_hidden('#skF_5',k10_relat_1('#skF_7',k1_relat_1('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_47,c_120])).

tff(c_138,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7','#skF_6')))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_131])).

tff(c_141,plain,(
    r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_138])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_141])).

tff(c_144,plain,(
    r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_246,plain,(
    ! [D_94,A_95,B_96] :
      ( r2_hidden(k4_tarski(D_94,'#skF_4'(A_95,B_96,k10_relat_1(A_95,B_96),D_94)),A_95)
      | ~ r2_hidden(D_94,k10_relat_1(A_95,B_96))
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [C_48,A_46,B_47] :
      ( k1_funct_1(C_48,A_46) = B_47
      | ~ r2_hidden(k4_tarski(A_46,B_47),C_48)
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_365,plain,(
    ! [A_109,B_110,D_111] :
      ( '#skF_4'(A_109,B_110,k10_relat_1(A_109,B_110),D_111) = k1_funct_1(A_109,D_111)
      | ~ v1_funct_1(A_109)
      | ~ r2_hidden(D_111,k10_relat_1(A_109,B_110))
      | ~ v1_relat_1(A_109) ) ),
    inference(resolution,[status(thm)],[c_246,c_24])).

tff(c_1039,plain,(
    ! [A_185,B_186,D_187] :
      ( '#skF_4'(A_185,k1_relat_1(B_186),k10_relat_1(A_185,k1_relat_1(B_186)),D_187) = k1_funct_1(A_185,D_187)
      | ~ v1_funct_1(A_185)
      | ~ r2_hidden(D_187,k1_relat_1(k5_relat_1(A_185,B_186)))
      | ~ v1_relat_1(A_185)
      | ~ v1_relat_1(B_186)
      | ~ v1_relat_1(A_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_365])).

tff(c_4,plain,(
    ! [A_1,B_24,D_39] :
      ( r2_hidden('#skF_4'(A_1,B_24,k10_relat_1(A_1,B_24),D_39),B_24)
      | ~ r2_hidden(D_39,k10_relat_1(A_1,B_24))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2069,plain,(
    ! [A_265,D_266,B_267] :
      ( r2_hidden(k1_funct_1(A_265,D_266),k1_relat_1(B_267))
      | ~ r2_hidden(D_266,k10_relat_1(A_265,k1_relat_1(B_267)))
      | ~ v1_relat_1(A_265)
      | ~ v1_funct_1(A_265)
      | ~ r2_hidden(D_266,k1_relat_1(k5_relat_1(A_265,B_267)))
      | ~ v1_relat_1(A_265)
      | ~ v1_relat_1(B_267)
      | ~ v1_relat_1(A_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1039,c_4])).

tff(c_147,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_47,c_36])).

tff(c_2082,plain,
    ( ~ r2_hidden('#skF_5',k10_relat_1('#skF_7',k1_relat_1('#skF_6')))
    | ~ v1_funct_1('#skF_7')
    | ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7','#skF_6')))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_2069,c_147])).

tff(c_2091,plain,(
    ~ r2_hidden('#skF_5',k10_relat_1('#skF_7',k1_relat_1('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_144,c_28,c_2082])).

tff(c_2094,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7','#skF_6')))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2091])).

tff(c_2097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_144,c_2094])).

tff(c_2099,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2098,plain,(
    r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2169,plain,(
    ! [D_293,A_294,B_295] :
      ( r2_hidden(k4_tarski(D_293,'#skF_4'(A_294,B_295,k10_relat_1(A_294,B_295),D_293)),A_294)
      | ~ r2_hidden(D_293,k10_relat_1(A_294,B_295))
      | ~ v1_relat_1(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [A_46,C_48,B_47] :
      ( r2_hidden(A_46,k1_relat_1(C_48))
      | ~ r2_hidden(k4_tarski(A_46,B_47),C_48)
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2184,plain,(
    ! [D_296,A_297,B_298] :
      ( r2_hidden(D_296,k1_relat_1(A_297))
      | ~ v1_funct_1(A_297)
      | ~ r2_hidden(D_296,k10_relat_1(A_297,B_298))
      | ~ v1_relat_1(A_297) ) ),
    inference(resolution,[status(thm)],[c_2169,c_26])).

tff(c_2230,plain,(
    ! [D_303,A_304,B_305] :
      ( r2_hidden(D_303,k1_relat_1(A_304))
      | ~ v1_funct_1(A_304)
      | ~ r2_hidden(D_303,k1_relat_1(k5_relat_1(A_304,B_305)))
      | ~ v1_relat_1(A_304)
      | ~ v1_relat_1(B_305)
      | ~ v1_relat_1(A_304) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2184])).

tff(c_2253,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_2098,c_2230])).

tff(c_2261,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_28,c_2253])).

tff(c_2263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2099,c_2261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:21:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.86  
% 4.55/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.87  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 4.55/1.87  
% 4.55/1.87  %Foreground sorts:
% 4.55/1.87  
% 4.55/1.87  
% 4.55/1.87  %Background operators:
% 4.55/1.87  
% 4.55/1.87  
% 4.55/1.87  %Foreground operators:
% 4.55/1.87  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.55/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.55/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/1.87  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.55/1.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.55/1.87  tff('#skF_7', type, '#skF_7': $i).
% 4.55/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.55/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.55/1.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.55/1.87  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.55/1.87  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.55/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.87  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.55/1.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.55/1.87  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.55/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.55/1.87  
% 4.55/1.88  tff(f_71, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 4.55/1.88  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 4.55/1.88  tff(f_55, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.55/1.88  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 4.55/1.88  tff(c_30, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.55/1.88  tff(c_34, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.55/1.88  tff(c_46, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', '#skF_6'))) | r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.55/1.88  tff(c_47, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_46])).
% 4.55/1.88  tff(c_42, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', '#skF_6'))) | r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.55/1.88  tff(c_57, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_42])).
% 4.55/1.88  tff(c_36, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.55/1.88  tff(c_59, plain, (~r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_57, c_36])).
% 4.55/1.88  tff(c_20, plain, (![A_43, B_45]: (k10_relat_1(A_43, k1_relat_1(B_45))=k1_relat_1(k5_relat_1(A_43, B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.55/1.88  tff(c_28, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.55/1.88  tff(c_22, plain, (![A_46, C_48]: (r2_hidden(k4_tarski(A_46, k1_funct_1(C_48, A_46)), C_48) | ~r2_hidden(A_46, k1_relat_1(C_48)) | ~v1_funct_1(C_48) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.55/1.88  tff(c_62, plain, (![D_58, A_59, B_60, E_61]: (r2_hidden(D_58, k10_relat_1(A_59, B_60)) | ~r2_hidden(E_61, B_60) | ~r2_hidden(k4_tarski(D_58, E_61), A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.55/1.88  tff(c_116, plain, (![D_68, A_69]: (r2_hidden(D_68, k10_relat_1(A_69, k1_relat_1('#skF_6'))) | ~r2_hidden(k4_tarski(D_68, k1_funct_1('#skF_7', '#skF_5')), A_69) | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_57, c_62])).
% 4.55/1.88  tff(c_120, plain, (r2_hidden('#skF_5', k10_relat_1('#skF_7', k1_relat_1('#skF_6'))) | ~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_22, c_116])).
% 4.55/1.88  tff(c_131, plain, (r2_hidden('#skF_5', k10_relat_1('#skF_7', k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_47, c_120])).
% 4.55/1.88  tff(c_138, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', '#skF_6'))) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_20, c_131])).
% 4.55/1.88  tff(c_141, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_138])).
% 4.55/1.88  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_141])).
% 4.55/1.88  tff(c_144, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_42])).
% 4.55/1.88  tff(c_246, plain, (![D_94, A_95, B_96]: (r2_hidden(k4_tarski(D_94, '#skF_4'(A_95, B_96, k10_relat_1(A_95, B_96), D_94)), A_95) | ~r2_hidden(D_94, k10_relat_1(A_95, B_96)) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.55/1.88  tff(c_24, plain, (![C_48, A_46, B_47]: (k1_funct_1(C_48, A_46)=B_47 | ~r2_hidden(k4_tarski(A_46, B_47), C_48) | ~v1_funct_1(C_48) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.55/1.88  tff(c_365, plain, (![A_109, B_110, D_111]: ('#skF_4'(A_109, B_110, k10_relat_1(A_109, B_110), D_111)=k1_funct_1(A_109, D_111) | ~v1_funct_1(A_109) | ~r2_hidden(D_111, k10_relat_1(A_109, B_110)) | ~v1_relat_1(A_109))), inference(resolution, [status(thm)], [c_246, c_24])).
% 4.55/1.88  tff(c_1039, plain, (![A_185, B_186, D_187]: ('#skF_4'(A_185, k1_relat_1(B_186), k10_relat_1(A_185, k1_relat_1(B_186)), D_187)=k1_funct_1(A_185, D_187) | ~v1_funct_1(A_185) | ~r2_hidden(D_187, k1_relat_1(k5_relat_1(A_185, B_186))) | ~v1_relat_1(A_185) | ~v1_relat_1(B_186) | ~v1_relat_1(A_185))), inference(superposition, [status(thm), theory('equality')], [c_20, c_365])).
% 4.55/1.88  tff(c_4, plain, (![A_1, B_24, D_39]: (r2_hidden('#skF_4'(A_1, B_24, k10_relat_1(A_1, B_24), D_39), B_24) | ~r2_hidden(D_39, k10_relat_1(A_1, B_24)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.55/1.88  tff(c_2069, plain, (![A_265, D_266, B_267]: (r2_hidden(k1_funct_1(A_265, D_266), k1_relat_1(B_267)) | ~r2_hidden(D_266, k10_relat_1(A_265, k1_relat_1(B_267))) | ~v1_relat_1(A_265) | ~v1_funct_1(A_265) | ~r2_hidden(D_266, k1_relat_1(k5_relat_1(A_265, B_267))) | ~v1_relat_1(A_265) | ~v1_relat_1(B_267) | ~v1_relat_1(A_265))), inference(superposition, [status(thm), theory('equality')], [c_1039, c_4])).
% 4.55/1.88  tff(c_147, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_47, c_36])).
% 4.55/1.88  tff(c_2082, plain, (~r2_hidden('#skF_5', k10_relat_1('#skF_7', k1_relat_1('#skF_6'))) | ~v1_funct_1('#skF_7') | ~r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', '#skF_6'))) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_2069, c_147])).
% 4.55/1.88  tff(c_2091, plain, (~r2_hidden('#skF_5', k10_relat_1('#skF_7', k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_144, c_28, c_2082])).
% 4.55/1.88  tff(c_2094, plain, (~r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', '#skF_6'))) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_20, c_2091])).
% 4.55/1.88  tff(c_2097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_144, c_2094])).
% 4.55/1.88  tff(c_2099, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_46])).
% 4.55/1.88  tff(c_2098, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_46])).
% 4.55/1.88  tff(c_2169, plain, (![D_293, A_294, B_295]: (r2_hidden(k4_tarski(D_293, '#skF_4'(A_294, B_295, k10_relat_1(A_294, B_295), D_293)), A_294) | ~r2_hidden(D_293, k10_relat_1(A_294, B_295)) | ~v1_relat_1(A_294))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.55/1.88  tff(c_26, plain, (![A_46, C_48, B_47]: (r2_hidden(A_46, k1_relat_1(C_48)) | ~r2_hidden(k4_tarski(A_46, B_47), C_48) | ~v1_funct_1(C_48) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.55/1.88  tff(c_2184, plain, (![D_296, A_297, B_298]: (r2_hidden(D_296, k1_relat_1(A_297)) | ~v1_funct_1(A_297) | ~r2_hidden(D_296, k10_relat_1(A_297, B_298)) | ~v1_relat_1(A_297))), inference(resolution, [status(thm)], [c_2169, c_26])).
% 4.55/1.88  tff(c_2230, plain, (![D_303, A_304, B_305]: (r2_hidden(D_303, k1_relat_1(A_304)) | ~v1_funct_1(A_304) | ~r2_hidden(D_303, k1_relat_1(k5_relat_1(A_304, B_305))) | ~v1_relat_1(A_304) | ~v1_relat_1(B_305) | ~v1_relat_1(A_304))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2184])).
% 4.55/1.88  tff(c_2253, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_2098, c_2230])).
% 4.55/1.88  tff(c_2261, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_28, c_2253])).
% 4.55/1.88  tff(c_2263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2099, c_2261])).
% 4.55/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.88  
% 4.55/1.88  Inference rules
% 4.55/1.88  ----------------------
% 4.55/1.88  #Ref     : 0
% 4.55/1.88  #Sup     : 507
% 4.55/1.88  #Fact    : 0
% 4.55/1.88  #Define  : 0
% 4.55/1.88  #Split   : 3
% 4.55/1.88  #Chain   : 0
% 4.55/1.88  #Close   : 0
% 4.55/1.88  
% 4.55/1.88  Ordering : KBO
% 4.55/1.88  
% 4.55/1.88  Simplification rules
% 4.55/1.88  ----------------------
% 4.55/1.88  #Subsume      : 41
% 4.55/1.88  #Demod        : 40
% 4.55/1.88  #Tautology    : 39
% 4.55/1.88  #SimpNegUnit  : 2
% 4.55/1.88  #BackRed      : 0
% 4.55/1.88  
% 4.55/1.88  #Partial instantiations: 0
% 4.55/1.88  #Strategies tried      : 1
% 4.55/1.88  
% 4.55/1.88  Timing (in seconds)
% 4.55/1.88  ----------------------
% 4.55/1.88  Preprocessing        : 0.31
% 4.55/1.88  Parsing              : 0.16
% 4.55/1.88  CNF conversion       : 0.03
% 4.55/1.88  Main loop            : 0.79
% 4.55/1.88  Inferencing          : 0.27
% 4.55/1.88  Reduction            : 0.20
% 4.55/1.88  Demodulation         : 0.14
% 4.55/1.88  BG Simplification    : 0.05
% 4.55/1.88  Subsumption          : 0.20
% 4.55/1.88  Abstraction          : 0.05
% 4.55/1.88  MUC search           : 0.00
% 4.55/1.88  Cooper               : 0.00
% 4.55/1.88  Total                : 1.13
% 4.55/1.88  Index Insertion      : 0.00
% 4.55/1.88  Index Deletion       : 0.00
% 4.55/1.88  Index Matching       : 0.00
% 4.55/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
