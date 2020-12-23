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
% DateTime   : Thu Dec  3 10:03:05 EST 2020

% Result     : Theorem 5.16s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 117 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 ( 401 expanded)
%              Number of equality atoms :   68 ( 199 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( ( k1_relat_1(B) = k1_relat_1(C)
                & k2_relat_1(B) = k1_tarski(A)
                & k2_relat_1(C) = k1_tarski(A) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(c_54,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_64,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_62,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_60,plain,(
    k1_relat_1('#skF_7') = k1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_68,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_52,plain,(
    ! [A_28,B_32] :
      ( r2_hidden('#skF_4'(A_28,B_32),k1_relat_1(A_28))
      | B_32 = A_28
      | k1_relat_1(B_32) != k1_relat_1(A_28)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_58,plain,(
    k2_relat_1('#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_171,plain,(
    ! [B_81,A_82] :
      ( r2_hidden(k1_funct_1(B_81,A_82),k2_relat_1(B_81))
      | ~ r2_hidden(A_82,k1_relat_1(B_81))
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_177,plain,(
    ! [A_82] :
      ( r2_hidden(k1_funct_1('#skF_6',A_82),k1_tarski('#skF_5'))
      | ~ r2_hidden(A_82,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_171])).

tff(c_184,plain,(
    ! [A_82] :
      ( r2_hidden(k1_funct_1('#skF_6',A_82),k1_tarski('#skF_5'))
      | ~ r2_hidden(A_82,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_177])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_251,plain,(
    ! [D_103,A_101,B_102,C_100,F_99] :
      ( F_99 = D_103
      | F_99 = C_100
      | F_99 = B_102
      | F_99 = A_101
      | ~ r2_hidden(F_99,k2_enumset1(A_101,B_102,C_100,D_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_339,plain,(
    ! [F_135,C_136,B_137,A_138] :
      ( F_135 = C_136
      | F_135 = B_137
      | F_135 = A_138
      | F_135 = A_138
      | ~ r2_hidden(F_135,k1_enumset1(A_138,B_137,C_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_251])).

tff(c_358,plain,(
    ! [F_139,B_140,A_141] :
      ( F_139 = B_140
      | F_139 = A_141
      | F_139 = A_141
      | F_139 = A_141
      | ~ r2_hidden(F_139,k2_tarski(A_141,B_140)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_339])).

tff(c_372,plain,(
    ! [F_142,A_143] :
      ( F_142 = A_143
      | F_142 = A_143
      | F_142 = A_143
      | F_142 = A_143
      | ~ r2_hidden(F_142,k1_tarski(A_143)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_358])).

tff(c_398,plain,(
    ! [A_145] :
      ( k1_funct_1('#skF_6',A_145) = '#skF_5'
      | ~ r2_hidden(A_145,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_184,c_372])).

tff(c_405,plain,(
    ! [B_32] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',B_32)) = '#skF_5'
      | B_32 = '#skF_6'
      | k1_relat_1(B_32) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_398])).

tff(c_409,plain,(
    ! [B_32] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',B_32)) = '#skF_5'
      | B_32 = '#skF_6'
      | k1_relat_1(B_32) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_405])).

tff(c_56,plain,(
    k2_relat_1('#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_180,plain,(
    ! [A_82] :
      ( r2_hidden(k1_funct_1('#skF_7',A_82),k1_tarski('#skF_5'))
      | ~ r2_hidden(A_82,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_171])).

tff(c_186,plain,(
    ! [A_82] :
      ( r2_hidden(k1_funct_1('#skF_7',A_82),k1_tarski('#skF_5'))
      | ~ r2_hidden(A_82,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_180])).

tff(c_386,plain,(
    ! [A_144] :
      ( k1_funct_1('#skF_7',A_144) = '#skF_5'
      | ~ r2_hidden(A_144,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_186,c_372])).

tff(c_393,plain,(
    ! [B_32] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_6',B_32)) = '#skF_5'
      | B_32 = '#skF_6'
      | k1_relat_1(B_32) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_386])).

tff(c_397,plain,(
    ! [B_32] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_6',B_32)) = '#skF_5'
      | B_32 = '#skF_6'
      | k1_relat_1(B_32) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_393])).

tff(c_4897,plain,(
    ! [B_292,A_293] :
      ( k1_funct_1(B_292,'#skF_4'(A_293,B_292)) != k1_funct_1(A_293,'#skF_4'(A_293,B_292))
      | B_292 = A_293
      | k1_relat_1(B_292) != k1_relat_1(A_293)
      | ~ v1_funct_1(B_292)
      | ~ v1_relat_1(B_292)
      | ~ v1_funct_1(A_293)
      | ~ v1_relat_1(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4901,plain,
    ( k1_funct_1('#skF_6','#skF_4'('#skF_6','#skF_7')) != '#skF_5'
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_4897])).

tff(c_4917,plain,
    ( k1_funct_1('#skF_6','#skF_4'('#skF_6','#skF_7')) != '#skF_5'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_68,c_66,c_64,c_62,c_60,c_4901])).

tff(c_4918,plain,(
    k1_funct_1('#skF_6','#skF_4'('#skF_6','#skF_7')) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4917])).

tff(c_4929,plain,
    ( '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_4918])).

tff(c_4932,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_4929])).

tff(c_4934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4932])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:07:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.16/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.03  
% 5.16/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.03  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 5.16/2.03  
% 5.16/2.03  %Foreground sorts:
% 5.16/2.03  
% 5.16/2.03  
% 5.16/2.03  %Background operators:
% 5.16/2.03  
% 5.16/2.03  
% 5.16/2.03  %Foreground operators:
% 5.16/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.16/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.16/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.16/2.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.16/2.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 5.16/2.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.16/2.03  tff('#skF_7', type, '#skF_7': $i).
% 5.16/2.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.16/2.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.16/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.16/2.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.16/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.16/2.03  tff('#skF_6', type, '#skF_6': $i).
% 5.16/2.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.16/2.03  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.16/2.03  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 5.16/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.16/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.16/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.16/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.16/2.03  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.16/2.03  
% 5.16/2.05  tff(f_107, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((k1_relat_1(B) = k1_relat_1(C)) & (k2_relat_1(B) = k1_tarski(A))) & (k2_relat_1(C) = k1_tarski(A))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_1)).
% 5.16/2.05  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 5.16/2.05  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 5.16/2.05  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.16/2.05  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.16/2.05  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.16/2.05  tff(f_51, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 5.16/2.05  tff(c_54, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.16/2.05  tff(c_64, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.16/2.05  tff(c_62, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.16/2.05  tff(c_60, plain, (k1_relat_1('#skF_7')=k1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.16/2.05  tff(c_68, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.16/2.05  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.16/2.05  tff(c_52, plain, (![A_28, B_32]: (r2_hidden('#skF_4'(A_28, B_32), k1_relat_1(A_28)) | B_32=A_28 | k1_relat_1(B_32)!=k1_relat_1(A_28) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.16/2.05  tff(c_58, plain, (k2_relat_1('#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.16/2.05  tff(c_171, plain, (![B_81, A_82]: (r2_hidden(k1_funct_1(B_81, A_82), k2_relat_1(B_81)) | ~r2_hidden(A_82, k1_relat_1(B_81)) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.16/2.05  tff(c_177, plain, (![A_82]: (r2_hidden(k1_funct_1('#skF_6', A_82), k1_tarski('#skF_5')) | ~r2_hidden(A_82, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_171])).
% 5.16/2.05  tff(c_184, plain, (![A_82]: (r2_hidden(k1_funct_1('#skF_6', A_82), k1_tarski('#skF_5')) | ~r2_hidden(A_82, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_177])).
% 5.16/2.05  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.16/2.05  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.16/2.05  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.16/2.05  tff(c_251, plain, (![D_103, A_101, B_102, C_100, F_99]: (F_99=D_103 | F_99=C_100 | F_99=B_102 | F_99=A_101 | ~r2_hidden(F_99, k2_enumset1(A_101, B_102, C_100, D_103)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.16/2.05  tff(c_339, plain, (![F_135, C_136, B_137, A_138]: (F_135=C_136 | F_135=B_137 | F_135=A_138 | F_135=A_138 | ~r2_hidden(F_135, k1_enumset1(A_138, B_137, C_136)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_251])).
% 5.16/2.05  tff(c_358, plain, (![F_139, B_140, A_141]: (F_139=B_140 | F_139=A_141 | F_139=A_141 | F_139=A_141 | ~r2_hidden(F_139, k2_tarski(A_141, B_140)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_339])).
% 5.16/2.05  tff(c_372, plain, (![F_142, A_143]: (F_142=A_143 | F_142=A_143 | F_142=A_143 | F_142=A_143 | ~r2_hidden(F_142, k1_tarski(A_143)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_358])).
% 5.16/2.05  tff(c_398, plain, (![A_145]: (k1_funct_1('#skF_6', A_145)='#skF_5' | ~r2_hidden(A_145, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_184, c_372])).
% 5.16/2.05  tff(c_405, plain, (![B_32]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', B_32))='#skF_5' | B_32='#skF_6' | k1_relat_1(B_32)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_398])).
% 5.16/2.05  tff(c_409, plain, (![B_32]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', B_32))='#skF_5' | B_32='#skF_6' | k1_relat_1(B_32)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_405])).
% 5.16/2.05  tff(c_56, plain, (k2_relat_1('#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.16/2.05  tff(c_180, plain, (![A_82]: (r2_hidden(k1_funct_1('#skF_7', A_82), k1_tarski('#skF_5')) | ~r2_hidden(A_82, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_171])).
% 5.16/2.05  tff(c_186, plain, (![A_82]: (r2_hidden(k1_funct_1('#skF_7', A_82), k1_tarski('#skF_5')) | ~r2_hidden(A_82, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_180])).
% 5.16/2.05  tff(c_386, plain, (![A_144]: (k1_funct_1('#skF_7', A_144)='#skF_5' | ~r2_hidden(A_144, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_186, c_372])).
% 5.16/2.05  tff(c_393, plain, (![B_32]: (k1_funct_1('#skF_7', '#skF_4'('#skF_6', B_32))='#skF_5' | B_32='#skF_6' | k1_relat_1(B_32)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_386])).
% 5.16/2.05  tff(c_397, plain, (![B_32]: (k1_funct_1('#skF_7', '#skF_4'('#skF_6', B_32))='#skF_5' | B_32='#skF_6' | k1_relat_1(B_32)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_393])).
% 5.16/2.05  tff(c_4897, plain, (![B_292, A_293]: (k1_funct_1(B_292, '#skF_4'(A_293, B_292))!=k1_funct_1(A_293, '#skF_4'(A_293, B_292)) | B_292=A_293 | k1_relat_1(B_292)!=k1_relat_1(A_293) | ~v1_funct_1(B_292) | ~v1_relat_1(B_292) | ~v1_funct_1(A_293) | ~v1_relat_1(A_293))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.16/2.05  tff(c_4901, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', '#skF_7'))!='#skF_5' | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_397, c_4897])).
% 5.16/2.05  tff(c_4917, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', '#skF_7'))!='#skF_5' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_68, c_66, c_64, c_62, c_60, c_4901])).
% 5.16/2.05  tff(c_4918, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', '#skF_7'))!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_54, c_4917])).
% 5.16/2.05  tff(c_4929, plain, ('#skF_7'='#skF_6' | k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_409, c_4918])).
% 5.16/2.05  tff(c_4932, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_4929])).
% 5.16/2.05  tff(c_4934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_4932])).
% 5.16/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.05  
% 5.16/2.05  Inference rules
% 5.16/2.05  ----------------------
% 5.16/2.05  #Ref     : 2
% 5.16/2.05  #Sup     : 1129
% 5.16/2.05  #Fact    : 0
% 5.16/2.05  #Define  : 0
% 5.16/2.05  #Split   : 1
% 5.16/2.05  #Chain   : 0
% 5.16/2.05  #Close   : 0
% 5.16/2.05  
% 5.16/2.05  Ordering : KBO
% 5.16/2.05  
% 5.16/2.05  Simplification rules
% 5.16/2.05  ----------------------
% 5.16/2.05  #Subsume      : 259
% 5.16/2.05  #Demod        : 1217
% 5.16/2.05  #Tautology    : 617
% 5.16/2.05  #SimpNegUnit  : 3
% 5.16/2.05  #BackRed      : 0
% 5.16/2.05  
% 5.16/2.05  #Partial instantiations: 0
% 5.16/2.05  #Strategies tried      : 1
% 5.16/2.05  
% 5.16/2.05  Timing (in seconds)
% 5.16/2.05  ----------------------
% 5.16/2.05  Preprocessing        : 0.33
% 5.16/2.05  Parsing              : 0.17
% 5.16/2.05  CNF conversion       : 0.03
% 5.16/2.05  Main loop            : 0.96
% 5.16/2.05  Inferencing          : 0.32
% 5.16/2.05  Reduction            : 0.40
% 5.16/2.05  Demodulation         : 0.33
% 5.16/2.05  BG Simplification    : 0.04
% 5.16/2.05  Subsumption          : 0.15
% 5.16/2.05  Abstraction          : 0.05
% 5.16/2.05  MUC search           : 0.00
% 5.16/2.05  Cooper               : 0.00
% 5.16/2.05  Total                : 1.31
% 5.16/2.05  Index Insertion      : 0.00
% 5.16/2.05  Index Deletion       : 0.00
% 5.16/2.05  Index Matching       : 0.00
% 5.16/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
