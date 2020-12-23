%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:06 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 122 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  151 ( 427 expanded)
%              Number of equality atoms :   80 ( 223 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_98,negated_conjecture,(
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

tff(f_80,axiom,(
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

tff(f_62,axiom,(
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

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

tff(c_52,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_66,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_58,plain,(
    k1_relat_1('#skF_5') = k1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_62,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_50,plain,(
    ! [A_22,B_26] :
      ( r2_hidden('#skF_3'(A_22,B_26),k1_relat_1(A_22))
      | B_26 = A_22
      | k1_relat_1(B_26) != k1_relat_1(A_22)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_54,plain,(
    k2_relat_1('#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_143,plain,(
    ! [B_71,A_72] :
      ( r2_hidden(k1_funct_1(B_71,A_72),k2_relat_1(B_71))
      | ~ r2_hidden(A_72,k1_relat_1(B_71))
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_149,plain,(
    ! [A_72] :
      ( r2_hidden(k1_funct_1('#skF_6',A_72),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_72,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_143])).

tff(c_153,plain,(
    ! [A_72] :
      ( r2_hidden(k1_funct_1('#skF_6',A_72),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_72,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_149])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_172,plain,(
    ! [A_88,G_89,D_91,E_92,C_87,B_90] :
      ( G_89 = E_92
      | G_89 = D_91
      | G_89 = C_87
      | G_89 = B_90
      | G_89 = A_88
      | ~ r2_hidden(G_89,k3_enumset1(A_88,B_90,C_87,D_91,E_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_218,plain,(
    ! [D_104,G_108,A_107,C_106,B_105] :
      ( G_108 = D_104
      | G_108 = C_106
      | G_108 = B_105
      | G_108 = A_107
      | G_108 = A_107
      | ~ r2_hidden(G_108,k2_enumset1(A_107,B_105,C_106,D_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_172])).

tff(c_242,plain,(
    ! [G_109,C_110,B_111,A_112] :
      ( G_109 = C_110
      | G_109 = B_111
      | G_109 = A_112
      | G_109 = A_112
      | G_109 = A_112
      | ~ r2_hidden(G_109,k1_enumset1(A_112,B_111,C_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_218])).

tff(c_261,plain,(
    ! [G_113,B_114,A_115] :
      ( G_113 = B_114
      | G_113 = A_115
      | G_113 = A_115
      | G_113 = A_115
      | G_113 = A_115
      | ~ r2_hidden(G_113,k2_tarski(A_115,B_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_242])).

tff(c_281,plain,(
    ! [G_118,A_119] :
      ( G_118 = A_119
      | G_118 = A_119
      | G_118 = A_119
      | G_118 = A_119
      | G_118 = A_119
      | ~ r2_hidden(G_118,k1_tarski(A_119)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_261])).

tff(c_295,plain,(
    ! [A_120] :
      ( k1_funct_1('#skF_6',A_120) = '#skF_4'
      | ~ r2_hidden(A_120,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_153,c_281])).

tff(c_299,plain,(
    ! [B_26] :
      ( k1_funct_1('#skF_6','#skF_3'('#skF_6',B_26)) = '#skF_4'
      | B_26 = '#skF_6'
      | k1_relat_1(B_26) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_295])).

tff(c_302,plain,(
    ! [B_26] :
      ( k1_funct_1('#skF_6','#skF_3'('#skF_6',B_26)) = '#skF_4'
      | B_26 = '#skF_6'
      | k1_relat_1(B_26) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_299])).

tff(c_56,plain,(
    k2_relat_1('#skF_5') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_146,plain,(
    ! [A_72] :
      ( r2_hidden(k1_funct_1('#skF_5',A_72),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_72,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_143])).

tff(c_151,plain,(
    ! [A_72] :
      ( r2_hidden(k1_funct_1('#skF_5',A_72),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_72,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_146])).

tff(c_303,plain,(
    ! [A_121] :
      ( k1_funct_1('#skF_5',A_121) = '#skF_4'
      | ~ r2_hidden(A_121,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_151,c_281])).

tff(c_307,plain,(
    ! [B_26] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_6',B_26)) = '#skF_4'
      | B_26 = '#skF_6'
      | k1_relat_1(B_26) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_303])).

tff(c_310,plain,(
    ! [B_26] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_6',B_26)) = '#skF_4'
      | B_26 = '#skF_6'
      | k1_relat_1(B_26) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_307])).

tff(c_402,plain,(
    ! [B_133,A_134] :
      ( k1_funct_1(B_133,'#skF_3'(A_134,B_133)) != k1_funct_1(A_134,'#skF_3'(A_134,B_133))
      | B_133 = A_134
      | k1_relat_1(B_133) != k1_relat_1(A_134)
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133)
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_412,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) != '#skF_4'
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_402])).

tff(c_418,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_62,c_60,c_66,c_64,c_58,c_412])).

tff(c_419,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_418])).

tff(c_422,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_419])).

tff(c_425,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_422])).

tff(c_427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_425])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.84  
% 3.37/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.85  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 3.37/1.85  
% 3.37/1.85  %Foreground sorts:
% 3.37/1.85  
% 3.37/1.85  
% 3.37/1.85  %Background operators:
% 3.37/1.85  
% 3.37/1.85  
% 3.37/1.85  %Foreground operators:
% 3.37/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.37/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.37/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.37/1.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.37/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.37/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.37/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.85  tff('#skF_5', type, '#skF_5': $i).
% 3.37/1.85  tff('#skF_6', type, '#skF_6': $i).
% 3.37/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.37/1.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.37/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.37/1.85  tff('#skF_4', type, '#skF_4': $i).
% 3.37/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.37/1.85  
% 3.37/1.87  tff(f_98, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((k1_relat_1(B) = k1_relat_1(C)) & (k2_relat_1(B) = k1_tarski(A))) & (k2_relat_1(C) = k1_tarski(A))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_1)).
% 3.37/1.87  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 3.37/1.87  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.37/1.87  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.37/1.87  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.37/1.87  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.37/1.87  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.37/1.87  tff(f_54, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 3.37/1.87  tff(c_52, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.37/1.87  tff(c_66, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.37/1.87  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.37/1.87  tff(c_58, plain, (k1_relat_1('#skF_5')=k1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.37/1.87  tff(c_62, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.37/1.87  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.37/1.87  tff(c_50, plain, (![A_22, B_26]: (r2_hidden('#skF_3'(A_22, B_26), k1_relat_1(A_22)) | B_26=A_22 | k1_relat_1(B_26)!=k1_relat_1(A_22) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.37/1.87  tff(c_54, plain, (k2_relat_1('#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.37/1.87  tff(c_143, plain, (![B_71, A_72]: (r2_hidden(k1_funct_1(B_71, A_72), k2_relat_1(B_71)) | ~r2_hidden(A_72, k1_relat_1(B_71)) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.37/1.87  tff(c_149, plain, (![A_72]: (r2_hidden(k1_funct_1('#skF_6', A_72), k1_tarski('#skF_4')) | ~r2_hidden(A_72, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_143])).
% 3.37/1.87  tff(c_153, plain, (![A_72]: (r2_hidden(k1_funct_1('#skF_6', A_72), k1_tarski('#skF_4')) | ~r2_hidden(A_72, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_149])).
% 3.37/1.87  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.37/1.87  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.37/1.87  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.37/1.87  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.37/1.87  tff(c_172, plain, (![A_88, G_89, D_91, E_92, C_87, B_90]: (G_89=E_92 | G_89=D_91 | G_89=C_87 | G_89=B_90 | G_89=A_88 | ~r2_hidden(G_89, k3_enumset1(A_88, B_90, C_87, D_91, E_92)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.37/1.87  tff(c_218, plain, (![D_104, G_108, A_107, C_106, B_105]: (G_108=D_104 | G_108=C_106 | G_108=B_105 | G_108=A_107 | G_108=A_107 | ~r2_hidden(G_108, k2_enumset1(A_107, B_105, C_106, D_104)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_172])).
% 3.37/1.87  tff(c_242, plain, (![G_109, C_110, B_111, A_112]: (G_109=C_110 | G_109=B_111 | G_109=A_112 | G_109=A_112 | G_109=A_112 | ~r2_hidden(G_109, k1_enumset1(A_112, B_111, C_110)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_218])).
% 3.37/1.87  tff(c_261, plain, (![G_113, B_114, A_115]: (G_113=B_114 | G_113=A_115 | G_113=A_115 | G_113=A_115 | G_113=A_115 | ~r2_hidden(G_113, k2_tarski(A_115, B_114)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_242])).
% 3.37/1.87  tff(c_281, plain, (![G_118, A_119]: (G_118=A_119 | G_118=A_119 | G_118=A_119 | G_118=A_119 | G_118=A_119 | ~r2_hidden(G_118, k1_tarski(A_119)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_261])).
% 3.37/1.87  tff(c_295, plain, (![A_120]: (k1_funct_1('#skF_6', A_120)='#skF_4' | ~r2_hidden(A_120, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_153, c_281])).
% 3.37/1.87  tff(c_299, plain, (![B_26]: (k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_26))='#skF_4' | B_26='#skF_6' | k1_relat_1(B_26)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_295])).
% 3.37/1.87  tff(c_302, plain, (![B_26]: (k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_26))='#skF_4' | B_26='#skF_6' | k1_relat_1(B_26)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_299])).
% 3.37/1.87  tff(c_56, plain, (k2_relat_1('#skF_5')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.37/1.87  tff(c_146, plain, (![A_72]: (r2_hidden(k1_funct_1('#skF_5', A_72), k1_tarski('#skF_4')) | ~r2_hidden(A_72, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_143])).
% 3.37/1.87  tff(c_151, plain, (![A_72]: (r2_hidden(k1_funct_1('#skF_5', A_72), k1_tarski('#skF_4')) | ~r2_hidden(A_72, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_146])).
% 3.37/1.87  tff(c_303, plain, (![A_121]: (k1_funct_1('#skF_5', A_121)='#skF_4' | ~r2_hidden(A_121, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_151, c_281])).
% 3.37/1.87  tff(c_307, plain, (![B_26]: (k1_funct_1('#skF_5', '#skF_3'('#skF_6', B_26))='#skF_4' | B_26='#skF_6' | k1_relat_1(B_26)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_303])).
% 3.37/1.87  tff(c_310, plain, (![B_26]: (k1_funct_1('#skF_5', '#skF_3'('#skF_6', B_26))='#skF_4' | B_26='#skF_6' | k1_relat_1(B_26)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_307])).
% 3.37/1.87  tff(c_402, plain, (![B_133, A_134]: (k1_funct_1(B_133, '#skF_3'(A_134, B_133))!=k1_funct_1(A_134, '#skF_3'(A_134, B_133)) | B_133=A_134 | k1_relat_1(B_133)!=k1_relat_1(A_134) | ~v1_funct_1(B_133) | ~v1_relat_1(B_133) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.37/1.87  tff(c_412, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4' | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_310, c_402])).
% 3.37/1.87  tff(c_418, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_62, c_60, c_66, c_64, c_58, c_412])).
% 3.37/1.87  tff(c_419, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_418])).
% 3.37/1.87  tff(c_422, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_302, c_419])).
% 3.37/1.87  tff(c_425, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_422])).
% 3.37/1.87  tff(c_427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_425])).
% 3.37/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.87  
% 3.37/1.87  Inference rules
% 3.37/1.87  ----------------------
% 3.37/1.87  #Ref     : 1
% 3.37/1.87  #Sup     : 76
% 3.37/1.87  #Fact    : 0
% 3.37/1.87  #Define  : 0
% 3.37/1.87  #Split   : 0
% 3.37/1.87  #Chain   : 0
% 3.37/1.87  #Close   : 0
% 3.37/1.87  
% 3.37/1.87  Ordering : KBO
% 3.37/1.87  
% 3.37/1.87  Simplification rules
% 3.37/1.87  ----------------------
% 3.37/1.87  #Subsume      : 0
% 3.37/1.87  #Demod        : 54
% 3.37/1.87  #Tautology    : 50
% 3.37/1.87  #SimpNegUnit  : 2
% 3.37/1.87  #BackRed      : 0
% 3.37/1.87  
% 3.37/1.87  #Partial instantiations: 0
% 3.37/1.87  #Strategies tried      : 1
% 3.37/1.87  
% 3.37/1.87  Timing (in seconds)
% 3.37/1.87  ----------------------
% 3.37/1.87  Preprocessing        : 0.52
% 3.37/1.88  Parsing              : 0.25
% 3.37/1.88  CNF conversion       : 0.04
% 3.37/1.88  Main loop            : 0.47
% 3.37/1.88  Inferencing          : 0.17
% 3.37/1.88  Reduction            : 0.14
% 3.37/1.88  Demodulation         : 0.10
% 3.37/1.88  BG Simplification    : 0.04
% 3.37/1.88  Subsumption          : 0.10
% 3.37/1.88  Abstraction          : 0.03
% 3.37/1.88  MUC search           : 0.00
% 3.37/1.88  Cooper               : 0.00
% 3.37/1.88  Total                : 1.04
% 3.37/1.88  Index Insertion      : 0.00
% 3.37/1.88  Index Deletion       : 0.00
% 3.37/1.88  Index Matching       : 0.00
% 3.37/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
