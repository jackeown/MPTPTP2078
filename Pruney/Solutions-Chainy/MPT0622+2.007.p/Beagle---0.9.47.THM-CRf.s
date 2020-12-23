%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:05 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
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
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_97,negated_conjecture,(
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

tff(f_79,axiom,(
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

tff(f_61,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(c_48,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_62,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_54,plain,(
    k1_relat_1('#skF_5') = k1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_58,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46,plain,(
    ! [A_26,B_30] :
      ( r2_hidden('#skF_3'(A_26,B_30),k1_relat_1(A_26))
      | B_30 = A_26
      | k1_relat_1(B_30) != k1_relat_1(A_26)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,(
    k2_relat_1('#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_160,plain,(
    ! [B_78,A_79] :
      ( r2_hidden(k1_funct_1(B_78,A_79),k2_relat_1(B_78))
      | ~ r2_hidden(A_79,k1_relat_1(B_78))
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_166,plain,(
    ! [A_79] :
      ( r2_hidden(k1_funct_1('#skF_6',A_79),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_79,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_160])).

tff(c_170,plain,(
    ! [A_79] :
      ( r2_hidden(k1_funct_1('#skF_6',A_79),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_79,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_166])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,(
    ! [A_81,C_84,B_80,F_82,D_83] :
      ( F_82 = D_83
      | F_82 = C_84
      | F_82 = B_80
      | F_82 = A_81
      | ~ r2_hidden(F_82,k2_enumset1(A_81,B_80,C_84,D_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_197,plain,(
    ! [F_87,C_88,B_89,A_90] :
      ( F_87 = C_88
      | F_87 = B_89
      | F_87 = A_90
      | F_87 = A_90
      | ~ r2_hidden(F_87,k1_enumset1(A_90,B_89,C_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_171])).

tff(c_222,plain,(
    ! [F_93,B_94,A_95] :
      ( F_93 = B_94
      | F_93 = A_95
      | F_93 = A_95
      | F_93 = A_95
      | ~ r2_hidden(F_93,k2_tarski(A_95,B_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_197])).

tff(c_236,plain,(
    ! [F_96,A_97] :
      ( F_96 = A_97
      | F_96 = A_97
      | F_96 = A_97
      | F_96 = A_97
      | ~ r2_hidden(F_96,k1_tarski(A_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_222])).

tff(c_250,plain,(
    ! [A_98] :
      ( k1_funct_1('#skF_6',A_98) = '#skF_4'
      | ~ r2_hidden(A_98,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_170,c_236])).

tff(c_254,plain,(
    ! [B_30] :
      ( k1_funct_1('#skF_6','#skF_3'('#skF_6',B_30)) = '#skF_4'
      | B_30 = '#skF_6'
      | k1_relat_1(B_30) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_250])).

tff(c_257,plain,(
    ! [B_30] :
      ( k1_funct_1('#skF_6','#skF_3'('#skF_6',B_30)) = '#skF_4'
      | B_30 = '#skF_6'
      | k1_relat_1(B_30) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_254])).

tff(c_52,plain,(
    k2_relat_1('#skF_5') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_163,plain,(
    ! [A_79] :
      ( r2_hidden(k1_funct_1('#skF_5',A_79),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_79,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_160])).

tff(c_168,plain,(
    ! [A_79] :
      ( r2_hidden(k1_funct_1('#skF_5',A_79),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_79,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_54,c_163])).

tff(c_258,plain,(
    ! [A_99] :
      ( k1_funct_1('#skF_5',A_99) = '#skF_4'
      | ~ r2_hidden(A_99,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_168,c_236])).

tff(c_262,plain,(
    ! [B_30] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_6',B_30)) = '#skF_4'
      | B_30 = '#skF_6'
      | k1_relat_1(B_30) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_258])).

tff(c_265,plain,(
    ! [B_30] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_6',B_30)) = '#skF_4'
      | B_30 = '#skF_6'
      | k1_relat_1(B_30) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_262])).

tff(c_391,plain,(
    ! [B_130,A_131] :
      ( k1_funct_1(B_130,'#skF_3'(A_131,B_130)) != k1_funct_1(A_131,'#skF_3'(A_131,B_130))
      | B_130 = A_131
      | k1_relat_1(B_130) != k1_relat_1(A_131)
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_395,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_265,c_391])).

tff(c_403,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_54,c_58,c_56,c_62,c_60,c_54,c_395])).

tff(c_404,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_403])).

tff(c_412,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_404])).

tff(c_415,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_54,c_412])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:58:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.36  
% 2.61/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.36  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 2.61/1.36  
% 2.61/1.36  %Foreground sorts:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Background operators:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Foreground operators:
% 2.61/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.61/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.61/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.61/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.61/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.36  
% 2.61/1.37  tff(f_97, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((k1_relat_1(B) = k1_relat_1(C)) & (k2_relat_1(B) = k1_tarski(A))) & (k2_relat_1(C) = k1_tarski(A))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_1)).
% 2.61/1.37  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 2.61/1.37  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.61/1.37  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.61/1.37  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.61/1.37  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.61/1.37  tff(f_53, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.61/1.37  tff(c_48, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.61/1.37  tff(c_62, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.61/1.37  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.61/1.37  tff(c_54, plain, (k1_relat_1('#skF_5')=k1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.61/1.37  tff(c_58, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.61/1.37  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.61/1.37  tff(c_46, plain, (![A_26, B_30]: (r2_hidden('#skF_3'(A_26, B_30), k1_relat_1(A_26)) | B_30=A_26 | k1_relat_1(B_30)!=k1_relat_1(A_26) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.61/1.37  tff(c_50, plain, (k2_relat_1('#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.61/1.37  tff(c_160, plain, (![B_78, A_79]: (r2_hidden(k1_funct_1(B_78, A_79), k2_relat_1(B_78)) | ~r2_hidden(A_79, k1_relat_1(B_78)) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.61/1.37  tff(c_166, plain, (![A_79]: (r2_hidden(k1_funct_1('#skF_6', A_79), k1_tarski('#skF_4')) | ~r2_hidden(A_79, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_160])).
% 2.61/1.37  tff(c_170, plain, (![A_79]: (r2_hidden(k1_funct_1('#skF_6', A_79), k1_tarski('#skF_4')) | ~r2_hidden(A_79, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_166])).
% 2.61/1.37  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.61/1.37  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.37  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.37  tff(c_171, plain, (![A_81, C_84, B_80, F_82, D_83]: (F_82=D_83 | F_82=C_84 | F_82=B_80 | F_82=A_81 | ~r2_hidden(F_82, k2_enumset1(A_81, B_80, C_84, D_83)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.37  tff(c_197, plain, (![F_87, C_88, B_89, A_90]: (F_87=C_88 | F_87=B_89 | F_87=A_90 | F_87=A_90 | ~r2_hidden(F_87, k1_enumset1(A_90, B_89, C_88)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_171])).
% 2.61/1.37  tff(c_222, plain, (![F_93, B_94, A_95]: (F_93=B_94 | F_93=A_95 | F_93=A_95 | F_93=A_95 | ~r2_hidden(F_93, k2_tarski(A_95, B_94)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_197])).
% 2.61/1.37  tff(c_236, plain, (![F_96, A_97]: (F_96=A_97 | F_96=A_97 | F_96=A_97 | F_96=A_97 | ~r2_hidden(F_96, k1_tarski(A_97)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_222])).
% 2.61/1.37  tff(c_250, plain, (![A_98]: (k1_funct_1('#skF_6', A_98)='#skF_4' | ~r2_hidden(A_98, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_170, c_236])).
% 2.61/1.37  tff(c_254, plain, (![B_30]: (k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_30))='#skF_4' | B_30='#skF_6' | k1_relat_1(B_30)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_30) | ~v1_relat_1(B_30) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_46, c_250])).
% 2.61/1.37  tff(c_257, plain, (![B_30]: (k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_30))='#skF_4' | B_30='#skF_6' | k1_relat_1(B_30)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_254])).
% 2.61/1.37  tff(c_52, plain, (k2_relat_1('#skF_5')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.61/1.37  tff(c_163, plain, (![A_79]: (r2_hidden(k1_funct_1('#skF_5', A_79), k1_tarski('#skF_4')) | ~r2_hidden(A_79, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_160])).
% 2.61/1.37  tff(c_168, plain, (![A_79]: (r2_hidden(k1_funct_1('#skF_5', A_79), k1_tarski('#skF_4')) | ~r2_hidden(A_79, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_54, c_163])).
% 2.61/1.37  tff(c_258, plain, (![A_99]: (k1_funct_1('#skF_5', A_99)='#skF_4' | ~r2_hidden(A_99, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_168, c_236])).
% 2.61/1.37  tff(c_262, plain, (![B_30]: (k1_funct_1('#skF_5', '#skF_3'('#skF_6', B_30))='#skF_4' | B_30='#skF_6' | k1_relat_1(B_30)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_30) | ~v1_relat_1(B_30) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_46, c_258])).
% 2.61/1.37  tff(c_265, plain, (![B_30]: (k1_funct_1('#skF_5', '#skF_3'('#skF_6', B_30))='#skF_4' | B_30='#skF_6' | k1_relat_1(B_30)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_262])).
% 2.61/1.37  tff(c_391, plain, (![B_130, A_131]: (k1_funct_1(B_130, '#skF_3'(A_131, B_130))!=k1_funct_1(A_131, '#skF_3'(A_131, B_130)) | B_130=A_131 | k1_relat_1(B_130)!=k1_relat_1(A_131) | ~v1_funct_1(B_130) | ~v1_relat_1(B_130) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.61/1.37  tff(c_395, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4' | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_265, c_391])).
% 2.61/1.37  tff(c_403, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_54, c_58, c_56, c_62, c_60, c_54, c_395])).
% 2.61/1.37  tff(c_404, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_403])).
% 2.61/1.37  tff(c_412, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_257, c_404])).
% 2.61/1.37  tff(c_415, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_54, c_412])).
% 2.61/1.37  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_415])).
% 2.61/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.37  
% 2.61/1.37  Inference rules
% 2.61/1.37  ----------------------
% 2.61/1.37  #Ref     : 1
% 2.61/1.37  #Sup     : 73
% 2.61/1.37  #Fact    : 0
% 2.61/1.37  #Define  : 0
% 2.61/1.37  #Split   : 0
% 2.61/1.37  #Chain   : 0
% 2.61/1.37  #Close   : 0
% 2.61/1.37  
% 2.61/1.37  Ordering : KBO
% 2.61/1.37  
% 2.61/1.37  Simplification rules
% 2.61/1.37  ----------------------
% 2.61/1.37  #Subsume      : 0
% 2.61/1.37  #Demod        : 53
% 2.61/1.37  #Tautology    : 46
% 2.61/1.37  #SimpNegUnit  : 2
% 2.61/1.37  #BackRed      : 0
% 2.61/1.37  
% 2.61/1.37  #Partial instantiations: 0
% 2.61/1.37  #Strategies tried      : 1
% 2.61/1.37  
% 2.61/1.37  Timing (in seconds)
% 2.61/1.37  ----------------------
% 2.61/1.38  Preprocessing        : 0.32
% 2.61/1.38  Parsing              : 0.16
% 2.61/1.38  CNF conversion       : 0.02
% 2.61/1.38  Main loop            : 0.28
% 2.61/1.38  Inferencing          : 0.11
% 2.61/1.38  Reduction            : 0.08
% 2.61/1.38  Demodulation         : 0.06
% 2.61/1.38  BG Simplification    : 0.02
% 2.61/1.38  Subsumption          : 0.06
% 2.61/1.38  Abstraction          : 0.02
% 2.61/1.38  MUC search           : 0.00
% 2.61/1.38  Cooper               : 0.00
% 2.61/1.38  Total                : 0.63
% 2.61/1.38  Index Insertion      : 0.00
% 2.61/1.38  Index Deletion       : 0.00
% 2.61/1.38  Index Matching       : 0.00
% 2.61/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
