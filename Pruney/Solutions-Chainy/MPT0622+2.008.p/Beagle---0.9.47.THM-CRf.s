%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:05 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 104 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 ( 361 expanded)
%              Number of equality atoms :   50 ( 163 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_86,negated_conjecture,(
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

tff(f_68,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

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

tff(c_34,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    k1_relat_1('#skF_5') = k1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2081,plain,(
    ! [A_3367,B_3368] :
      ( r2_hidden('#skF_3'(A_3367,B_3368),k1_relat_1(A_3367))
      | B_3368 = A_3367
      | k1_relat_1(B_3368) != k1_relat_1(A_3367)
      | ~ v1_funct_1(B_3368)
      | ~ v1_relat_1(B_3368)
      | ~ v1_funct_1(A_3367)
      | ~ v1_relat_1(A_3367) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    k2_relat_1('#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_127,plain,(
    ! [B_46,A_47] :
      ( r2_hidden(k1_funct_1(B_46,A_47),k2_relat_1(B_46))
      | ~ r2_hidden(A_47,k1_relat_1(B_46))
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_133,plain,(
    ! [A_47] :
      ( r2_hidden(k1_funct_1('#skF_6',A_47),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_47,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_127])).

tff(c_143,plain,(
    ! [A_49] :
      ( r2_hidden(k1_funct_1('#skF_6',A_49),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_49,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_133])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_89,plain,(
    ! [D_34,B_35,A_36] :
      ( D_34 = B_35
      | D_34 = A_36
      | ~ r2_hidden(D_34,k2_tarski(A_36,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_98,plain,(
    ! [D_34,A_7] :
      ( D_34 = A_7
      | D_34 = A_7
      | ~ r2_hidden(D_34,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_89])).

tff(c_147,plain,(
    ! [A_49] :
      ( k1_funct_1('#skF_6',A_49) = '#skF_4'
      | ~ r2_hidden(A_49,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_143,c_98])).

tff(c_2087,plain,(
    ! [B_3368] :
      ( k1_funct_1('#skF_6','#skF_3'('#skF_6',B_3368)) = '#skF_4'
      | B_3368 = '#skF_6'
      | k1_relat_1(B_3368) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_3368)
      | ~ v1_relat_1(B_3368)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2081,c_147])).

tff(c_2104,plain,(
    ! [B_3368] :
      ( k1_funct_1('#skF_6','#skF_3'('#skF_6',B_3368)) = '#skF_4'
      | B_3368 = '#skF_6'
      | k1_relat_1(B_3368) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_3368)
      | ~ v1_relat_1(B_3368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2087])).

tff(c_38,plain,(
    k2_relat_1('#skF_5') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_130,plain,(
    ! [A_47] :
      ( r2_hidden(k1_funct_1('#skF_5',A_47),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_47,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_127])).

tff(c_138,plain,(
    ! [A_48] :
      ( r2_hidden(k1_funct_1('#skF_5',A_48),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_48,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_130])).

tff(c_142,plain,(
    ! [A_48] :
      ( k1_funct_1('#skF_5',A_48) = '#skF_4'
      | ~ r2_hidden(A_48,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_138,c_98])).

tff(c_2091,plain,(
    ! [B_3368] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_6',B_3368)) = '#skF_4'
      | B_3368 = '#skF_6'
      | k1_relat_1(B_3368) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_3368)
      | ~ v1_relat_1(B_3368)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2081,c_142])).

tff(c_2107,plain,(
    ! [B_3368] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_6',B_3368)) = '#skF_4'
      | B_3368 = '#skF_6'
      | k1_relat_1(B_3368) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_3368)
      | ~ v1_relat_1(B_3368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2091])).

tff(c_2785,plain,(
    ! [B_4274,A_4275] :
      ( k1_funct_1(B_4274,'#skF_3'(A_4275,B_4274)) != k1_funct_1(A_4275,'#skF_3'(A_4275,B_4274))
      | B_4274 = A_4275
      | k1_relat_1(B_4274) != k1_relat_1(A_4275)
      | ~ v1_funct_1(B_4274)
      | ~ v1_relat_1(B_4274)
      | ~ v1_funct_1(A_4275)
      | ~ v1_relat_1(A_4275) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2789,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_2107,c_2785])).

tff(c_2809,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_44,c_42,c_48,c_46,c_40,c_2789])).

tff(c_2810,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2809])).

tff(c_2817,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_2810])).

tff(c_2823,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_2817])).

tff(c_2825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2823])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:26:12 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.76  
% 3.77/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.77  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.77/1.77  
% 3.77/1.77  %Foreground sorts:
% 3.77/1.77  
% 3.77/1.77  
% 3.77/1.77  %Background operators:
% 3.77/1.77  
% 3.77/1.77  
% 3.77/1.77  %Foreground operators:
% 3.77/1.77  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.77/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.77/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.77/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.77/1.77  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.77/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.77/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.77/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.77/1.77  tff('#skF_5', type, '#skF_5': $i).
% 3.77/1.77  tff('#skF_6', type, '#skF_6': $i).
% 3.77/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.77/1.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.77/1.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.77/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.77/1.77  tff('#skF_4', type, '#skF_4': $i).
% 3.77/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.77/1.77  
% 4.12/1.78  tff(f_86, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((k1_relat_1(B) = k1_relat_1(C)) & (k2_relat_1(B) = k1_tarski(A))) & (k2_relat_1(C) = k1_tarski(A))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_1)).
% 4.12/1.78  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 4.12/1.78  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 4.12/1.78  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.12/1.78  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.12/1.78  tff(c_34, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.12/1.78  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.12/1.78  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.12/1.78  tff(c_40, plain, (k1_relat_1('#skF_5')=k1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.12/1.78  tff(c_44, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.12/1.78  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.12/1.78  tff(c_2081, plain, (![A_3367, B_3368]: (r2_hidden('#skF_3'(A_3367, B_3368), k1_relat_1(A_3367)) | B_3368=A_3367 | k1_relat_1(B_3368)!=k1_relat_1(A_3367) | ~v1_funct_1(B_3368) | ~v1_relat_1(B_3368) | ~v1_funct_1(A_3367) | ~v1_relat_1(A_3367))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.12/1.78  tff(c_36, plain, (k2_relat_1('#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.12/1.78  tff(c_127, plain, (![B_46, A_47]: (r2_hidden(k1_funct_1(B_46, A_47), k2_relat_1(B_46)) | ~r2_hidden(A_47, k1_relat_1(B_46)) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.12/1.78  tff(c_133, plain, (![A_47]: (r2_hidden(k1_funct_1('#skF_6', A_47), k1_tarski('#skF_4')) | ~r2_hidden(A_47, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_127])).
% 4.12/1.78  tff(c_143, plain, (![A_49]: (r2_hidden(k1_funct_1('#skF_6', A_49), k1_tarski('#skF_4')) | ~r2_hidden(A_49, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_133])).
% 4.12/1.78  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.12/1.78  tff(c_89, plain, (![D_34, B_35, A_36]: (D_34=B_35 | D_34=A_36 | ~r2_hidden(D_34, k2_tarski(A_36, B_35)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.12/1.78  tff(c_98, plain, (![D_34, A_7]: (D_34=A_7 | D_34=A_7 | ~r2_hidden(D_34, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_89])).
% 4.12/1.78  tff(c_147, plain, (![A_49]: (k1_funct_1('#skF_6', A_49)='#skF_4' | ~r2_hidden(A_49, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_143, c_98])).
% 4.12/1.78  tff(c_2087, plain, (![B_3368]: (k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_3368))='#skF_4' | B_3368='#skF_6' | k1_relat_1(B_3368)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_3368) | ~v1_relat_1(B_3368) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_2081, c_147])).
% 4.12/1.78  tff(c_2104, plain, (![B_3368]: (k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_3368))='#skF_4' | B_3368='#skF_6' | k1_relat_1(B_3368)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_3368) | ~v1_relat_1(B_3368))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2087])).
% 4.12/1.78  tff(c_38, plain, (k2_relat_1('#skF_5')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.12/1.78  tff(c_130, plain, (![A_47]: (r2_hidden(k1_funct_1('#skF_5', A_47), k1_tarski('#skF_4')) | ~r2_hidden(A_47, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_127])).
% 4.12/1.78  tff(c_138, plain, (![A_48]: (r2_hidden(k1_funct_1('#skF_5', A_48), k1_tarski('#skF_4')) | ~r2_hidden(A_48, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_130])).
% 4.12/1.78  tff(c_142, plain, (![A_48]: (k1_funct_1('#skF_5', A_48)='#skF_4' | ~r2_hidden(A_48, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_138, c_98])).
% 4.12/1.78  tff(c_2091, plain, (![B_3368]: (k1_funct_1('#skF_5', '#skF_3'('#skF_6', B_3368))='#skF_4' | B_3368='#skF_6' | k1_relat_1(B_3368)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_3368) | ~v1_relat_1(B_3368) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_2081, c_142])).
% 4.12/1.78  tff(c_2107, plain, (![B_3368]: (k1_funct_1('#skF_5', '#skF_3'('#skF_6', B_3368))='#skF_4' | B_3368='#skF_6' | k1_relat_1(B_3368)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_3368) | ~v1_relat_1(B_3368))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2091])).
% 4.12/1.78  tff(c_2785, plain, (![B_4274, A_4275]: (k1_funct_1(B_4274, '#skF_3'(A_4275, B_4274))!=k1_funct_1(A_4275, '#skF_3'(A_4275, B_4274)) | B_4274=A_4275 | k1_relat_1(B_4274)!=k1_relat_1(A_4275) | ~v1_funct_1(B_4274) | ~v1_relat_1(B_4274) | ~v1_funct_1(A_4275) | ~v1_relat_1(A_4275))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.12/1.78  tff(c_2789, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4' | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2107, c_2785])).
% 4.12/1.78  tff(c_2809, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_44, c_42, c_48, c_46, c_40, c_2789])).
% 4.12/1.78  tff(c_2810, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_34, c_2809])).
% 4.12/1.78  tff(c_2817, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2104, c_2810])).
% 4.12/1.78  tff(c_2823, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_2817])).
% 4.12/1.78  tff(c_2825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_2823])).
% 4.12/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.78  
% 4.12/1.78  Inference rules
% 4.12/1.78  ----------------------
% 4.12/1.78  #Ref     : 1
% 4.12/1.78  #Sup     : 381
% 4.12/1.78  #Fact    : 14
% 4.12/1.78  #Define  : 0
% 4.12/1.78  #Split   : 3
% 4.12/1.78  #Chain   : 0
% 4.12/1.78  #Close   : 0
% 4.12/1.78  
% 4.12/1.78  Ordering : KBO
% 4.12/1.78  
% 4.12/1.78  Simplification rules
% 4.12/1.78  ----------------------
% 4.12/1.78  #Subsume      : 104
% 4.12/1.78  #Demod        : 94
% 4.12/1.78  #Tautology    : 135
% 4.12/1.78  #SimpNegUnit  : 2
% 4.12/1.78  #BackRed      : 0
% 4.12/1.78  
% 4.12/1.78  #Partial instantiations: 2226
% 4.12/1.78  #Strategies tried      : 1
% 4.12/1.78  
% 4.12/1.78  Timing (in seconds)
% 4.12/1.78  ----------------------
% 4.12/1.78  Preprocessing        : 0.35
% 4.12/1.78  Parsing              : 0.16
% 4.12/1.78  CNF conversion       : 0.03
% 4.12/1.78  Main loop            : 0.66
% 4.12/1.78  Inferencing          : 0.34
% 4.12/1.78  Reduction            : 0.14
% 4.12/1.78  Demodulation         : 0.10
% 4.12/1.78  BG Simplification    : 0.04
% 4.12/1.78  Subsumption          : 0.11
% 4.12/1.78  Abstraction          : 0.03
% 4.12/1.78  MUC search           : 0.00
% 4.12/1.78  Cooper               : 0.00
% 4.12/1.78  Total                : 1.04
% 4.12/1.78  Index Insertion      : 0.00
% 4.12/1.78  Index Deletion       : 0.00
% 4.12/1.78  Index Matching       : 0.00
% 4.12/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
