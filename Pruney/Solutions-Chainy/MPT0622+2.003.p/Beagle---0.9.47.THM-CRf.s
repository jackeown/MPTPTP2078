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

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 110 expanded)
%              Number of leaves         :   26 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  127 ( 379 expanded)
%              Number of equality atoms :   58 ( 179 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_92,negated_conjecture,(
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

tff(f_74,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_40,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    k1_relat_1('#skF_5') = k1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_217,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_3'(A_82,B_83),k1_relat_1(A_82))
      | B_83 = A_82
      | k1_relat_1(B_83) != k1_relat_1(A_82)
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83)
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    k2_relat_1('#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_165,plain,(
    ! [B_60,A_61] :
      ( r2_hidden(k1_funct_1(B_60,A_61),k2_relat_1(B_60))
      | ~ r2_hidden(A_61,k1_relat_1(B_60))
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_171,plain,(
    ! [A_61] :
      ( r2_hidden(k1_funct_1('#skF_6',A_61),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_61,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_165])).

tff(c_183,plain,(
    ! [A_68] :
      ( r2_hidden(k1_funct_1('#skF_6',A_68),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_68,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_171])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_126,plain,(
    ! [E_51,C_52,B_53,A_54] :
      ( E_51 = C_52
      | E_51 = B_53
      | E_51 = A_54
      | ~ r2_hidden(E_51,k1_enumset1(A_54,B_53,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_145,plain,(
    ! [E_55,B_56,A_57] :
      ( E_55 = B_56
      | E_55 = A_57
      | E_55 = A_57
      | ~ r2_hidden(E_55,k2_tarski(A_57,B_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_126])).

tff(c_154,plain,(
    ! [E_55,A_8] :
      ( E_55 = A_8
      | E_55 = A_8
      | E_55 = A_8
      | ~ r2_hidden(E_55,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_145])).

tff(c_187,plain,(
    ! [A_68] :
      ( k1_funct_1('#skF_6',A_68) = '#skF_4'
      | ~ r2_hidden(A_68,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_183,c_154])).

tff(c_221,plain,(
    ! [B_83] :
      ( k1_funct_1('#skF_6','#skF_3'('#skF_6',B_83)) = '#skF_4'
      | B_83 = '#skF_6'
      | k1_relat_1(B_83) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_217,c_187])).

tff(c_231,plain,(
    ! [B_83] :
      ( k1_funct_1('#skF_6','#skF_3'('#skF_6',B_83)) = '#skF_4'
      | B_83 = '#skF_6'
      | k1_relat_1(B_83) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_221])).

tff(c_44,plain,(
    k2_relat_1('#skF_5') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_168,plain,(
    ! [A_61] :
      ( r2_hidden(k1_funct_1('#skF_5',A_61),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_61,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_165])).

tff(c_176,plain,(
    ! [A_62] :
      ( r2_hidden(k1_funct_1('#skF_5',A_62),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_62,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_46,c_168])).

tff(c_180,plain,(
    ! [A_62] :
      ( k1_funct_1('#skF_5',A_62) = '#skF_4'
      | ~ r2_hidden(A_62,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_176,c_154])).

tff(c_225,plain,(
    ! [B_83] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_6',B_83)) = '#skF_4'
      | B_83 = '#skF_6'
      | k1_relat_1(B_83) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_217,c_180])).

tff(c_234,plain,(
    ! [B_83] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_6',B_83)) = '#skF_4'
      | B_83 = '#skF_6'
      | k1_relat_1(B_83) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_225])).

tff(c_289,plain,(
    ! [B_87,A_88] :
      ( k1_funct_1(B_87,'#skF_3'(A_88,B_87)) != k1_funct_1(A_88,'#skF_3'(A_88,B_87))
      | B_87 = A_88
      | k1_relat_1(B_87) != k1_relat_1(A_88)
      | ~ v1_funct_1(B_87)
      | ~ v1_relat_1(B_87)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_293,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_234,c_289])).

tff(c_298,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_46,c_50,c_48,c_54,c_52,c_46,c_293])).

tff(c_299,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_298])).

tff(c_304,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_299])).

tff(c_307,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_46,c_304])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:11:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.36  
% 2.49/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.37  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_1
% 2.49/1.37  
% 2.49/1.37  %Foreground sorts:
% 2.49/1.37  
% 2.49/1.37  
% 2.49/1.37  %Background operators:
% 2.49/1.37  
% 2.49/1.37  
% 2.49/1.37  %Foreground operators:
% 2.49/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.49/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.49/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.49/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.49/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.37  
% 2.49/1.38  tff(f_92, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((k1_relat_1(B) = k1_relat_1(C)) & (k2_relat_1(B) = k1_tarski(A))) & (k2_relat_1(C) = k1_tarski(A))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_1)).
% 2.49/1.38  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 2.49/1.38  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.49/1.38  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.49/1.38  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.49/1.39  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.49/1.39  tff(c_40, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.49/1.39  tff(c_54, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.49/1.39  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.49/1.39  tff(c_46, plain, (k1_relat_1('#skF_5')=k1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.49/1.39  tff(c_50, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.49/1.39  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.49/1.39  tff(c_217, plain, (![A_82, B_83]: (r2_hidden('#skF_3'(A_82, B_83), k1_relat_1(A_82)) | B_83=A_82 | k1_relat_1(B_83)!=k1_relat_1(A_82) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.49/1.39  tff(c_42, plain, (k2_relat_1('#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.49/1.39  tff(c_165, plain, (![B_60, A_61]: (r2_hidden(k1_funct_1(B_60, A_61), k2_relat_1(B_60)) | ~r2_hidden(A_61, k1_relat_1(B_60)) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.39  tff(c_171, plain, (![A_61]: (r2_hidden(k1_funct_1('#skF_6', A_61), k1_tarski('#skF_4')) | ~r2_hidden(A_61, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_165])).
% 2.49/1.39  tff(c_183, plain, (![A_68]: (r2_hidden(k1_funct_1('#skF_6', A_68), k1_tarski('#skF_4')) | ~r2_hidden(A_68, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_171])).
% 2.49/1.39  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.49/1.39  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.49/1.39  tff(c_126, plain, (![E_51, C_52, B_53, A_54]: (E_51=C_52 | E_51=B_53 | E_51=A_54 | ~r2_hidden(E_51, k1_enumset1(A_54, B_53, C_52)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.49/1.39  tff(c_145, plain, (![E_55, B_56, A_57]: (E_55=B_56 | E_55=A_57 | E_55=A_57 | ~r2_hidden(E_55, k2_tarski(A_57, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_126])).
% 2.49/1.39  tff(c_154, plain, (![E_55, A_8]: (E_55=A_8 | E_55=A_8 | E_55=A_8 | ~r2_hidden(E_55, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_145])).
% 2.49/1.39  tff(c_187, plain, (![A_68]: (k1_funct_1('#skF_6', A_68)='#skF_4' | ~r2_hidden(A_68, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_183, c_154])).
% 2.49/1.39  tff(c_221, plain, (![B_83]: (k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_83))='#skF_4' | B_83='#skF_6' | k1_relat_1(B_83)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_83) | ~v1_relat_1(B_83) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_217, c_187])).
% 2.49/1.39  tff(c_231, plain, (![B_83]: (k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_83))='#skF_4' | B_83='#skF_6' | k1_relat_1(B_83)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_221])).
% 2.49/1.39  tff(c_44, plain, (k2_relat_1('#skF_5')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.49/1.39  tff(c_168, plain, (![A_61]: (r2_hidden(k1_funct_1('#skF_5', A_61), k1_tarski('#skF_4')) | ~r2_hidden(A_61, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_165])).
% 2.49/1.39  tff(c_176, plain, (![A_62]: (r2_hidden(k1_funct_1('#skF_5', A_62), k1_tarski('#skF_4')) | ~r2_hidden(A_62, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_46, c_168])).
% 2.49/1.39  tff(c_180, plain, (![A_62]: (k1_funct_1('#skF_5', A_62)='#skF_4' | ~r2_hidden(A_62, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_176, c_154])).
% 2.49/1.39  tff(c_225, plain, (![B_83]: (k1_funct_1('#skF_5', '#skF_3'('#skF_6', B_83))='#skF_4' | B_83='#skF_6' | k1_relat_1(B_83)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_83) | ~v1_relat_1(B_83) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_217, c_180])).
% 2.49/1.39  tff(c_234, plain, (![B_83]: (k1_funct_1('#skF_5', '#skF_3'('#skF_6', B_83))='#skF_4' | B_83='#skF_6' | k1_relat_1(B_83)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_225])).
% 2.49/1.39  tff(c_289, plain, (![B_87, A_88]: (k1_funct_1(B_87, '#skF_3'(A_88, B_87))!=k1_funct_1(A_88, '#skF_3'(A_88, B_87)) | B_87=A_88 | k1_relat_1(B_87)!=k1_relat_1(A_88) | ~v1_funct_1(B_87) | ~v1_relat_1(B_87) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.49/1.39  tff(c_293, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4' | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_234, c_289])).
% 2.49/1.39  tff(c_298, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_46, c_50, c_48, c_54, c_52, c_46, c_293])).
% 2.49/1.39  tff(c_299, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_40, c_298])).
% 2.49/1.39  tff(c_304, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_231, c_299])).
% 2.49/1.39  tff(c_307, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_46, c_304])).
% 2.49/1.39  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_307])).
% 2.49/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.39  
% 2.49/1.39  Inference rules
% 2.49/1.39  ----------------------
% 2.49/1.39  #Ref     : 1
% 2.49/1.39  #Sup     : 52
% 2.49/1.39  #Fact    : 0
% 2.49/1.39  #Define  : 0
% 2.49/1.39  #Split   : 0
% 2.49/1.39  #Chain   : 0
% 2.49/1.39  #Close   : 0
% 2.49/1.39  
% 2.49/1.39  Ordering : KBO
% 2.49/1.39  
% 2.49/1.39  Simplification rules
% 2.49/1.39  ----------------------
% 2.49/1.39  #Subsume      : 0
% 2.49/1.39  #Demod        : 38
% 2.49/1.39  #Tautology    : 31
% 2.49/1.39  #SimpNegUnit  : 2
% 2.49/1.39  #BackRed      : 0
% 2.49/1.39  
% 2.49/1.39  #Partial instantiations: 0
% 2.49/1.39  #Strategies tried      : 1
% 2.49/1.39  
% 2.49/1.39  Timing (in seconds)
% 2.49/1.39  ----------------------
% 2.49/1.39  Preprocessing        : 0.33
% 2.49/1.39  Parsing              : 0.17
% 2.49/1.39  CNF conversion       : 0.02
% 2.49/1.39  Main loop            : 0.24
% 2.49/1.39  Inferencing          : 0.09
% 2.49/1.39  Reduction            : 0.07
% 2.49/1.39  Demodulation         : 0.05
% 2.49/1.39  BG Simplification    : 0.02
% 2.49/1.39  Subsumption          : 0.05
% 2.49/1.39  Abstraction          : 0.02
% 2.49/1.39  MUC search           : 0.00
% 2.49/1.39  Cooper               : 0.00
% 2.49/1.39  Total                : 0.61
% 2.49/1.39  Index Insertion      : 0.00
% 2.49/1.39  Index Deletion       : 0.00
% 2.49/1.39  Index Matching       : 0.00
% 2.49/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
