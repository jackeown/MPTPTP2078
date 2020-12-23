%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:41 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 109 expanded)
%              Number of leaves         :   24 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 459 expanded)
%              Number of equality atoms :   36 ( 171 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( ( k1_relat_1(B) = A
                & k1_relat_1(C) = A
                & r1_tarski(k2_relat_1(C),A)
                & v2_funct_1(B)
                & k5_relat_1(C,B) = B )
             => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_28,plain,(
    k6_relat_1('#skF_4') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_482,plain,(
    ! [B_63] :
      ( k1_funct_1(B_63,'#skF_3'(k1_relat_1(B_63),B_63)) != '#skF_3'(k1_relat_1(B_63),B_63)
      | k6_relat_1(k1_relat_1(B_63)) = B_63
      | ~ v1_funct_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_485,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) != '#skF_3'(k1_relat_1('#skF_6'),'#skF_6')
    | k6_relat_1(k1_relat_1('#skF_6')) = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_482])).

tff(c_490,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) != '#skF_3'('#skF_4','#skF_6')
    | k6_relat_1('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_36,c_485])).

tff(c_491,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) != '#skF_3'('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_490])).

tff(c_94,plain,(
    ! [B_29] :
      ( r2_hidden('#skF_3'(k1_relat_1(B_29),B_29),k1_relat_1(B_29))
      | k6_relat_1(k1_relat_1(B_29)) = B_29
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_97,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_6'),k1_relat_1('#skF_6'))
    | k6_relat_1(k1_relat_1('#skF_6')) = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_94])).

tff(c_108,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_6'),'#skF_4')
    | k6_relat_1('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_36,c_97])).

tff(c_109,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_108])).

tff(c_38,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    k5_relat_1('#skF_6','#skF_5') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_516,plain,(
    ! [C_67,A_68,B_69] :
      ( r2_hidden(k1_funct_1(C_67,A_68),k1_relat_1(B_69))
      | ~ r2_hidden(A_68,k1_relat_1(k5_relat_1(C_67,B_69)))
      | ~ v1_funct_1(C_67)
      | ~ v1_relat_1(C_67)
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_529,plain,(
    ! [C_67,A_68] :
      ( r2_hidden(k1_funct_1(C_67,A_68),'#skF_4')
      | ~ r2_hidden(A_68,k1_relat_1(k5_relat_1(C_67,'#skF_5')))
      | ~ v1_funct_1(C_67)
      | ~ v1_relat_1(C_67)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_516])).

tff(c_556,plain,(
    ! [C_72,A_73] :
      ( r2_hidden(k1_funct_1(C_72,A_73),'#skF_4')
      | ~ r2_hidden(A_73,k1_relat_1(k5_relat_1(C_72,'#skF_5')))
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_529])).

tff(c_575,plain,(
    ! [A_73] :
      ( r2_hidden(k1_funct_1('#skF_6',A_73),'#skF_4')
      | ~ r2_hidden(A_73,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_556])).

tff(c_581,plain,(
    ! [A_73] :
      ( r2_hidden(k1_funct_1('#skF_6',A_73),'#skF_4')
      | ~ r2_hidden(A_73,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_575])).

tff(c_32,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_659,plain,(
    ! [C_86,B_87,A_88] :
      ( k1_funct_1(k5_relat_1(C_86,B_87),A_88) = k1_funct_1(B_87,k1_funct_1(C_86,A_88))
      | ~ r2_hidden(A_88,k1_relat_1(k5_relat_1(C_86,B_87)))
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86)
      | ~ v1_funct_1(B_87)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_684,plain,(
    ! [A_88] :
      ( k1_funct_1(k5_relat_1('#skF_6','#skF_5'),A_88) = k1_funct_1('#skF_5',k1_funct_1('#skF_6',A_88))
      | ~ r2_hidden(A_88,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_659])).

tff(c_697,plain,(
    ! [A_89] :
      ( k1_funct_1('#skF_5',k1_funct_1('#skF_6',A_89)) = k1_funct_1('#skF_5',A_89)
      | ~ r2_hidden(A_89,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_30,c_684])).

tff(c_2,plain,(
    ! [C_7,B_6,A_1] :
      ( C_7 = B_6
      | k1_funct_1(A_1,C_7) != k1_funct_1(A_1,B_6)
      | ~ r2_hidden(C_7,k1_relat_1(A_1))
      | ~ r2_hidden(B_6,k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_705,plain,(
    ! [A_89,B_6] :
      ( k1_funct_1('#skF_6',A_89) = B_6
      | k1_funct_1('#skF_5',B_6) != k1_funct_1('#skF_5',A_89)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_89),k1_relat_1('#skF_5'))
      | ~ r2_hidden(B_6,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(A_89,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_2])).

tff(c_722,plain,(
    ! [A_89,B_6] :
      ( k1_funct_1('#skF_6',A_89) = B_6
      | k1_funct_1('#skF_5',B_6) != k1_funct_1('#skF_5',A_89)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_89),'#skF_4')
      | ~ r2_hidden(B_6,'#skF_4')
      | ~ r2_hidden(A_89,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_32,c_38,c_38,c_705])).

tff(c_748,plain,(
    ! [A_92] :
      ( k1_funct_1('#skF_6',A_92) = A_92
      | ~ r2_hidden(k1_funct_1('#skF_6',A_92),'#skF_4')
      | ~ r2_hidden(A_92,'#skF_4')
      | ~ r2_hidden(A_92,'#skF_4') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_722])).

tff(c_766,plain,(
    ! [A_93] :
      ( k1_funct_1('#skF_6',A_93) = A_93
      | ~ r2_hidden(A_93,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_581,c_748])).

tff(c_778,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) = '#skF_3'('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_109,c_766])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_778])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n025.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 17:50:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.43  
% 2.88/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.44  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 2.88/1.44  
% 2.88/1.44  %Foreground sorts:
% 2.88/1.44  
% 2.88/1.44  
% 2.88/1.44  %Background operators:
% 2.88/1.44  
% 2.88/1.44  
% 2.88/1.44  %Foreground operators:
% 2.88/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.88/1.44  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.88/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.88/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.88/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.88/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.88/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.88/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.88/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.88/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.88/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.88/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.44  
% 2.88/1.45  tff(f_103, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_1)).
% 2.88/1.45  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.88/1.45  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 2.88/1.45  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 2.88/1.45  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 2.88/1.45  tff(c_28, plain, (k6_relat_1('#skF_4')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.45  tff(c_42, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.45  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.45  tff(c_36, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.45  tff(c_482, plain, (![B_63]: (k1_funct_1(B_63, '#skF_3'(k1_relat_1(B_63), B_63))!='#skF_3'(k1_relat_1(B_63), B_63) | k6_relat_1(k1_relat_1(B_63))=B_63 | ~v1_funct_1(B_63) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.88/1.45  tff(c_485, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'(k1_relat_1('#skF_6'), '#skF_6') | k6_relat_1(k1_relat_1('#skF_6'))='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_36, c_482])).
% 2.88/1.45  tff(c_490, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'('#skF_4', '#skF_6') | k6_relat_1('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_36, c_485])).
% 2.88/1.45  tff(c_491, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_28, c_490])).
% 2.88/1.45  tff(c_94, plain, (![B_29]: (r2_hidden('#skF_3'(k1_relat_1(B_29), B_29), k1_relat_1(B_29)) | k6_relat_1(k1_relat_1(B_29))=B_29 | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.88/1.45  tff(c_97, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), k1_relat_1('#skF_6')) | k6_relat_1(k1_relat_1('#skF_6'))='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_36, c_94])).
% 2.88/1.45  tff(c_108, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), '#skF_4') | k6_relat_1('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_36, c_97])).
% 2.88/1.45  tff(c_109, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_28, c_108])).
% 2.88/1.45  tff(c_38, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.45  tff(c_30, plain, (k5_relat_1('#skF_6', '#skF_5')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.45  tff(c_46, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.45  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.45  tff(c_516, plain, (![C_67, A_68, B_69]: (r2_hidden(k1_funct_1(C_67, A_68), k1_relat_1(B_69)) | ~r2_hidden(A_68, k1_relat_1(k5_relat_1(C_67, B_69))) | ~v1_funct_1(C_67) | ~v1_relat_1(C_67) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.88/1.45  tff(c_529, plain, (![C_67, A_68]: (r2_hidden(k1_funct_1(C_67, A_68), '#skF_4') | ~r2_hidden(A_68, k1_relat_1(k5_relat_1(C_67, '#skF_5'))) | ~v1_funct_1(C_67) | ~v1_relat_1(C_67) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_516])).
% 2.88/1.45  tff(c_556, plain, (![C_72, A_73]: (r2_hidden(k1_funct_1(C_72, A_73), '#skF_4') | ~r2_hidden(A_73, k1_relat_1(k5_relat_1(C_72, '#skF_5'))) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_529])).
% 2.88/1.45  tff(c_575, plain, (![A_73]: (r2_hidden(k1_funct_1('#skF_6', A_73), '#skF_4') | ~r2_hidden(A_73, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_556])).
% 2.88/1.45  tff(c_581, plain, (![A_73]: (r2_hidden(k1_funct_1('#skF_6', A_73), '#skF_4') | ~r2_hidden(A_73, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_575])).
% 2.88/1.45  tff(c_32, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.88/1.45  tff(c_659, plain, (![C_86, B_87, A_88]: (k1_funct_1(k5_relat_1(C_86, B_87), A_88)=k1_funct_1(B_87, k1_funct_1(C_86, A_88)) | ~r2_hidden(A_88, k1_relat_1(k5_relat_1(C_86, B_87))) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86) | ~v1_funct_1(B_87) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.88/1.45  tff(c_684, plain, (![A_88]: (k1_funct_1(k5_relat_1('#skF_6', '#skF_5'), A_88)=k1_funct_1('#skF_5', k1_funct_1('#skF_6', A_88)) | ~r2_hidden(A_88, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_659])).
% 2.88/1.45  tff(c_697, plain, (![A_89]: (k1_funct_1('#skF_5', k1_funct_1('#skF_6', A_89))=k1_funct_1('#skF_5', A_89) | ~r2_hidden(A_89, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_30, c_684])).
% 2.88/1.45  tff(c_2, plain, (![C_7, B_6, A_1]: (C_7=B_6 | k1_funct_1(A_1, C_7)!=k1_funct_1(A_1, B_6) | ~r2_hidden(C_7, k1_relat_1(A_1)) | ~r2_hidden(B_6, k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.45  tff(c_705, plain, (![A_89, B_6]: (k1_funct_1('#skF_6', A_89)=B_6 | k1_funct_1('#skF_5', B_6)!=k1_funct_1('#skF_5', A_89) | ~r2_hidden(k1_funct_1('#skF_6', A_89), k1_relat_1('#skF_5')) | ~r2_hidden(B_6, k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(A_89, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_697, c_2])).
% 2.88/1.45  tff(c_722, plain, (![A_89, B_6]: (k1_funct_1('#skF_6', A_89)=B_6 | k1_funct_1('#skF_5', B_6)!=k1_funct_1('#skF_5', A_89) | ~r2_hidden(k1_funct_1('#skF_6', A_89), '#skF_4') | ~r2_hidden(B_6, '#skF_4') | ~r2_hidden(A_89, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_32, c_38, c_38, c_705])).
% 2.88/1.45  tff(c_748, plain, (![A_92]: (k1_funct_1('#skF_6', A_92)=A_92 | ~r2_hidden(k1_funct_1('#skF_6', A_92), '#skF_4') | ~r2_hidden(A_92, '#skF_4') | ~r2_hidden(A_92, '#skF_4'))), inference(reflexivity, [status(thm), theory('equality')], [c_722])).
% 2.88/1.45  tff(c_766, plain, (![A_93]: (k1_funct_1('#skF_6', A_93)=A_93 | ~r2_hidden(A_93, '#skF_4'))), inference(resolution, [status(thm)], [c_581, c_748])).
% 2.88/1.45  tff(c_778, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))='#skF_3'('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_109, c_766])).
% 2.88/1.45  tff(c_785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_491, c_778])).
% 2.88/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.45  
% 2.88/1.45  Inference rules
% 2.88/1.45  ----------------------
% 2.88/1.45  #Ref     : 3
% 2.88/1.45  #Sup     : 151
% 2.88/1.45  #Fact    : 0
% 2.88/1.45  #Define  : 0
% 2.88/1.45  #Split   : 2
% 2.88/1.45  #Chain   : 0
% 2.88/1.45  #Close   : 0
% 2.88/1.45  
% 2.88/1.45  Ordering : KBO
% 2.88/1.45  
% 2.88/1.45  Simplification rules
% 2.88/1.45  ----------------------
% 2.88/1.45  #Subsume      : 3
% 2.88/1.45  #Demod        : 240
% 2.88/1.45  #Tautology    : 59
% 2.88/1.45  #SimpNegUnit  : 8
% 2.88/1.45  #BackRed      : 1
% 2.88/1.45  
% 2.88/1.45  #Partial instantiations: 0
% 2.88/1.45  #Strategies tried      : 1
% 2.88/1.45  
% 2.88/1.45  Timing (in seconds)
% 2.88/1.45  ----------------------
% 2.88/1.45  Preprocessing        : 0.32
% 2.88/1.45  Parsing              : 0.17
% 2.88/1.45  CNF conversion       : 0.02
% 2.88/1.45  Main loop            : 0.37
% 2.88/1.45  Inferencing          : 0.13
% 2.88/1.45  Reduction            : 0.11
% 2.88/1.45  Demodulation         : 0.08
% 2.88/1.45  BG Simplification    : 0.02
% 2.88/1.45  Subsumption          : 0.06
% 2.88/1.45  Abstraction          : 0.02
% 2.88/1.45  MUC search           : 0.00
% 2.88/1.45  Cooper               : 0.00
% 2.88/1.45  Total                : 0.71
% 2.88/1.45  Index Insertion      : 0.00
% 2.88/1.45  Index Deletion       : 0.00
% 2.88/1.45  Index Matching       : 0.00
% 2.88/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
