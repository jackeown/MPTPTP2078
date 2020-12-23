%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:43 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 174 expanded)
%              Number of leaves         :   19 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  145 ( 632 expanded)
%              Number of equality atoms :   28 ( 126 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( ? [B] :
              ( v1_relat_1(B)
              & v1_funct_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
         => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( r1_tarski(k2_relat_1(B),k1_relat_1(A))
                    & r1_tarski(k2_relat_1(C),k1_relat_1(A))
                    & k1_relat_1(B) = k1_relat_1(C)
                    & k5_relat_1(B,A) = k5_relat_1(C,A) )
                 => B = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_26,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_45,plain,(
    ! [A_26] :
      ( '#skF_2'(A_26) != '#skF_1'(A_26)
      | v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48,plain,
    ( '#skF_2'('#skF_3') != '#skF_1'('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_45,c_26])).

tff(c_51,plain,(
    '#skF_2'('#skF_3') != '#skF_1'('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_48])).

tff(c_20,plain,(
    ! [A_10] :
      ( v1_relat_1('#skF_2'(A_10))
      | v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    k6_relat_1(k1_relat_1('#skF_3')) = k5_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_70,plain,(
    ! [A_31] :
      ( r1_tarski(k2_relat_1('#skF_2'(A_31)),k1_relat_1(A_31))
      | v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = B_9
      | ~ r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_146,plain,(
    ! [A_37] :
      ( k5_relat_1('#skF_2'(A_37),k6_relat_1(k1_relat_1(A_37))) = '#skF_2'(A_37)
      | ~ v1_relat_1('#skF_2'(A_37))
      | v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_70,c_4])).

tff(c_161,plain,
    ( k5_relat_1('#skF_2'('#skF_3'),k5_relat_1('#skF_3','#skF_4')) = '#skF_2'('#skF_3')
    | ~ v1_relat_1('#skF_2'('#skF_3'))
    | v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_146])).

tff(c_165,plain,
    ( k5_relat_1('#skF_2'('#skF_3'),k5_relat_1('#skF_3','#skF_4')) = '#skF_2'('#skF_3')
    | ~ v1_relat_1('#skF_2'('#skF_3'))
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_161])).

tff(c_166,plain,
    ( k5_relat_1('#skF_2'('#skF_3'),k5_relat_1('#skF_3','#skF_4')) = '#skF_2'('#skF_3')
    | ~ v1_relat_1('#skF_2'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_165])).

tff(c_167,plain,(
    ~ v1_relat_1('#skF_2'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_200,plain,
    ( v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_167])).

tff(c_203,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_200])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_203])).

tff(c_207,plain,(
    v1_relat_1('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    ! [A_10] :
      ( v1_relat_1('#skF_1'(A_10))
      | v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_62,plain,(
    ! [A_30] :
      ( r1_tarski(k2_relat_1('#skF_1'(A_30)),k1_relat_1(A_30))
      | v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_105,plain,(
    ! [A_36] :
      ( k5_relat_1('#skF_1'(A_36),k6_relat_1(k1_relat_1(A_36))) = '#skF_1'(A_36)
      | ~ v1_relat_1('#skF_1'(A_36))
      | v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(resolution,[status(thm)],[c_62,c_4])).

tff(c_120,plain,
    ( k5_relat_1('#skF_1'('#skF_3'),k5_relat_1('#skF_3','#skF_4')) = '#skF_1'('#skF_3')
    | ~ v1_relat_1('#skF_1'('#skF_3'))
    | v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_105])).

tff(c_124,plain,
    ( k5_relat_1('#skF_1'('#skF_3'),k5_relat_1('#skF_3','#skF_4')) = '#skF_1'('#skF_3')
    | ~ v1_relat_1('#skF_1'('#skF_3'))
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_120])).

tff(c_125,plain,
    ( k5_relat_1('#skF_1'('#skF_3'),k5_relat_1('#skF_3','#skF_4')) = '#skF_1'('#skF_3')
    | ~ v1_relat_1('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_124])).

tff(c_126,plain,(
    ~ v1_relat_1('#skF_1'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_129,plain,
    ( v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_126])).

tff(c_132,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_129])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_132])).

tff(c_136,plain,(
    v1_relat_1('#skF_1'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_135,plain,(
    k5_relat_1('#skF_1'('#skF_3'),k5_relat_1('#skF_3','#skF_4')) = '#skF_1'('#skF_3') ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_10,plain,(
    ! [A_10] :
      ( k5_relat_1('#skF_2'(A_10),A_10) = k5_relat_1('#skF_1'(A_10),A_10)
      | v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_87,plain,(
    ! [A_33,B_34,C_35] :
      ( k5_relat_1(k5_relat_1(A_33,B_34),C_35) = k5_relat_1(A_33,k5_relat_1(B_34,C_35))
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_228,plain,(
    ! [A_43,C_44] :
      ( k5_relat_1(k5_relat_1('#skF_1'(A_43),A_43),C_44) = k5_relat_1('#skF_2'(A_43),k5_relat_1(A_43,C_44))
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(A_43)
      | ~ v1_relat_1('#skF_2'(A_43))
      | v2_funct_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_87])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_569,plain,(
    ! [A_62,C_63] :
      ( k5_relat_1('#skF_2'(A_62),k5_relat_1(A_62,C_63)) = k5_relat_1('#skF_1'(A_62),k5_relat_1(A_62,C_63))
      | ~ v1_relat_1(C_63)
      | ~ v1_relat_1(A_62)
      | ~ v1_relat_1('#skF_1'(A_62))
      | ~ v1_relat_1(C_63)
      | ~ v1_relat_1(A_62)
      | ~ v1_relat_1('#skF_2'(A_62))
      | v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_2])).

tff(c_206,plain,(
    k5_relat_1('#skF_2'('#skF_3'),k5_relat_1('#skF_3','#skF_4')) = '#skF_2'('#skF_3') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_594,plain,
    ( k5_relat_1('#skF_1'('#skF_3'),k5_relat_1('#skF_3','#skF_4')) = '#skF_2'('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_1'('#skF_3'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2'('#skF_3'))
    | v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_206])).

tff(c_645,plain,
    ( '#skF_2'('#skF_3') = '#skF_1'('#skF_3')
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_207,c_36,c_32,c_136,c_36,c_32,c_135,c_594])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_51,c_645])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:06:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.49  
% 3.16/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.49  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 3.16/1.49  
% 3.16/1.49  %Foreground sorts:
% 3.16/1.49  
% 3.16/1.49  
% 3.16/1.49  %Background operators:
% 3.16/1.49  
% 3.16/1.49  
% 3.16/1.49  %Foreground operators:
% 3.16/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.16/1.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.16/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.16/1.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.16/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.49  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.16/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.49  
% 3.32/1.50  tff(f_81, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 3.32/1.50  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((r1_tarski(k2_relat_1(B), k1_relat_1(A)) & r1_tarski(k2_relat_1(C), k1_relat_1(A))) & (k1_relat_1(B) = k1_relat_1(C))) & (k5_relat_1(B, A) = k5_relat_1(C, A))) => (B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_funct_1)).
% 3.32/1.50  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.32/1.50  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 3.32/1.50  tff(c_26, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.32/1.50  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.32/1.50  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.32/1.50  tff(c_45, plain, (![A_26]: ('#skF_2'(A_26)!='#skF_1'(A_26) | v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.32/1.50  tff(c_48, plain, ('#skF_2'('#skF_3')!='#skF_1'('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_45, c_26])).
% 3.32/1.50  tff(c_51, plain, ('#skF_2'('#skF_3')!='#skF_1'('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_48])).
% 3.32/1.50  tff(c_20, plain, (![A_10]: (v1_relat_1('#skF_2'(A_10)) | v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.32/1.50  tff(c_28, plain, (k6_relat_1(k1_relat_1('#skF_3'))=k5_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.32/1.50  tff(c_70, plain, (![A_31]: (r1_tarski(k2_relat_1('#skF_2'(A_31)), k1_relat_1(A_31)) | v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.32/1.50  tff(c_4, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=B_9 | ~r1_tarski(k2_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.50  tff(c_146, plain, (![A_37]: (k5_relat_1('#skF_2'(A_37), k6_relat_1(k1_relat_1(A_37)))='#skF_2'(A_37) | ~v1_relat_1('#skF_2'(A_37)) | v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_70, c_4])).
% 3.32/1.50  tff(c_161, plain, (k5_relat_1('#skF_2'('#skF_3'), k5_relat_1('#skF_3', '#skF_4'))='#skF_2'('#skF_3') | ~v1_relat_1('#skF_2'('#skF_3')) | v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_146])).
% 3.32/1.50  tff(c_165, plain, (k5_relat_1('#skF_2'('#skF_3'), k5_relat_1('#skF_3', '#skF_4'))='#skF_2'('#skF_3') | ~v1_relat_1('#skF_2'('#skF_3')) | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_161])).
% 3.32/1.50  tff(c_166, plain, (k5_relat_1('#skF_2'('#skF_3'), k5_relat_1('#skF_3', '#skF_4'))='#skF_2'('#skF_3') | ~v1_relat_1('#skF_2'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_26, c_165])).
% 3.32/1.50  tff(c_167, plain, (~v1_relat_1('#skF_2'('#skF_3'))), inference(splitLeft, [status(thm)], [c_166])).
% 3.32/1.50  tff(c_200, plain, (v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_167])).
% 3.32/1.50  tff(c_203, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_200])).
% 3.32/1.50  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_203])).
% 3.32/1.50  tff(c_207, plain, (v1_relat_1('#skF_2'('#skF_3'))), inference(splitRight, [status(thm)], [c_166])).
% 3.32/1.50  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.32/1.50  tff(c_24, plain, (![A_10]: (v1_relat_1('#skF_1'(A_10)) | v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.32/1.50  tff(c_62, plain, (![A_30]: (r1_tarski(k2_relat_1('#skF_1'(A_30)), k1_relat_1(A_30)) | v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.32/1.50  tff(c_105, plain, (![A_36]: (k5_relat_1('#skF_1'(A_36), k6_relat_1(k1_relat_1(A_36)))='#skF_1'(A_36) | ~v1_relat_1('#skF_1'(A_36)) | v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(resolution, [status(thm)], [c_62, c_4])).
% 3.32/1.50  tff(c_120, plain, (k5_relat_1('#skF_1'('#skF_3'), k5_relat_1('#skF_3', '#skF_4'))='#skF_1'('#skF_3') | ~v1_relat_1('#skF_1'('#skF_3')) | v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_105])).
% 3.32/1.50  tff(c_124, plain, (k5_relat_1('#skF_1'('#skF_3'), k5_relat_1('#skF_3', '#skF_4'))='#skF_1'('#skF_3') | ~v1_relat_1('#skF_1'('#skF_3')) | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_120])).
% 3.32/1.50  tff(c_125, plain, (k5_relat_1('#skF_1'('#skF_3'), k5_relat_1('#skF_3', '#skF_4'))='#skF_1'('#skF_3') | ~v1_relat_1('#skF_1'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_26, c_124])).
% 3.32/1.50  tff(c_126, plain, (~v1_relat_1('#skF_1'('#skF_3'))), inference(splitLeft, [status(thm)], [c_125])).
% 3.32/1.50  tff(c_129, plain, (v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_126])).
% 3.32/1.50  tff(c_132, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_129])).
% 3.32/1.50  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_132])).
% 3.32/1.50  tff(c_136, plain, (v1_relat_1('#skF_1'('#skF_3'))), inference(splitRight, [status(thm)], [c_125])).
% 3.32/1.50  tff(c_135, plain, (k5_relat_1('#skF_1'('#skF_3'), k5_relat_1('#skF_3', '#skF_4'))='#skF_1'('#skF_3')), inference(splitRight, [status(thm)], [c_125])).
% 3.32/1.50  tff(c_10, plain, (![A_10]: (k5_relat_1('#skF_2'(A_10), A_10)=k5_relat_1('#skF_1'(A_10), A_10) | v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.32/1.50  tff(c_87, plain, (![A_33, B_34, C_35]: (k5_relat_1(k5_relat_1(A_33, B_34), C_35)=k5_relat_1(A_33, k5_relat_1(B_34, C_35)) | ~v1_relat_1(C_35) | ~v1_relat_1(B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.50  tff(c_228, plain, (![A_43, C_44]: (k5_relat_1(k5_relat_1('#skF_1'(A_43), A_43), C_44)=k5_relat_1('#skF_2'(A_43), k5_relat_1(A_43, C_44)) | ~v1_relat_1(C_44) | ~v1_relat_1(A_43) | ~v1_relat_1('#skF_2'(A_43)) | v2_funct_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_10, c_87])).
% 3.32/1.50  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.50  tff(c_569, plain, (![A_62, C_63]: (k5_relat_1('#skF_2'(A_62), k5_relat_1(A_62, C_63))=k5_relat_1('#skF_1'(A_62), k5_relat_1(A_62, C_63)) | ~v1_relat_1(C_63) | ~v1_relat_1(A_62) | ~v1_relat_1('#skF_1'(A_62)) | ~v1_relat_1(C_63) | ~v1_relat_1(A_62) | ~v1_relat_1('#skF_2'(A_62)) | v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(superposition, [status(thm), theory('equality')], [c_228, c_2])).
% 3.32/1.50  tff(c_206, plain, (k5_relat_1('#skF_2'('#skF_3'), k5_relat_1('#skF_3', '#skF_4'))='#skF_2'('#skF_3')), inference(splitRight, [status(thm)], [c_166])).
% 3.32/1.50  tff(c_594, plain, (k5_relat_1('#skF_1'('#skF_3'), k5_relat_1('#skF_3', '#skF_4'))='#skF_2'('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_1'('#skF_3')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2'('#skF_3')) | v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_569, c_206])).
% 3.32/1.50  tff(c_645, plain, ('#skF_2'('#skF_3')='#skF_1'('#skF_3') | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_207, c_36, c_32, c_136, c_36, c_32, c_135, c_594])).
% 3.32/1.50  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_51, c_645])).
% 3.32/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.50  
% 3.32/1.50  Inference rules
% 3.32/1.50  ----------------------
% 3.32/1.50  #Ref     : 2
% 3.32/1.50  #Sup     : 179
% 3.32/1.50  #Fact    : 0
% 3.32/1.50  #Define  : 0
% 3.32/1.50  #Split   : 4
% 3.32/1.50  #Chain   : 0
% 3.32/1.50  #Close   : 0
% 3.32/1.50  
% 3.32/1.50  Ordering : KBO
% 3.32/1.50  
% 3.32/1.50  Simplification rules
% 3.32/1.50  ----------------------
% 3.32/1.50  #Subsume      : 19
% 3.32/1.50  #Demod        : 63
% 3.32/1.50  #Tautology    : 37
% 3.32/1.50  #SimpNegUnit  : 8
% 3.32/1.50  #BackRed      : 0
% 3.32/1.50  
% 3.32/1.50  #Partial instantiations: 0
% 3.32/1.50  #Strategies tried      : 1
% 3.32/1.50  
% 3.32/1.50  Timing (in seconds)
% 3.32/1.50  ----------------------
% 3.32/1.51  Preprocessing        : 0.28
% 3.32/1.51  Parsing              : 0.14
% 3.32/1.51  CNF conversion       : 0.02
% 3.32/1.51  Main loop            : 0.45
% 3.32/1.51  Inferencing          : 0.17
% 3.32/1.51  Reduction            : 0.12
% 3.32/1.51  Demodulation         : 0.09
% 3.32/1.51  BG Simplification    : 0.03
% 3.32/1.51  Subsumption          : 0.10
% 3.32/1.51  Abstraction          : 0.03
% 3.32/1.51  MUC search           : 0.00
% 3.32/1.51  Cooper               : 0.00
% 3.32/1.51  Total                : 0.76
% 3.32/1.51  Index Insertion      : 0.00
% 3.32/1.51  Index Deletion       : 0.00
% 3.32/1.51  Index Matching       : 0.00
% 3.32/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
