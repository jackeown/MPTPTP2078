%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:38 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 197 expanded)
%              Number of leaves         :   24 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          :  119 ( 654 expanded)
%              Number of equality atoms :   35 ( 228 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = A )
             => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_30,plain,(
    k6_relat_1(k1_relat_1('#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_36,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    ! [B_25] :
      ( r2_hidden('#skF_5'(k1_relat_1(B_25),B_25),k1_relat_1(B_25))
      | k6_relat_1(k1_relat_1(B_25)) = B_25
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    k2_relat_1('#skF_6') = k1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_55,plain,(
    ! [A_42,C_43] :
      ( r2_hidden(k4_tarski('#skF_4'(A_42,k2_relat_1(A_42),C_43),C_43),A_42)
      | ~ r2_hidden(C_43,k2_relat_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [C_43] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_43),C_43),'#skF_6')
      | ~ r2_hidden(C_43,k2_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_55])).

tff(c_73,plain,(
    ! [C_47] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_47),C_47),'#skF_6')
      | ~ r2_hidden(C_47,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_64])).

tff(c_26,plain,(
    ! [C_31,A_29,B_30] :
      ( k1_funct_1(C_31,A_29) = B_30
      | ~ r2_hidden(k4_tarski(A_29,B_30),C_31)
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_79,plain,(
    ! [C_47] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_47)) = C_47
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_47,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_73,c_26])).

tff(c_88,plain,(
    ! [C_47] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_47)) = C_47
      | ~ r2_hidden(C_47,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_79])).

tff(c_32,plain,(
    k5_relat_1('#skF_6','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28,plain,(
    ! [A_29,C_31,B_30] :
      ( r2_hidden(A_29,k1_relat_1(C_31))
      | ~ r2_hidden(k4_tarski(A_29,B_30),C_31)
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_76,plain,(
    ! [C_47] :
      ( r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_47),k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_47,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_73,c_28])).

tff(c_85,plain,(
    ! [C_47] :
      ( r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_47),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_47,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_76])).

tff(c_321,plain,(
    ! [B_83,C_84,A_85] :
      ( k1_funct_1(k5_relat_1(B_83,C_84),A_85) = k1_funct_1(C_84,k1_funct_1(B_83,A_85))
      | ~ r2_hidden(A_85,k1_relat_1(B_83))
      | ~ v1_funct_1(C_84)
      | ~ v1_relat_1(C_84)
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_351,plain,(
    ! [C_84,C_47] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_84),'#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_47)) = k1_funct_1(C_84,k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_47)))
      | ~ v1_funct_1(C_84)
      | ~ v1_relat_1(C_84)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_47,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_85,c_321])).

tff(c_586,plain,(
    ! [C_97,C_98] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_97),'#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_98)) = k1_funct_1(C_97,k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_98)))
      | ~ v1_funct_1(C_97)
      | ~ v1_relat_1(C_97)
      | ~ r2_hidden(C_98,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_351])).

tff(c_601,plain,(
    ! [C_98] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_98))) = k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_98))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_98,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_586])).

tff(c_606,plain,(
    ! [C_99] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_99))) = k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_99))
      | ~ r2_hidden(C_99,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_601])).

tff(c_628,plain,(
    ! [C_100] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_100)) = k1_funct_1('#skF_7',C_100)
      | ~ r2_hidden(C_100,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_100,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_606])).

tff(c_682,plain,(
    ! [C_103] :
      ( k1_funct_1('#skF_7',C_103) = C_103
      | ~ r2_hidden(C_103,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_103,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_103,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_88])).

tff(c_713,plain,
    ( k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7'))
    | k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_18,c_682])).

tff(c_741,plain,
    ( k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7'))
    | k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_713])).

tff(c_742,plain,
    ( k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_741])).

tff(c_747,plain,(
    ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_742])).

tff(c_750,plain,
    ( k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_18,c_747])).

tff(c_753,plain,(
    k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_750])).

tff(c_755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_753])).

tff(c_756,plain,(
    k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_742])).

tff(c_16,plain,(
    ! [B_25] :
      ( k1_funct_1(B_25,'#skF_5'(k1_relat_1(B_25),B_25)) != '#skF_5'(k1_relat_1(B_25),B_25)
      | k6_relat_1(k1_relat_1(B_25)) = B_25
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_771,plain,
    ( k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_16])).

tff(c_782,plain,(
    k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_771])).

tff(c_784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:30:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  
% 2.81/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.41  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5
% 2.81/1.41  
% 2.81/1.41  %Foreground sorts:
% 2.81/1.41  
% 2.81/1.41  
% 2.81/1.41  %Background operators:
% 2.81/1.41  
% 2.81/1.41  
% 2.81/1.41  %Foreground operators:
% 2.81/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.81/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.81/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.81/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.81/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.81/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.81/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.81/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.41  
% 2.81/1.42  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 2.81/1.42  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.81/1.42  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.81/1.42  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.81/1.42  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 2.81/1.42  tff(c_30, plain, (k6_relat_1(k1_relat_1('#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.42  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.42  tff(c_36, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.42  tff(c_18, plain, (![B_25]: (r2_hidden('#skF_5'(k1_relat_1(B_25), B_25), k1_relat_1(B_25)) | k6_relat_1(k1_relat_1(B_25))=B_25 | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.81/1.42  tff(c_42, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.42  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.42  tff(c_34, plain, (k2_relat_1('#skF_6')=k1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.42  tff(c_55, plain, (![A_42, C_43]: (r2_hidden(k4_tarski('#skF_4'(A_42, k2_relat_1(A_42), C_43), C_43), A_42) | ~r2_hidden(C_43, k2_relat_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.42  tff(c_64, plain, (![C_43]: (r2_hidden(k4_tarski('#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_43), C_43), '#skF_6') | ~r2_hidden(C_43, k2_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_55])).
% 2.81/1.42  tff(c_73, plain, (![C_47]: (r2_hidden(k4_tarski('#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_47), C_47), '#skF_6') | ~r2_hidden(C_47, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_64])).
% 2.81/1.42  tff(c_26, plain, (![C_31, A_29, B_30]: (k1_funct_1(C_31, A_29)=B_30 | ~r2_hidden(k4_tarski(A_29, B_30), C_31) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.81/1.42  tff(c_79, plain, (![C_47]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_47))=C_47 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(C_47, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_73, c_26])).
% 2.81/1.42  tff(c_88, plain, (![C_47]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_47))=C_47 | ~r2_hidden(C_47, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_79])).
% 2.81/1.42  tff(c_32, plain, (k5_relat_1('#skF_6', '#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.42  tff(c_28, plain, (![A_29, C_31, B_30]: (r2_hidden(A_29, k1_relat_1(C_31)) | ~r2_hidden(k4_tarski(A_29, B_30), C_31) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.81/1.42  tff(c_76, plain, (![C_47]: (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_47), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(C_47, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_73, c_28])).
% 2.81/1.42  tff(c_85, plain, (![C_47]: (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_47), k1_relat_1('#skF_6')) | ~r2_hidden(C_47, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_76])).
% 2.81/1.42  tff(c_321, plain, (![B_83, C_84, A_85]: (k1_funct_1(k5_relat_1(B_83, C_84), A_85)=k1_funct_1(C_84, k1_funct_1(B_83, A_85)) | ~r2_hidden(A_85, k1_relat_1(B_83)) | ~v1_funct_1(C_84) | ~v1_relat_1(C_84) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.42  tff(c_351, plain, (![C_84, C_47]: (k1_funct_1(k5_relat_1('#skF_6', C_84), '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_47))=k1_funct_1(C_84, k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_47))) | ~v1_funct_1(C_84) | ~v1_relat_1(C_84) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(C_47, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_85, c_321])).
% 2.81/1.42  tff(c_586, plain, (![C_97, C_98]: (k1_funct_1(k5_relat_1('#skF_6', C_97), '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_98))=k1_funct_1(C_97, k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_98))) | ~v1_funct_1(C_97) | ~v1_relat_1(C_97) | ~r2_hidden(C_98, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_351])).
% 2.81/1.42  tff(c_601, plain, (![C_98]: (k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_98)))=k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_98)) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_98, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_586])).
% 2.81/1.42  tff(c_606, plain, (![C_99]: (k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_99)))=k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_99)) | ~r2_hidden(C_99, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_601])).
% 2.81/1.42  tff(c_628, plain, (![C_100]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_100))=k1_funct_1('#skF_7', C_100) | ~r2_hidden(C_100, k1_relat_1('#skF_7')) | ~r2_hidden(C_100, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_88, c_606])).
% 2.81/1.42  tff(c_682, plain, (![C_103]: (k1_funct_1('#skF_7', C_103)=C_103 | ~r2_hidden(C_103, k1_relat_1('#skF_7')) | ~r2_hidden(C_103, k1_relat_1('#skF_7')) | ~r2_hidden(C_103, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_628, c_88])).
% 2.81/1.42  tff(c_713, plain, (k1_funct_1('#skF_7', '#skF_5'(k1_relat_1('#skF_7'), '#skF_7'))='#skF_5'(k1_relat_1('#skF_7'), '#skF_7') | ~r2_hidden('#skF_5'(k1_relat_1('#skF_7'), '#skF_7'), k1_relat_1('#skF_7')) | k6_relat_1(k1_relat_1('#skF_7'))='#skF_7' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_18, c_682])).
% 2.81/1.42  tff(c_741, plain, (k1_funct_1('#skF_7', '#skF_5'(k1_relat_1('#skF_7'), '#skF_7'))='#skF_5'(k1_relat_1('#skF_7'), '#skF_7') | ~r2_hidden('#skF_5'(k1_relat_1('#skF_7'), '#skF_7'), k1_relat_1('#skF_7')) | k6_relat_1(k1_relat_1('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_713])).
% 2.81/1.42  tff(c_742, plain, (k1_funct_1('#skF_7', '#skF_5'(k1_relat_1('#skF_7'), '#skF_7'))='#skF_5'(k1_relat_1('#skF_7'), '#skF_7') | ~r2_hidden('#skF_5'(k1_relat_1('#skF_7'), '#skF_7'), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_30, c_741])).
% 2.81/1.42  tff(c_747, plain, (~r2_hidden('#skF_5'(k1_relat_1('#skF_7'), '#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_742])).
% 2.81/1.42  tff(c_750, plain, (k6_relat_1(k1_relat_1('#skF_7'))='#skF_7' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_18, c_747])).
% 2.81/1.42  tff(c_753, plain, (k6_relat_1(k1_relat_1('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_750])).
% 2.81/1.42  tff(c_755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_753])).
% 2.81/1.42  tff(c_756, plain, (k1_funct_1('#skF_7', '#skF_5'(k1_relat_1('#skF_7'), '#skF_7'))='#skF_5'(k1_relat_1('#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_742])).
% 2.81/1.42  tff(c_16, plain, (![B_25]: (k1_funct_1(B_25, '#skF_5'(k1_relat_1(B_25), B_25))!='#skF_5'(k1_relat_1(B_25), B_25) | k6_relat_1(k1_relat_1(B_25))=B_25 | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.81/1.42  tff(c_771, plain, (k6_relat_1(k1_relat_1('#skF_7'))='#skF_7' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_756, c_16])).
% 2.81/1.42  tff(c_782, plain, (k6_relat_1(k1_relat_1('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_771])).
% 2.81/1.42  tff(c_784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_782])).
% 2.81/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.42  
% 2.81/1.42  Inference rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Ref     : 0
% 2.81/1.42  #Sup     : 150
% 2.81/1.42  #Fact    : 0
% 2.81/1.42  #Define  : 0
% 2.81/1.42  #Split   : 1
% 2.81/1.42  #Chain   : 0
% 2.81/1.42  #Close   : 0
% 2.81/1.42  
% 2.81/1.42  Ordering : KBO
% 2.81/1.42  
% 2.81/1.42  Simplification rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Subsume      : 11
% 2.81/1.42  #Demod        : 130
% 2.81/1.42  #Tautology    : 62
% 2.81/1.42  #SimpNegUnit  : 3
% 2.81/1.42  #BackRed      : 0
% 2.81/1.42  
% 2.81/1.42  #Partial instantiations: 0
% 2.81/1.42  #Strategies tried      : 1
% 2.81/1.42  
% 2.81/1.42  Timing (in seconds)
% 2.81/1.42  ----------------------
% 2.81/1.42  Preprocessing        : 0.30
% 2.81/1.42  Parsing              : 0.15
% 2.81/1.42  CNF conversion       : 0.02
% 2.81/1.42  Main loop            : 0.36
% 2.81/1.42  Inferencing          : 0.15
% 2.81/1.42  Reduction            : 0.10
% 2.81/1.42  Demodulation         : 0.07
% 2.81/1.42  BG Simplification    : 0.02
% 2.81/1.42  Subsumption          : 0.06
% 2.81/1.42  Abstraction          : 0.02
% 2.81/1.42  MUC search           : 0.00
% 2.81/1.42  Cooper               : 0.00
% 2.81/1.42  Total                : 0.68
% 2.81/1.42  Index Insertion      : 0.00
% 2.81/1.42  Index Deletion       : 0.00
% 2.81/1.42  Index Matching       : 0.00
% 2.81/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
