%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:37 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 199 expanded)
%              Number of leaves         :   24 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :  113 ( 658 expanded)
%              Number of equality atoms :   34 ( 234 expanded)
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
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

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

tff(c_32,plain,(
    k5_relat_1('#skF_6','#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_321,plain,(
    ! [C_83,B_84,A_85] :
      ( k1_funct_1(k5_relat_1(C_83,B_84),A_85) = k1_funct_1(B_84,k1_funct_1(C_83,A_85))
      | ~ r2_hidden(A_85,k1_relat_1(k5_relat_1(C_83,B_84)))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_368,plain,(
    ! [A_85] :
      ( k1_funct_1(k5_relat_1('#skF_6','#skF_7'),A_85) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_85))
      | ~ r2_hidden(A_85,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_321])).

tff(c_382,plain,(
    ! [A_86] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_86)) = k1_funct_1('#skF_6',A_86)
      | ~ r2_hidden(A_86,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_42,c_40,c_32,c_368])).

tff(c_1031,plain,(
    ! [C_102] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_102))) = k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_102))
      | ~ r2_hidden(C_102,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_85,c_382])).

tff(c_1053,plain,(
    ! [C_103] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k1_relat_1('#skF_7'),C_103)) = k1_funct_1('#skF_7',C_103)
      | ~ r2_hidden(C_103,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_103,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_1031])).

tff(c_1084,plain,(
    ! [C_104] :
      ( k1_funct_1('#skF_7',C_104) = C_104
      | ~ r2_hidden(C_104,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_104,k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_104,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_88])).

tff(c_1112,plain,
    ( k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7'))
    | k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_18,c_1084])).

tff(c_1141,plain,
    ( k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7'))
    | k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1112])).

tff(c_1142,plain,
    ( k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1141])).

tff(c_1147,plain,(
    ~ r2_hidden('#skF_5'(k1_relat_1('#skF_7'),'#skF_7'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1142])).

tff(c_1211,plain,
    ( k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_18,c_1147])).

tff(c_1214,plain,(
    k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1211])).

tff(c_1216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1214])).

tff(c_1217,plain,(
    k1_funct_1('#skF_7','#skF_5'(k1_relat_1('#skF_7'),'#skF_7')) = '#skF_5'(k1_relat_1('#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1142])).

tff(c_16,plain,(
    ! [B_25] :
      ( k1_funct_1(B_25,'#skF_5'(k1_relat_1(B_25),B_25)) != '#skF_5'(k1_relat_1(B_25),B_25)
      | k6_relat_1(k1_relat_1(B_25)) = B_25
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1227,plain,
    ( k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1217,c_16])).

tff(c_1238,plain,(
    k6_relat_1(k1_relat_1('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1227])).

tff(c_1240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n024.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:12:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.53  
% 3.53/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.53  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5
% 3.53/1.53  
% 3.53/1.53  %Foreground sorts:
% 3.53/1.53  
% 3.53/1.53  
% 3.53/1.53  %Background operators:
% 3.53/1.53  
% 3.53/1.53  
% 3.53/1.53  %Foreground operators:
% 3.53/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.53/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.53/1.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.53/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.53/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.53/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.53/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.53/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.53/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.53/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.53/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.53/1.53  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.53/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.53  
% 3.53/1.54  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 3.53/1.54  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 3.53/1.54  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.53/1.54  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.53/1.54  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 3.53/1.54  tff(c_30, plain, (k6_relat_1(k1_relat_1('#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.53/1.54  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.53/1.54  tff(c_36, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.53/1.54  tff(c_18, plain, (![B_25]: (r2_hidden('#skF_5'(k1_relat_1(B_25), B_25), k1_relat_1(B_25)) | k6_relat_1(k1_relat_1(B_25))=B_25 | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.53/1.54  tff(c_42, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.53/1.54  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.53/1.54  tff(c_34, plain, (k2_relat_1('#skF_6')=k1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.53/1.54  tff(c_55, plain, (![A_42, C_43]: (r2_hidden(k4_tarski('#skF_4'(A_42, k2_relat_1(A_42), C_43), C_43), A_42) | ~r2_hidden(C_43, k2_relat_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.53/1.54  tff(c_64, plain, (![C_43]: (r2_hidden(k4_tarski('#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_43), C_43), '#skF_6') | ~r2_hidden(C_43, k2_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_55])).
% 3.53/1.54  tff(c_73, plain, (![C_47]: (r2_hidden(k4_tarski('#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_47), C_47), '#skF_6') | ~r2_hidden(C_47, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_64])).
% 3.53/1.54  tff(c_26, plain, (![C_31, A_29, B_30]: (k1_funct_1(C_31, A_29)=B_30 | ~r2_hidden(k4_tarski(A_29, B_30), C_31) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.53/1.54  tff(c_79, plain, (![C_47]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_47))=C_47 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(C_47, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_73, c_26])).
% 3.53/1.54  tff(c_88, plain, (![C_47]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_47))=C_47 | ~r2_hidden(C_47, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_79])).
% 3.53/1.54  tff(c_28, plain, (![A_29, C_31, B_30]: (r2_hidden(A_29, k1_relat_1(C_31)) | ~r2_hidden(k4_tarski(A_29, B_30), C_31) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.53/1.54  tff(c_76, plain, (![C_47]: (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_47), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(C_47, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_73, c_28])).
% 3.53/1.54  tff(c_85, plain, (![C_47]: (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_47), k1_relat_1('#skF_6')) | ~r2_hidden(C_47, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_76])).
% 3.53/1.54  tff(c_32, plain, (k5_relat_1('#skF_6', '#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.53/1.54  tff(c_321, plain, (![C_83, B_84, A_85]: (k1_funct_1(k5_relat_1(C_83, B_84), A_85)=k1_funct_1(B_84, k1_funct_1(C_83, A_85)) | ~r2_hidden(A_85, k1_relat_1(k5_relat_1(C_83, B_84))) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.53/1.54  tff(c_368, plain, (![A_85]: (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), A_85)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_85)) | ~r2_hidden(A_85, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_321])).
% 3.53/1.54  tff(c_382, plain, (![A_86]: (k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_86))=k1_funct_1('#skF_6', A_86) | ~r2_hidden(A_86, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_42, c_40, c_32, c_368])).
% 3.53/1.54  tff(c_1031, plain, (![C_102]: (k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_102)))=k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_102)) | ~r2_hidden(C_102, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_85, c_382])).
% 3.53/1.54  tff(c_1053, plain, (![C_103]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k1_relat_1('#skF_7'), C_103))=k1_funct_1('#skF_7', C_103) | ~r2_hidden(C_103, k1_relat_1('#skF_7')) | ~r2_hidden(C_103, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_88, c_1031])).
% 3.53/1.54  tff(c_1084, plain, (![C_104]: (k1_funct_1('#skF_7', C_104)=C_104 | ~r2_hidden(C_104, k1_relat_1('#skF_7')) | ~r2_hidden(C_104, k1_relat_1('#skF_7')) | ~r2_hidden(C_104, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1053, c_88])).
% 3.53/1.54  tff(c_1112, plain, (k1_funct_1('#skF_7', '#skF_5'(k1_relat_1('#skF_7'), '#skF_7'))='#skF_5'(k1_relat_1('#skF_7'), '#skF_7') | ~r2_hidden('#skF_5'(k1_relat_1('#skF_7'), '#skF_7'), k1_relat_1('#skF_7')) | k6_relat_1(k1_relat_1('#skF_7'))='#skF_7' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_18, c_1084])).
% 3.53/1.54  tff(c_1141, plain, (k1_funct_1('#skF_7', '#skF_5'(k1_relat_1('#skF_7'), '#skF_7'))='#skF_5'(k1_relat_1('#skF_7'), '#skF_7') | ~r2_hidden('#skF_5'(k1_relat_1('#skF_7'), '#skF_7'), k1_relat_1('#skF_7')) | k6_relat_1(k1_relat_1('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1112])).
% 3.53/1.54  tff(c_1142, plain, (k1_funct_1('#skF_7', '#skF_5'(k1_relat_1('#skF_7'), '#skF_7'))='#skF_5'(k1_relat_1('#skF_7'), '#skF_7') | ~r2_hidden('#skF_5'(k1_relat_1('#skF_7'), '#skF_7'), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_30, c_1141])).
% 3.53/1.54  tff(c_1147, plain, (~r2_hidden('#skF_5'(k1_relat_1('#skF_7'), '#skF_7'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1142])).
% 3.53/1.54  tff(c_1211, plain, (k6_relat_1(k1_relat_1('#skF_7'))='#skF_7' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_18, c_1147])).
% 3.53/1.54  tff(c_1214, plain, (k6_relat_1(k1_relat_1('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1211])).
% 3.53/1.54  tff(c_1216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1214])).
% 3.53/1.54  tff(c_1217, plain, (k1_funct_1('#skF_7', '#skF_5'(k1_relat_1('#skF_7'), '#skF_7'))='#skF_5'(k1_relat_1('#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_1142])).
% 3.53/1.54  tff(c_16, plain, (![B_25]: (k1_funct_1(B_25, '#skF_5'(k1_relat_1(B_25), B_25))!='#skF_5'(k1_relat_1(B_25), B_25) | k6_relat_1(k1_relat_1(B_25))=B_25 | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.53/1.54  tff(c_1227, plain, (k6_relat_1(k1_relat_1('#skF_7'))='#skF_7' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1217, c_16])).
% 3.53/1.54  tff(c_1238, plain, (k6_relat_1(k1_relat_1('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1227])).
% 3.53/1.54  tff(c_1240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1238])).
% 3.53/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.54  
% 3.53/1.54  Inference rules
% 3.53/1.54  ----------------------
% 3.53/1.54  #Ref     : 0
% 3.53/1.54  #Sup     : 240
% 3.53/1.54  #Fact    : 0
% 3.53/1.54  #Define  : 0
% 3.53/1.54  #Split   : 4
% 3.53/1.54  #Chain   : 0
% 3.53/1.54  #Close   : 0
% 3.53/1.54  
% 3.53/1.54  Ordering : KBO
% 3.53/1.54  
% 3.53/1.54  Simplification rules
% 3.53/1.54  ----------------------
% 3.53/1.54  #Subsume      : 17
% 3.53/1.54  #Demod        : 226
% 3.53/1.54  #Tautology    : 86
% 3.53/1.54  #SimpNegUnit  : 7
% 3.53/1.54  #BackRed      : 0
% 3.53/1.54  
% 3.53/1.54  #Partial instantiations: 0
% 3.53/1.54  #Strategies tried      : 1
% 3.53/1.54  
% 3.53/1.54  Timing (in seconds)
% 3.53/1.54  ----------------------
% 3.53/1.55  Preprocessing        : 0.34
% 3.53/1.55  Parsing              : 0.16
% 3.53/1.55  CNF conversion       : 0.03
% 3.53/1.55  Main loop            : 0.44
% 3.53/1.55  Inferencing          : 0.17
% 3.53/1.55  Reduction            : 0.13
% 3.53/1.55  Demodulation         : 0.09
% 3.53/1.55  BG Simplification    : 0.03
% 3.53/1.55  Subsumption          : 0.07
% 3.53/1.55  Abstraction          : 0.03
% 3.53/1.55  MUC search           : 0.00
% 3.53/1.55  Cooper               : 0.00
% 3.53/1.55  Total                : 0.80
% 3.53/1.55  Index Insertion      : 0.00
% 3.53/1.55  Index Deletion       : 0.00
% 3.53/1.55  Index Matching       : 0.00
% 3.53/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
