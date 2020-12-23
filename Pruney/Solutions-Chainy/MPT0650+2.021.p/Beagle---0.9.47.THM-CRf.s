%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:47 EST 2020

% Result     : Theorem 4.48s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 128 expanded)
%              Number of leaves         :   27 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 395 expanded)
%              Number of equality atoms :   26 ( 102 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_18,plain,(
    ! [A_23] :
      ( v1_funct_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_23] :
      ( v1_relat_1(k2_funct_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_72,plain,(
    ! [A_49,C_50] :
      ( r2_hidden(k4_tarski('#skF_4'(A_49,k2_relat_1(A_49),C_50),C_50),A_49)
      | ~ r2_hidden(C_50,k2_relat_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [C_33,A_31,B_32] :
      ( k1_funct_1(C_33,A_31) = B_32
      | ~ r2_hidden(k4_tarski(A_31,B_32),C_33)
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_85,plain,(
    ! [A_49,C_50] :
      ( k1_funct_1(A_49,'#skF_4'(A_49,k2_relat_1(A_49),C_50)) = C_50
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49)
      | ~ r2_hidden(C_50,k2_relat_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_72,c_34])).

tff(c_16,plain,(
    ! [A_20,C_22,B_21] :
      ( r2_hidden(A_20,k1_relat_1(C_22))
      | ~ r2_hidden(k4_tarski(A_20,B_21),C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_49,C_50] :
      ( r2_hidden('#skF_4'(A_49,k2_relat_1(A_49),C_50),k1_relat_1(A_49))
      | ~ v1_relat_1(A_49)
      | ~ r2_hidden(C_50,k2_relat_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_72,c_16])).

tff(c_177,plain,(
    ! [B_70,A_71] :
      ( k1_funct_1(k2_funct_1(B_70),k1_funct_1(B_70,A_71)) = A_71
      | ~ r2_hidden(A_71,k1_relat_1(B_70))
      | ~ v2_funct_1(B_70)
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_769,plain,(
    ! [A_123,C_124] :
      ( k1_funct_1(k2_funct_1(A_123),C_124) = '#skF_4'(A_123,k2_relat_1(A_123),C_124)
      | ~ r2_hidden('#skF_4'(A_123,k2_relat_1(A_123),C_124),k1_relat_1(A_123))
      | ~ v2_funct_1(A_123)
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123)
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123)
      | ~ r2_hidden(C_124,k2_relat_1(A_123)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_177])).

tff(c_780,plain,(
    ! [A_125,C_126] :
      ( k1_funct_1(k2_funct_1(A_125),C_126) = '#skF_4'(A_125,k2_relat_1(A_125),C_126)
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125)
      | ~ r2_hidden(C_126,k2_relat_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_86,c_769])).

tff(c_829,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_780])).

tff(c_849,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_829])).

tff(c_38,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5'
    | k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_60,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_850,plain,(
    k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_60])).

tff(c_910,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_850])).

tff(c_914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_46,c_44,c_910])).

tff(c_916,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_26,plain,(
    ! [A_28] :
      ( k1_relat_1(k2_funct_1(A_28)) = k2_relat_1(A_28)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1555,plain,(
    ! [B_205,C_206,A_207] :
      ( k1_funct_1(k5_relat_1(B_205,C_206),A_207) = k1_funct_1(C_206,k1_funct_1(B_205,A_207))
      | ~ r2_hidden(A_207,k1_relat_1(B_205))
      | ~ v1_funct_1(C_206)
      | ~ v1_relat_1(C_206)
      | ~ v1_funct_1(B_205)
      | ~ v1_relat_1(B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1950,plain,(
    ! [A_237,C_238,A_239] :
      ( k1_funct_1(k5_relat_1(k2_funct_1(A_237),C_238),A_239) = k1_funct_1(C_238,k1_funct_1(k2_funct_1(A_237),A_239))
      | ~ r2_hidden(A_239,k2_relat_1(A_237))
      | ~ v1_funct_1(C_238)
      | ~ v1_relat_1(C_238)
      | ~ v1_funct_1(k2_funct_1(A_237))
      | ~ v1_relat_1(k2_funct_1(A_237))
      | ~ v2_funct_1(A_237)
      | ~ v1_funct_1(A_237)
      | ~ v1_relat_1(A_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1555])).

tff(c_915,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1987,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5'
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1950,c_915])).

tff(c_2005,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_46,c_44,c_40,c_916,c_1987])).

tff(c_2007,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2005])).

tff(c_2010,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_2007])).

tff(c_2014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2010])).

tff(c_2015,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2005])).

tff(c_2019,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_2015])).

tff(c_2023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2019])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:50:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.48/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.78  
% 4.48/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.78  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 4.55/1.78  
% 4.55/1.78  %Foreground sorts:
% 4.55/1.78  
% 4.55/1.78  
% 4.55/1.78  %Background operators:
% 4.55/1.78  
% 4.55/1.78  
% 4.55/1.78  %Foreground operators:
% 4.55/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.55/1.78  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.55/1.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.55/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/1.78  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.55/1.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.55/1.78  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.55/1.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.55/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.55/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.55/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.55/1.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.55/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.55/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.55/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.55/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.55/1.78  
% 4.55/1.79  tff(f_107, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 4.55/1.79  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.55/1.79  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 4.55/1.79  tff(f_94, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 4.55/1.79  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 4.55/1.79  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 4.55/1.79  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.55/1.79  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 4.55/1.79  tff(c_46, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.55/1.79  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.55/1.79  tff(c_18, plain, (![A_23]: (v1_funct_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.55/1.79  tff(c_20, plain, (![A_23]: (v1_relat_1(k2_funct_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.55/1.79  tff(c_42, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.55/1.79  tff(c_40, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.55/1.79  tff(c_72, plain, (![A_49, C_50]: (r2_hidden(k4_tarski('#skF_4'(A_49, k2_relat_1(A_49), C_50), C_50), A_49) | ~r2_hidden(C_50, k2_relat_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.55/1.79  tff(c_34, plain, (![C_33, A_31, B_32]: (k1_funct_1(C_33, A_31)=B_32 | ~r2_hidden(k4_tarski(A_31, B_32), C_33) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.55/1.79  tff(c_85, plain, (![A_49, C_50]: (k1_funct_1(A_49, '#skF_4'(A_49, k2_relat_1(A_49), C_50))=C_50 | ~v1_funct_1(A_49) | ~v1_relat_1(A_49) | ~r2_hidden(C_50, k2_relat_1(A_49)))), inference(resolution, [status(thm)], [c_72, c_34])).
% 4.55/1.79  tff(c_16, plain, (![A_20, C_22, B_21]: (r2_hidden(A_20, k1_relat_1(C_22)) | ~r2_hidden(k4_tarski(A_20, B_21), C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.55/1.79  tff(c_86, plain, (![A_49, C_50]: (r2_hidden('#skF_4'(A_49, k2_relat_1(A_49), C_50), k1_relat_1(A_49)) | ~v1_relat_1(A_49) | ~r2_hidden(C_50, k2_relat_1(A_49)))), inference(resolution, [status(thm)], [c_72, c_16])).
% 4.55/1.79  tff(c_177, plain, (![B_70, A_71]: (k1_funct_1(k2_funct_1(B_70), k1_funct_1(B_70, A_71))=A_71 | ~r2_hidden(A_71, k1_relat_1(B_70)) | ~v2_funct_1(B_70) | ~v1_funct_1(B_70) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.55/1.79  tff(c_769, plain, (![A_123, C_124]: (k1_funct_1(k2_funct_1(A_123), C_124)='#skF_4'(A_123, k2_relat_1(A_123), C_124) | ~r2_hidden('#skF_4'(A_123, k2_relat_1(A_123), C_124), k1_relat_1(A_123)) | ~v2_funct_1(A_123) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123) | ~r2_hidden(C_124, k2_relat_1(A_123)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_177])).
% 4.55/1.79  tff(c_780, plain, (![A_125, C_126]: (k1_funct_1(k2_funct_1(A_125), C_126)='#skF_4'(A_125, k2_relat_1(A_125), C_126) | ~v2_funct_1(A_125) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125) | ~r2_hidden(C_126, k2_relat_1(A_125)))), inference(resolution, [status(thm)], [c_86, c_769])).
% 4.55/1.79  tff(c_829, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_780])).
% 4.55/1.79  tff(c_849, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_829])).
% 4.55/1.79  tff(c_38, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5' | k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.55/1.79  tff(c_60, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_38])).
% 4.55/1.79  tff(c_850, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_849, c_60])).
% 4.55/1.79  tff(c_910, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_850])).
% 4.55/1.79  tff(c_914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_46, c_44, c_910])).
% 4.55/1.79  tff(c_916, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_38])).
% 4.55/1.79  tff(c_26, plain, (![A_28]: (k1_relat_1(k2_funct_1(A_28))=k2_relat_1(A_28) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.55/1.79  tff(c_1555, plain, (![B_205, C_206, A_207]: (k1_funct_1(k5_relat_1(B_205, C_206), A_207)=k1_funct_1(C_206, k1_funct_1(B_205, A_207)) | ~r2_hidden(A_207, k1_relat_1(B_205)) | ~v1_funct_1(C_206) | ~v1_relat_1(C_206) | ~v1_funct_1(B_205) | ~v1_relat_1(B_205))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.55/1.79  tff(c_1950, plain, (![A_237, C_238, A_239]: (k1_funct_1(k5_relat_1(k2_funct_1(A_237), C_238), A_239)=k1_funct_1(C_238, k1_funct_1(k2_funct_1(A_237), A_239)) | ~r2_hidden(A_239, k2_relat_1(A_237)) | ~v1_funct_1(C_238) | ~v1_relat_1(C_238) | ~v1_funct_1(k2_funct_1(A_237)) | ~v1_relat_1(k2_funct_1(A_237)) | ~v2_funct_1(A_237) | ~v1_funct_1(A_237) | ~v1_relat_1(A_237))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1555])).
% 4.55/1.79  tff(c_915, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_38])).
% 4.55/1.79  tff(c_1987, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5' | ~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1950, c_915])).
% 4.55/1.79  tff(c_2005, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_46, c_44, c_40, c_916, c_1987])).
% 4.55/1.79  tff(c_2007, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2005])).
% 4.55/1.79  tff(c_2010, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_2007])).
% 4.55/1.79  tff(c_2014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2010])).
% 4.55/1.79  tff(c_2015, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_2005])).
% 4.55/1.79  tff(c_2019, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_18, c_2015])).
% 4.55/1.79  tff(c_2023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2019])).
% 4.55/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.79  
% 4.55/1.79  Inference rules
% 4.55/1.79  ----------------------
% 4.55/1.79  #Ref     : 0
% 4.55/1.79  #Sup     : 475
% 4.55/1.79  #Fact    : 0
% 4.55/1.79  #Define  : 0
% 4.55/1.79  #Split   : 5
% 4.55/1.79  #Chain   : 0
% 4.55/1.79  #Close   : 0
% 4.55/1.79  
% 4.55/1.79  Ordering : KBO
% 4.55/1.79  
% 4.55/1.79  Simplification rules
% 4.55/1.79  ----------------------
% 4.55/1.79  #Subsume      : 48
% 4.55/1.79  #Demod        : 76
% 4.55/1.79  #Tautology    : 136
% 4.55/1.79  #SimpNegUnit  : 0
% 4.55/1.79  #BackRed      : 1
% 4.55/1.79  
% 4.55/1.79  #Partial instantiations: 0
% 4.55/1.79  #Strategies tried      : 1
% 4.55/1.79  
% 4.55/1.79  Timing (in seconds)
% 4.55/1.79  ----------------------
% 4.55/1.80  Preprocessing        : 0.31
% 4.55/1.80  Parsing              : 0.17
% 4.55/1.80  CNF conversion       : 0.02
% 4.55/1.80  Main loop            : 0.73
% 4.55/1.80  Inferencing          : 0.30
% 4.55/1.80  Reduction            : 0.18
% 4.55/1.80  Demodulation         : 0.12
% 4.55/1.80  BG Simplification    : 0.05
% 4.55/1.80  Subsumption          : 0.15
% 4.55/1.80  Abstraction          : 0.05
% 4.55/1.80  MUC search           : 0.00
% 4.55/1.80  Cooper               : 0.00
% 4.55/1.80  Total                : 1.07
% 4.55/1.80  Index Insertion      : 0.00
% 4.55/1.80  Index Deletion       : 0.00
% 4.55/1.80  Index Matching       : 0.00
% 4.55/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
