%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:45 EST 2020

% Result     : Theorem 6.59s
% Output     : CNFRefutation 6.59s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 132 expanded)
%              Number of leaves         :   31 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 392 expanded)
%              Number of equality atoms :   27 ( 103 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

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

tff(f_41,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

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

tff(c_54,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_52,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    ! [A_39] :
      ( v1_funct_1(k2_funct_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_39] :
      ( v1_relat_1(k2_funct_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    v2_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_102,plain,(
    ! [A_67,C_68] :
      ( r2_hidden(k4_tarski('#skF_8'(A_67,k2_relat_1(A_67),C_68),C_68),A_67)
      | ~ r2_hidden(C_68,k2_relat_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_42,plain,(
    ! [C_49,A_47,B_48] :
      ( k1_funct_1(C_49,A_47) = B_48
      | ~ r2_hidden(k4_tarski(A_47,B_48),C_49)
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_115,plain,(
    ! [A_67,C_68] :
      ( k1_funct_1(A_67,'#skF_8'(A_67,k2_relat_1(A_67),C_68)) = C_68
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67)
      | ~ r2_hidden(C_68,k2_relat_1(A_67)) ) ),
    inference(resolution,[status(thm)],[c_102,c_42])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k1_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(C_16,D_19),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_117,plain,(
    ! [A_67,C_68] :
      ( r2_hidden('#skF_8'(A_67,k2_relat_1(A_67),C_68),k1_relat_1(A_67))
      | ~ r2_hidden(C_68,k2_relat_1(A_67)) ) ),
    inference(resolution,[status(thm)],[c_102,c_4])).

tff(c_191,plain,(
    ! [B_89,A_90] :
      ( k1_funct_1(k2_funct_1(B_89),k1_funct_1(B_89,A_90)) = A_90
      | ~ r2_hidden(A_90,k1_relat_1(B_89))
      | ~ v2_funct_1(B_89)
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2152,plain,(
    ! [A_229,C_230] :
      ( k1_funct_1(k2_funct_1(A_229),C_230) = '#skF_8'(A_229,k2_relat_1(A_229),C_230)
      | ~ r2_hidden('#skF_8'(A_229,k2_relat_1(A_229),C_230),k1_relat_1(A_229))
      | ~ v2_funct_1(A_229)
      | ~ v1_funct_1(A_229)
      | ~ v1_relat_1(A_229)
      | ~ v1_funct_1(A_229)
      | ~ v1_relat_1(A_229)
      | ~ r2_hidden(C_230,k2_relat_1(A_229)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_191])).

tff(c_2207,plain,(
    ! [A_234,C_235] :
      ( k1_funct_1(k2_funct_1(A_234),C_235) = '#skF_8'(A_234,k2_relat_1(A_234),C_235)
      | ~ v2_funct_1(A_234)
      | ~ v1_funct_1(A_234)
      | ~ v1_relat_1(A_234)
      | ~ r2_hidden(C_235,k2_relat_1(A_234)) ) ),
    inference(resolution,[status(thm)],[c_117,c_2152])).

tff(c_2314,plain,
    ( k1_funct_1(k2_funct_1('#skF_10'),'#skF_9') = '#skF_8'('#skF_10',k2_relat_1('#skF_10'),'#skF_9')
    | ~ v2_funct_1('#skF_10')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_48,c_2207])).

tff(c_2356,plain,(
    k1_funct_1(k2_funct_1('#skF_10'),'#skF_9') = '#skF_8'('#skF_10',k2_relat_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2314])).

tff(c_46,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),'#skF_10'),'#skF_9') != '#skF_9'
    | k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_68,plain,(
    k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2357,plain,(
    k1_funct_1('#skF_10','#skF_8'('#skF_10',k2_relat_1('#skF_10'),'#skF_9')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2356,c_68])).

tff(c_2389,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_2357])).

tff(c_2393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_54,c_52,c_2389])).

tff(c_2395,plain,(
    k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_34,plain,(
    ! [A_44] :
      ( k1_relat_1(k2_funct_1(A_44)) = k2_relat_1(A_44)
      | ~ v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3675,plain,(
    ! [B_377,C_378,A_379] :
      ( k1_funct_1(k5_relat_1(B_377,C_378),A_379) = k1_funct_1(C_378,k1_funct_1(B_377,A_379))
      | ~ r2_hidden(A_379,k1_relat_1(B_377))
      | ~ v1_funct_1(C_378)
      | ~ v1_relat_1(C_378)
      | ~ v1_funct_1(B_377)
      | ~ v1_relat_1(B_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4409,plain,(
    ! [A_430,C_431,A_432] :
      ( k1_funct_1(k5_relat_1(k2_funct_1(A_430),C_431),A_432) = k1_funct_1(C_431,k1_funct_1(k2_funct_1(A_430),A_432))
      | ~ r2_hidden(A_432,k2_relat_1(A_430))
      | ~ v1_funct_1(C_431)
      | ~ v1_relat_1(C_431)
      | ~ v1_funct_1(k2_funct_1(A_430))
      | ~ v1_relat_1(k2_funct_1(A_430))
      | ~ v2_funct_1(A_430)
      | ~ v1_funct_1(A_430)
      | ~ v1_relat_1(A_430) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3675])).

tff(c_2394,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'),'#skF_10'),'#skF_9') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4447,plain,
    ( k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),'#skF_9')) != '#skF_9'
    | ~ r2_hidden('#skF_9',k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_funct_1(k2_funct_1('#skF_10'))
    | ~ v1_relat_1(k2_funct_1('#skF_10'))
    | ~ v2_funct_1('#skF_10')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_4409,c_2394])).

tff(c_4469,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_10'))
    | ~ v1_relat_1(k2_funct_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_54,c_52,c_48,c_2395,c_4447])).

tff(c_4471,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_4469])).

tff(c_4474,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_28,c_4471])).

tff(c_4478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4474])).

tff(c_4479,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_4469])).

tff(c_4483,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_26,c_4479])).

tff(c_4487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.59/2.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.47  
% 6.59/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.47  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5
% 6.59/2.47  
% 6.59/2.47  %Foreground sorts:
% 6.59/2.47  
% 6.59/2.47  
% 6.59/2.47  %Background operators:
% 6.59/2.47  
% 6.59/2.47  
% 6.59/2.47  %Foreground operators:
% 6.59/2.47  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.59/2.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.59/2.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.59/2.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.59/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.59/2.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.59/2.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.59/2.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.59/2.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.59/2.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.59/2.47  tff('#skF_10', type, '#skF_10': $i).
% 6.59/2.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.59/2.47  tff('#skF_9', type, '#skF_9': $i).
% 6.59/2.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.59/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.59/2.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.59/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.59/2.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.59/2.47  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 6.59/2.47  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 6.59/2.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.59/2.47  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.59/2.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.59/2.47  
% 6.59/2.48  tff(f_107, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 6.59/2.48  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.59/2.48  tff(f_41, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 6.59/2.48  tff(f_94, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 6.59/2.48  tff(f_33, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 6.59/2.48  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 6.59/2.48  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.59/2.48  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 6.59/2.48  tff(c_54, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.59/2.48  tff(c_52, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.59/2.48  tff(c_26, plain, (![A_39]: (v1_funct_1(k2_funct_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.59/2.48  tff(c_28, plain, (![A_39]: (v1_relat_1(k2_funct_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.59/2.48  tff(c_50, plain, (v2_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.59/2.48  tff(c_48, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.59/2.48  tff(c_102, plain, (![A_67, C_68]: (r2_hidden(k4_tarski('#skF_8'(A_67, k2_relat_1(A_67), C_68), C_68), A_67) | ~r2_hidden(C_68, k2_relat_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.59/2.48  tff(c_42, plain, (![C_49, A_47, B_48]: (k1_funct_1(C_49, A_47)=B_48 | ~r2_hidden(k4_tarski(A_47, B_48), C_49) | ~v1_funct_1(C_49) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.59/2.48  tff(c_115, plain, (![A_67, C_68]: (k1_funct_1(A_67, '#skF_8'(A_67, k2_relat_1(A_67), C_68))=C_68 | ~v1_funct_1(A_67) | ~v1_relat_1(A_67) | ~r2_hidden(C_68, k2_relat_1(A_67)))), inference(resolution, [status(thm)], [c_102, c_42])).
% 6.59/2.48  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k1_relat_1(A_1)) | ~r2_hidden(k4_tarski(C_16, D_19), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.59/2.48  tff(c_117, plain, (![A_67, C_68]: (r2_hidden('#skF_8'(A_67, k2_relat_1(A_67), C_68), k1_relat_1(A_67)) | ~r2_hidden(C_68, k2_relat_1(A_67)))), inference(resolution, [status(thm)], [c_102, c_4])).
% 6.59/2.48  tff(c_191, plain, (![B_89, A_90]: (k1_funct_1(k2_funct_1(B_89), k1_funct_1(B_89, A_90))=A_90 | ~r2_hidden(A_90, k1_relat_1(B_89)) | ~v2_funct_1(B_89) | ~v1_funct_1(B_89) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.59/2.48  tff(c_2152, plain, (![A_229, C_230]: (k1_funct_1(k2_funct_1(A_229), C_230)='#skF_8'(A_229, k2_relat_1(A_229), C_230) | ~r2_hidden('#skF_8'(A_229, k2_relat_1(A_229), C_230), k1_relat_1(A_229)) | ~v2_funct_1(A_229) | ~v1_funct_1(A_229) | ~v1_relat_1(A_229) | ~v1_funct_1(A_229) | ~v1_relat_1(A_229) | ~r2_hidden(C_230, k2_relat_1(A_229)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_191])).
% 6.59/2.48  tff(c_2207, plain, (![A_234, C_235]: (k1_funct_1(k2_funct_1(A_234), C_235)='#skF_8'(A_234, k2_relat_1(A_234), C_235) | ~v2_funct_1(A_234) | ~v1_funct_1(A_234) | ~v1_relat_1(A_234) | ~r2_hidden(C_235, k2_relat_1(A_234)))), inference(resolution, [status(thm)], [c_117, c_2152])).
% 6.59/2.48  tff(c_2314, plain, (k1_funct_1(k2_funct_1('#skF_10'), '#skF_9')='#skF_8'('#skF_10', k2_relat_1('#skF_10'), '#skF_9') | ~v2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_48, c_2207])).
% 6.59/2.48  tff(c_2356, plain, (k1_funct_1(k2_funct_1('#skF_10'), '#skF_9')='#skF_8'('#skF_10', k2_relat_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2314])).
% 6.59/2.48  tff(c_46, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), '#skF_10'), '#skF_9')!='#skF_9' | k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.59/2.48  tff(c_68, plain, (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))!='#skF_9'), inference(splitLeft, [status(thm)], [c_46])).
% 6.59/2.48  tff(c_2357, plain, (k1_funct_1('#skF_10', '#skF_8'('#skF_10', k2_relat_1('#skF_10'), '#skF_9'))!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2356, c_68])).
% 6.59/2.48  tff(c_2389, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_2357])).
% 6.59/2.48  tff(c_2393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_54, c_52, c_2389])).
% 6.59/2.48  tff(c_2395, plain, (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))='#skF_9'), inference(splitRight, [status(thm)], [c_46])).
% 6.59/2.48  tff(c_34, plain, (![A_44]: (k1_relat_1(k2_funct_1(A_44))=k2_relat_1(A_44) | ~v2_funct_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.59/2.48  tff(c_3675, plain, (![B_377, C_378, A_379]: (k1_funct_1(k5_relat_1(B_377, C_378), A_379)=k1_funct_1(C_378, k1_funct_1(B_377, A_379)) | ~r2_hidden(A_379, k1_relat_1(B_377)) | ~v1_funct_1(C_378) | ~v1_relat_1(C_378) | ~v1_funct_1(B_377) | ~v1_relat_1(B_377))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.59/2.48  tff(c_4409, plain, (![A_430, C_431, A_432]: (k1_funct_1(k5_relat_1(k2_funct_1(A_430), C_431), A_432)=k1_funct_1(C_431, k1_funct_1(k2_funct_1(A_430), A_432)) | ~r2_hidden(A_432, k2_relat_1(A_430)) | ~v1_funct_1(C_431) | ~v1_relat_1(C_431) | ~v1_funct_1(k2_funct_1(A_430)) | ~v1_relat_1(k2_funct_1(A_430)) | ~v2_funct_1(A_430) | ~v1_funct_1(A_430) | ~v1_relat_1(A_430))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3675])).
% 6.59/2.48  tff(c_2394, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_10'), '#skF_10'), '#skF_9')!='#skF_9'), inference(splitRight, [status(thm)], [c_46])).
% 6.59/2.48  tff(c_4447, plain, (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), '#skF_9'))!='#skF_9' | ~r2_hidden('#skF_9', k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10')) | ~v2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_4409, c_2394])).
% 6.59/2.48  tff(c_4469, plain, (~v1_funct_1(k2_funct_1('#skF_10')) | ~v1_relat_1(k2_funct_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_54, c_52, c_48, c_2395, c_4447])).
% 6.59/2.48  tff(c_4471, plain, (~v1_relat_1(k2_funct_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_4469])).
% 6.59/2.48  tff(c_4474, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_28, c_4471])).
% 6.59/2.48  tff(c_4478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4474])).
% 6.59/2.48  tff(c_4479, plain, (~v1_funct_1(k2_funct_1('#skF_10'))), inference(splitRight, [status(thm)], [c_4469])).
% 6.59/2.48  tff(c_4483, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_26, c_4479])).
% 6.59/2.48  tff(c_4487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4483])).
% 6.59/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.48  
% 6.59/2.48  Inference rules
% 6.59/2.48  ----------------------
% 6.59/2.48  #Ref     : 0
% 6.59/2.48  #Sup     : 1061
% 6.59/2.48  #Fact    : 0
% 6.59/2.48  #Define  : 0
% 6.59/2.48  #Split   : 5
% 6.59/2.48  #Chain   : 0
% 6.59/2.48  #Close   : 0
% 6.59/2.48  
% 6.59/2.48  Ordering : KBO
% 6.59/2.48  
% 6.59/2.48  Simplification rules
% 6.59/2.48  ----------------------
% 6.59/2.48  #Subsume      : 122
% 6.59/2.48  #Demod        : 78
% 6.59/2.48  #Tautology    : 297
% 6.59/2.48  #SimpNegUnit  : 0
% 6.59/2.48  #BackRed      : 1
% 6.59/2.48  
% 6.59/2.48  #Partial instantiations: 0
% 6.59/2.48  #Strategies tried      : 1
% 6.59/2.48  
% 6.59/2.48  Timing (in seconds)
% 6.59/2.48  ----------------------
% 6.59/2.48  Preprocessing        : 0.36
% 6.59/2.48  Parsing              : 0.20
% 6.59/2.48  CNF conversion       : 0.03
% 6.59/2.48  Main loop            : 1.29
% 6.59/2.48  Inferencing          : 0.52
% 6.59/2.48  Reduction            : 0.31
% 6.59/2.48  Demodulation         : 0.20
% 6.59/2.48  BG Simplification    : 0.09
% 6.59/2.48  Subsumption          : 0.26
% 6.59/2.48  Abstraction          : 0.09
% 6.59/2.48  MUC search           : 0.00
% 6.59/2.48  Cooper               : 0.00
% 6.59/2.48  Total                : 1.69
% 6.59/2.48  Index Insertion      : 0.00
% 6.59/2.48  Index Deletion       : 0.00
% 6.59/2.48  Index Matching       : 0.00
% 6.59/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
