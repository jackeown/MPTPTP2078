%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:01 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 183 expanded)
%              Number of leaves         :   25 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  127 ( 581 expanded)
%              Number of equality atoms :   40 ( 210 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_28,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_34,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_131,plain,(
    ! [A_27] :
      ( k4_relat_1(A_27) = k2_funct_1(A_27)
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_134,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_131])).

tff(c_137,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_134])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k4_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_2])).

tff(c_150,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_144])).

tff(c_16,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k6_relat_1(k2_relat_1(A_15))) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_159,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_16])).

tff(c_162,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_159])).

tff(c_244,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_248,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_244])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_248])).

tff(c_253,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_254,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_32,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_24,plain,(
    ! [A_18] :
      ( k5_relat_1(k2_funct_1(A_18),A_18) = k6_relat_1(k2_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_409,plain,(
    ! [A_41,B_42,C_43] :
      ( k5_relat_1(k5_relat_1(A_41,B_42),C_43) = k5_relat_1(A_41,k5_relat_1(B_42,C_43))
      | ~ v1_relat_1(C_43)
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2627,plain,(
    ! [A_90,C_91] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_90)),C_91) = k5_relat_1(k2_funct_1(A_90),k5_relat_1(A_90,C_91))
      | ~ v1_relat_1(C_91)
      | ~ v1_relat_1(A_90)
      | ~ v1_relat_1(k2_funct_1(A_90))
      | ~ v2_funct_1(A_90)
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_409])).

tff(c_2849,plain,(
    ! [C_91] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_91) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_91))
      | ~ v1_relat_1(C_91)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2627])).

tff(c_2893,plain,(
    ! [C_92] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_92) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_92))
      | ~ v1_relat_1(C_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_254,c_42,c_2849])).

tff(c_10,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k4_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_4])).

tff(c_148,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32,c_141])).

tff(c_181,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_29,B_30)),k1_relat_1(A_29))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_187,plain,(
    ! [B_30] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_30)),k1_relat_1('#skF_2'))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_181])).

tff(c_589,plain,(
    ! [B_47] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_47)),k1_relat_1('#skF_2'))
      | ~ v1_relat_1(B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_187])).

tff(c_596,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(k2_relat_1('#skF_1'))),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_589])).

tff(c_610,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_42,c_32,c_10,c_596])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = B_14
      | ~ r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_618,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_2') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_610,c_14])).

tff(c_621,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_618])).

tff(c_2945,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2893,c_621])).

tff(c_3039,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_253,c_2945])).

tff(c_3041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_3039])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:22:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.18  
% 5.73/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.18  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.73/2.18  
% 5.73/2.18  %Foreground sorts:
% 5.73/2.18  
% 5.73/2.18  
% 5.73/2.18  %Background operators:
% 5.73/2.18  
% 5.73/2.18  
% 5.73/2.18  %Foreground operators:
% 5.73/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.73/2.18  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.73/2.18  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.73/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.73/2.18  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.73/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.73/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.73/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.73/2.18  tff('#skF_1', type, '#skF_1': $i).
% 5.73/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.73/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.73/2.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.73/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.73/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.73/2.18  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.73/2.18  
% 5.73/2.19  tff(f_106, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 5.73/2.19  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.73/2.19  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 5.73/2.19  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 5.73/2.19  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 5.73/2.19  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.73/2.19  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 5.73/2.19  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.73/2.19  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 5.73/2.19  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 5.73/2.19  tff(c_28, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.73/2.19  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.73/2.19  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.73/2.19  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.73/2.19  tff(c_22, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.73/2.19  tff(c_30, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.73/2.19  tff(c_34, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.73/2.19  tff(c_131, plain, (![A_27]: (k4_relat_1(A_27)=k2_funct_1(A_27) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.73/2.19  tff(c_134, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_34, c_131])).
% 5.73/2.19  tff(c_137, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_134])).
% 5.73/2.19  tff(c_2, plain, (![A_1]: (k2_relat_1(k4_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.73/2.19  tff(c_144, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_137, c_2])).
% 5.73/2.19  tff(c_150, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_144])).
% 5.73/2.19  tff(c_16, plain, (![A_15]: (k5_relat_1(A_15, k6_relat_1(k2_relat_1(A_15)))=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.73/2.19  tff(c_159, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_150, c_16])).
% 5.73/2.19  tff(c_162, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_159])).
% 5.73/2.19  tff(c_244, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_162])).
% 5.73/2.19  tff(c_248, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_244])).
% 5.73/2.19  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_248])).
% 5.73/2.19  tff(c_253, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_162])).
% 5.73/2.19  tff(c_254, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_162])).
% 5.73/2.19  tff(c_32, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.73/2.19  tff(c_24, plain, (![A_18]: (k5_relat_1(k2_funct_1(A_18), A_18)=k6_relat_1(k2_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.73/2.19  tff(c_409, plain, (![A_41, B_42, C_43]: (k5_relat_1(k5_relat_1(A_41, B_42), C_43)=k5_relat_1(A_41, k5_relat_1(B_42, C_43)) | ~v1_relat_1(C_43) | ~v1_relat_1(B_42) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.73/2.19  tff(c_2627, plain, (![A_90, C_91]: (k5_relat_1(k6_relat_1(k2_relat_1(A_90)), C_91)=k5_relat_1(k2_funct_1(A_90), k5_relat_1(A_90, C_91)) | ~v1_relat_1(C_91) | ~v1_relat_1(A_90) | ~v1_relat_1(k2_funct_1(A_90)) | ~v2_funct_1(A_90) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(superposition, [status(thm), theory('equality')], [c_24, c_409])).
% 5.73/2.19  tff(c_2849, plain, (![C_91]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_91)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_91)) | ~v1_relat_1(C_91) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2627])).
% 5.73/2.19  tff(c_2893, plain, (![C_92]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_92)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_92)) | ~v1_relat_1(C_92))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_254, c_42, c_2849])).
% 5.73/2.19  tff(c_10, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.73/2.19  tff(c_4, plain, (![A_1]: (k1_relat_1(k4_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.73/2.19  tff(c_141, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_137, c_4])).
% 5.73/2.19  tff(c_148, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_32, c_141])).
% 5.73/2.19  tff(c_181, plain, (![A_29, B_30]: (r1_tarski(k1_relat_1(k5_relat_1(A_29, B_30)), k1_relat_1(A_29)) | ~v1_relat_1(B_30) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.73/2.19  tff(c_187, plain, (![B_30]: (r1_tarski(k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_30)), k1_relat_1('#skF_2')) | ~v1_relat_1(B_30) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_148, c_181])).
% 5.73/2.19  tff(c_589, plain, (![B_47]: (r1_tarski(k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_47)), k1_relat_1('#skF_2')) | ~v1_relat_1(B_47))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_187])).
% 5.73/2.19  tff(c_596, plain, (r1_tarski(k1_relat_1(k6_relat_1(k2_relat_1('#skF_1'))), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_589])).
% 5.73/2.19  tff(c_610, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_42, c_32, c_10, c_596])).
% 5.73/2.19  tff(c_14, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=B_14 | ~r1_tarski(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.73/2.19  tff(c_618, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_2')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_610, c_14])).
% 5.73/2.19  tff(c_621, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_618])).
% 5.73/2.19  tff(c_2945, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2893, c_621])).
% 5.73/2.19  tff(c_3039, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_253, c_2945])).
% 5.73/2.19  tff(c_3041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_3039])).
% 5.73/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.19  
% 5.73/2.19  Inference rules
% 5.73/2.19  ----------------------
% 5.73/2.19  #Ref     : 0
% 5.73/2.19  #Sup     : 714
% 5.73/2.19  #Fact    : 0
% 5.73/2.19  #Define  : 0
% 5.73/2.19  #Split   : 14
% 5.73/2.19  #Chain   : 0
% 5.73/2.19  #Close   : 0
% 5.73/2.19  
% 5.73/2.19  Ordering : KBO
% 5.73/2.19  
% 5.73/2.19  Simplification rules
% 5.73/2.19  ----------------------
% 5.73/2.19  #Subsume      : 211
% 5.73/2.19  #Demod        : 954
% 5.73/2.19  #Tautology    : 160
% 5.73/2.19  #SimpNegUnit  : 2
% 5.73/2.19  #BackRed      : 0
% 5.73/2.19  
% 5.73/2.19  #Partial instantiations: 0
% 5.73/2.19  #Strategies tried      : 1
% 5.73/2.19  
% 5.73/2.19  Timing (in seconds)
% 5.73/2.19  ----------------------
% 5.73/2.20  Preprocessing        : 0.37
% 5.73/2.20  Parsing              : 0.21
% 5.73/2.20  CNF conversion       : 0.02
% 5.73/2.20  Main loop            : 0.97
% 5.73/2.20  Inferencing          : 0.34
% 5.73/2.20  Reduction            : 0.35
% 5.73/2.20  Demodulation         : 0.26
% 5.73/2.20  BG Simplification    : 0.05
% 5.73/2.20  Subsumption          : 0.19
% 5.73/2.20  Abstraction          : 0.06
% 5.73/2.20  MUC search           : 0.00
% 5.73/2.20  Cooper               : 0.00
% 5.73/2.20  Total                : 1.37
% 5.73/2.20  Index Insertion      : 0.00
% 5.73/2.20  Index Deletion       : 0.00
% 5.73/2.20  Index Matching       : 0.00
% 5.73/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
