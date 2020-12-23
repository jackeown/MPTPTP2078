%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:07 EST 2020

% Result     : Theorem 24.23s
% Output     : CNFRefutation 24.23s
% Verified   : 
% Statistics : Number of formulae       :   42 (  55 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 ( 101 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_41,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(A,k3_zfmisc_1(B,C,D))
          & ! [E,F,G] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & r2_hidden(G,D)
                & A = k3_mcart_1(E,F,G) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

tff(c_28,plain,(
    ! [A_38,B_39,C_40] : k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40) = k3_zfmisc_1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [A_65,B_66,D_67] :
      ( r2_hidden('#skF_6'(A_65,B_66,k2_zfmisc_1(A_65,B_66),D_67),B_66)
      | ~ r2_hidden(D_67,k2_zfmisc_1(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [A_38,B_39,C_40,D_67] :
      ( r2_hidden('#skF_6'(k2_zfmisc_1(A_38,B_39),C_40,k3_zfmisc_1(A_38,B_39,C_40),D_67),C_40)
      | ~ r2_hidden(D_67,k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_98])).

tff(c_102,plain,(
    ! [A_38,B_39,C_40,D_67] :
      ( r2_hidden('#skF_6'(k2_zfmisc_1(A_38,B_39),C_40,k3_zfmisc_1(A_38,B_39,C_40),D_67),C_40)
      | ~ r2_hidden(D_67,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_101])).

tff(c_8,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_1)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),B_2)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_1,B_2,D_28] :
      ( k4_tarski('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),'#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28)) = D_28
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    ! [A_88,B_89,D_90] :
      ( k4_tarski('#skF_5'(A_88,B_89,k2_zfmisc_1(A_88,B_89),D_90),'#skF_6'(A_88,B_89,k2_zfmisc_1(A_88,B_89),D_90)) = D_90
      | ~ r2_hidden(D_90,k2_zfmisc_1(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_35,B_36,C_37] : k4_tarski(k4_tarski(A_35,B_36),C_37) = k3_mcart_1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_230,plain,(
    ! [A_132,B_133,D_134,C_135] :
      ( k3_mcart_1('#skF_5'(A_132,B_133,k2_zfmisc_1(A_132,B_133),D_134),'#skF_6'(A_132,B_133,k2_zfmisc_1(A_132,B_133),D_134),C_135) = k4_tarski(D_134,C_135)
      | ~ r2_hidden(D_134,k2_zfmisc_1(A_132,B_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_26])).

tff(c_30,plain,(
    ! [E_44,F_45,G_46] :
      ( k3_mcart_1(E_44,F_45,G_46) != '#skF_7'
      | ~ r2_hidden(G_46,'#skF_10')
      | ~ r2_hidden(F_45,'#skF_9')
      | ~ r2_hidden(E_44,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_286,plain,(
    ! [D_146,C_147,A_148,B_149] :
      ( k4_tarski(D_146,C_147) != '#skF_7'
      | ~ r2_hidden(C_147,'#skF_10')
      | ~ r2_hidden('#skF_6'(A_148,B_149,k2_zfmisc_1(A_148,B_149),D_146),'#skF_9')
      | ~ r2_hidden('#skF_5'(A_148,B_149,k2_zfmisc_1(A_148,B_149),D_146),'#skF_8')
      | ~ r2_hidden(D_146,k2_zfmisc_1(A_148,B_149)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_30])).

tff(c_35681,plain,(
    ! [D_2967,B_2971,A_2970,B_2969,A_2968] :
      ( D_2967 != '#skF_7'
      | ~ r2_hidden('#skF_6'(A_2970,B_2969,k2_zfmisc_1(A_2970,B_2969),D_2967),'#skF_10')
      | ~ r2_hidden('#skF_6'(A_2968,B_2971,k2_zfmisc_1(A_2968,B_2971),'#skF_5'(A_2970,B_2969,k2_zfmisc_1(A_2970,B_2969),D_2967)),'#skF_9')
      | ~ r2_hidden('#skF_5'(A_2968,B_2971,k2_zfmisc_1(A_2968,B_2971),'#skF_5'(A_2970,B_2969,k2_zfmisc_1(A_2970,B_2969),D_2967)),'#skF_8')
      | ~ r2_hidden('#skF_5'(A_2970,B_2969,k2_zfmisc_1(A_2970,B_2969),D_2967),k2_zfmisc_1(A_2968,B_2971))
      | ~ r2_hidden(D_2967,k2_zfmisc_1(A_2970,B_2969)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_286])).

tff(c_35853,plain,(
    ! [D_2979,A_2980,B_2981,A_2982] :
      ( D_2979 != '#skF_7'
      | ~ r2_hidden('#skF_6'(A_2980,B_2981,k2_zfmisc_1(A_2980,B_2981),D_2979),'#skF_10')
      | ~ r2_hidden('#skF_5'(A_2982,'#skF_9',k2_zfmisc_1(A_2982,'#skF_9'),'#skF_5'(A_2980,B_2981,k2_zfmisc_1(A_2980,B_2981),D_2979)),'#skF_8')
      | ~ r2_hidden(D_2979,k2_zfmisc_1(A_2980,B_2981))
      | ~ r2_hidden('#skF_5'(A_2980,B_2981,k2_zfmisc_1(A_2980,B_2981),D_2979),k2_zfmisc_1(A_2982,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_6,c_35681])).

tff(c_35869,plain,(
    ! [D_2983,A_2984,B_2985] :
      ( D_2983 != '#skF_7'
      | ~ r2_hidden('#skF_6'(A_2984,B_2985,k2_zfmisc_1(A_2984,B_2985),D_2983),'#skF_10')
      | ~ r2_hidden(D_2983,k2_zfmisc_1(A_2984,B_2985))
      | ~ r2_hidden('#skF_5'(A_2984,B_2985,k2_zfmisc_1(A_2984,B_2985),D_2983),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_8,c_35853])).

tff(c_35873,plain,(
    ! [D_28,B_2] :
      ( D_28 != '#skF_7'
      | ~ r2_hidden('#skF_6'(k2_zfmisc_1('#skF_8','#skF_9'),B_2,k2_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'),B_2),D_28),'#skF_10')
      | ~ r2_hidden(D_28,k2_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'),B_2)) ) ),
    inference(resolution,[status(thm)],[c_8,c_35869])).

tff(c_35885,plain,(
    ! [D_2986,B_2987] :
      ( D_2986 != '#skF_7'
      | ~ r2_hidden('#skF_6'(k2_zfmisc_1('#skF_8','#skF_9'),B_2987,k3_zfmisc_1('#skF_8','#skF_9',B_2987),D_2986),'#skF_10')
      | ~ r2_hidden(D_2986,k3_zfmisc_1('#skF_8','#skF_9',B_2987)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_35873])).

tff(c_35891,plain,(
    ~ r2_hidden('#skF_7',k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_102,c_35885])).

tff(c_32,plain,(
    r2_hidden('#skF_7',k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_35893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35891,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.23/13.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.23/13.08  
% 24.23/13.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.23/13.08  %$ r2_hidden > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 24.23/13.08  
% 24.23/13.08  %Foreground sorts:
% 24.23/13.08  
% 24.23/13.08  
% 24.23/13.08  %Background operators:
% 24.23/13.08  
% 24.23/13.08  
% 24.23/13.08  %Foreground operators:
% 24.23/13.08  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 24.23/13.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.23/13.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.23/13.08  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 24.23/13.08  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 24.23/13.08  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 24.23/13.08  tff('#skF_7', type, '#skF_7': $i).
% 24.23/13.08  tff('#skF_10', type, '#skF_10': $i).
% 24.23/13.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 24.23/13.08  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 24.23/13.08  tff('#skF_9', type, '#skF_9': $i).
% 24.23/13.08  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 24.23/13.08  tff('#skF_8', type, '#skF_8': $i).
% 24.23/13.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.23/13.08  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 24.23/13.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 24.23/13.08  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 24.23/13.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.23/13.08  
% 24.23/13.09  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 24.23/13.09  tff(f_37, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 24.23/13.09  tff(f_39, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 24.23/13.09  tff(f_55, negated_conjecture, ~(![A, B, C, D]: ~(r2_hidden(A, k3_zfmisc_1(B, C, D)) & (![E, F, G]: ~(((r2_hidden(E, B) & r2_hidden(F, C)) & r2_hidden(G, D)) & (A = k3_mcart_1(E, F, G)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_mcart_1)).
% 24.23/13.09  tff(c_28, plain, (![A_38, B_39, C_40]: (k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40)=k3_zfmisc_1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 24.23/13.09  tff(c_98, plain, (![A_65, B_66, D_67]: (r2_hidden('#skF_6'(A_65, B_66, k2_zfmisc_1(A_65, B_66), D_67), B_66) | ~r2_hidden(D_67, k2_zfmisc_1(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.23/13.09  tff(c_101, plain, (![A_38, B_39, C_40, D_67]: (r2_hidden('#skF_6'(k2_zfmisc_1(A_38, B_39), C_40, k3_zfmisc_1(A_38, B_39, C_40), D_67), C_40) | ~r2_hidden(D_67, k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_98])).
% 24.23/13.09  tff(c_102, plain, (![A_38, B_39, C_40, D_67]: (r2_hidden('#skF_6'(k2_zfmisc_1(A_38, B_39), C_40, k3_zfmisc_1(A_38, B_39, C_40), D_67), C_40) | ~r2_hidden(D_67, k3_zfmisc_1(A_38, B_39, C_40)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_101])).
% 24.23/13.09  tff(c_8, plain, (![A_1, B_2, D_28]: (r2_hidden('#skF_5'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), A_1) | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.23/13.09  tff(c_6, plain, (![A_1, B_2, D_28]: (r2_hidden('#skF_6'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), B_2) | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.23/13.09  tff(c_4, plain, (![A_1, B_2, D_28]: (k4_tarski('#skF_5'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), '#skF_6'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28))=D_28 | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.23/13.09  tff(c_122, plain, (![A_88, B_89, D_90]: (k4_tarski('#skF_5'(A_88, B_89, k2_zfmisc_1(A_88, B_89), D_90), '#skF_6'(A_88, B_89, k2_zfmisc_1(A_88, B_89), D_90))=D_90 | ~r2_hidden(D_90, k2_zfmisc_1(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.23/13.09  tff(c_26, plain, (![A_35, B_36, C_37]: (k4_tarski(k4_tarski(A_35, B_36), C_37)=k3_mcart_1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 24.23/13.09  tff(c_230, plain, (![A_132, B_133, D_134, C_135]: (k3_mcart_1('#skF_5'(A_132, B_133, k2_zfmisc_1(A_132, B_133), D_134), '#skF_6'(A_132, B_133, k2_zfmisc_1(A_132, B_133), D_134), C_135)=k4_tarski(D_134, C_135) | ~r2_hidden(D_134, k2_zfmisc_1(A_132, B_133)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_26])).
% 24.23/13.09  tff(c_30, plain, (![E_44, F_45, G_46]: (k3_mcart_1(E_44, F_45, G_46)!='#skF_7' | ~r2_hidden(G_46, '#skF_10') | ~r2_hidden(F_45, '#skF_9') | ~r2_hidden(E_44, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.23/13.09  tff(c_286, plain, (![D_146, C_147, A_148, B_149]: (k4_tarski(D_146, C_147)!='#skF_7' | ~r2_hidden(C_147, '#skF_10') | ~r2_hidden('#skF_6'(A_148, B_149, k2_zfmisc_1(A_148, B_149), D_146), '#skF_9') | ~r2_hidden('#skF_5'(A_148, B_149, k2_zfmisc_1(A_148, B_149), D_146), '#skF_8') | ~r2_hidden(D_146, k2_zfmisc_1(A_148, B_149)))), inference(superposition, [status(thm), theory('equality')], [c_230, c_30])).
% 24.23/13.09  tff(c_35681, plain, (![D_2967, B_2971, A_2970, B_2969, A_2968]: (D_2967!='#skF_7' | ~r2_hidden('#skF_6'(A_2970, B_2969, k2_zfmisc_1(A_2970, B_2969), D_2967), '#skF_10') | ~r2_hidden('#skF_6'(A_2968, B_2971, k2_zfmisc_1(A_2968, B_2971), '#skF_5'(A_2970, B_2969, k2_zfmisc_1(A_2970, B_2969), D_2967)), '#skF_9') | ~r2_hidden('#skF_5'(A_2968, B_2971, k2_zfmisc_1(A_2968, B_2971), '#skF_5'(A_2970, B_2969, k2_zfmisc_1(A_2970, B_2969), D_2967)), '#skF_8') | ~r2_hidden('#skF_5'(A_2970, B_2969, k2_zfmisc_1(A_2970, B_2969), D_2967), k2_zfmisc_1(A_2968, B_2971)) | ~r2_hidden(D_2967, k2_zfmisc_1(A_2970, B_2969)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_286])).
% 24.23/13.09  tff(c_35853, plain, (![D_2979, A_2980, B_2981, A_2982]: (D_2979!='#skF_7' | ~r2_hidden('#skF_6'(A_2980, B_2981, k2_zfmisc_1(A_2980, B_2981), D_2979), '#skF_10') | ~r2_hidden('#skF_5'(A_2982, '#skF_9', k2_zfmisc_1(A_2982, '#skF_9'), '#skF_5'(A_2980, B_2981, k2_zfmisc_1(A_2980, B_2981), D_2979)), '#skF_8') | ~r2_hidden(D_2979, k2_zfmisc_1(A_2980, B_2981)) | ~r2_hidden('#skF_5'(A_2980, B_2981, k2_zfmisc_1(A_2980, B_2981), D_2979), k2_zfmisc_1(A_2982, '#skF_9')))), inference(resolution, [status(thm)], [c_6, c_35681])).
% 24.23/13.09  tff(c_35869, plain, (![D_2983, A_2984, B_2985]: (D_2983!='#skF_7' | ~r2_hidden('#skF_6'(A_2984, B_2985, k2_zfmisc_1(A_2984, B_2985), D_2983), '#skF_10') | ~r2_hidden(D_2983, k2_zfmisc_1(A_2984, B_2985)) | ~r2_hidden('#skF_5'(A_2984, B_2985, k2_zfmisc_1(A_2984, B_2985), D_2983), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_8, c_35853])).
% 24.23/13.09  tff(c_35873, plain, (![D_28, B_2]: (D_28!='#skF_7' | ~r2_hidden('#skF_6'(k2_zfmisc_1('#skF_8', '#skF_9'), B_2, k2_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'), B_2), D_28), '#skF_10') | ~r2_hidden(D_28, k2_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'), B_2)))), inference(resolution, [status(thm)], [c_8, c_35869])).
% 24.23/13.09  tff(c_35885, plain, (![D_2986, B_2987]: (D_2986!='#skF_7' | ~r2_hidden('#skF_6'(k2_zfmisc_1('#skF_8', '#skF_9'), B_2987, k3_zfmisc_1('#skF_8', '#skF_9', B_2987), D_2986), '#skF_10') | ~r2_hidden(D_2986, k3_zfmisc_1('#skF_8', '#skF_9', B_2987)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_35873])).
% 24.23/13.09  tff(c_35891, plain, (~r2_hidden('#skF_7', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_102, c_35885])).
% 24.23/13.09  tff(c_32, plain, (r2_hidden('#skF_7', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.23/13.09  tff(c_35893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35891, c_32])).
% 24.23/13.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.23/13.09  
% 24.23/13.09  Inference rules
% 24.23/13.09  ----------------------
% 24.23/13.09  #Ref     : 6
% 24.23/13.09  #Sup     : 11239
% 24.23/13.09  #Fact    : 0
% 24.23/13.09  #Define  : 0
% 24.23/13.09  #Split   : 6
% 24.23/13.09  #Chain   : 0
% 24.23/13.09  #Close   : 0
% 24.23/13.09  
% 24.23/13.09  Ordering : KBO
% 24.23/13.09  
% 24.23/13.09  Simplification rules
% 24.23/13.09  ----------------------
% 24.23/13.09  #Subsume      : 631
% 24.23/13.09  #Demod        : 5712
% 24.23/13.09  #Tautology    : 183
% 24.23/13.09  #SimpNegUnit  : 7
% 24.23/13.09  #BackRed      : 7
% 24.23/13.09  
% 24.23/13.09  #Partial instantiations: 0
% 24.23/13.09  #Strategies tried      : 1
% 24.23/13.09  
% 24.23/13.09  Timing (in seconds)
% 24.23/13.09  ----------------------
% 24.23/13.09  Preprocessing        : 0.28
% 24.23/13.09  Parsing              : 0.15
% 24.23/13.09  CNF conversion       : 0.02
% 24.23/13.09  Main loop            : 12.04
% 24.23/13.09  Inferencing          : 1.28
% 24.23/13.09  Reduction            : 1.87
% 24.23/13.09  Demodulation         : 1.62
% 24.23/13.09  BG Simplification    : 0.29
% 24.23/13.09  Subsumption          : 7.96
% 24.23/13.09  Abstraction          : 0.44
% 24.23/13.09  MUC search           : 0.00
% 24.23/13.10  Cooper               : 0.00
% 24.23/13.10  Total                : 12.35
% 24.23/13.10  Index Insertion      : 0.00
% 24.23/13.10  Index Deletion       : 0.00
% 24.23/13.10  Index Matching       : 0.00
% 24.23/13.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
