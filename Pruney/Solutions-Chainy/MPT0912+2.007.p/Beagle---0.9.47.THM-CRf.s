%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:08 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 148 expanded)
%              Number of leaves         :   24 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :   83 ( 248 expanded)
%              Number of equality atoms :   31 (  92 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(A,k3_zfmisc_1(B,C,D))
          & ! [E,F,G] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & r2_hidden(G,D)
                & A = k3_mcart_1(E,F,G) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_36,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

tff(c_20,plain,(
    r2_hidden('#skF_3',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_6,B_7,C_8] : k2_zfmisc_1(k2_zfmisc_1(A_6,B_7),C_8) = k3_zfmisc_1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_57,plain,(
    ! [A_38,B_39,C_40] :
      ( r2_hidden(k1_mcart_1(A_38),B_39)
      | ~ r2_hidden(A_38,k2_zfmisc_1(B_39,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_250,plain,(
    ! [A_90,A_91,B_92,C_93] :
      ( r2_hidden(k1_mcart_1(A_90),k2_zfmisc_1(A_91,B_92))
      | ~ r2_hidden(A_90,k3_zfmisc_1(A_91,B_92,C_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_256,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_250])).

tff(c_167,plain,(
    ! [A_70,B_71,C_72] :
      ( k4_tarski('#skF_1'(A_70,B_71,C_72),'#skF_2'(A_70,B_71,C_72)) = A_70
      | ~ r2_hidden(A_70,k2_zfmisc_1(B_71,C_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_20,B_21] : k2_mcart_1(k4_tarski(A_20,B_21)) = B_21 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_179,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_mcart_1(A_70) = '#skF_2'(A_70,B_71,C_72)
      | ~ r2_hidden(A_70,k2_zfmisc_1(B_71,C_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_16])).

tff(c_267,plain,(
    k2_mcart_1(k1_mcart_1('#skF_3')) = '#skF_2'(k1_mcart_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_256,c_179])).

tff(c_8,plain,(
    ! [A_13,C_15,B_14] :
      ( r2_hidden(k2_mcart_1(A_13),C_15)
      | ~ r2_hidden(A_13,k2_zfmisc_1(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_270,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_3')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_256,c_8])).

tff(c_298,plain,(
    r2_hidden('#skF_2'(k1_mcart_1('#skF_3'),'#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_270])).

tff(c_14,plain,(
    ! [A_20,B_21] : k1_mcart_1(k4_tarski(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_176,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_mcart_1(A_70) = '#skF_1'(A_70,B_71,C_72)
      | ~ r2_hidden(A_70,k2_zfmisc_1(B_71,C_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_14])).

tff(c_268,plain,(
    k1_mcart_1(k1_mcart_1('#skF_3')) = '#skF_1'(k1_mcart_1('#skF_3'),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_256,c_176])).

tff(c_10,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden(k1_mcart_1(A_13),B_14)
      | ~ r2_hidden(A_13,k2_zfmisc_1(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_269,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_256,c_10])).

tff(c_307,plain,(
    r2_hidden('#skF_1'(k1_mcart_1('#skF_3'),'#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_269])).

tff(c_54,plain,(
    ! [A_35,C_36,B_37] :
      ( r2_hidden(k2_mcart_1(A_35),C_36)
      | ~ r2_hidden(A_35,k2_zfmisc_1(B_37,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    ! [A_41,C_42,A_43,B_44] :
      ( r2_hidden(k2_mcart_1(A_41),C_42)
      | ~ r2_hidden(A_41,k3_zfmisc_1(A_43,B_44,C_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_54])).

tff(c_63,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_60])).

tff(c_198,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_mcart_1(A_79) = '#skF_2'(A_79,B_80,C_81)
      | ~ r2_hidden(A_79,k2_zfmisc_1(B_80,C_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_16])).

tff(c_377,plain,(
    ! [A_114,A_115,B_116,C_117] :
      ( '#skF_2'(A_114,k2_zfmisc_1(A_115,B_116),C_117) = k2_mcart_1(A_114)
      | ~ r2_hidden(A_114,k3_zfmisc_1(A_115,B_116,C_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_198])).

tff(c_385,plain,(
    '#skF_2'('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') = k2_mcart_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_377])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k4_tarski('#skF_1'(A_1,B_2,C_3),'#skF_2'(A_1,B_2,C_3)) = A_1
      | ~ r2_hidden(A_1,k2_zfmisc_1(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_389,plain,
    ( k4_tarski('#skF_1'('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k2_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_2])).

tff(c_393,plain,(
    k4_tarski('#skF_1'('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6'),k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4,c_389])).

tff(c_407,plain,(
    '#skF_1'('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') = k1_mcart_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_14])).

tff(c_422,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_393])).

tff(c_64,plain,(
    ! [A_45,B_46,C_47,D_48] : k4_tarski(k3_mcart_1(A_45,B_46,C_47),D_48) = k4_mcart_1(A_45,B_46,C_47,D_48) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_70,plain,(
    ! [A_45,B_46,C_47,D_48] : k1_mcart_1(k4_mcart_1(A_45,B_46,C_47,D_48)) = k3_mcart_1(A_45,B_46,C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_14])).

tff(c_98,plain,(
    ! [A_60,B_61,C_62,D_63] : k4_tarski(k4_tarski(k4_tarski(A_60,B_61),C_62),D_63) = k4_mcart_1(A_60,B_61,C_62,D_63) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,(
    ! [A_60,B_61,C_62,D_63] : k4_tarski(k4_tarski(A_60,B_61),C_62) = k1_mcart_1(k4_mcart_1(A_60,B_61,C_62,D_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_14])).

tff(c_127,plain,(
    ! [A_60,B_61,C_62] : k4_tarski(k4_tarski(A_60,B_61),C_62) = k3_mcart_1(A_60,B_61,C_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_110])).

tff(c_532,plain,(
    ! [A_130,B_131,C_132,C_133] :
      ( k3_mcart_1('#skF_1'(A_130,B_131,C_132),'#skF_2'(A_130,B_131,C_132),C_133) = k4_tarski(A_130,C_133)
      | ~ r2_hidden(A_130,k2_zfmisc_1(B_131,C_132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_127])).

tff(c_18,plain,(
    ! [E_25,F_26,G_27] :
      ( k3_mcart_1(E_25,F_26,G_27) != '#skF_3'
      | ~ r2_hidden(G_27,'#skF_6')
      | ~ r2_hidden(F_26,'#skF_5')
      | ~ r2_hidden(E_25,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_651,plain,(
    ! [A_145,C_146,B_147,C_148] :
      ( k4_tarski(A_145,C_146) != '#skF_3'
      | ~ r2_hidden(C_146,'#skF_6')
      | ~ r2_hidden('#skF_2'(A_145,B_147,C_148),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_145,B_147,C_148),'#skF_4')
      | ~ r2_hidden(A_145,k2_zfmisc_1(B_147,C_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_18])).

tff(c_655,plain,(
    ! [B_147,C_148] :
      ( ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6')
      | ~ r2_hidden('#skF_2'(k1_mcart_1('#skF_3'),B_147,C_148),'#skF_5')
      | ~ r2_hidden('#skF_1'(k1_mcart_1('#skF_3'),B_147,C_148),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(B_147,C_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_651])).

tff(c_665,plain,(
    ! [B_149,C_150] :
      ( ~ r2_hidden('#skF_2'(k1_mcart_1('#skF_3'),B_149,C_150),'#skF_5')
      | ~ r2_hidden('#skF_1'(k1_mcart_1('#skF_3'),B_149,C_150),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(B_149,C_150)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_655])).

tff(c_668,plain,
    ( ~ r2_hidden('#skF_2'(k1_mcart_1('#skF_3'),'#skF_4','#skF_5'),'#skF_5')
    | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_307,c_665])).

tff(c_672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_298,c_668])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.37  
% 2.74/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.37  %$ r2_hidden > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.74/1.37  
% 2.74/1.37  %Foreground sorts:
% 2.74/1.37  
% 2.74/1.37  
% 2.74/1.37  %Background operators:
% 2.74/1.37  
% 2.74/1.37  
% 2.74/1.37  %Foreground operators:
% 2.74/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.74/1.37  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.74/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.74/1.37  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.37  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.74/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.37  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.74/1.37  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.74/1.37  
% 2.74/1.39  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ~(r2_hidden(A, k3_zfmisc_1(B, C, D)) & (![E, F, G]: ~(((r2_hidden(E, B) & r2_hidden(F, C)) & r2_hidden(G, D)) & (A = k3_mcart_1(E, F, G)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_mcart_1)).
% 2.74/1.39  tff(f_34, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.74/1.39  tff(f_42, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.74/1.39  tff(f_32, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 2.74/1.39  tff(f_48, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.74/1.39  tff(f_36, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 2.74/1.39  tff(f_44, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_mcart_1)).
% 2.74/1.39  tff(c_20, plain, (r2_hidden('#skF_3', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.74/1.39  tff(c_4, plain, (![A_6, B_7, C_8]: (k2_zfmisc_1(k2_zfmisc_1(A_6, B_7), C_8)=k3_zfmisc_1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.74/1.39  tff(c_57, plain, (![A_38, B_39, C_40]: (r2_hidden(k1_mcart_1(A_38), B_39) | ~r2_hidden(A_38, k2_zfmisc_1(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.74/1.39  tff(c_250, plain, (![A_90, A_91, B_92, C_93]: (r2_hidden(k1_mcart_1(A_90), k2_zfmisc_1(A_91, B_92)) | ~r2_hidden(A_90, k3_zfmisc_1(A_91, B_92, C_93)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_57])).
% 2.74/1.39  tff(c_256, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_20, c_250])).
% 2.74/1.39  tff(c_167, plain, (![A_70, B_71, C_72]: (k4_tarski('#skF_1'(A_70, B_71, C_72), '#skF_2'(A_70, B_71, C_72))=A_70 | ~r2_hidden(A_70, k2_zfmisc_1(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.39  tff(c_16, plain, (![A_20, B_21]: (k2_mcart_1(k4_tarski(A_20, B_21))=B_21)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.74/1.39  tff(c_179, plain, (![A_70, B_71, C_72]: (k2_mcart_1(A_70)='#skF_2'(A_70, B_71, C_72) | ~r2_hidden(A_70, k2_zfmisc_1(B_71, C_72)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_16])).
% 2.74/1.39  tff(c_267, plain, (k2_mcart_1(k1_mcart_1('#skF_3'))='#skF_2'(k1_mcart_1('#skF_3'), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_256, c_179])).
% 2.74/1.39  tff(c_8, plain, (![A_13, C_15, B_14]: (r2_hidden(k2_mcart_1(A_13), C_15) | ~r2_hidden(A_13, k2_zfmisc_1(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.74/1.39  tff(c_270, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_3')), '#skF_5')), inference(resolution, [status(thm)], [c_256, c_8])).
% 2.74/1.39  tff(c_298, plain, (r2_hidden('#skF_2'(k1_mcart_1('#skF_3'), '#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_267, c_270])).
% 2.74/1.39  tff(c_14, plain, (![A_20, B_21]: (k1_mcart_1(k4_tarski(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.74/1.39  tff(c_176, plain, (![A_70, B_71, C_72]: (k1_mcart_1(A_70)='#skF_1'(A_70, B_71, C_72) | ~r2_hidden(A_70, k2_zfmisc_1(B_71, C_72)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_14])).
% 2.74/1.39  tff(c_268, plain, (k1_mcart_1(k1_mcart_1('#skF_3'))='#skF_1'(k1_mcart_1('#skF_3'), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_256, c_176])).
% 2.74/1.39  tff(c_10, plain, (![A_13, B_14, C_15]: (r2_hidden(k1_mcart_1(A_13), B_14) | ~r2_hidden(A_13, k2_zfmisc_1(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.74/1.39  tff(c_269, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_3')), '#skF_4')), inference(resolution, [status(thm)], [c_256, c_10])).
% 2.74/1.39  tff(c_307, plain, (r2_hidden('#skF_1'(k1_mcart_1('#skF_3'), '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_269])).
% 2.74/1.39  tff(c_54, plain, (![A_35, C_36, B_37]: (r2_hidden(k2_mcart_1(A_35), C_36) | ~r2_hidden(A_35, k2_zfmisc_1(B_37, C_36)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.74/1.39  tff(c_60, plain, (![A_41, C_42, A_43, B_44]: (r2_hidden(k2_mcart_1(A_41), C_42) | ~r2_hidden(A_41, k3_zfmisc_1(A_43, B_44, C_42)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_54])).
% 2.74/1.39  tff(c_63, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(resolution, [status(thm)], [c_20, c_60])).
% 2.74/1.39  tff(c_198, plain, (![A_79, B_80, C_81]: (k2_mcart_1(A_79)='#skF_2'(A_79, B_80, C_81) | ~r2_hidden(A_79, k2_zfmisc_1(B_80, C_81)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_16])).
% 2.74/1.39  tff(c_377, plain, (![A_114, A_115, B_116, C_117]: ('#skF_2'(A_114, k2_zfmisc_1(A_115, B_116), C_117)=k2_mcart_1(A_114) | ~r2_hidden(A_114, k3_zfmisc_1(A_115, B_116, C_117)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_198])).
% 2.74/1.39  tff(c_385, plain, ('#skF_2'('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')=k2_mcart_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_377])).
% 2.74/1.39  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_tarski('#skF_1'(A_1, B_2, C_3), '#skF_2'(A_1, B_2, C_3))=A_1 | ~r2_hidden(A_1, k2_zfmisc_1(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.39  tff(c_389, plain, (k4_tarski('#skF_1'('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'), k2_mcart_1('#skF_3'))='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_385, c_2])).
% 2.74/1.39  tff(c_393, plain, (k4_tarski('#skF_1'('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'), k2_mcart_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4, c_389])).
% 2.74/1.39  tff(c_407, plain, ('#skF_1'('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')=k1_mcart_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_393, c_14])).
% 2.74/1.39  tff(c_422, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_407, c_393])).
% 2.74/1.39  tff(c_64, plain, (![A_45, B_46, C_47, D_48]: (k4_tarski(k3_mcart_1(A_45, B_46, C_47), D_48)=k4_mcart_1(A_45, B_46, C_47, D_48))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.74/1.39  tff(c_70, plain, (![A_45, B_46, C_47, D_48]: (k1_mcart_1(k4_mcart_1(A_45, B_46, C_47, D_48))=k3_mcart_1(A_45, B_46, C_47))), inference(superposition, [status(thm), theory('equality')], [c_64, c_14])).
% 2.74/1.39  tff(c_98, plain, (![A_60, B_61, C_62, D_63]: (k4_tarski(k4_tarski(k4_tarski(A_60, B_61), C_62), D_63)=k4_mcart_1(A_60, B_61, C_62, D_63))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.74/1.39  tff(c_110, plain, (![A_60, B_61, C_62, D_63]: (k4_tarski(k4_tarski(A_60, B_61), C_62)=k1_mcart_1(k4_mcart_1(A_60, B_61, C_62, D_63)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_14])).
% 2.74/1.39  tff(c_127, plain, (![A_60, B_61, C_62]: (k4_tarski(k4_tarski(A_60, B_61), C_62)=k3_mcart_1(A_60, B_61, C_62))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_110])).
% 2.74/1.39  tff(c_532, plain, (![A_130, B_131, C_132, C_133]: (k3_mcart_1('#skF_1'(A_130, B_131, C_132), '#skF_2'(A_130, B_131, C_132), C_133)=k4_tarski(A_130, C_133) | ~r2_hidden(A_130, k2_zfmisc_1(B_131, C_132)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_127])).
% 2.74/1.39  tff(c_18, plain, (![E_25, F_26, G_27]: (k3_mcart_1(E_25, F_26, G_27)!='#skF_3' | ~r2_hidden(G_27, '#skF_6') | ~r2_hidden(F_26, '#skF_5') | ~r2_hidden(E_25, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.74/1.39  tff(c_651, plain, (![A_145, C_146, B_147, C_148]: (k4_tarski(A_145, C_146)!='#skF_3' | ~r2_hidden(C_146, '#skF_6') | ~r2_hidden('#skF_2'(A_145, B_147, C_148), '#skF_5') | ~r2_hidden('#skF_1'(A_145, B_147, C_148), '#skF_4') | ~r2_hidden(A_145, k2_zfmisc_1(B_147, C_148)))), inference(superposition, [status(thm), theory('equality')], [c_532, c_18])).
% 2.74/1.39  tff(c_655, plain, (![B_147, C_148]: (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6') | ~r2_hidden('#skF_2'(k1_mcart_1('#skF_3'), B_147, C_148), '#skF_5') | ~r2_hidden('#skF_1'(k1_mcart_1('#skF_3'), B_147, C_148), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(B_147, C_148)))), inference(superposition, [status(thm), theory('equality')], [c_422, c_651])).
% 2.74/1.39  tff(c_665, plain, (![B_149, C_150]: (~r2_hidden('#skF_2'(k1_mcart_1('#skF_3'), B_149, C_150), '#skF_5') | ~r2_hidden('#skF_1'(k1_mcart_1('#skF_3'), B_149, C_150), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(B_149, C_150)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_655])).
% 2.74/1.39  tff(c_668, plain, (~r2_hidden('#skF_2'(k1_mcart_1('#skF_3'), '#skF_4', '#skF_5'), '#skF_5') | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_307, c_665])).
% 2.74/1.39  tff(c_672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_256, c_298, c_668])).
% 2.74/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.39  
% 2.74/1.39  Inference rules
% 2.74/1.39  ----------------------
% 2.74/1.39  #Ref     : 0
% 2.74/1.39  #Sup     : 168
% 2.74/1.39  #Fact    : 0
% 2.74/1.39  #Define  : 0
% 2.74/1.39  #Split   : 1
% 2.74/1.39  #Chain   : 0
% 2.74/1.39  #Close   : 0
% 2.74/1.39  
% 2.74/1.39  Ordering : KBO
% 2.74/1.39  
% 2.74/1.39  Simplification rules
% 2.74/1.39  ----------------------
% 2.74/1.39  #Subsume      : 14
% 2.74/1.39  #Demod        : 139
% 2.74/1.39  #Tautology    : 107
% 2.74/1.39  #SimpNegUnit  : 0
% 2.74/1.39  #BackRed      : 4
% 2.74/1.39  
% 2.74/1.39  #Partial instantiations: 0
% 2.74/1.39  #Strategies tried      : 1
% 2.74/1.39  
% 2.74/1.39  Timing (in seconds)
% 2.74/1.39  ----------------------
% 2.74/1.39  Preprocessing        : 0.26
% 2.74/1.39  Parsing              : 0.15
% 2.74/1.39  CNF conversion       : 0.02
% 2.74/1.39  Main loop            : 0.35
% 2.74/1.39  Inferencing          : 0.16
% 2.74/1.39  Reduction            : 0.11
% 2.74/1.39  Demodulation         : 0.09
% 2.74/1.39  BG Simplification    : 0.02
% 2.74/1.39  Subsumption          : 0.04
% 2.74/1.39  Abstraction          : 0.02
% 2.74/1.39  MUC search           : 0.00
% 2.74/1.39  Cooper               : 0.00
% 2.74/1.39  Total                : 0.65
% 2.74/1.39  Index Insertion      : 0.00
% 2.74/1.39  Index Deletion       : 0.00
% 2.74/1.39  Index Matching       : 0.00
% 2.74/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
