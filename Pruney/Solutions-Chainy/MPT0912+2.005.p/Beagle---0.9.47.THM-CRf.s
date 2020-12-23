%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:08 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 264 expanded)
%              Number of leaves         :   22 ( 102 expanded)
%              Depth                    :   14
%              Number of atoms          :   83 ( 468 expanded)
%              Number of equality atoms :   22 ( 206 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(A,k3_zfmisc_1(B,C,D))
          & ! [E,F,G] :
              ~ ( r2_hidden(E,B)
                & r2_hidden(F,C)
                & r2_hidden(G,D)
                & A = k3_mcart_1(E,F,G) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

tff(f_42,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_20,plain,(
    r2_hidden('#skF_3',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_13,B_14,C_15] : k2_zfmisc_1(k2_zfmisc_1(A_13,B_14),C_15) = k3_zfmisc_1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_202,plain,(
    ! [A_93,B_94,C_95] :
      ( k4_tarski('#skF_1'(A_93,B_94,C_95),'#skF_2'(A_93,B_94,C_95)) = A_93
      | ~ r2_hidden(A_93,k2_zfmisc_1(B_94,C_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_16,B_17] : k2_mcart_1(k4_tarski(A_16,B_17)) = B_17 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_247,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_mcart_1(A_99) = '#skF_2'(A_99,B_100,C_101)
      | ~ r2_hidden(A_99,k2_zfmisc_1(B_100,C_101)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_16])).

tff(c_298,plain,(
    ! [A_115,A_116,B_117,C_118] :
      ( '#skF_2'(A_115,k2_zfmisc_1(A_116,B_117),C_118) = k2_mcart_1(A_115)
      | ~ r2_hidden(A_115,k3_zfmisc_1(A_116,B_117,C_118)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_247])).

tff(c_306,plain,(
    '#skF_2'('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') = k2_mcart_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_298])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k4_tarski('#skF_1'(A_1,B_2,C_3),'#skF_2'(A_1,B_2,C_3)) = A_1
      | ~ r2_hidden(A_1,k2_zfmisc_1(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_310,plain,
    ( k4_tarski('#skF_1'('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k2_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_2])).

tff(c_314,plain,(
    k4_tarski('#skF_1'('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6'),k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12,c_310])).

tff(c_14,plain,(
    ! [A_16,B_17] : k1_mcart_1(k4_tarski(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_346,plain,(
    '#skF_1'('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') = k1_mcart_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_14])).

tff(c_354,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_314])).

tff(c_100,plain,(
    ! [A_44,C_45,B_46,D_47] :
      ( r2_hidden(A_44,C_45)
      | ~ r2_hidden(k4_tarski(A_44,B_46),k2_zfmisc_1(C_45,D_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_106,plain,(
    ! [A_13,B_14,A_44,C_15,B_46] :
      ( r2_hidden(A_44,k2_zfmisc_1(A_13,B_14))
      | ~ r2_hidden(k4_tarski(A_44,B_46),k3_zfmisc_1(A_13,B_14,C_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_100])).

tff(c_509,plain,(
    ! [A_137,B_138,C_139] :
      ( r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(A_137,B_138))
      | ~ r2_hidden('#skF_3',k3_zfmisc_1(A_137,B_138,C_139)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_106])).

tff(c_515,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_509])).

tff(c_6,plain,(
    ! [B_7,D_9,A_6,C_8] :
      ( r2_hidden(B_7,D_9)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_542,plain,(
    ! [D_144,A_143,B_142,C_145,C_146] :
      ( r2_hidden('#skF_2'(A_143,B_142,C_146),D_144)
      | ~ r2_hidden(A_143,k2_zfmisc_1(C_145,D_144))
      | ~ r2_hidden(A_143,k2_zfmisc_1(B_142,C_146)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_6])).

tff(c_551,plain,(
    ! [B_142,C_146] :
      ( r2_hidden('#skF_2'(k1_mcart_1('#skF_3'),B_142,C_146),'#skF_5')
      | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(B_142,C_146)) ) ),
    inference(resolution,[status(thm)],[c_515,c_542])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_220,plain,(
    ! [D_9,C_8,C_95,B_94,A_93] :
      ( r2_hidden('#skF_1'(A_93,B_94,C_95),C_8)
      | ~ r2_hidden(A_93,k2_zfmisc_1(C_8,D_9))
      | ~ r2_hidden(A_93,k2_zfmisc_1(B_94,C_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_8])).

tff(c_524,plain,(
    ! [B_94,C_95] :
      ( r2_hidden('#skF_1'(k1_mcart_1('#skF_3'),B_94,C_95),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(B_94,C_95)) ) ),
    inference(resolution,[status(thm)],[c_515,c_220])).

tff(c_75,plain,(
    ! [B_34,D_35,A_36,C_37] :
      ( r2_hidden(B_34,D_35)
      | ~ r2_hidden(k4_tarski(A_36,B_34),k2_zfmisc_1(C_37,D_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,(
    ! [A_36,A_13,B_14,C_15,B_34] :
      ( r2_hidden(B_34,C_15)
      | ~ r2_hidden(k4_tarski(A_36,B_34),k3_zfmisc_1(A_13,B_14,C_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_75])).

tff(c_476,plain,(
    ! [C_129,A_130,B_131] :
      ( r2_hidden(k2_mcart_1('#skF_3'),C_129)
      | ~ r2_hidden('#skF_3',k3_zfmisc_1(A_130,B_131,C_129)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_81])).

tff(c_481,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_476])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] : k4_tarski(k4_tarski(A_10,B_11),C_12) = k3_mcart_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_598,plain,(
    ! [A_162,B_163,C_164,C_165] :
      ( k3_mcart_1('#skF_1'(A_162,B_163,C_164),'#skF_2'(A_162,B_163,C_164),C_165) = k4_tarski(A_162,C_165)
      | ~ r2_hidden(A_162,k2_zfmisc_1(B_163,C_164)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_10])).

tff(c_18,plain,(
    ! [E_21,F_22,G_23] :
      ( k3_mcart_1(E_21,F_22,G_23) != '#skF_3'
      | ~ r2_hidden(G_23,'#skF_6')
      | ~ r2_hidden(F_22,'#skF_5')
      | ~ r2_hidden(E_21,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_681,plain,(
    ! [A_177,C_178,B_179,C_180] :
      ( k4_tarski(A_177,C_178) != '#skF_3'
      | ~ r2_hidden(C_178,'#skF_6')
      | ~ r2_hidden('#skF_2'(A_177,B_179,C_180),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_177,B_179,C_180),'#skF_4')
      | ~ r2_hidden(A_177,k2_zfmisc_1(B_179,C_180)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_18])).

tff(c_683,plain,(
    ! [B_179,C_180] :
      ( ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6')
      | ~ r2_hidden('#skF_2'(k1_mcart_1('#skF_3'),B_179,C_180),'#skF_5')
      | ~ r2_hidden('#skF_1'(k1_mcart_1('#skF_3'),B_179,C_180),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(B_179,C_180)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_681])).

tff(c_893,plain,(
    ! [B_243,C_244] :
      ( ~ r2_hidden('#skF_2'(k1_mcart_1('#skF_3'),B_243,C_244),'#skF_5')
      | ~ r2_hidden('#skF_1'(k1_mcart_1('#skF_3'),B_243,C_244),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(B_243,C_244)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_683])).

tff(c_979,plain,(
    ! [B_250,C_251] :
      ( ~ r2_hidden('#skF_2'(k1_mcart_1('#skF_3'),B_250,C_251),'#skF_5')
      | ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(B_250,C_251)) ) ),
    inference(resolution,[status(thm)],[c_524,c_893])).

tff(c_983,plain,(
    ! [B_142,C_146] : ~ r2_hidden(k1_mcart_1('#skF_3'),k2_zfmisc_1(B_142,C_146)) ),
    inference(resolution,[status(thm)],[c_551,c_979])).

tff(c_987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_983,c_515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 12:51:52 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.49  
% 3.05/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.49  %$ r2_hidden > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.05/1.49  
% 3.05/1.49  %Foreground sorts:
% 3.05/1.49  
% 3.05/1.49  
% 3.05/1.49  %Background operators:
% 3.05/1.49  
% 3.05/1.49  
% 3.05/1.49  %Foreground operators:
% 3.05/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.05/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.05/1.49  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.05/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.05/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.05/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.05/1.49  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.05/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.49  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.05/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.05/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.49  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.05/1.49  
% 3.05/1.51  tff(f_60, negated_conjecture, ~(![A, B, C, D]: ~(r2_hidden(A, k3_zfmisc_1(B, C, D)) & (![E, F, G]: ~(((r2_hidden(E, B) & r2_hidden(F, C)) & r2_hidden(G, D)) & (A = k3_mcart_1(E, F, G)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_mcart_1)).
% 3.05/1.51  tff(f_42, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.05/1.51  tff(f_32, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 3.05/1.51  tff(f_46, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.05/1.51  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.05/1.51  tff(f_40, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.05/1.51  tff(c_20, plain, (r2_hidden('#skF_3', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.05/1.51  tff(c_12, plain, (![A_13, B_14, C_15]: (k2_zfmisc_1(k2_zfmisc_1(A_13, B_14), C_15)=k3_zfmisc_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.05/1.51  tff(c_202, plain, (![A_93, B_94, C_95]: (k4_tarski('#skF_1'(A_93, B_94, C_95), '#skF_2'(A_93, B_94, C_95))=A_93 | ~r2_hidden(A_93, k2_zfmisc_1(B_94, C_95)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.05/1.51  tff(c_16, plain, (![A_16, B_17]: (k2_mcart_1(k4_tarski(A_16, B_17))=B_17)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.05/1.51  tff(c_247, plain, (![A_99, B_100, C_101]: (k2_mcart_1(A_99)='#skF_2'(A_99, B_100, C_101) | ~r2_hidden(A_99, k2_zfmisc_1(B_100, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_202, c_16])).
% 3.05/1.51  tff(c_298, plain, (![A_115, A_116, B_117, C_118]: ('#skF_2'(A_115, k2_zfmisc_1(A_116, B_117), C_118)=k2_mcart_1(A_115) | ~r2_hidden(A_115, k3_zfmisc_1(A_116, B_117, C_118)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_247])).
% 3.05/1.51  tff(c_306, plain, ('#skF_2'('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')=k2_mcart_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_298])).
% 3.05/1.51  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_tarski('#skF_1'(A_1, B_2, C_3), '#skF_2'(A_1, B_2, C_3))=A_1 | ~r2_hidden(A_1, k2_zfmisc_1(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.05/1.51  tff(c_310, plain, (k4_tarski('#skF_1'('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'), k2_mcart_1('#skF_3'))='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_306, c_2])).
% 3.05/1.51  tff(c_314, plain, (k4_tarski('#skF_1'('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6'), k2_mcart_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_12, c_310])).
% 3.05/1.51  tff(c_14, plain, (![A_16, B_17]: (k1_mcart_1(k4_tarski(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.05/1.51  tff(c_346, plain, ('#skF_1'('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')=k1_mcart_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_314, c_14])).
% 3.05/1.51  tff(c_354, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_346, c_314])).
% 3.05/1.51  tff(c_100, plain, (![A_44, C_45, B_46, D_47]: (r2_hidden(A_44, C_45) | ~r2_hidden(k4_tarski(A_44, B_46), k2_zfmisc_1(C_45, D_47)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.05/1.51  tff(c_106, plain, (![A_13, B_14, A_44, C_15, B_46]: (r2_hidden(A_44, k2_zfmisc_1(A_13, B_14)) | ~r2_hidden(k4_tarski(A_44, B_46), k3_zfmisc_1(A_13, B_14, C_15)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_100])).
% 3.05/1.51  tff(c_509, plain, (![A_137, B_138, C_139]: (r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(A_137, B_138)) | ~r2_hidden('#skF_3', k3_zfmisc_1(A_137, B_138, C_139)))), inference(superposition, [status(thm), theory('equality')], [c_354, c_106])).
% 3.05/1.51  tff(c_515, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_20, c_509])).
% 3.05/1.51  tff(c_6, plain, (![B_7, D_9, A_6, C_8]: (r2_hidden(B_7, D_9) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.05/1.51  tff(c_542, plain, (![D_144, A_143, B_142, C_145, C_146]: (r2_hidden('#skF_2'(A_143, B_142, C_146), D_144) | ~r2_hidden(A_143, k2_zfmisc_1(C_145, D_144)) | ~r2_hidden(A_143, k2_zfmisc_1(B_142, C_146)))), inference(superposition, [status(thm), theory('equality')], [c_202, c_6])).
% 3.05/1.51  tff(c_551, plain, (![B_142, C_146]: (r2_hidden('#skF_2'(k1_mcart_1('#skF_3'), B_142, C_146), '#skF_5') | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(B_142, C_146)))), inference(resolution, [status(thm)], [c_515, c_542])).
% 3.05/1.51  tff(c_8, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.05/1.51  tff(c_220, plain, (![D_9, C_8, C_95, B_94, A_93]: (r2_hidden('#skF_1'(A_93, B_94, C_95), C_8) | ~r2_hidden(A_93, k2_zfmisc_1(C_8, D_9)) | ~r2_hidden(A_93, k2_zfmisc_1(B_94, C_95)))), inference(superposition, [status(thm), theory('equality')], [c_202, c_8])).
% 3.05/1.51  tff(c_524, plain, (![B_94, C_95]: (r2_hidden('#skF_1'(k1_mcart_1('#skF_3'), B_94, C_95), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(B_94, C_95)))), inference(resolution, [status(thm)], [c_515, c_220])).
% 3.05/1.51  tff(c_75, plain, (![B_34, D_35, A_36, C_37]: (r2_hidden(B_34, D_35) | ~r2_hidden(k4_tarski(A_36, B_34), k2_zfmisc_1(C_37, D_35)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.05/1.51  tff(c_81, plain, (![A_36, A_13, B_14, C_15, B_34]: (r2_hidden(B_34, C_15) | ~r2_hidden(k4_tarski(A_36, B_34), k3_zfmisc_1(A_13, B_14, C_15)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_75])).
% 3.05/1.51  tff(c_476, plain, (![C_129, A_130, B_131]: (r2_hidden(k2_mcart_1('#skF_3'), C_129) | ~r2_hidden('#skF_3', k3_zfmisc_1(A_130, B_131, C_129)))), inference(superposition, [status(thm), theory('equality')], [c_314, c_81])).
% 3.05/1.51  tff(c_481, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(resolution, [status(thm)], [c_20, c_476])).
% 3.05/1.51  tff(c_10, plain, (![A_10, B_11, C_12]: (k4_tarski(k4_tarski(A_10, B_11), C_12)=k3_mcart_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.05/1.51  tff(c_598, plain, (![A_162, B_163, C_164, C_165]: (k3_mcart_1('#skF_1'(A_162, B_163, C_164), '#skF_2'(A_162, B_163, C_164), C_165)=k4_tarski(A_162, C_165) | ~r2_hidden(A_162, k2_zfmisc_1(B_163, C_164)))), inference(superposition, [status(thm), theory('equality')], [c_202, c_10])).
% 3.05/1.51  tff(c_18, plain, (![E_21, F_22, G_23]: (k3_mcart_1(E_21, F_22, G_23)!='#skF_3' | ~r2_hidden(G_23, '#skF_6') | ~r2_hidden(F_22, '#skF_5') | ~r2_hidden(E_21, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.05/1.51  tff(c_681, plain, (![A_177, C_178, B_179, C_180]: (k4_tarski(A_177, C_178)!='#skF_3' | ~r2_hidden(C_178, '#skF_6') | ~r2_hidden('#skF_2'(A_177, B_179, C_180), '#skF_5') | ~r2_hidden('#skF_1'(A_177, B_179, C_180), '#skF_4') | ~r2_hidden(A_177, k2_zfmisc_1(B_179, C_180)))), inference(superposition, [status(thm), theory('equality')], [c_598, c_18])).
% 3.05/1.51  tff(c_683, plain, (![B_179, C_180]: (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6') | ~r2_hidden('#skF_2'(k1_mcart_1('#skF_3'), B_179, C_180), '#skF_5') | ~r2_hidden('#skF_1'(k1_mcart_1('#skF_3'), B_179, C_180), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(B_179, C_180)))), inference(superposition, [status(thm), theory('equality')], [c_354, c_681])).
% 3.05/1.51  tff(c_893, plain, (![B_243, C_244]: (~r2_hidden('#skF_2'(k1_mcart_1('#skF_3'), B_243, C_244), '#skF_5') | ~r2_hidden('#skF_1'(k1_mcart_1('#skF_3'), B_243, C_244), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(B_243, C_244)))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_683])).
% 3.05/1.51  tff(c_979, plain, (![B_250, C_251]: (~r2_hidden('#skF_2'(k1_mcart_1('#skF_3'), B_250, C_251), '#skF_5') | ~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(B_250, C_251)))), inference(resolution, [status(thm)], [c_524, c_893])).
% 3.05/1.51  tff(c_983, plain, (![B_142, C_146]: (~r2_hidden(k1_mcart_1('#skF_3'), k2_zfmisc_1(B_142, C_146)))), inference(resolution, [status(thm)], [c_551, c_979])).
% 3.05/1.51  tff(c_987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_983, c_515])).
% 3.05/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.51  
% 3.05/1.51  Inference rules
% 3.05/1.51  ----------------------
% 3.05/1.51  #Ref     : 0
% 3.05/1.51  #Sup     : 261
% 3.05/1.51  #Fact    : 0
% 3.05/1.51  #Define  : 0
% 3.05/1.51  #Split   : 1
% 3.05/1.51  #Chain   : 0
% 3.05/1.51  #Close   : 0
% 3.05/1.51  
% 3.05/1.51  Ordering : KBO
% 3.05/1.51  
% 3.05/1.51  Simplification rules
% 3.05/1.51  ----------------------
% 3.05/1.51  #Subsume      : 68
% 3.05/1.51  #Demod        : 127
% 3.05/1.51  #Tautology    : 81
% 3.05/1.51  #SimpNegUnit  : 3
% 3.05/1.51  #BackRed      : 3
% 3.05/1.51  
% 3.05/1.51  #Partial instantiations: 0
% 3.05/1.51  #Strategies tried      : 1
% 3.05/1.51  
% 3.05/1.51  Timing (in seconds)
% 3.05/1.51  ----------------------
% 3.05/1.51  Preprocessing        : 0.27
% 3.05/1.51  Parsing              : 0.16
% 3.05/1.51  CNF conversion       : 0.02
% 3.05/1.51  Main loop            : 0.47
% 3.05/1.51  Inferencing          : 0.20
% 3.05/1.51  Reduction            : 0.13
% 3.05/1.51  Demodulation         : 0.10
% 3.05/1.51  BG Simplification    : 0.02
% 3.05/1.51  Subsumption          : 0.08
% 3.05/1.51  Abstraction          : 0.02
% 3.05/1.51  MUC search           : 0.00
% 3.05/1.51  Cooper               : 0.00
% 3.05/1.51  Total                : 0.77
% 3.05/1.51  Index Insertion      : 0.00
% 3.05/1.51  Index Deletion       : 0.00
% 3.05/1.51  Index Matching       : 0.00
% 3.05/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
