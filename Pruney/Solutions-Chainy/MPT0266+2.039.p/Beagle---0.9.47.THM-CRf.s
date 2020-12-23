%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:31 EST 2020

% Result     : Theorem 13.47s
% Output     : CNFRefutation 13.61s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 147 expanded)
%              Number of leaves         :   37 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :   75 ( 142 expanded)
%              Number of equality atoms :   50 ( 115 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_40,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_83,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_66,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_530,plain,(
    ! [A_132,B_133,C_134] : k5_xboole_0(k5_xboole_0(A_132,B_133),C_134) = k5_xboole_0(A_132,k5_xboole_0(B_133,C_134)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_666,plain,(
    ! [A_137,B_138] : k5_xboole_0(A_137,k5_xboole_0(B_138,k5_xboole_0(A_137,B_138))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_16])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_444,plain,(
    ! [A_128,B_129] : k5_xboole_0(k5_xboole_0(A_128,B_129),k2_xboole_0(A_128,B_129)) = k3_xboole_0(A_128,B_129) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_459,plain,(
    ! [A_6] : k5_xboole_0(k5_xboole_0(A_6,A_6),A_6) = k3_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_444])).

tff(c_468,plain,(
    ! [A_6] : k5_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16,c_459])).

tff(c_587,plain,(
    ! [A_14,C_134] : k5_xboole_0(A_14,k5_xboole_0(A_14,C_134)) = k5_xboole_0(k1_xboole_0,C_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_530])).

tff(c_600,plain,(
    ! [A_14,C_134] : k5_xboole_0(A_14,k5_xboole_0(A_14,C_134)) = C_134 ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_587])).

tff(c_674,plain,(
    ! [B_138,A_137] : k5_xboole_0(B_138,k5_xboole_0(A_137,B_138)) = k5_xboole_0(A_137,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_600])).

tff(c_745,plain,(
    ! [B_138,A_137] : k5_xboole_0(B_138,k5_xboole_0(A_137,B_138)) = A_137 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_674])).

tff(c_1429,plain,(
    ! [A_163,B_164,C_165,D_166] : k2_xboole_0(k2_tarski(A_163,B_164),k2_tarski(C_165,D_166)) = k2_enumset1(A_163,B_164,C_165,D_166) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1457,plain,(
    ! [C_167,D_168] : k2_enumset1(C_167,D_168,C_167,D_168) = k2_tarski(C_167,D_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_1429,c_8])).

tff(c_46,plain,(
    ! [D_31,C_30,B_29,A_28] : k2_enumset1(D_31,C_30,B_29,A_28) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1540,plain,(
    ! [D_170,C_171] : k2_enumset1(D_170,C_171,D_170,C_171) = k2_tarski(C_171,D_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_1457,c_46])).

tff(c_1439,plain,(
    ! [C_165,D_166] : k2_enumset1(C_165,D_166,C_165,D_166) = k2_tarski(C_165,D_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_1429,c_8])).

tff(c_1592,plain,(
    ! [D_177,C_178] : k2_tarski(D_177,C_178) = k2_tarski(C_178,D_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_1540,c_1439])).

tff(c_64,plain,(
    ! [A_58,B_59] : k3_tarski(k2_tarski(A_58,B_59)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1677,plain,(
    ! [D_179,C_180] : k3_tarski(k2_tarski(D_179,C_180)) = k2_xboole_0(C_180,D_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_1592,c_64])).

tff(c_1683,plain,(
    ! [D_179,C_180] : k2_xboole_0(D_179,C_180) = k2_xboole_0(C_180,D_179) ),
    inference(superposition,[status(thm),theory(equality)],[c_1677,c_64])).

tff(c_68,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(k5_xboole_0(A_15,B_16),k2_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9358,plain,(
    ! [A_13970,B_13971] : k5_xboole_0(A_13970,k5_xboole_0(B_13971,k2_xboole_0(A_13970,B_13971))) = k3_xboole_0(A_13970,B_13971) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_18])).

tff(c_43399,plain,(
    ! [B_81721,A_81722] : k5_xboole_0(B_81721,k2_xboole_0(A_81722,B_81721)) = k5_xboole_0(A_81722,k3_xboole_0(A_81722,B_81721)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9358,c_600])).

tff(c_43651,plain,(
    k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k2_tarski('#skF_4','#skF_5')) = k5_xboole_0('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_43399])).

tff(c_43683,plain,(
    k5_xboole_0('#skF_6',k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1683,c_16,c_43651])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k5_xboole_0(k5_xboole_0(A_11,B_12),C_13) = k5_xboole_0(A_11,k5_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_681,plain,(
    ! [A_137,B_138,C_13] : k5_xboole_0(A_137,k5_xboole_0(k5_xboole_0(B_138,k5_xboole_0(A_137,B_138)),C_13)) = k5_xboole_0(k1_xboole_0,C_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_14])).

tff(c_747,plain,(
    ! [A_137,B_138,C_13] : k5_xboole_0(A_137,k5_xboole_0(B_138,k5_xboole_0(A_137,k5_xboole_0(B_138,C_13)))) = C_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_468,c_681])).

tff(c_43688,plain,(
    ! [A_137] : k5_xboole_0(A_137,k5_xboole_0('#skF_6',k5_xboole_0(A_137,k1_xboole_0))) = k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_43683,c_747])).

tff(c_43903,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_12,c_43688])).

tff(c_129,plain,(
    ! [A_74,B_75] : k1_enumset1(A_74,A_74,B_75) = k2_tarski(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [E_23,A_17,B_18] : r2_hidden(E_23,k1_enumset1(A_17,B_18,E_23)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_141,plain,(
    ! [B_75,A_74] : r2_hidden(B_75,k2_tarski(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_22])).

tff(c_159,plain,(
    ! [A_83,B_84] : k3_tarski(k2_tarski(A_83,B_84)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_62,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,k3_tarski(B_57))
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9972,plain,(
    ! [A_14789,A_14790,B_14791] :
      ( r1_tarski(A_14789,k2_xboole_0(A_14790,B_14791))
      | ~ r2_hidden(A_14789,k2_tarski(A_14790,B_14791)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_62])).

tff(c_10004,plain,(
    ! [B_14927,A_14928] : r1_tarski(B_14927,k2_xboole_0(A_14928,B_14927)) ),
    inference(resolution,[status(thm)],[c_141,c_9972])).

tff(c_26,plain,(
    ! [E_23,B_18,C_19] : r2_hidden(E_23,k1_enumset1(E_23,B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_135,plain,(
    ! [A_74,B_75] : r2_hidden(A_74,k2_tarski(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_26])).

tff(c_206,plain,(
    ! [C_93,B_94,A_95] :
      ( r2_hidden(C_93,B_94)
      | ~ r2_hidden(C_93,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_224,plain,(
    ! [A_74,B_94,B_75] :
      ( r2_hidden(A_74,B_94)
      | ~ r1_tarski(k2_tarski(A_74,B_75),B_94) ) ),
    inference(resolution,[status(thm)],[c_135,c_206])).

tff(c_10059,plain,(
    ! [A_74,A_14928,B_75] : r2_hidden(A_74,k2_xboole_0(A_14928,k2_tarski(A_74,B_75))) ),
    inference(resolution,[status(thm)],[c_10004,c_224])).

tff(c_43948,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_43903,c_10059])).

tff(c_44142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_43948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n013.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 09:24:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.47/5.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.47/5.62  
% 13.47/5.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.47/5.62  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 13.47/5.62  
% 13.47/5.62  %Foreground sorts:
% 13.47/5.62  
% 13.47/5.62  
% 13.47/5.62  %Background operators:
% 13.47/5.62  
% 13.47/5.62  
% 13.47/5.62  %Foreground operators:
% 13.47/5.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.47/5.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.47/5.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.47/5.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.47/5.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.47/5.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.47/5.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.47/5.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.47/5.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.47/5.62  tff('#skF_5', type, '#skF_5': $i).
% 13.47/5.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 13.47/5.62  tff('#skF_6', type, '#skF_6': $i).
% 13.47/5.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.47/5.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.47/5.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.47/5.62  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.47/5.62  tff('#skF_4', type, '#skF_4': $i).
% 13.47/5.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.47/5.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.47/5.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 13.47/5.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.47/5.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.47/5.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.47/5.62  
% 13.61/5.64  tff(f_88, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 13.61/5.64  tff(f_38, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 13.61/5.64  tff(f_40, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 13.61/5.64  tff(f_42, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 13.61/5.64  tff(f_36, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 13.61/5.64  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 13.61/5.64  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 13.61/5.64  tff(f_61, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 13.61/5.64  tff(f_63, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 13.61/5.64  tff(f_83, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 13.61/5.64  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 13.61/5.64  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 13.61/5.64  tff(f_81, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 13.61/5.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 13.61/5.64  tff(c_66, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.61/5.64  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.61/5.64  tff(c_530, plain, (![A_132, B_133, C_134]: (k5_xboole_0(k5_xboole_0(A_132, B_133), C_134)=k5_xboole_0(A_132, k5_xboole_0(B_133, C_134)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.61/5.64  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.61/5.64  tff(c_666, plain, (![A_137, B_138]: (k5_xboole_0(A_137, k5_xboole_0(B_138, k5_xboole_0(A_137, B_138)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_530, c_16])).
% 13.61/5.64  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.61/5.64  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.61/5.64  tff(c_444, plain, (![A_128, B_129]: (k5_xboole_0(k5_xboole_0(A_128, B_129), k2_xboole_0(A_128, B_129))=k3_xboole_0(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.61/5.64  tff(c_459, plain, (![A_6]: (k5_xboole_0(k5_xboole_0(A_6, A_6), A_6)=k3_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_444])).
% 13.61/5.64  tff(c_468, plain, (![A_6]: (k5_xboole_0(k1_xboole_0, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16, c_459])).
% 13.61/5.64  tff(c_587, plain, (![A_14, C_134]: (k5_xboole_0(A_14, k5_xboole_0(A_14, C_134))=k5_xboole_0(k1_xboole_0, C_134))), inference(superposition, [status(thm), theory('equality')], [c_16, c_530])).
% 13.61/5.64  tff(c_600, plain, (![A_14, C_134]: (k5_xboole_0(A_14, k5_xboole_0(A_14, C_134))=C_134)), inference(demodulation, [status(thm), theory('equality')], [c_468, c_587])).
% 13.61/5.64  tff(c_674, plain, (![B_138, A_137]: (k5_xboole_0(B_138, k5_xboole_0(A_137, B_138))=k5_xboole_0(A_137, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_666, c_600])).
% 13.61/5.64  tff(c_745, plain, (![B_138, A_137]: (k5_xboole_0(B_138, k5_xboole_0(A_137, B_138))=A_137)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_674])).
% 13.61/5.64  tff(c_1429, plain, (![A_163, B_164, C_165, D_166]: (k2_xboole_0(k2_tarski(A_163, B_164), k2_tarski(C_165, D_166))=k2_enumset1(A_163, B_164, C_165, D_166))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.61/5.64  tff(c_1457, plain, (![C_167, D_168]: (k2_enumset1(C_167, D_168, C_167, D_168)=k2_tarski(C_167, D_168))), inference(superposition, [status(thm), theory('equality')], [c_1429, c_8])).
% 13.61/5.64  tff(c_46, plain, (![D_31, C_30, B_29, A_28]: (k2_enumset1(D_31, C_30, B_29, A_28)=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.61/5.64  tff(c_1540, plain, (![D_170, C_171]: (k2_enumset1(D_170, C_171, D_170, C_171)=k2_tarski(C_171, D_170))), inference(superposition, [status(thm), theory('equality')], [c_1457, c_46])).
% 13.61/5.64  tff(c_1439, plain, (![C_165, D_166]: (k2_enumset1(C_165, D_166, C_165, D_166)=k2_tarski(C_165, D_166))), inference(superposition, [status(thm), theory('equality')], [c_1429, c_8])).
% 13.61/5.64  tff(c_1592, plain, (![D_177, C_178]: (k2_tarski(D_177, C_178)=k2_tarski(C_178, D_177))), inference(superposition, [status(thm), theory('equality')], [c_1540, c_1439])).
% 13.61/5.64  tff(c_64, plain, (![A_58, B_59]: (k3_tarski(k2_tarski(A_58, B_59))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.61/5.64  tff(c_1677, plain, (![D_179, C_180]: (k3_tarski(k2_tarski(D_179, C_180))=k2_xboole_0(C_180, D_179))), inference(superposition, [status(thm), theory('equality')], [c_1592, c_64])).
% 13.61/5.64  tff(c_1683, plain, (![D_179, C_180]: (k2_xboole_0(D_179, C_180)=k2_xboole_0(C_180, D_179))), inference(superposition, [status(thm), theory('equality')], [c_1677, c_64])).
% 13.61/5.64  tff(c_68, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.61/5.64  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(k5_xboole_0(A_15, B_16), k2_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.61/5.64  tff(c_9358, plain, (![A_13970, B_13971]: (k5_xboole_0(A_13970, k5_xboole_0(B_13971, k2_xboole_0(A_13970, B_13971)))=k3_xboole_0(A_13970, B_13971))), inference(superposition, [status(thm), theory('equality')], [c_530, c_18])).
% 13.61/5.64  tff(c_43399, plain, (![B_81721, A_81722]: (k5_xboole_0(B_81721, k2_xboole_0(A_81722, B_81721))=k5_xboole_0(A_81722, k3_xboole_0(A_81722, B_81721)))), inference(superposition, [status(thm), theory('equality')], [c_9358, c_600])).
% 13.61/5.64  tff(c_43651, plain, (k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k2_tarski('#skF_4', '#skF_5'))=k5_xboole_0('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_43399])).
% 13.61/5.64  tff(c_43683, plain, (k5_xboole_0('#skF_6', k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1683, c_16, c_43651])).
% 13.61/5.64  tff(c_14, plain, (![A_11, B_12, C_13]: (k5_xboole_0(k5_xboole_0(A_11, B_12), C_13)=k5_xboole_0(A_11, k5_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.61/5.64  tff(c_681, plain, (![A_137, B_138, C_13]: (k5_xboole_0(A_137, k5_xboole_0(k5_xboole_0(B_138, k5_xboole_0(A_137, B_138)), C_13))=k5_xboole_0(k1_xboole_0, C_13))), inference(superposition, [status(thm), theory('equality')], [c_666, c_14])).
% 13.61/5.64  tff(c_747, plain, (![A_137, B_138, C_13]: (k5_xboole_0(A_137, k5_xboole_0(B_138, k5_xboole_0(A_137, k5_xboole_0(B_138, C_13))))=C_13)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_468, c_681])).
% 13.61/5.64  tff(c_43688, plain, (![A_137]: (k5_xboole_0(A_137, k5_xboole_0('#skF_6', k5_xboole_0(A_137, k1_xboole_0)))=k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_43683, c_747])).
% 13.61/5.64  tff(c_43903, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_745, c_12, c_43688])).
% 13.61/5.64  tff(c_129, plain, (![A_74, B_75]: (k1_enumset1(A_74, A_74, B_75)=k2_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.61/5.64  tff(c_22, plain, (![E_23, A_17, B_18]: (r2_hidden(E_23, k1_enumset1(A_17, B_18, E_23)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.61/5.64  tff(c_141, plain, (![B_75, A_74]: (r2_hidden(B_75, k2_tarski(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_22])).
% 13.61/5.64  tff(c_159, plain, (![A_83, B_84]: (k3_tarski(k2_tarski(A_83, B_84))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.61/5.64  tff(c_62, plain, (![A_56, B_57]: (r1_tarski(A_56, k3_tarski(B_57)) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.61/5.64  tff(c_9972, plain, (![A_14789, A_14790, B_14791]: (r1_tarski(A_14789, k2_xboole_0(A_14790, B_14791)) | ~r2_hidden(A_14789, k2_tarski(A_14790, B_14791)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_62])).
% 13.61/5.64  tff(c_10004, plain, (![B_14927, A_14928]: (r1_tarski(B_14927, k2_xboole_0(A_14928, B_14927)))), inference(resolution, [status(thm)], [c_141, c_9972])).
% 13.61/5.64  tff(c_26, plain, (![E_23, B_18, C_19]: (r2_hidden(E_23, k1_enumset1(E_23, B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.61/5.64  tff(c_135, plain, (![A_74, B_75]: (r2_hidden(A_74, k2_tarski(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_26])).
% 13.61/5.64  tff(c_206, plain, (![C_93, B_94, A_95]: (r2_hidden(C_93, B_94) | ~r2_hidden(C_93, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.61/5.64  tff(c_224, plain, (![A_74, B_94, B_75]: (r2_hidden(A_74, B_94) | ~r1_tarski(k2_tarski(A_74, B_75), B_94))), inference(resolution, [status(thm)], [c_135, c_206])).
% 13.61/5.64  tff(c_10059, plain, (![A_74, A_14928, B_75]: (r2_hidden(A_74, k2_xboole_0(A_14928, k2_tarski(A_74, B_75))))), inference(resolution, [status(thm)], [c_10004, c_224])).
% 13.61/5.64  tff(c_43948, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_43903, c_10059])).
% 13.61/5.64  tff(c_44142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_43948])).
% 13.61/5.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.61/5.64  
% 13.61/5.64  Inference rules
% 13.61/5.64  ----------------------
% 13.61/5.64  #Ref     : 0
% 13.61/5.64  #Sup     : 4989
% 13.61/5.64  #Fact    : 30
% 13.61/5.64  #Define  : 0
% 13.61/5.64  #Split   : 12
% 13.61/5.64  #Chain   : 0
% 13.61/5.64  #Close   : 0
% 13.61/5.64  
% 13.61/5.64  Ordering : KBO
% 13.61/5.64  
% 13.61/5.64  Simplification rules
% 13.61/5.64  ----------------------
% 13.61/5.64  #Subsume      : 409
% 13.61/5.64  #Demod        : 2981
% 13.61/5.64  #Tautology    : 1570
% 13.61/5.64  #SimpNegUnit  : 1
% 13.61/5.64  #BackRed      : 8
% 13.61/5.64  
% 13.61/5.64  #Partial instantiations: 32940
% 13.61/5.64  #Strategies tried      : 1
% 13.61/5.64  
% 13.61/5.64  Timing (in seconds)
% 13.61/5.64  ----------------------
% 13.61/5.64  Preprocessing        : 0.33
% 13.61/5.64  Parsing              : 0.17
% 13.61/5.64  CNF conversion       : 0.02
% 13.61/5.64  Main loop            : 4.56
% 13.61/5.64  Inferencing          : 1.87
% 13.61/5.64  Reduction            : 1.81
% 13.61/5.64  Demodulation         : 1.59
% 13.61/5.64  BG Simplification    : 0.14
% 13.61/5.64  Subsumption          : 0.58
% 13.61/5.64  Abstraction          : 0.16
% 13.61/5.64  MUC search           : 0.00
% 13.61/5.64  Cooper               : 0.00
% 13.61/5.64  Total                : 4.92
% 13.61/5.64  Index Insertion      : 0.00
% 13.61/5.64  Index Deletion       : 0.00
% 13.61/5.64  Index Matching       : 0.00
% 13.61/5.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
