%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:09 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   68 (  74 expanded)
%              Number of leaves         :   38 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   57 (  67 expanded)
%              Number of equality atoms :   47 (  55 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_85,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_80,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_78,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_62,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_64,plain,(
    ! [A_40,B_41,C_42,D_43] : k3_enumset1(A_40,A_40,B_41,C_42,D_43) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_647,plain,(
    ! [E_149,B_147,A_148,D_146,C_150] : k2_xboole_0(k2_enumset1(A_148,B_147,C_150,D_146),k1_tarski(E_149)) = k3_enumset1(A_148,B_147,C_150,D_146,E_149) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_656,plain,(
    ! [A_37,B_38,C_39,E_149] : k3_enumset1(A_37,A_37,B_38,C_39,E_149) = k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(E_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_647])).

tff(c_672,plain,(
    ! [A_156,B_157,C_158,E_159] : k2_xboole_0(k1_enumset1(A_156,B_157,C_158),k1_tarski(E_159)) = k2_enumset1(A_156,B_157,C_158,E_159) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_656])).

tff(c_696,plain,(
    ! [A_35,B_36,E_159] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(E_159)) = k2_enumset1(A_35,A_35,B_36,E_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_672])).

tff(c_700,plain,(
    ! [A_160,B_161,E_162] : k2_xboole_0(k2_tarski(A_160,B_161),k1_tarski(E_162)) = k1_enumset1(A_160,B_161,E_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_696])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [A_67,B_68] : k4_xboole_0(k1_tarski(A_67),k2_tarski(A_67,B_68)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_322,plain,(
    ! [A_102,B_103] : k3_xboole_0(k1_tarski(A_102),k2_tarski(A_102,B_103)) = k1_tarski(A_102) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_328,plain,(
    ! [A_102,B_103] : k5_xboole_0(k1_tarski(A_102),k1_tarski(A_102)) = k4_xboole_0(k1_tarski(A_102),k2_tarski(A_102,B_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_2])).

tff(c_336,plain,(
    ! [A_102] : k5_xboole_0(k1_tarski(A_102),k1_tarski(A_102)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_328])).

tff(c_82,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_131,plain,(
    ! [A_88,B_89] :
      ( k3_xboole_0(A_88,B_89) = A_88
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_131])).

tff(c_195,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_2])).

tff(c_372,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_195])).

tff(c_8,plain,(
    ! [A_6,B_7] : k5_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_376,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_8])).

tff(c_379,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_376])).

tff(c_706,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_379])).

tff(c_12,plain,(
    ! [E_14,A_8,B_9] : r2_hidden(E_14,k1_enumset1(A_8,B_9,E_14)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_746,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_12])).

tff(c_34,plain,(
    ! [D_20,B_16,A_15] :
      ( D_20 = B_16
      | D_20 = A_15
      | ~ r2_hidden(D_20,k2_tarski(A_15,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_767,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_746,c_34])).

tff(c_771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_767])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:00:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.52  
% 2.89/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.53  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 2.99/1.53  
% 2.99/1.53  %Foreground sorts:
% 2.99/1.53  
% 2.99/1.53  
% 2.99/1.53  %Background operators:
% 2.99/1.53  
% 2.99/1.53  
% 2.99/1.53  %Foreground operators:
% 2.99/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.99/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.99/1.53  tff('#skF_7', type, '#skF_7': $i).
% 2.99/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.99/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.53  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.99/1.53  tff('#skF_6', type, '#skF_6': $i).
% 2.99/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.99/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.99/1.53  
% 2.99/1.54  tff(f_95, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.99/1.54  tff(f_71, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.99/1.54  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.99/1.54  tff(f_73, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.99/1.54  tff(f_65, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 2.99/1.54  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.99/1.54  tff(f_85, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 2.99/1.54  tff(f_83, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.99/1.54  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.99/1.54  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.99/1.54  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.99/1.54  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.99/1.54  tff(f_59, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.99/1.54  tff(c_80, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.54  tff(c_78, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.54  tff(c_62, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.99/1.54  tff(c_60, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.99/1.54  tff(c_64, plain, (![A_40, B_41, C_42, D_43]: (k3_enumset1(A_40, A_40, B_41, C_42, D_43)=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.99/1.54  tff(c_647, plain, (![E_149, B_147, A_148, D_146, C_150]: (k2_xboole_0(k2_enumset1(A_148, B_147, C_150, D_146), k1_tarski(E_149))=k3_enumset1(A_148, B_147, C_150, D_146, E_149))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.99/1.54  tff(c_656, plain, (![A_37, B_38, C_39, E_149]: (k3_enumset1(A_37, A_37, B_38, C_39, E_149)=k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(E_149)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_647])).
% 2.99/1.54  tff(c_672, plain, (![A_156, B_157, C_158, E_159]: (k2_xboole_0(k1_enumset1(A_156, B_157, C_158), k1_tarski(E_159))=k2_enumset1(A_156, B_157, C_158, E_159))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_656])).
% 2.99/1.54  tff(c_696, plain, (![A_35, B_36, E_159]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(E_159))=k2_enumset1(A_35, A_35, B_36, E_159))), inference(superposition, [status(thm), theory('equality')], [c_60, c_672])).
% 2.99/1.54  tff(c_700, plain, (![A_160, B_161, E_162]: (k2_xboole_0(k2_tarski(A_160, B_161), k1_tarski(E_162))=k1_enumset1(A_160, B_161, E_162))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_696])).
% 2.99/1.54  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.99/1.54  tff(c_76, plain, (![A_67, B_68]: (k4_xboole_0(k1_tarski(A_67), k2_tarski(A_67, B_68))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.99/1.54  tff(c_322, plain, (![A_102, B_103]: (k3_xboole_0(k1_tarski(A_102), k2_tarski(A_102, B_103))=k1_tarski(A_102))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.99/1.54  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.99/1.54  tff(c_328, plain, (![A_102, B_103]: (k5_xboole_0(k1_tarski(A_102), k1_tarski(A_102))=k4_xboole_0(k1_tarski(A_102), k2_tarski(A_102, B_103)))), inference(superposition, [status(thm), theory('equality')], [c_322, c_2])).
% 2.99/1.54  tff(c_336, plain, (![A_102]: (k5_xboole_0(k1_tarski(A_102), k1_tarski(A_102))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_328])).
% 2.99/1.54  tff(c_82, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.54  tff(c_131, plain, (![A_88, B_89]: (k3_xboole_0(A_88, B_89)=A_88 | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.54  tff(c_135, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_82, c_131])).
% 2.99/1.54  tff(c_195, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_2])).
% 2.99/1.54  tff(c_372, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_336, c_195])).
% 2.99/1.54  tff(c_8, plain, (![A_6, B_7]: (k5_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.99/1.54  tff(c_376, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_372, c_8])).
% 2.99/1.54  tff(c_379, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_376])).
% 2.99/1.54  tff(c_706, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_700, c_379])).
% 2.99/1.54  tff(c_12, plain, (![E_14, A_8, B_9]: (r2_hidden(E_14, k1_enumset1(A_8, B_9, E_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.99/1.54  tff(c_746, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_706, c_12])).
% 2.99/1.54  tff(c_34, plain, (![D_20, B_16, A_15]: (D_20=B_16 | D_20=A_15 | ~r2_hidden(D_20, k2_tarski(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.99/1.54  tff(c_767, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_746, c_34])).
% 2.99/1.54  tff(c_771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_767])).
% 2.99/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.54  
% 2.99/1.54  Inference rules
% 2.99/1.54  ----------------------
% 2.99/1.54  #Ref     : 0
% 2.99/1.54  #Sup     : 171
% 2.99/1.54  #Fact    : 0
% 2.99/1.54  #Define  : 0
% 2.99/1.54  #Split   : 0
% 2.99/1.54  #Chain   : 0
% 2.99/1.54  #Close   : 0
% 2.99/1.54  
% 2.99/1.54  Ordering : KBO
% 2.99/1.54  
% 2.99/1.54  Simplification rules
% 2.99/1.54  ----------------------
% 2.99/1.54  #Subsume      : 16
% 2.99/1.54  #Demod        : 64
% 2.99/1.54  #Tautology    : 120
% 2.99/1.54  #SimpNegUnit  : 1
% 2.99/1.54  #BackRed      : 0
% 2.99/1.54  
% 2.99/1.54  #Partial instantiations: 0
% 2.99/1.54  #Strategies tried      : 1
% 2.99/1.54  
% 2.99/1.54  Timing (in seconds)
% 2.99/1.54  ----------------------
% 2.99/1.54  Preprocessing        : 0.37
% 2.99/1.54  Parsing              : 0.19
% 2.99/1.54  CNF conversion       : 0.03
% 2.99/1.54  Main loop            : 0.32
% 2.99/1.54  Inferencing          : 0.11
% 2.99/1.54  Reduction            : 0.12
% 2.99/1.54  Demodulation         : 0.09
% 2.99/1.54  BG Simplification    : 0.02
% 2.99/1.54  Subsumption          : 0.06
% 2.99/1.54  Abstraction          : 0.02
% 2.99/1.54  MUC search           : 0.00
% 2.99/1.54  Cooper               : 0.00
% 2.99/1.54  Total                : 0.73
% 2.99/1.55  Index Insertion      : 0.00
% 2.99/1.55  Index Deletion       : 0.00
% 2.99/1.55  Index Matching       : 0.00
% 2.99/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
