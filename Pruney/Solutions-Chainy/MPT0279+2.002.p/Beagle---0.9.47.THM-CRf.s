%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:23 EST 2020

% Result     : Theorem 6.00s
% Output     : CNFRefutation 6.27s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 121 expanded)
%              Number of leaves         :   37 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 135 expanded)
%              Number of equality atoms :   46 (  75 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_67,axiom,(
    ! [A] : k4_enumset1(A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,B)
     => ( ( r2_hidden(C,B)
          & A != C )
        | k3_xboole_0(k2_tarski(A,C),B) = k1_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(c_14,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    ! [C_43,A_39] :
      ( r2_hidden(C_43,k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_43,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1049,plain,(
    ! [A_125,B_126,C_127] : k4_xboole_0(k3_xboole_0(A_125,B_126),C_127) = k3_xboole_0(A_125,k4_xboole_0(B_126,C_127)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1140,plain,(
    ! [A_3,C_127] : k3_xboole_0(A_3,k4_xboole_0(A_3,C_127)) = k4_xboole_0(A_3,C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1049])).

tff(c_26,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_73,plain,(
    ! [B_53,A_54] :
      ( r1_xboole_0(B_53,A_54)
      | ~ r1_xboole_0(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [B_19,A_18] : r1_xboole_0(B_19,k4_xboole_0(A_18,B_19)) ),
    inference(resolution,[status(thm)],[c_26,c_73])).

tff(c_181,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(A_79,B_80) = A_79
      | ~ r1_xboole_0(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_199,plain,(
    ! [B_19,A_18] : k4_xboole_0(B_19,k4_xboole_0(A_18,B_19)) = B_19 ),
    inference(resolution,[status(thm)],[c_76,c_181])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k3_xboole_0(A_13,B_14),C_15) = k3_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_201,plain,(
    ! [A_18,B_19] : k4_xboole_0(k4_xboole_0(A_18,B_19),B_19) = k4_xboole_0(A_18,B_19) ),
    inference(resolution,[status(thm)],[c_26,c_181])).

tff(c_24,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_xboole_0(A_16,B_17),k4_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_427,plain,(
    ! [A_92,B_93] : k4_xboole_0(k2_xboole_0(A_92,B_93),B_93) = k4_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4575,plain,(
    ! [A_214,B_215] : k4_xboole_0(k3_xboole_0(A_214,B_215),k4_xboole_0(A_214,B_215)) = k4_xboole_0(A_214,k4_xboole_0(A_214,B_215)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_427])).

tff(c_4655,plain,(
    ! [A_214,B_215] : k4_xboole_0(k4_xboole_0(A_214,k4_xboole_0(A_214,B_215)),k4_xboole_0(A_214,B_215)) = k4_xboole_0(k3_xboole_0(A_214,B_215),k4_xboole_0(A_214,B_215)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4575,c_201])).

tff(c_5011,plain,(
    ! [A_220,B_221] : k4_xboole_0(A_220,k4_xboole_0(A_220,B_221)) = k3_xboole_0(A_220,B_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_22,c_201,c_4655])).

tff(c_4817,plain,(
    ! [A_214,B_215] : k4_xboole_0(A_214,k4_xboole_0(A_214,B_215)) = k3_xboole_0(A_214,B_215) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_22,c_201,c_4655])).

tff(c_5014,plain,(
    ! [A_220,B_221] : k4_xboole_0(A_220,k3_xboole_0(A_220,B_221)) = k3_xboole_0(A_220,k4_xboole_0(A_220,B_221)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5011,c_4817])).

tff(c_5207,plain,(
    ! [A_220,B_221] : k4_xboole_0(A_220,k3_xboole_0(A_220,B_221)) = k4_xboole_0(A_220,B_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1140,c_5014])).

tff(c_1777,plain,(
    ! [C_151,D_155,B_152,A_154,E_153] : k4_enumset1(A_154,A_154,B_152,C_151,D_155,E_153) = k3_enumset1(A_154,B_152,C_151,D_155,E_153) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    ! [A_38] : k4_enumset1(A_38,A_38,A_38,A_38,A_38,A_38) = k1_tarski(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1793,plain,(
    ! [E_156] : k3_enumset1(E_156,E_156,E_156,E_156,E_156) = k1_tarski(E_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_1777,c_40])).

tff(c_38,plain,(
    ! [A_35,B_36,C_37] : k3_enumset1(A_35,A_35,A_35,B_36,C_37) = k1_enumset1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1809,plain,(
    ! [E_157] : k1_enumset1(E_157,E_157,E_157) = k1_tarski(E_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_1793,c_38])).

tff(c_32,plain,(
    ! [A_22,B_23] : k1_enumset1(A_22,A_22,B_23) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1815,plain,(
    ! [E_157] : k2_tarski(E_157,E_157) = k1_tarski(E_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_1809,c_32])).

tff(c_56,plain,(
    ! [C_48,B_47] :
      ( k3_xboole_0(k2_tarski(C_48,C_48),B_47) = k1_tarski(C_48)
      | ~ r2_hidden(C_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1105,plain,(
    ! [C_48,B_47,C_127] :
      ( k3_xboole_0(k2_tarski(C_48,C_48),k4_xboole_0(B_47,C_127)) = k4_xboole_0(k1_tarski(C_48),C_127)
      | ~ r2_hidden(C_48,B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1049])).

tff(c_11054,plain,(
    ! [C_293,B_294,C_295] :
      ( k3_xboole_0(k1_tarski(C_293),k4_xboole_0(B_294,C_295)) = k4_xboole_0(k1_tarski(C_293),C_295)
      | ~ r2_hidden(C_293,B_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1815,c_1105])).

tff(c_145,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k1_xboole_0
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_153,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_145])).

tff(c_1131,plain,(
    ! [A_125,B_126] : k3_xboole_0(A_125,k4_xboole_0(B_126,k3_xboole_0(A_125,B_126))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_1049])).

tff(c_11131,plain,(
    ! [C_293,B_294] :
      ( k4_xboole_0(k1_tarski(C_293),k3_xboole_0(k1_tarski(C_293),B_294)) = k1_xboole_0
      | ~ r2_hidden(C_293,B_294) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11054,c_1131])).

tff(c_11286,plain,(
    ! [C_296,B_297] :
      ( k4_xboole_0(k1_tarski(C_296),B_297) = k1_xboole_0
      | ~ r2_hidden(C_296,B_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5207,c_11131])).

tff(c_139,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | k4_xboole_0(A_71,B_72) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_143,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_60])).

tff(c_11621,plain,(
    ~ r2_hidden('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11286,c_143])).

tff(c_11632,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_11621])).

tff(c_11636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_11632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:57:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.00/2.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.40  
% 6.24/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 6.27/2.40  
% 6.27/2.40  %Foreground sorts:
% 6.27/2.40  
% 6.27/2.40  
% 6.27/2.40  %Background operators:
% 6.27/2.40  
% 6.27/2.40  
% 6.27/2.40  %Foreground operators:
% 6.27/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.27/2.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.27/2.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.27/2.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.27/2.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.27/2.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.27/2.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.27/2.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.27/2.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.27/2.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.27/2.40  tff('#skF_3', type, '#skF_3': $i).
% 6.27/2.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.27/2.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.27/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.27/2.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.27/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.27/2.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.27/2.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.27/2.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.27/2.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.27/2.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.27/2.40  
% 6.27/2.42  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.27/2.42  tff(f_74, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.27/2.42  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.27/2.42  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.27/2.42  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.27/2.42  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.27/2.42  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.27/2.42  tff(f_51, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 6.27/2.42  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.27/2.42  tff(f_61, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 6.27/2.42  tff(f_67, axiom, (![A]: (k4_enumset1(A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_enumset1)).
% 6.27/2.42  tff(f_65, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_enumset1)).
% 6.27/2.42  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.27/2.42  tff(f_85, axiom, (![A, B, C]: (r2_hidden(A, B) => ((r2_hidden(C, B) & ~(A = C)) | (k3_xboole_0(k2_tarski(A, C), B) = k1_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 6.27/2.42  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 6.27/2.42  tff(f_88, negated_conjecture, ~(![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 6.27/2.42  tff(c_14, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.27/2.42  tff(c_44, plain, (![C_43, A_39]: (r2_hidden(C_43, k1_zfmisc_1(A_39)) | ~r1_tarski(C_43, A_39))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.27/2.42  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.27/2.42  tff(c_1049, plain, (![A_125, B_126, C_127]: (k4_xboole_0(k3_xboole_0(A_125, B_126), C_127)=k3_xboole_0(A_125, k4_xboole_0(B_126, C_127)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.27/2.42  tff(c_1140, plain, (![A_3, C_127]: (k3_xboole_0(A_3, k4_xboole_0(A_3, C_127))=k4_xboole_0(A_3, C_127))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1049])).
% 6.27/2.42  tff(c_26, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.27/2.42  tff(c_73, plain, (![B_53, A_54]: (r1_xboole_0(B_53, A_54) | ~r1_xboole_0(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.27/2.42  tff(c_76, plain, (![B_19, A_18]: (r1_xboole_0(B_19, k4_xboole_0(A_18, B_19)))), inference(resolution, [status(thm)], [c_26, c_73])).
% 6.27/2.42  tff(c_181, plain, (![A_79, B_80]: (k4_xboole_0(A_79, B_80)=A_79 | ~r1_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.27/2.42  tff(c_199, plain, (![B_19, A_18]: (k4_xboole_0(B_19, k4_xboole_0(A_18, B_19))=B_19)), inference(resolution, [status(thm)], [c_76, c_181])).
% 6.27/2.42  tff(c_22, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k3_xboole_0(A_13, B_14), C_15)=k3_xboole_0(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.27/2.42  tff(c_201, plain, (![A_18, B_19]: (k4_xboole_0(k4_xboole_0(A_18, B_19), B_19)=k4_xboole_0(A_18, B_19))), inference(resolution, [status(thm)], [c_26, c_181])).
% 6.27/2.42  tff(c_24, plain, (![A_16, B_17]: (k2_xboole_0(k3_xboole_0(A_16, B_17), k4_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.27/2.42  tff(c_427, plain, (![A_92, B_93]: (k4_xboole_0(k2_xboole_0(A_92, B_93), B_93)=k4_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.27/2.42  tff(c_4575, plain, (![A_214, B_215]: (k4_xboole_0(k3_xboole_0(A_214, B_215), k4_xboole_0(A_214, B_215))=k4_xboole_0(A_214, k4_xboole_0(A_214, B_215)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_427])).
% 6.27/2.42  tff(c_4655, plain, (![A_214, B_215]: (k4_xboole_0(k4_xboole_0(A_214, k4_xboole_0(A_214, B_215)), k4_xboole_0(A_214, B_215))=k4_xboole_0(k3_xboole_0(A_214, B_215), k4_xboole_0(A_214, B_215)))), inference(superposition, [status(thm), theory('equality')], [c_4575, c_201])).
% 6.27/2.42  tff(c_5011, plain, (![A_220, B_221]: (k4_xboole_0(A_220, k4_xboole_0(A_220, B_221))=k3_xboole_0(A_220, B_221))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_22, c_201, c_4655])).
% 6.27/2.42  tff(c_4817, plain, (![A_214, B_215]: (k4_xboole_0(A_214, k4_xboole_0(A_214, B_215))=k3_xboole_0(A_214, B_215))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_22, c_201, c_4655])).
% 6.27/2.42  tff(c_5014, plain, (![A_220, B_221]: (k4_xboole_0(A_220, k3_xboole_0(A_220, B_221))=k3_xboole_0(A_220, k4_xboole_0(A_220, B_221)))), inference(superposition, [status(thm), theory('equality')], [c_5011, c_4817])).
% 6.27/2.42  tff(c_5207, plain, (![A_220, B_221]: (k4_xboole_0(A_220, k3_xboole_0(A_220, B_221))=k4_xboole_0(A_220, B_221))), inference(demodulation, [status(thm), theory('equality')], [c_1140, c_5014])).
% 6.27/2.42  tff(c_1777, plain, (![C_151, D_155, B_152, A_154, E_153]: (k4_enumset1(A_154, A_154, B_152, C_151, D_155, E_153)=k3_enumset1(A_154, B_152, C_151, D_155, E_153))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.27/2.42  tff(c_40, plain, (![A_38]: (k4_enumset1(A_38, A_38, A_38, A_38, A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.27/2.42  tff(c_1793, plain, (![E_156]: (k3_enumset1(E_156, E_156, E_156, E_156, E_156)=k1_tarski(E_156))), inference(superposition, [status(thm), theory('equality')], [c_1777, c_40])).
% 6.27/2.42  tff(c_38, plain, (![A_35, B_36, C_37]: (k3_enumset1(A_35, A_35, A_35, B_36, C_37)=k1_enumset1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.27/2.42  tff(c_1809, plain, (![E_157]: (k1_enumset1(E_157, E_157, E_157)=k1_tarski(E_157))), inference(superposition, [status(thm), theory('equality')], [c_1793, c_38])).
% 6.27/2.42  tff(c_32, plain, (![A_22, B_23]: (k1_enumset1(A_22, A_22, B_23)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.27/2.42  tff(c_1815, plain, (![E_157]: (k2_tarski(E_157, E_157)=k1_tarski(E_157))), inference(superposition, [status(thm), theory('equality')], [c_1809, c_32])).
% 6.27/2.42  tff(c_56, plain, (![C_48, B_47]: (k3_xboole_0(k2_tarski(C_48, C_48), B_47)=k1_tarski(C_48) | ~r2_hidden(C_48, B_47))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.27/2.42  tff(c_1105, plain, (![C_48, B_47, C_127]: (k3_xboole_0(k2_tarski(C_48, C_48), k4_xboole_0(B_47, C_127))=k4_xboole_0(k1_tarski(C_48), C_127) | ~r2_hidden(C_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1049])).
% 6.27/2.42  tff(c_11054, plain, (![C_293, B_294, C_295]: (k3_xboole_0(k1_tarski(C_293), k4_xboole_0(B_294, C_295))=k4_xboole_0(k1_tarski(C_293), C_295) | ~r2_hidden(C_293, B_294))), inference(demodulation, [status(thm), theory('equality')], [c_1815, c_1105])).
% 6.27/2.42  tff(c_145, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k1_xboole_0 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.27/2.42  tff(c_153, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_145])).
% 6.27/2.42  tff(c_1131, plain, (![A_125, B_126]: (k3_xboole_0(A_125, k4_xboole_0(B_126, k3_xboole_0(A_125, B_126)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_153, c_1049])).
% 6.27/2.42  tff(c_11131, plain, (![C_293, B_294]: (k4_xboole_0(k1_tarski(C_293), k3_xboole_0(k1_tarski(C_293), B_294))=k1_xboole_0 | ~r2_hidden(C_293, B_294))), inference(superposition, [status(thm), theory('equality')], [c_11054, c_1131])).
% 6.27/2.42  tff(c_11286, plain, (![C_296, B_297]: (k4_xboole_0(k1_tarski(C_296), B_297)=k1_xboole_0 | ~r2_hidden(C_296, B_297))), inference(demodulation, [status(thm), theory('equality')], [c_5207, c_11131])).
% 6.27/2.42  tff(c_139, plain, (![A_71, B_72]: (r1_tarski(A_71, B_72) | k4_xboole_0(A_71, B_72)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.27/2.42  tff(c_60, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.27/2.42  tff(c_143, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_139, c_60])).
% 6.27/2.42  tff(c_11621, plain, (~r2_hidden('#skF_3', k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11286, c_143])).
% 6.27/2.42  tff(c_11632, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_11621])).
% 6.27/2.42  tff(c_11636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_11632])).
% 6.27/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.42  
% 6.27/2.42  Inference rules
% 6.27/2.42  ----------------------
% 6.27/2.42  #Ref     : 0
% 6.27/2.42  #Sup     : 2929
% 6.27/2.42  #Fact    : 0
% 6.27/2.42  #Define  : 0
% 6.27/2.42  #Split   : 2
% 6.27/2.42  #Chain   : 0
% 6.27/2.42  #Close   : 0
% 6.27/2.42  
% 6.27/2.42  Ordering : KBO
% 6.27/2.42  
% 6.27/2.42  Simplification rules
% 6.27/2.42  ----------------------
% 6.27/2.42  #Subsume      : 104
% 6.27/2.42  #Demod        : 2492
% 6.27/2.42  #Tautology    : 1920
% 6.27/2.42  #SimpNegUnit  : 0
% 6.27/2.42  #BackRed      : 2
% 6.27/2.42  
% 6.27/2.42  #Partial instantiations: 0
% 6.27/2.42  #Strategies tried      : 1
% 6.27/2.42  
% 6.27/2.42  Timing (in seconds)
% 6.27/2.42  ----------------------
% 6.27/2.42  Preprocessing        : 0.35
% 6.27/2.42  Parsing              : 0.19
% 6.27/2.42  CNF conversion       : 0.02
% 6.27/2.42  Main loop            : 1.28
% 6.27/2.42  Inferencing          : 0.38
% 6.27/2.42  Reduction            : 0.55
% 6.27/2.42  Demodulation         : 0.45
% 6.27/2.42  BG Simplification    : 0.05
% 6.27/2.42  Subsumption          : 0.22
% 6.27/2.42  Abstraction          : 0.07
% 6.27/2.42  MUC search           : 0.00
% 6.27/2.42  Cooper               : 0.00
% 6.27/2.42  Total                : 1.67
% 6.27/2.42  Index Insertion      : 0.00
% 6.27/2.42  Index Deletion       : 0.00
% 6.27/2.42  Index Matching       : 0.00
% 6.27/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
