%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:06 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 136 expanded)
%              Number of leaves         :   32 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 207 expanded)
%              Number of equality atoms :   30 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    ! [A_46,D_49,C_48] :
      ( r2_hidden(k4_tarski(A_46,D_49),k2_zfmisc_1(C_48,k1_tarski(D_49)))
      | ~ r2_hidden(A_46,C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_350,plain,(
    ! [B_109,D_110,A_111,C_112] :
      ( r2_hidden(B_109,D_110)
      | ~ r2_hidden(k4_tarski(A_111,B_109),k2_zfmisc_1(k1_tarski(C_112),D_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_358,plain,(
    ! [D_49,A_46,C_112] :
      ( r2_hidden(D_49,k1_tarski(D_49))
      | ~ r2_hidden(A_46,k1_tarski(C_112)) ) ),
    inference(resolution,[status(thm)],[c_48,c_350])).

tff(c_360,plain,(
    ! [A_113,C_114] : ~ r2_hidden(A_113,k1_tarski(C_114)) ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_379,plain,(
    ! [C_114] : k1_tarski(C_114) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_360])).

tff(c_359,plain,(
    ! [A_46,C_112] : ~ r2_hidden(A_46,k1_tarski(C_112)) ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_380,plain,(
    ! [A_46] : ~ r2_hidden(A_46,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_359])).

tff(c_58,plain,
    ( k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_119,plain,(
    k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_386,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_119])).

tff(c_42,plain,(
    ! [C_44,B_43,D_45] :
      ( r2_hidden(k4_tarski(C_44,B_43),k2_zfmisc_1(k1_tarski(C_44),D_45))
      | ~ r2_hidden(B_43,D_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_477,plain,(
    ! [C_135,B_136,D_137] :
      ( r2_hidden(k4_tarski(C_135,B_136),k2_zfmisc_1(k1_xboole_0,D_137))
      | ~ r2_hidden(B_136,D_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_42])).

tff(c_485,plain,(
    ! [C_135,B_136] :
      ( r2_hidden(k4_tarski(C_135,B_136),k1_xboole_0)
      | ~ r2_hidden(B_136,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_477])).

tff(c_489,plain,(
    ! [B_138] : ~ r2_hidden(B_138,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_380,c_485])).

tff(c_501,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_489])).

tff(c_507,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_501])).

tff(c_509,plain,(
    ! [D_139] : r2_hidden(D_139,k1_tarski(D_139)) ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_26,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_124,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_124])).

tff(c_137,plain,(
    ! [A_73] : k4_xboole_0(A_73,A_73) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_133])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    ! [D_6,A_73] :
      ( ~ r2_hidden(D_6,A_73)
      | ~ r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_4])).

tff(c_521,plain,(
    ! [D_139] : ~ r2_hidden(D_139,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_509,c_145])).

tff(c_645,plain,(
    ! [C_158,B_159,D_160] :
      ( r2_hidden(k4_tarski(C_158,B_159),k2_zfmisc_1(k1_tarski(C_158),D_160))
      | ~ r2_hidden(B_159,D_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_662,plain,(
    ! [B_159] :
      ( r2_hidden(k4_tarski('#skF_6',B_159),k1_xboole_0)
      | ~ r2_hidden(B_159,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_645])).

tff(c_670,plain,(
    ! [B_161] : ~ r2_hidden(B_161,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_521,c_662])).

tff(c_682,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_670])).

tff(c_688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_682])).

tff(c_689,plain,(
    k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_894,plain,(
    ! [A_197,D_198,C_199] :
      ( r2_hidden(k4_tarski(A_197,D_198),k2_zfmisc_1(C_199,k1_tarski(D_198)))
      | ~ r2_hidden(A_197,C_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_906,plain,(
    ! [A_197] :
      ( r2_hidden(k4_tarski(A_197,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden(A_197,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_894])).

tff(c_695,plain,(
    ! [A_162,B_163] : k5_xboole_0(A_162,k3_xboole_0(A_162,B_163)) = k4_xboole_0(A_162,B_163) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_704,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_695])).

tff(c_708,plain,(
    ! [A_164] : k4_xboole_0(A_164,A_164) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_704])).

tff(c_716,plain,(
    ! [D_6,A_164] :
      ( ~ r2_hidden(D_6,A_164)
      | ~ r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_4])).

tff(c_982,plain,(
    ! [A_206,D_207,C_208] :
      ( ~ r2_hidden(k4_tarski(A_206,D_207),k1_xboole_0)
      | ~ r2_hidden(A_206,C_208) ) ),
    inference(resolution,[status(thm)],[c_894,c_716])).

tff(c_995,plain,(
    ! [A_213,C_214] :
      ( ~ r2_hidden(A_213,C_214)
      | ~ r2_hidden(A_213,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_906,c_982])).

tff(c_1017,plain,(
    ! [A_215] :
      ( ~ r2_hidden('#skF_3'(A_215),'#skF_5')
      | k1_xboole_0 = A_215 ) ),
    inference(resolution,[status(thm)],[c_22,c_995])).

tff(c_1028,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_1017])).

tff(c_1033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_1028])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.42  
% 2.86/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.43  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.86/1.43  
% 2.86/1.43  %Foreground sorts:
% 2.86/1.43  
% 2.86/1.43  
% 2.86/1.43  %Background operators:
% 2.86/1.43  
% 2.86/1.43  
% 2.86/1.43  %Foreground operators:
% 2.86/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.86/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.86/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.86/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.86/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.86/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.86/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.86/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.43  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.86/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.86/1.43  
% 2.86/1.44  tff(f_98, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.86/1.44  tff(f_45, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.86/1.44  tff(f_75, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.86/1.44  tff(f_69, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.86/1.44  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.86/1.44  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.86/1.44  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.86/1.44  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.86/1.44  tff(c_60, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.44  tff(c_22, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.86/1.44  tff(c_48, plain, (![A_46, D_49, C_48]: (r2_hidden(k4_tarski(A_46, D_49), k2_zfmisc_1(C_48, k1_tarski(D_49))) | ~r2_hidden(A_46, C_48))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.86/1.44  tff(c_350, plain, (![B_109, D_110, A_111, C_112]: (r2_hidden(B_109, D_110) | ~r2_hidden(k4_tarski(A_111, B_109), k2_zfmisc_1(k1_tarski(C_112), D_110)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.86/1.44  tff(c_358, plain, (![D_49, A_46, C_112]: (r2_hidden(D_49, k1_tarski(D_49)) | ~r2_hidden(A_46, k1_tarski(C_112)))), inference(resolution, [status(thm)], [c_48, c_350])).
% 2.86/1.44  tff(c_360, plain, (![A_113, C_114]: (~r2_hidden(A_113, k1_tarski(C_114)))), inference(splitLeft, [status(thm)], [c_358])).
% 2.86/1.44  tff(c_379, plain, (![C_114]: (k1_tarski(C_114)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_360])).
% 2.86/1.44  tff(c_359, plain, (![A_46, C_112]: (~r2_hidden(A_46, k1_tarski(C_112)))), inference(splitLeft, [status(thm)], [c_358])).
% 2.86/1.44  tff(c_380, plain, (![A_46]: (~r2_hidden(A_46, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_359])).
% 2.86/1.44  tff(c_58, plain, (k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.44  tff(c_119, plain, (k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 2.86/1.44  tff(c_386, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_379, c_119])).
% 2.86/1.44  tff(c_42, plain, (![C_44, B_43, D_45]: (r2_hidden(k4_tarski(C_44, B_43), k2_zfmisc_1(k1_tarski(C_44), D_45)) | ~r2_hidden(B_43, D_45))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.86/1.44  tff(c_477, plain, (![C_135, B_136, D_137]: (r2_hidden(k4_tarski(C_135, B_136), k2_zfmisc_1(k1_xboole_0, D_137)) | ~r2_hidden(B_136, D_137))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_42])).
% 2.86/1.44  tff(c_485, plain, (![C_135, B_136]: (r2_hidden(k4_tarski(C_135, B_136), k1_xboole_0) | ~r2_hidden(B_136, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_386, c_477])).
% 2.86/1.44  tff(c_489, plain, (![B_138]: (~r2_hidden(B_138, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_380, c_485])).
% 2.86/1.44  tff(c_501, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_489])).
% 2.86/1.44  tff(c_507, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_501])).
% 2.86/1.44  tff(c_509, plain, (![D_139]: (r2_hidden(D_139, k1_tarski(D_139)))), inference(splitRight, [status(thm)], [c_358])).
% 2.86/1.44  tff(c_26, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.86/1.44  tff(c_20, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.86/1.44  tff(c_124, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.86/1.44  tff(c_133, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_124])).
% 2.86/1.44  tff(c_137, plain, (![A_73]: (k4_xboole_0(A_73, A_73)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_133])).
% 2.86/1.44  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.86/1.44  tff(c_145, plain, (![D_6, A_73]: (~r2_hidden(D_6, A_73) | ~r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_137, c_4])).
% 2.86/1.44  tff(c_521, plain, (![D_139]: (~r2_hidden(D_139, k1_xboole_0))), inference(resolution, [status(thm)], [c_509, c_145])).
% 2.86/1.44  tff(c_645, plain, (![C_158, B_159, D_160]: (r2_hidden(k4_tarski(C_158, B_159), k2_zfmisc_1(k1_tarski(C_158), D_160)) | ~r2_hidden(B_159, D_160))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.86/1.44  tff(c_662, plain, (![B_159]: (r2_hidden(k4_tarski('#skF_6', B_159), k1_xboole_0) | ~r2_hidden(B_159, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_645])).
% 2.86/1.44  tff(c_670, plain, (![B_161]: (~r2_hidden(B_161, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_521, c_662])).
% 2.86/1.44  tff(c_682, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_670])).
% 2.86/1.44  tff(c_688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_682])).
% 2.86/1.44  tff(c_689, plain, (k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 2.86/1.44  tff(c_894, plain, (![A_197, D_198, C_199]: (r2_hidden(k4_tarski(A_197, D_198), k2_zfmisc_1(C_199, k1_tarski(D_198))) | ~r2_hidden(A_197, C_199))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.86/1.44  tff(c_906, plain, (![A_197]: (r2_hidden(k4_tarski(A_197, '#skF_6'), k1_xboole_0) | ~r2_hidden(A_197, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_689, c_894])).
% 2.86/1.44  tff(c_695, plain, (![A_162, B_163]: (k5_xboole_0(A_162, k3_xboole_0(A_162, B_163))=k4_xboole_0(A_162, B_163))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.86/1.44  tff(c_704, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_695])).
% 2.86/1.44  tff(c_708, plain, (![A_164]: (k4_xboole_0(A_164, A_164)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_704])).
% 2.86/1.44  tff(c_716, plain, (![D_6, A_164]: (~r2_hidden(D_6, A_164) | ~r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_708, c_4])).
% 2.86/1.44  tff(c_982, plain, (![A_206, D_207, C_208]: (~r2_hidden(k4_tarski(A_206, D_207), k1_xboole_0) | ~r2_hidden(A_206, C_208))), inference(resolution, [status(thm)], [c_894, c_716])).
% 2.86/1.44  tff(c_995, plain, (![A_213, C_214]: (~r2_hidden(A_213, C_214) | ~r2_hidden(A_213, '#skF_5'))), inference(resolution, [status(thm)], [c_906, c_982])).
% 2.86/1.44  tff(c_1017, plain, (![A_215]: (~r2_hidden('#skF_3'(A_215), '#skF_5') | k1_xboole_0=A_215)), inference(resolution, [status(thm)], [c_22, c_995])).
% 2.86/1.44  tff(c_1028, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_1017])).
% 2.86/1.44  tff(c_1033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_1028])).
% 2.86/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.44  
% 2.86/1.44  Inference rules
% 2.86/1.44  ----------------------
% 2.86/1.44  #Ref     : 0
% 2.86/1.44  #Sup     : 214
% 2.86/1.44  #Fact    : 0
% 2.86/1.44  #Define  : 0
% 2.86/1.44  #Split   : 2
% 2.86/1.44  #Chain   : 0
% 2.86/1.44  #Close   : 0
% 2.86/1.44  
% 2.86/1.44  Ordering : KBO
% 2.86/1.44  
% 2.86/1.44  Simplification rules
% 2.86/1.44  ----------------------
% 2.86/1.44  #Subsume      : 64
% 2.86/1.44  #Demod        : 45
% 2.86/1.44  #Tautology    : 101
% 2.86/1.44  #SimpNegUnit  : 9
% 2.86/1.44  #BackRed      : 7
% 2.86/1.44  
% 2.86/1.44  #Partial instantiations: 0
% 2.86/1.44  #Strategies tried      : 1
% 2.86/1.44  
% 2.86/1.44  Timing (in seconds)
% 2.86/1.44  ----------------------
% 3.14/1.44  Preprocessing        : 0.34
% 3.14/1.44  Parsing              : 0.18
% 3.14/1.44  CNF conversion       : 0.03
% 3.14/1.44  Main loop            : 0.33
% 3.14/1.44  Inferencing          : 0.13
% 3.14/1.44  Reduction            : 0.09
% 3.14/1.44  Demodulation         : 0.06
% 3.14/1.44  BG Simplification    : 0.02
% 3.14/1.44  Subsumption          : 0.06
% 3.14/1.44  Abstraction          : 0.02
% 3.14/1.44  MUC search           : 0.00
% 3.14/1.44  Cooper               : 0.00
% 3.14/1.44  Total                : 0.70
% 3.14/1.44  Index Insertion      : 0.00
% 3.14/1.44  Index Deletion       : 0.00
% 3.14/1.44  Index Matching       : 0.00
% 3.14/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
