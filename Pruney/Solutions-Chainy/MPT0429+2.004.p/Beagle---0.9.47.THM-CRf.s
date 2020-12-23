%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:06 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 199 expanded)
%              Number of leaves         :   36 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :   95 ( 332 expanded)
%              Number of equality atoms :   34 (  89 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_98,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_91,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_67,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_135,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(A_69,k1_zfmisc_1(B_70))
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_92,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_143,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_135,c_92])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] : k2_enumset1(A_13,A_13,B_14,C_15) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [A_16,B_17,C_18,D_19] : k3_enumset1(A_16,A_16,B_17,C_18,D_19) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_507,plain,(
    ! [C_151,A_155,B_152,D_153,E_154] : k4_enumset1(A_155,A_155,B_152,C_151,D_153,E_154) = k3_enumset1(A_155,B_152,C_151,D_153,E_154) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [C_46,E_48,H_53,A_44,B_45,D_47] : r2_hidden(H_53,k4_enumset1(A_44,B_45,C_46,D_47,E_48,H_53)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_534,plain,(
    ! [C_158,A_159,D_156,B_157,E_160] : r2_hidden(E_160,k3_enumset1(A_159,B_157,C_158,D_156,E_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_48])).

tff(c_541,plain,(
    ! [D_161,A_162,B_163,C_164] : r2_hidden(D_161,k2_enumset1(A_162,B_163,C_164,D_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_534])).

tff(c_548,plain,(
    ! [C_165,A_166,B_167] : r2_hidden(C_165,k1_enumset1(A_166,B_167,C_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_541])).

tff(c_564,plain,(
    ! [B_174,A_175] : r2_hidden(B_174,k2_tarski(A_175,B_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_548])).

tff(c_569,plain,(
    ! [A_10] : r2_hidden(A_10,k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_564])).

tff(c_150,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73,B_74),A_73)
      | r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [C_42,A_38] :
      ( r1_tarski(C_42,A_38)
      | ~ r2_hidden(C_42,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_226,plain,(
    ! [A_126,B_127] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_126),B_127),A_126)
      | r1_tarski(k1_zfmisc_1(A_126),B_127) ) ),
    inference(resolution,[status(thm)],[c_150,c_32])).

tff(c_16,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_241,plain,(
    ! [B_128] :
      ( '#skF_1'(k1_zfmisc_1(k1_xboole_0),B_128) = k1_xboole_0
      | r1_tarski(k1_zfmisc_1(k1_xboole_0),B_128) ) ),
    inference(resolution,[status(thm)],[c_226,c_16])).

tff(c_44,plain,(
    ! [A_43] : r1_tarski(k1_tarski(A_43),k1_zfmisc_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_162,plain,(
    ! [B_75,A_76] :
      ( B_75 = A_76
      | ~ r1_tarski(B_75,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_169,plain,(
    ! [A_43] :
      ( k1_zfmisc_1(A_43) = k1_tarski(A_43)
      | ~ r1_tarski(k1_zfmisc_1(A_43),k1_tarski(A_43)) ) ),
    inference(resolution,[status(thm)],[c_44,c_162])).

tff(c_252,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)
    | '#skF_1'(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_241,c_169])).

tff(c_458,plain,(
    '#skF_1'(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_471,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_4])).

tff(c_482,plain,(
    ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_482])).

tff(c_574,plain,(
    r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_592,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_574,c_169])).

tff(c_240,plain,(
    ! [B_127] :
      ( '#skF_1'(k1_zfmisc_1(k1_xboole_0),B_127) = k1_xboole_0
      | r1_tarski(k1_zfmisc_1(k1_xboole_0),B_127) ) ),
    inference(resolution,[status(thm)],[c_226,c_16])).

tff(c_1127,plain,(
    ! [B_327] :
      ( '#skF_1'(k1_tarski(k1_xboole_0),B_327) = k1_xboole_0
      | r1_tarski(k1_tarski(k1_xboole_0),B_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_592,c_240])).

tff(c_1147,plain,(
    '#skF_1'(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1127,c_143])).

tff(c_34,plain,(
    ! [C_42,A_38] :
      ( r2_hidden(C_42,k1_zfmisc_1(A_38))
      | ~ r1_tarski(C_42,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_144,plain,(
    ! [A_71,B_72] :
      ( ~ r2_hidden('#skF_1'(A_71,B_72),B_72)
      | r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_149,plain,(
    ! [A_71,A_38] :
      ( r1_tarski(A_71,k1_zfmisc_1(A_38))
      | ~ r1_tarski('#skF_1'(A_71,k1_zfmisc_1(A_38)),A_38) ) ),
    inference(resolution,[status(thm)],[c_34,c_144])).

tff(c_1156,plain,
    ( r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_6'))
    | ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1147,c_149])).

tff(c_1171,plain,(
    r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1156])).

tff(c_1173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_1171])).

tff(c_1174,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_1636,plain,(
    ! [B_453] :
      ( '#skF_1'(k1_tarski(k1_xboole_0),B_453) = k1_xboole_0
      | r1_tarski(k1_tarski(k1_xboole_0),B_453) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1174,c_1174,c_240])).

tff(c_1656,plain,(
    '#skF_1'(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1636,c_143])).

tff(c_1676,plain,
    ( r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_6'))
    | ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1656,c_149])).

tff(c_1691,plain,(
    r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1676])).

tff(c_1693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_1691])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:13:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.72  
% 3.85/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.72  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4 > #skF_1
% 3.85/1.72  
% 3.85/1.72  %Foreground sorts:
% 3.85/1.72  
% 3.85/1.72  
% 3.85/1.72  %Background operators:
% 3.85/1.72  
% 3.85/1.72  
% 3.85/1.72  %Foreground operators:
% 3.85/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.85/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.85/1.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.85/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.85/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.85/1.72  tff('#skF_6', type, '#skF_6': $i).
% 3.85/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.85/1.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.85/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.85/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.72  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.85/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.85/1.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.85/1.72  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.85/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.85/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.72  
% 3.85/1.73  tff(f_95, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.85/1.73  tff(f_98, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 3.85/1.73  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.85/1.73  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.85/1.73  tff(f_48, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.85/1.73  tff(f_50, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.85/1.73  tff(f_52, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.85/1.73  tff(f_54, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.85/1.73  tff(f_91, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 3.85/1.73  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.85/1.73  tff(f_65, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.85/1.73  tff(f_44, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.85/1.73  tff(f_67, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 3.85/1.73  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.85/1.73  tff(c_135, plain, (![A_69, B_70]: (m1_subset_1(A_69, k1_zfmisc_1(B_70)) | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.85/1.73  tff(c_92, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.85/1.73  tff(c_143, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_135, c_92])).
% 3.85/1.73  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.85/1.73  tff(c_18, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.85/1.73  tff(c_20, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.85/1.73  tff(c_22, plain, (![A_13, B_14, C_15]: (k2_enumset1(A_13, A_13, B_14, C_15)=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.85/1.73  tff(c_24, plain, (![A_16, B_17, C_18, D_19]: (k3_enumset1(A_16, A_16, B_17, C_18, D_19)=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.85/1.73  tff(c_507, plain, (![C_151, A_155, B_152, D_153, E_154]: (k4_enumset1(A_155, A_155, B_152, C_151, D_153, E_154)=k3_enumset1(A_155, B_152, C_151, D_153, E_154))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.85/1.73  tff(c_48, plain, (![C_46, E_48, H_53, A_44, B_45, D_47]: (r2_hidden(H_53, k4_enumset1(A_44, B_45, C_46, D_47, E_48, H_53)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.85/1.73  tff(c_534, plain, (![C_158, A_159, D_156, B_157, E_160]: (r2_hidden(E_160, k3_enumset1(A_159, B_157, C_158, D_156, E_160)))), inference(superposition, [status(thm), theory('equality')], [c_507, c_48])).
% 3.85/1.73  tff(c_541, plain, (![D_161, A_162, B_163, C_164]: (r2_hidden(D_161, k2_enumset1(A_162, B_163, C_164, D_161)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_534])).
% 3.85/1.73  tff(c_548, plain, (![C_165, A_166, B_167]: (r2_hidden(C_165, k1_enumset1(A_166, B_167, C_165)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_541])).
% 3.85/1.73  tff(c_564, plain, (![B_174, A_175]: (r2_hidden(B_174, k2_tarski(A_175, B_174)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_548])).
% 3.85/1.73  tff(c_569, plain, (![A_10]: (r2_hidden(A_10, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_564])).
% 3.85/1.73  tff(c_150, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73, B_74), A_73) | r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.85/1.73  tff(c_32, plain, (![C_42, A_38]: (r1_tarski(C_42, A_38) | ~r2_hidden(C_42, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.85/1.73  tff(c_226, plain, (![A_126, B_127]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_126), B_127), A_126) | r1_tarski(k1_zfmisc_1(A_126), B_127))), inference(resolution, [status(thm)], [c_150, c_32])).
% 3.85/1.73  tff(c_16, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.85/1.73  tff(c_241, plain, (![B_128]: ('#skF_1'(k1_zfmisc_1(k1_xboole_0), B_128)=k1_xboole_0 | r1_tarski(k1_zfmisc_1(k1_xboole_0), B_128))), inference(resolution, [status(thm)], [c_226, c_16])).
% 3.85/1.73  tff(c_44, plain, (![A_43]: (r1_tarski(k1_tarski(A_43), k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.85/1.73  tff(c_162, plain, (![B_75, A_76]: (B_75=A_76 | ~r1_tarski(B_75, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.85/1.73  tff(c_169, plain, (![A_43]: (k1_zfmisc_1(A_43)=k1_tarski(A_43) | ~r1_tarski(k1_zfmisc_1(A_43), k1_tarski(A_43)))), inference(resolution, [status(thm)], [c_44, c_162])).
% 3.85/1.73  tff(c_252, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0) | '#skF_1'(k1_zfmisc_1(k1_xboole_0), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_241, c_169])).
% 3.85/1.73  tff(c_458, plain, ('#skF_1'(k1_zfmisc_1(k1_xboole_0), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_252])).
% 3.85/1.73  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.85/1.73  tff(c_471, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_458, c_4])).
% 3.85/1.73  tff(c_482, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_471])).
% 3.85/1.73  tff(c_573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_569, c_482])).
% 3.85/1.73  tff(c_574, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_tarski(k1_xboole_0))), inference(splitRight, [status(thm)], [c_471])).
% 3.85/1.73  tff(c_592, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_574, c_169])).
% 3.85/1.73  tff(c_240, plain, (![B_127]: ('#skF_1'(k1_zfmisc_1(k1_xboole_0), B_127)=k1_xboole_0 | r1_tarski(k1_zfmisc_1(k1_xboole_0), B_127))), inference(resolution, [status(thm)], [c_226, c_16])).
% 3.85/1.73  tff(c_1127, plain, (![B_327]: ('#skF_1'(k1_tarski(k1_xboole_0), B_327)=k1_xboole_0 | r1_tarski(k1_tarski(k1_xboole_0), B_327))), inference(demodulation, [status(thm), theory('equality')], [c_592, c_592, c_240])).
% 3.85/1.73  tff(c_1147, plain, ('#skF_1'(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1127, c_143])).
% 3.85/1.73  tff(c_34, plain, (![C_42, A_38]: (r2_hidden(C_42, k1_zfmisc_1(A_38)) | ~r1_tarski(C_42, A_38))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.85/1.73  tff(c_144, plain, (![A_71, B_72]: (~r2_hidden('#skF_1'(A_71, B_72), B_72) | r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.85/1.73  tff(c_149, plain, (![A_71, A_38]: (r1_tarski(A_71, k1_zfmisc_1(A_38)) | ~r1_tarski('#skF_1'(A_71, k1_zfmisc_1(A_38)), A_38))), inference(resolution, [status(thm)], [c_34, c_144])).
% 3.85/1.73  tff(c_1156, plain, (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_6')) | ~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1147, c_149])).
% 3.85/1.73  tff(c_1171, plain, (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1156])).
% 3.85/1.73  tff(c_1173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_1171])).
% 3.85/1.73  tff(c_1174, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(splitRight, [status(thm)], [c_252])).
% 3.85/1.73  tff(c_1636, plain, (![B_453]: ('#skF_1'(k1_tarski(k1_xboole_0), B_453)=k1_xboole_0 | r1_tarski(k1_tarski(k1_xboole_0), B_453))), inference(demodulation, [status(thm), theory('equality')], [c_1174, c_1174, c_240])).
% 3.85/1.73  tff(c_1656, plain, ('#skF_1'(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1636, c_143])).
% 3.85/1.73  tff(c_1676, plain, (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_6')) | ~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1656, c_149])).
% 3.85/1.73  tff(c_1691, plain, (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1676])).
% 3.85/1.73  tff(c_1693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_1691])).
% 3.85/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.73  
% 3.85/1.73  Inference rules
% 3.85/1.73  ----------------------
% 3.85/1.73  #Ref     : 0
% 3.85/1.73  #Sup     : 370
% 3.85/1.73  #Fact    : 0
% 3.85/1.73  #Define  : 0
% 3.85/1.73  #Split   : 5
% 3.85/1.73  #Chain   : 0
% 3.85/1.73  #Close   : 0
% 3.85/1.73  
% 3.85/1.73  Ordering : KBO
% 3.85/1.73  
% 3.85/1.73  Simplification rules
% 3.85/1.73  ----------------------
% 3.85/1.73  #Subsume      : 25
% 3.85/1.73  #Demod        : 120
% 3.85/1.73  #Tautology    : 160
% 3.85/1.73  #SimpNegUnit  : 13
% 3.85/1.73  #BackRed      : 16
% 3.85/1.73  
% 3.85/1.73  #Partial instantiations: 0
% 3.85/1.73  #Strategies tried      : 1
% 3.85/1.73  
% 3.85/1.73  Timing (in seconds)
% 3.85/1.73  ----------------------
% 3.85/1.74  Preprocessing        : 0.36
% 3.85/1.74  Parsing              : 0.18
% 3.85/1.74  CNF conversion       : 0.03
% 3.85/1.74  Main loop            : 0.54
% 3.85/1.74  Inferencing          : 0.20
% 3.85/1.74  Reduction            : 0.16
% 3.85/1.74  Demodulation         : 0.11
% 3.85/1.74  BG Simplification    : 0.03
% 3.85/1.74  Subsumption          : 0.11
% 3.85/1.74  Abstraction          : 0.04
% 3.85/1.74  MUC search           : 0.00
% 3.85/1.74  Cooper               : 0.00
% 3.85/1.74  Total                : 0.94
% 3.85/1.74  Index Insertion      : 0.00
% 3.85/1.74  Index Deletion       : 0.00
% 3.85/1.74  Index Matching       : 0.00
% 3.85/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
