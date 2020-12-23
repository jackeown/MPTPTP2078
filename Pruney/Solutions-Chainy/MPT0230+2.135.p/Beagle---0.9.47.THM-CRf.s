%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:13 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   71 (  78 expanded)
%              Number of leaves         :   37 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :   73 (  84 expanded)
%              Number of equality atoms :   41 (  50 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_77,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_64,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_62,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_26,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_207,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_224,plain,(
    ! [A_19,C_78] :
      ( ~ r1_xboole_0(A_19,k1_xboole_0)
      | ~ r2_hidden(C_78,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_207])).

tff(c_229,plain,(
    ! [C_79] : ~ r2_hidden(C_79,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_224])).

tff(c_260,plain,(
    ! [B_82] : r1_xboole_0(k1_xboole_0,B_82) ),
    inference(resolution,[status(thm)],[c_12,c_229])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_292,plain,(
    ! [B_85] : k3_xboole_0(k1_xboole_0,B_85) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_260,c_2])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_297,plain,(
    ! [B_85] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_18])).

tff(c_326,plain,(
    ! [B_86] : k4_xboole_0(k1_xboole_0,B_86) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_297])).

tff(c_30,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_335,plain,(
    ! [B_86] : k5_xboole_0(B_86,k1_xboole_0) = k2_xboole_0(B_86,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_30])).

tff(c_355,plain,(
    ! [B_87] : k2_xboole_0(B_87,k1_xboole_0) = B_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_335])).

tff(c_24,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_365,plain,(
    ! [B_87] : k4_xboole_0(B_87,B_87) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_24])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_241,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_253,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_241])).

tff(c_458,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_253])).

tff(c_66,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_139,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_143,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_139])).

tff(c_250,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_241])).

tff(c_516,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_250])).

tff(c_58,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | k4_xboole_0(k1_tarski(A_42),B_43) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_532,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_58])).

tff(c_862,plain,(
    ! [D_120,B_121,A_122] :
      ( D_120 = B_121
      | D_120 = A_122
      | ~ r2_hidden(D_120,k2_tarski(A_122,B_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_865,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_532,c_862])).

tff(c_886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_62,c_865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:03:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.43  
% 2.99/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 2.99/1.43  
% 2.99/1.43  %Foreground sorts:
% 2.99/1.43  
% 2.99/1.43  
% 2.99/1.43  %Background operators:
% 2.99/1.43  
% 2.99/1.43  
% 2.99/1.43  %Foreground operators:
% 2.99/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.99/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.99/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.99/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.99/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.99/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.99/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.99/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.99/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.99/1.44  
% 2.99/1.45  tff(f_110, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.99/1.45  tff(f_75, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.99/1.45  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.99/1.45  tff(f_77, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.99/1.45  tff(f_71, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.99/1.45  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.99/1.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.99/1.45  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.99/1.45  tff(f_79, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.99/1.45  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.99/1.45  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.99/1.45  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.99/1.45  tff(f_100, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.99/1.45  tff(f_88, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.99/1.45  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.99/1.45  tff(c_62, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.99/1.45  tff(c_26, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.99/1.45  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.99/1.45  tff(c_28, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.99/1.45  tff(c_22, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.99/1.45  tff(c_207, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.99/1.45  tff(c_224, plain, (![A_19, C_78]: (~r1_xboole_0(A_19, k1_xboole_0) | ~r2_hidden(C_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_207])).
% 2.99/1.45  tff(c_229, plain, (![C_79]: (~r2_hidden(C_79, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_224])).
% 2.99/1.45  tff(c_260, plain, (![B_82]: (r1_xboole_0(k1_xboole_0, B_82))), inference(resolution, [status(thm)], [c_12, c_229])).
% 2.99/1.45  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.45  tff(c_292, plain, (![B_85]: (k3_xboole_0(k1_xboole_0, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_260, c_2])).
% 2.99/1.45  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.99/1.45  tff(c_297, plain, (![B_85]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_85))), inference(superposition, [status(thm), theory('equality')], [c_292, c_18])).
% 2.99/1.45  tff(c_326, plain, (![B_86]: (k4_xboole_0(k1_xboole_0, B_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_297])).
% 2.99/1.45  tff(c_30, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.99/1.45  tff(c_335, plain, (![B_86]: (k5_xboole_0(B_86, k1_xboole_0)=k2_xboole_0(B_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_326, c_30])).
% 2.99/1.45  tff(c_355, plain, (![B_87]: (k2_xboole_0(B_87, k1_xboole_0)=B_87)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_335])).
% 2.99/1.45  tff(c_24, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k2_xboole_0(A_20, B_21))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.99/1.45  tff(c_365, plain, (![B_87]: (k4_xboole_0(B_87, B_87)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_355, c_24])).
% 2.99/1.45  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.45  tff(c_241, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.99/1.45  tff(c_253, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_241])).
% 2.99/1.45  tff(c_458, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_365, c_253])).
% 2.99/1.45  tff(c_66, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.99/1.45  tff(c_139, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.99/1.45  tff(c_143, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_66, c_139])).
% 2.99/1.45  tff(c_250, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_241])).
% 2.99/1.45  tff(c_516, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_458, c_250])).
% 2.99/1.45  tff(c_58, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | k4_xboole_0(k1_tarski(A_42), B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.99/1.45  tff(c_532, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_516, c_58])).
% 2.99/1.45  tff(c_862, plain, (![D_120, B_121, A_122]: (D_120=B_121 | D_120=A_122 | ~r2_hidden(D_120, k2_tarski(A_122, B_121)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.99/1.45  tff(c_865, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_532, c_862])).
% 2.99/1.45  tff(c_886, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_62, c_865])).
% 2.99/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.45  
% 2.99/1.45  Inference rules
% 2.99/1.45  ----------------------
% 2.99/1.45  #Ref     : 0
% 2.99/1.45  #Sup     : 190
% 2.99/1.45  #Fact    : 0
% 2.99/1.45  #Define  : 0
% 2.99/1.45  #Split   : 1
% 2.99/1.45  #Chain   : 0
% 2.99/1.45  #Close   : 0
% 2.99/1.45  
% 2.99/1.45  Ordering : KBO
% 2.99/1.45  
% 2.99/1.45  Simplification rules
% 2.99/1.45  ----------------------
% 2.99/1.45  #Subsume      : 35
% 2.99/1.45  #Demod        : 43
% 2.99/1.45  #Tautology    : 118
% 2.99/1.45  #SimpNegUnit  : 15
% 2.99/1.45  #BackRed      : 0
% 2.99/1.45  
% 2.99/1.45  #Partial instantiations: 0
% 2.99/1.45  #Strategies tried      : 1
% 2.99/1.45  
% 2.99/1.45  Timing (in seconds)
% 2.99/1.45  ----------------------
% 2.99/1.45  Preprocessing        : 0.34
% 2.99/1.45  Parsing              : 0.17
% 2.99/1.45  CNF conversion       : 0.03
% 2.99/1.45  Main loop            : 0.33
% 2.99/1.45  Inferencing          : 0.12
% 2.99/1.45  Reduction            : 0.11
% 2.99/1.45  Demodulation         : 0.08
% 2.99/1.45  BG Simplification    : 0.02
% 2.99/1.45  Subsumption          : 0.06
% 2.99/1.45  Abstraction          : 0.02
% 2.99/1.45  MUC search           : 0.00
% 2.99/1.45  Cooper               : 0.00
% 2.99/1.45  Total                : 0.70
% 2.99/1.45  Index Insertion      : 0.00
% 2.99/1.45  Index Deletion       : 0.00
% 2.99/1.45  Index Matching       : 0.00
% 2.99/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
