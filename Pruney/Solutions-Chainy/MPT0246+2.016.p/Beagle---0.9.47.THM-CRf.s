%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:02 EST 2020

% Result     : Theorem 23.42s
% Output     : CNFRefutation 23.42s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 141 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :   16
%              Number of atoms          :  102 ( 297 expanded)
%              Number of equality atoms :   83 ( 237 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_46,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_59,plain,(
    ! [A_48] :
      ( r2_hidden('#skF_1'(A_48),A_48)
      | k1_xboole_0 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [C_39] :
      ( C_39 = '#skF_5'
      | ~ r2_hidden(C_39,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_63,plain,
    ( '#skF_1'('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_59,c_42])).

tff(c_66,plain,(
    '#skF_1'('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_63])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_2])).

tff(c_73,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_70])).

tff(c_28,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( '#skF_2'(A_3,B_4,C_5,D_6) = C_5
      | '#skF_2'(A_3,B_4,C_5,D_6) = B_4
      | '#skF_2'(A_3,B_4,C_5,D_6) = A_3
      | '#skF_3'(A_3,B_4,C_5,D_6) != C_5
      | k1_enumset1(A_3,B_4,C_5) = D_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_318,plain,(
    ! [B_4,C_5,D_6] :
      ( '#skF_2'(B_4,B_4,C_5,D_6) = C_5
      | '#skF_3'(B_4,B_4,C_5,D_6) != C_5
      | k1_enumset1(B_4,B_4,C_5) = D_6
      | '#skF_2'(B_4,B_4,C_5,D_6) = B_4 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_14])).

tff(c_325,plain,(
    ! [B_4,C_5,D_6] :
      ( '#skF_2'(B_4,B_4,C_5,D_6) = C_5
      | '#skF_3'(B_4,B_4,C_5,D_6) != C_5
      | k2_tarski(B_4,C_5) = D_6
      | '#skF_2'(B_4,B_4,C_5,D_6) = B_4 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_318])).

tff(c_787,plain,(
    ! [C_5,D_6] :
      ( '#skF_3'(C_5,C_5,C_5,D_6) != C_5
      | k2_tarski(C_5,C_5) = D_6
      | '#skF_2'(C_5,C_5,C_5,D_6) = C_5 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_325])).

tff(c_1250,plain,(
    ! [C_2965,D_2966] :
      ( '#skF_3'(C_2965,C_2965,C_2965,D_2966) != C_2965
      | k1_tarski(C_2965) = D_2966
      | '#skF_2'(C_2965,C_2965,C_2965,D_2966) = C_2965 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_787])).

tff(c_1532,plain,(
    ! [D_4497] :
      ( D_4497 != '#skF_4'
      | '#skF_3'('#skF_5','#skF_5','#skF_5',D_4497) != '#skF_5'
      | '#skF_2'('#skF_5','#skF_5','#skF_5',D_4497) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1250,c_46])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( ~ r2_hidden('#skF_2'(A_3,B_4,C_5,D_6),D_6)
      | '#skF_3'(A_3,B_4,C_5,D_6) != A_3
      | k1_enumset1(A_3,B_4,C_5) = D_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1565,plain,(
    ! [D_4497] :
      ( ~ r2_hidden('#skF_5',D_4497)
      | '#skF_3'('#skF_5','#skF_5','#skF_5',D_4497) != '#skF_5'
      | k1_enumset1('#skF_5','#skF_5','#skF_5') = D_4497
      | D_4497 != '#skF_4'
      | '#skF_3'('#skF_5','#skF_5','#skF_5',D_4497) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1532,c_20])).

tff(c_2654,plain,(
    ! [D_7026] :
      ( ~ r2_hidden('#skF_5',D_7026)
      | '#skF_3'('#skF_5','#skF_5','#skF_5',D_7026) != '#skF_5'
      | k1_tarski('#skF_5') = D_7026
      | D_7026 != '#skF_4'
      | '#skF_3'('#skF_5','#skF_5','#skF_5',D_7026) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_1565])).

tff(c_2699,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | '#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_73,c_2654])).

tff(c_2718,plain,(
    '#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2699])).

tff(c_4742,plain,(
    ! [A_13704,B_13705,C_13706,D_13707] :
      ( '#skF_2'(A_13704,B_13705,C_13706,D_13707) = C_13706
      | '#skF_2'(A_13704,B_13705,C_13706,D_13707) = B_13705
      | '#skF_2'(A_13704,B_13705,C_13706,D_13707) = A_13704
      | r2_hidden('#skF_3'(A_13704,B_13705,C_13706,D_13707),D_13707)
      | k1_enumset1(A_13704,B_13705,C_13706) = D_13707 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4814,plain,(
    ! [A_13978,B_13979,C_13980] :
      ( '#skF_3'(A_13978,B_13979,C_13980,'#skF_4') = '#skF_5'
      | '#skF_2'(A_13978,B_13979,C_13980,'#skF_4') = C_13980
      | '#skF_2'(A_13978,B_13979,C_13980,'#skF_4') = B_13979
      | '#skF_2'(A_13978,B_13979,C_13980,'#skF_4') = A_13978
      | k1_enumset1(A_13978,B_13979,C_13980) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_4742,c_42])).

tff(c_4977,plain,(
    ! [A_11,B_12] :
      ( '#skF_3'(A_11,A_11,B_12,'#skF_4') = '#skF_5'
      | '#skF_2'(A_11,A_11,B_12,'#skF_4') = B_12
      | '#skF_2'(A_11,A_11,B_12,'#skF_4') = A_11
      | '#skF_2'(A_11,A_11,B_12,'#skF_4') = A_11
      | k2_tarski(A_11,B_12) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4814])).

tff(c_107349,plain,(
    ! [B_12] :
      ( '#skF_3'(B_12,B_12,B_12,'#skF_4') = '#skF_5'
      | k2_tarski(B_12,B_12) = '#skF_4'
      | '#skF_2'(B_12,B_12,B_12,'#skF_4') = B_12 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_4977])).

tff(c_109504,plain,(
    ! [B_81160] :
      ( '#skF_3'(B_81160,B_81160,B_81160,'#skF_4') = '#skF_5'
      | k1_tarski(B_81160) = '#skF_4'
      | '#skF_2'(B_81160,B_81160,B_81160,'#skF_4') = B_81160 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_107349])).

tff(c_109525,plain,
    ( '#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4') = '#skF_5'
    | '#skF_2'('#skF_5','#skF_5','#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_109504,c_46])).

tff(c_110328,plain,(
    '#skF_2'('#skF_5','#skF_5','#skF_5','#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_2718,c_109525])).

tff(c_24,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( ~ r2_hidden('#skF_2'(A_3,B_4,C_5,D_6),D_6)
      | r2_hidden('#skF_3'(A_3,B_4,C_5,D_6),D_6)
      | k1_enumset1(A_3,B_4,C_5) = D_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_110645,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4'),'#skF_4')
    | k1_enumset1('#skF_5','#skF_5','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_110328,c_24])).

tff(c_110925,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4'),'#skF_4')
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_73,c_110645])).

tff(c_110926,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_110925])).

tff(c_110944,plain,(
    '#skF_3'('#skF_5','#skF_5','#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_110926,c_42])).

tff(c_110949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2718,c_110944])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:29:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.42/13.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.42/13.99  
% 23.42/13.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.42/13.99  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 23.42/13.99  
% 23.42/13.99  %Foreground sorts:
% 23.42/13.99  
% 23.42/13.99  
% 23.42/13.99  %Background operators:
% 23.42/13.99  
% 23.42/13.99  
% 23.42/13.99  %Foreground operators:
% 23.42/13.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.42/13.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.42/13.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 23.42/13.99  tff('#skF_1', type, '#skF_1': $i > $i).
% 23.42/13.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.42/13.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 23.42/13.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 23.42/13.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.42/13.99  tff('#skF_5', type, '#skF_5': $i).
% 23.42/13.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 23.42/13.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.42/13.99  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 23.42/13.99  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 23.42/13.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.42/13.99  tff('#skF_4', type, '#skF_4': $i).
% 23.42/13.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.42/13.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 23.42/13.99  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 23.42/13.99  
% 23.42/14.00  tff(f_77, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 23.42/14.00  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 23.42/14.00  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 23.42/14.00  tff(f_52, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 23.42/14.00  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 23.42/14.00  tff(c_46, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 23.42/14.00  tff(c_44, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 23.42/14.00  tff(c_59, plain, (![A_48]: (r2_hidden('#skF_1'(A_48), A_48) | k1_xboole_0=A_48)), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.42/14.00  tff(c_42, plain, (![C_39]: (C_39='#skF_5' | ~r2_hidden(C_39, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 23.42/14.00  tff(c_63, plain, ('#skF_1'('#skF_4')='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_59, c_42])).
% 23.42/14.00  tff(c_66, plain, ('#skF_1'('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_44, c_63])).
% 23.42/14.00  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.42/14.00  tff(c_70, plain, (r2_hidden('#skF_5', '#skF_4') | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_66, c_2])).
% 23.42/14.00  tff(c_73, plain, (r2_hidden('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_70])).
% 23.42/14.00  tff(c_28, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 23.42/14.00  tff(c_30, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 23.42/14.00  tff(c_14, plain, (![A_3, B_4, C_5, D_6]: ('#skF_2'(A_3, B_4, C_5, D_6)=C_5 | '#skF_2'(A_3, B_4, C_5, D_6)=B_4 | '#skF_2'(A_3, B_4, C_5, D_6)=A_3 | '#skF_3'(A_3, B_4, C_5, D_6)!=C_5 | k1_enumset1(A_3, B_4, C_5)=D_6)), inference(cnfTransformation, [status(thm)], [f_48])).
% 23.42/14.00  tff(c_318, plain, (![B_4, C_5, D_6]: ('#skF_2'(B_4, B_4, C_5, D_6)=C_5 | '#skF_3'(B_4, B_4, C_5, D_6)!=C_5 | k1_enumset1(B_4, B_4, C_5)=D_6 | '#skF_2'(B_4, B_4, C_5, D_6)=B_4)), inference(factorization, [status(thm), theory('equality')], [c_14])).
% 23.42/14.00  tff(c_325, plain, (![B_4, C_5, D_6]: ('#skF_2'(B_4, B_4, C_5, D_6)=C_5 | '#skF_3'(B_4, B_4, C_5, D_6)!=C_5 | k2_tarski(B_4, C_5)=D_6 | '#skF_2'(B_4, B_4, C_5, D_6)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_318])).
% 23.42/14.00  tff(c_787, plain, (![C_5, D_6]: ('#skF_3'(C_5, C_5, C_5, D_6)!=C_5 | k2_tarski(C_5, C_5)=D_6 | '#skF_2'(C_5, C_5, C_5, D_6)=C_5)), inference(factorization, [status(thm), theory('equality')], [c_325])).
% 23.42/14.00  tff(c_1250, plain, (![C_2965, D_2966]: ('#skF_3'(C_2965, C_2965, C_2965, D_2966)!=C_2965 | k1_tarski(C_2965)=D_2966 | '#skF_2'(C_2965, C_2965, C_2965, D_2966)=C_2965)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_787])).
% 23.42/14.00  tff(c_1532, plain, (![D_4497]: (D_4497!='#skF_4' | '#skF_3'('#skF_5', '#skF_5', '#skF_5', D_4497)!='#skF_5' | '#skF_2'('#skF_5', '#skF_5', '#skF_5', D_4497)='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1250, c_46])).
% 23.42/14.00  tff(c_20, plain, (![A_3, B_4, C_5, D_6]: (~r2_hidden('#skF_2'(A_3, B_4, C_5, D_6), D_6) | '#skF_3'(A_3, B_4, C_5, D_6)!=A_3 | k1_enumset1(A_3, B_4, C_5)=D_6)), inference(cnfTransformation, [status(thm)], [f_48])).
% 23.42/14.00  tff(c_1565, plain, (![D_4497]: (~r2_hidden('#skF_5', D_4497) | '#skF_3'('#skF_5', '#skF_5', '#skF_5', D_4497)!='#skF_5' | k1_enumset1('#skF_5', '#skF_5', '#skF_5')=D_4497 | D_4497!='#skF_4' | '#skF_3'('#skF_5', '#skF_5', '#skF_5', D_4497)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1532, c_20])).
% 23.42/14.00  tff(c_2654, plain, (![D_7026]: (~r2_hidden('#skF_5', D_7026) | '#skF_3'('#skF_5', '#skF_5', '#skF_5', D_7026)!='#skF_5' | k1_tarski('#skF_5')=D_7026 | D_7026!='#skF_4' | '#skF_3'('#skF_5', '#skF_5', '#skF_5', D_7026)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_1565])).
% 23.42/14.00  tff(c_2699, plain, (k1_tarski('#skF_5')='#skF_4' | '#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4')!='#skF_5'), inference(resolution, [status(thm)], [c_73, c_2654])).
% 23.42/14.00  tff(c_2718, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_46, c_2699])).
% 23.42/14.00  tff(c_4742, plain, (![A_13704, B_13705, C_13706, D_13707]: ('#skF_2'(A_13704, B_13705, C_13706, D_13707)=C_13706 | '#skF_2'(A_13704, B_13705, C_13706, D_13707)=B_13705 | '#skF_2'(A_13704, B_13705, C_13706, D_13707)=A_13704 | r2_hidden('#skF_3'(A_13704, B_13705, C_13706, D_13707), D_13707) | k1_enumset1(A_13704, B_13705, C_13706)=D_13707)), inference(cnfTransformation, [status(thm)], [f_48])).
% 23.42/14.00  tff(c_4814, plain, (![A_13978, B_13979, C_13980]: ('#skF_3'(A_13978, B_13979, C_13980, '#skF_4')='#skF_5' | '#skF_2'(A_13978, B_13979, C_13980, '#skF_4')=C_13980 | '#skF_2'(A_13978, B_13979, C_13980, '#skF_4')=B_13979 | '#skF_2'(A_13978, B_13979, C_13980, '#skF_4')=A_13978 | k1_enumset1(A_13978, B_13979, C_13980)='#skF_4')), inference(resolution, [status(thm)], [c_4742, c_42])).
% 23.42/14.00  tff(c_4977, plain, (![A_11, B_12]: ('#skF_3'(A_11, A_11, B_12, '#skF_4')='#skF_5' | '#skF_2'(A_11, A_11, B_12, '#skF_4')=B_12 | '#skF_2'(A_11, A_11, B_12, '#skF_4')=A_11 | '#skF_2'(A_11, A_11, B_12, '#skF_4')=A_11 | k2_tarski(A_11, B_12)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_4814])).
% 23.42/14.00  tff(c_107349, plain, (![B_12]: ('#skF_3'(B_12, B_12, B_12, '#skF_4')='#skF_5' | k2_tarski(B_12, B_12)='#skF_4' | '#skF_2'(B_12, B_12, B_12, '#skF_4')=B_12)), inference(factorization, [status(thm), theory('equality')], [c_4977])).
% 23.42/14.00  tff(c_109504, plain, (![B_81160]: ('#skF_3'(B_81160, B_81160, B_81160, '#skF_4')='#skF_5' | k1_tarski(B_81160)='#skF_4' | '#skF_2'(B_81160, B_81160, B_81160, '#skF_4')=B_81160)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_107349])).
% 23.42/14.00  tff(c_109525, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4')='#skF_5' | '#skF_2'('#skF_5', '#skF_5', '#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_109504, c_46])).
% 23.42/14.00  tff(c_110328, plain, ('#skF_2'('#skF_5', '#skF_5', '#skF_5', '#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_2718, c_109525])).
% 23.42/14.00  tff(c_24, plain, (![A_3, B_4, C_5, D_6]: (~r2_hidden('#skF_2'(A_3, B_4, C_5, D_6), D_6) | r2_hidden('#skF_3'(A_3, B_4, C_5, D_6), D_6) | k1_enumset1(A_3, B_4, C_5)=D_6)), inference(cnfTransformation, [status(thm)], [f_48])).
% 23.42/14.00  tff(c_110645, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4'), '#skF_4') | k1_enumset1('#skF_5', '#skF_5', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_110328, c_24])).
% 23.42/14.00  tff(c_110925, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4'), '#skF_4') | k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_73, c_110645])).
% 23.42/14.00  tff(c_110926, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_110925])).
% 23.42/14.00  tff(c_110944, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_110926, c_42])).
% 23.42/14.00  tff(c_110949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2718, c_110944])).
% 23.42/14.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.42/14.00  
% 23.42/14.00  Inference rules
% 23.42/14.00  ----------------------
% 23.42/14.00  #Ref     : 0
% 23.42/14.00  #Sup     : 18677
% 23.42/14.00  #Fact    : 380
% 23.42/14.00  #Define  : 0
% 23.42/14.00  #Split   : 0
% 23.42/14.00  #Chain   : 0
% 23.42/14.00  #Close   : 0
% 23.42/14.00  
% 23.42/14.00  Ordering : KBO
% 23.42/14.00  
% 23.42/14.00  Simplification rules
% 23.42/14.00  ----------------------
% 23.42/14.00  #Subsume      : 12237
% 23.42/14.00  #Demod        : 851
% 23.42/14.00  #Tautology    : 5258
% 23.42/14.00  #SimpNegUnit  : 114
% 23.42/14.00  #BackRed      : 0
% 23.42/14.00  
% 23.42/14.00  #Partial instantiations: 24236
% 23.42/14.00  #Strategies tried      : 1
% 23.42/14.00  
% 23.42/14.00  Timing (in seconds)
% 23.42/14.00  ----------------------
% 23.42/14.00  Preprocessing        : 0.32
% 23.42/14.00  Parsing              : 0.16
% 23.42/14.00  CNF conversion       : 0.03
% 23.42/14.00  Main loop            : 12.92
% 23.42/14.00  Inferencing          : 4.34
% 23.42/14.01  Reduction            : 1.85
% 23.42/14.01  Demodulation         : 1.26
% 23.42/14.01  BG Simplification    : 0.28
% 23.42/14.01  Subsumption          : 6.18
% 23.42/14.01  Abstraction          : 0.59
% 23.42/14.01  MUC search           : 0.00
% 23.42/14.01  Cooper               : 0.00
% 23.42/14.01  Total                : 13.26
% 23.42/14.01  Index Insertion      : 0.00
% 23.42/14.01  Index Deletion       : 0.00
% 23.42/14.01  Index Matching       : 0.00
% 23.42/14.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
