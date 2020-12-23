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
% DateTime   : Thu Dec  3 09:53:10 EST 2020

% Result     : Theorem 5.43s
% Output     : CNFRefutation 5.43s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 197 expanded)
%              Number of leaves         :   23 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :   96 ( 482 expanded)
%              Number of equality atoms :   46 ( 168 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(c_24,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_838,plain,(
    ! [A_956,B_957,C_958] :
      ( ~ r2_hidden('#skF_1'(A_956,B_957,C_958),B_957)
      | r2_hidden('#skF_2'(A_956,B_957,C_958),C_958)
      | k4_xboole_0(A_956,B_957) = C_958 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_860,plain,(
    ! [A_987,C_988] :
      ( r2_hidden('#skF_2'(A_987,A_987,C_988),C_988)
      | k4_xboole_0(A_987,A_987) = C_988 ) ),
    inference(resolution,[status(thm)],[c_18,c_838])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_877,plain,(
    ! [A_987,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_987,A_987,k4_xboole_0(A_1,B_2)),A_1)
      | k4_xboole_0(A_987,A_987) = k4_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_860,c_6])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1120,plain,(
    ! [A_1108,A_1109,B_1110] :
      ( ~ r2_hidden('#skF_2'(A_1108,A_1108,k4_xboole_0(A_1109,B_1110)),B_1110)
      | k4_xboole_0(A_1109,B_1110) = k4_xboole_0(A_1108,A_1108) ) ),
    inference(resolution,[status(thm)],[c_860,c_4])).

tff(c_1170,plain,(
    ! [A_1171,A_1170] : k4_xboole_0(A_1171,A_1171) = k4_xboole_0(A_1170,A_1170) ),
    inference(resolution,[status(thm)],[c_877,c_1120])).

tff(c_1272,plain,(
    ! [D_1259,A_1260,A_1261] :
      ( ~ r2_hidden(D_1259,A_1260)
      | ~ r2_hidden(D_1259,k4_xboole_0(A_1261,A_1261)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1170,c_4])).

tff(c_1308,plain,(
    ! [C_13,A_1261] : ~ r2_hidden(C_13,k4_xboole_0(A_1261,A_1261)) ),
    inference(resolution,[status(thm)],[c_24,c_1272])).

tff(c_42,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_5'(A_20,B_21),A_20)
      | k1_xboole_0 = A_20
      | k1_tarski(B_21) = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1309,plain,(
    ! [C_1290,A_1291] : ~ r2_hidden(C_1290,k4_xboole_0(A_1291,A_1291)) ),
    inference(resolution,[status(thm)],[c_24,c_1272])).

tff(c_1606,plain,(
    ! [A_1413,B_1414] :
      ( k4_xboole_0(A_1413,A_1413) = k1_xboole_0
      | k4_xboole_0(A_1413,A_1413) = k1_tarski(B_1414) ) ),
    inference(resolution,[status(thm)],[c_42,c_1309])).

tff(c_1681,plain,(
    ! [B_1414,A_1413] :
      ( r2_hidden(B_1414,k4_xboole_0(A_1413,A_1413))
      | k4_xboole_0(A_1413,A_1413) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1606,c_24])).

tff(c_1738,plain,(
    ! [A_1413] : k4_xboole_0(A_1413,A_1413) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1308,c_1681])).

tff(c_2654,plain,(
    ! [A_1976,A_1977,B_1978] :
      ( r2_hidden('#skF_2'(A_1976,A_1976,k4_xboole_0(A_1977,B_1978)),A_1977)
      | k4_xboole_0(A_1977,B_1978) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1738,c_877])).

tff(c_22,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3625,plain,(
    ! [A_2342,A_2343,B_2344] :
      ( '#skF_2'(A_2342,A_2342,k4_xboole_0(k1_tarski(A_2343),B_2344)) = A_2343
      | k4_xboole_0(k1_tarski(A_2343),B_2344) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2654,c_22])).

tff(c_878,plain,(
    ! [A_987,A_1,B_2] :
      ( ~ r2_hidden('#skF_2'(A_987,A_987,k4_xboole_0(A_1,B_2)),B_2)
      | k4_xboole_0(A_987,A_987) = k4_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_860,c_4])).

tff(c_1744,plain,(
    ! [A_987,A_1,B_2] :
      ( ~ r2_hidden('#skF_2'(A_987,A_987,k4_xboole_0(A_1,B_2)),B_2)
      | k4_xboole_0(A_1,B_2) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1738,c_878])).

tff(c_3639,plain,(
    ! [A_2343,B_2344] :
      ( ~ r2_hidden(A_2343,B_2344)
      | k4_xboole_0(k1_tarski(A_2343),B_2344) = k1_xboole_0
      | k4_xboole_0(k1_tarski(A_2343),B_2344) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3625,c_1744])).

tff(c_4512,plain,(
    ! [A_2555,B_2556] :
      ( ~ r2_hidden(A_2555,B_2556)
      | k4_xboole_0(k1_tarski(A_2555),B_2556) = k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3639])).

tff(c_46,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4637,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4512,c_46])).

tff(c_774,plain,(
    ! [A_895,B_896,C_897] :
      ( r2_hidden('#skF_1'(A_895,B_896,C_897),A_895)
      | r2_hidden('#skF_2'(A_895,B_896,C_897),C_897)
      | k4_xboole_0(A_895,B_896) = C_897 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_809,plain,(
    ! [A_895,B_896] :
      ( r2_hidden('#skF_2'(A_895,B_896,A_895),A_895)
      | k4_xboole_0(A_895,B_896) = A_895 ) ),
    inference(resolution,[status(thm)],[c_774,c_14])).

tff(c_1459,plain,(
    ! [A_1351,B_1352,C_1353] :
      ( r2_hidden('#skF_1'(A_1351,B_1352,C_1353),A_1351)
      | r2_hidden('#skF_2'(A_1351,B_1352,C_1353),B_1352)
      | ~ r2_hidden('#skF_2'(A_1351,B_1352,C_1353),A_1351)
      | k4_xboole_0(A_1351,B_1352) = C_1353 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2172,plain,(
    ! [A_1766,B_1767] :
      ( r2_hidden('#skF_2'(A_1766,B_1767,A_1766),B_1767)
      | ~ r2_hidden('#skF_2'(A_1766,B_1767,A_1766),A_1766)
      | k4_xboole_0(A_1766,B_1767) = A_1766 ) ),
    inference(resolution,[status(thm)],[c_1459,c_8])).

tff(c_2205,plain,(
    ! [A_1796,B_1797] :
      ( r2_hidden('#skF_2'(A_1796,B_1797,A_1796),B_1797)
      | k4_xboole_0(A_1796,B_1797) = A_1796 ) ),
    inference(resolution,[status(thm)],[c_809,c_2172])).

tff(c_2414,plain,(
    ! [A_1915,A_1916] :
      ( '#skF_2'(A_1915,k1_tarski(A_1916),A_1915) = A_1916
      | k4_xboole_0(A_1915,k1_tarski(A_1916)) = A_1915 ) ),
    inference(resolution,[status(thm)],[c_2205,c_22])).

tff(c_2440,plain,(
    ! [A_1916,A_1915] :
      ( r2_hidden(A_1916,A_1915)
      | k4_xboole_0(A_1915,k1_tarski(A_1916)) = A_1915
      | k4_xboole_0(A_1915,k1_tarski(A_1916)) = A_1915 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2414,c_809])).

tff(c_3233,plain,(
    ! [A_1916,A_1915] :
      ( r2_hidden(A_1916,A_1915)
      | k4_xboole_0(A_1915,k1_tarski(A_1916)) = A_1915 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2440])).

tff(c_6478,plain,(
    ! [A_3010,A_3011,B_3012] :
      ( ~ r2_hidden('#skF_2'(A_3010,k4_xboole_0(A_3011,B_3012),A_3010),B_3012)
      | k4_xboole_0(A_3010,k4_xboole_0(A_3011,B_3012)) = A_3010 ) ),
    inference(resolution,[status(thm)],[c_2205,c_4])).

tff(c_6546,plain,(
    ! [A_3041,A_3042] : k4_xboole_0(A_3041,k4_xboole_0(A_3042,A_3041)) = A_3041 ),
    inference(resolution,[status(thm)],[c_809,c_6478])).

tff(c_6994,plain,(
    ! [A_3163,A_3164] :
      ( k4_xboole_0(k1_tarski(A_3163),A_3164) = k1_tarski(A_3163)
      | r2_hidden(A_3163,A_3164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3233,c_6546])).

tff(c_44,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7076,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6994,c_44])).

tff(c_7170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4637,c_7076])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:39:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.43/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.05  
% 5.43/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.05  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 5.43/2.05  
% 5.43/2.05  %Foreground sorts:
% 5.43/2.05  
% 5.43/2.05  
% 5.43/2.05  %Background operators:
% 5.43/2.05  
% 5.43/2.05  
% 5.43/2.05  %Foreground operators:
% 5.43/2.05  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.43/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.43/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.43/2.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.43/2.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.43/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.43/2.05  tff('#skF_7', type, '#skF_7': $i).
% 5.43/2.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.43/2.05  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.43/2.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.43/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.43/2.05  tff('#skF_6', type, '#skF_6': $i).
% 5.43/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.43/2.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.43/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.43/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.43/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.43/2.05  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.43/2.05  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.43/2.05  
% 5.43/2.06  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.43/2.06  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.43/2.06  tff(f_64, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 5.43/2.06  tff(f_69, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 5.43/2.06  tff(c_24, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.43/2.06  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.43/2.06  tff(c_838, plain, (![A_956, B_957, C_958]: (~r2_hidden('#skF_1'(A_956, B_957, C_958), B_957) | r2_hidden('#skF_2'(A_956, B_957, C_958), C_958) | k4_xboole_0(A_956, B_957)=C_958)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.43/2.06  tff(c_860, plain, (![A_987, C_988]: (r2_hidden('#skF_2'(A_987, A_987, C_988), C_988) | k4_xboole_0(A_987, A_987)=C_988)), inference(resolution, [status(thm)], [c_18, c_838])).
% 5.43/2.06  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.43/2.06  tff(c_877, plain, (![A_987, A_1, B_2]: (r2_hidden('#skF_2'(A_987, A_987, k4_xboole_0(A_1, B_2)), A_1) | k4_xboole_0(A_987, A_987)=k4_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_860, c_6])).
% 5.43/2.06  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.43/2.06  tff(c_1120, plain, (![A_1108, A_1109, B_1110]: (~r2_hidden('#skF_2'(A_1108, A_1108, k4_xboole_0(A_1109, B_1110)), B_1110) | k4_xboole_0(A_1109, B_1110)=k4_xboole_0(A_1108, A_1108))), inference(resolution, [status(thm)], [c_860, c_4])).
% 5.43/2.06  tff(c_1170, plain, (![A_1171, A_1170]: (k4_xboole_0(A_1171, A_1171)=k4_xboole_0(A_1170, A_1170))), inference(resolution, [status(thm)], [c_877, c_1120])).
% 5.43/2.06  tff(c_1272, plain, (![D_1259, A_1260, A_1261]: (~r2_hidden(D_1259, A_1260) | ~r2_hidden(D_1259, k4_xboole_0(A_1261, A_1261)))), inference(superposition, [status(thm), theory('equality')], [c_1170, c_4])).
% 5.43/2.06  tff(c_1308, plain, (![C_13, A_1261]: (~r2_hidden(C_13, k4_xboole_0(A_1261, A_1261)))), inference(resolution, [status(thm)], [c_24, c_1272])).
% 5.43/2.06  tff(c_42, plain, (![A_20, B_21]: (r2_hidden('#skF_5'(A_20, B_21), A_20) | k1_xboole_0=A_20 | k1_tarski(B_21)=A_20)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.43/2.06  tff(c_1309, plain, (![C_1290, A_1291]: (~r2_hidden(C_1290, k4_xboole_0(A_1291, A_1291)))), inference(resolution, [status(thm)], [c_24, c_1272])).
% 5.43/2.06  tff(c_1606, plain, (![A_1413, B_1414]: (k4_xboole_0(A_1413, A_1413)=k1_xboole_0 | k4_xboole_0(A_1413, A_1413)=k1_tarski(B_1414))), inference(resolution, [status(thm)], [c_42, c_1309])).
% 5.43/2.06  tff(c_1681, plain, (![B_1414, A_1413]: (r2_hidden(B_1414, k4_xboole_0(A_1413, A_1413)) | k4_xboole_0(A_1413, A_1413)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1606, c_24])).
% 5.43/2.06  tff(c_1738, plain, (![A_1413]: (k4_xboole_0(A_1413, A_1413)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1308, c_1681])).
% 5.43/2.06  tff(c_2654, plain, (![A_1976, A_1977, B_1978]: (r2_hidden('#skF_2'(A_1976, A_1976, k4_xboole_0(A_1977, B_1978)), A_1977) | k4_xboole_0(A_1977, B_1978)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1738, c_877])).
% 5.43/2.06  tff(c_22, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.43/2.06  tff(c_3625, plain, (![A_2342, A_2343, B_2344]: ('#skF_2'(A_2342, A_2342, k4_xboole_0(k1_tarski(A_2343), B_2344))=A_2343 | k4_xboole_0(k1_tarski(A_2343), B_2344)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2654, c_22])).
% 5.43/2.06  tff(c_878, plain, (![A_987, A_1, B_2]: (~r2_hidden('#skF_2'(A_987, A_987, k4_xboole_0(A_1, B_2)), B_2) | k4_xboole_0(A_987, A_987)=k4_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_860, c_4])).
% 5.43/2.06  tff(c_1744, plain, (![A_987, A_1, B_2]: (~r2_hidden('#skF_2'(A_987, A_987, k4_xboole_0(A_1, B_2)), B_2) | k4_xboole_0(A_1, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1738, c_878])).
% 5.43/2.06  tff(c_3639, plain, (![A_2343, B_2344]: (~r2_hidden(A_2343, B_2344) | k4_xboole_0(k1_tarski(A_2343), B_2344)=k1_xboole_0 | k4_xboole_0(k1_tarski(A_2343), B_2344)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3625, c_1744])).
% 5.43/2.06  tff(c_4512, plain, (![A_2555, B_2556]: (~r2_hidden(A_2555, B_2556) | k4_xboole_0(k1_tarski(A_2555), B_2556)=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_3639])).
% 5.43/2.06  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.43/2.06  tff(c_4637, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4512, c_46])).
% 5.43/2.06  tff(c_774, plain, (![A_895, B_896, C_897]: (r2_hidden('#skF_1'(A_895, B_896, C_897), A_895) | r2_hidden('#skF_2'(A_895, B_896, C_897), C_897) | k4_xboole_0(A_895, B_896)=C_897)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.43/2.06  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.43/2.06  tff(c_809, plain, (![A_895, B_896]: (r2_hidden('#skF_2'(A_895, B_896, A_895), A_895) | k4_xboole_0(A_895, B_896)=A_895)), inference(resolution, [status(thm)], [c_774, c_14])).
% 5.43/2.06  tff(c_1459, plain, (![A_1351, B_1352, C_1353]: (r2_hidden('#skF_1'(A_1351, B_1352, C_1353), A_1351) | r2_hidden('#skF_2'(A_1351, B_1352, C_1353), B_1352) | ~r2_hidden('#skF_2'(A_1351, B_1352, C_1353), A_1351) | k4_xboole_0(A_1351, B_1352)=C_1353)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.43/2.06  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.43/2.06  tff(c_2172, plain, (![A_1766, B_1767]: (r2_hidden('#skF_2'(A_1766, B_1767, A_1766), B_1767) | ~r2_hidden('#skF_2'(A_1766, B_1767, A_1766), A_1766) | k4_xboole_0(A_1766, B_1767)=A_1766)), inference(resolution, [status(thm)], [c_1459, c_8])).
% 5.43/2.06  tff(c_2205, plain, (![A_1796, B_1797]: (r2_hidden('#skF_2'(A_1796, B_1797, A_1796), B_1797) | k4_xboole_0(A_1796, B_1797)=A_1796)), inference(resolution, [status(thm)], [c_809, c_2172])).
% 5.43/2.06  tff(c_2414, plain, (![A_1915, A_1916]: ('#skF_2'(A_1915, k1_tarski(A_1916), A_1915)=A_1916 | k4_xboole_0(A_1915, k1_tarski(A_1916))=A_1915)), inference(resolution, [status(thm)], [c_2205, c_22])).
% 5.43/2.06  tff(c_2440, plain, (![A_1916, A_1915]: (r2_hidden(A_1916, A_1915) | k4_xboole_0(A_1915, k1_tarski(A_1916))=A_1915 | k4_xboole_0(A_1915, k1_tarski(A_1916))=A_1915)), inference(superposition, [status(thm), theory('equality')], [c_2414, c_809])).
% 5.43/2.06  tff(c_3233, plain, (![A_1916, A_1915]: (r2_hidden(A_1916, A_1915) | k4_xboole_0(A_1915, k1_tarski(A_1916))=A_1915)), inference(factorization, [status(thm), theory('equality')], [c_2440])).
% 5.43/2.06  tff(c_6478, plain, (![A_3010, A_3011, B_3012]: (~r2_hidden('#skF_2'(A_3010, k4_xboole_0(A_3011, B_3012), A_3010), B_3012) | k4_xboole_0(A_3010, k4_xboole_0(A_3011, B_3012))=A_3010)), inference(resolution, [status(thm)], [c_2205, c_4])).
% 5.43/2.06  tff(c_6546, plain, (![A_3041, A_3042]: (k4_xboole_0(A_3041, k4_xboole_0(A_3042, A_3041))=A_3041)), inference(resolution, [status(thm)], [c_809, c_6478])).
% 5.43/2.06  tff(c_6994, plain, (![A_3163, A_3164]: (k4_xboole_0(k1_tarski(A_3163), A_3164)=k1_tarski(A_3163) | r2_hidden(A_3163, A_3164))), inference(superposition, [status(thm), theory('equality')], [c_3233, c_6546])).
% 5.43/2.06  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.43/2.06  tff(c_7076, plain, (r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6994, c_44])).
% 5.43/2.06  tff(c_7170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4637, c_7076])).
% 5.43/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.06  
% 5.43/2.06  Inference rules
% 5.43/2.06  ----------------------
% 5.43/2.06  #Ref     : 0
% 5.43/2.06  #Sup     : 1220
% 5.43/2.06  #Fact    : 9
% 5.43/2.06  #Define  : 0
% 5.43/2.06  #Split   : 3
% 5.43/2.06  #Chain   : 0
% 5.43/2.06  #Close   : 0
% 5.43/2.06  
% 5.43/2.06  Ordering : KBO
% 5.43/2.06  
% 5.43/2.06  Simplification rules
% 5.43/2.06  ----------------------
% 5.43/2.06  #Subsume      : 367
% 5.43/2.06  #Demod        : 408
% 5.43/2.06  #Tautology    : 354
% 5.43/2.06  #SimpNegUnit  : 38
% 5.43/2.06  #BackRed      : 8
% 5.43/2.06  
% 5.43/2.06  #Partial instantiations: 1560
% 5.43/2.06  #Strategies tried      : 1
% 5.43/2.06  
% 5.43/2.06  Timing (in seconds)
% 5.43/2.06  ----------------------
% 5.43/2.07  Preprocessing        : 0.30
% 5.43/2.07  Parsing              : 0.15
% 5.43/2.07  CNF conversion       : 0.02
% 5.43/2.07  Main loop            : 1.00
% 5.66/2.07  Inferencing          : 0.45
% 5.66/2.07  Reduction            : 0.23
% 5.66/2.07  Demodulation         : 0.15
% 5.66/2.07  BG Simplification    : 0.05
% 5.66/2.07  Subsumption          : 0.21
% 5.66/2.07  Abstraction          : 0.06
% 5.66/2.07  MUC search           : 0.00
% 5.66/2.07  Cooper               : 0.00
% 5.66/2.07  Total                : 1.33
% 5.66/2.07  Index Insertion      : 0.00
% 5.66/2.07  Index Deletion       : 0.00
% 5.66/2.07  Index Matching       : 0.00
% 5.66/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
