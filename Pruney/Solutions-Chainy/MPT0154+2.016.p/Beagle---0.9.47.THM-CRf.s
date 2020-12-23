%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:06 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 103 expanded)
%              Number of leaves         :   30 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :   73 ( 122 expanded)
%              Number of equality atoms :   31 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_73,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_62,plain,(
    ! [A_35,B_36] : k2_xboole_0(k1_tarski(A_35),k1_tarski(B_36)) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_46,plain,(
    ! [A_20] : k2_xboole_0(A_20,A_20) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_148,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k2_xboole_0(A_47,B_48)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_155,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_148])).

tff(c_311,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k4_xboole_0(B_80,A_79)) = k2_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_323,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = k2_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_311])).

tff(c_332,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_323])).

tff(c_56,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k2_xboole_0(A_28,B_29)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_326,plain,(
    ! [A_28,B_29] : k5_xboole_0(k2_xboole_0(A_28,B_29),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_28,B_29),A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_311])).

tff(c_1125,plain,(
    ! [A_128,B_129] : k2_xboole_0(k2_xboole_0(A_128,B_129),A_128) = k2_xboole_0(A_128,B_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_326])).

tff(c_1153,plain,(
    ! [A_35,B_36] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(A_35)) = k2_xboole_0(k1_tarski(A_35),k1_tarski(B_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1125])).

tff(c_1172,plain,(
    ! [A_35,B_36] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(A_35)) = k2_tarski(A_35,B_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1153])).

tff(c_64,plain,(
    ! [A_37,B_38,C_39] : k2_xboole_0(k1_tarski(A_37),k2_tarski(B_38,C_39)) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    ! [A_27] : k4_xboole_0(A_27,k1_xboole_0) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_213,plain,(
    ! [D_62,B_63,A_64] :
      ( ~ r2_hidden(D_62,B_63)
      | ~ r2_hidden(D_62,k4_xboole_0(A_64,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_228,plain,(
    ! [D_65,A_66] :
      ( ~ r2_hidden(D_65,k1_xboole_0)
      | ~ r2_hidden(D_65,A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_213])).

tff(c_647,plain,(
    ! [B_105,A_106] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_105),A_106)
      | r1_tarski(k1_xboole_0,B_105) ) ),
    inference(resolution,[status(thm)],[c_8,c_228])).

tff(c_657,plain,(
    ! [B_4] : r1_tarski(k1_xboole_0,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_647])).

tff(c_664,plain,(
    ! [D_108,A_109,B_110] :
      ( r2_hidden(D_108,k4_xboole_0(A_109,B_110))
      | r2_hidden(D_108,B_110)
      | ~ r2_hidden(D_108,A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3462,plain,(
    ! [D_263,B_264,A_265,B_266] :
      ( r2_hidden(D_263,B_264)
      | ~ r1_tarski(k4_xboole_0(A_265,B_266),B_264)
      | r2_hidden(D_263,B_266)
      | ~ r2_hidden(D_263,A_265) ) ),
    inference(resolution,[status(thm)],[c_664,c_4])).

tff(c_3483,plain,(
    ! [D_263,B_264,A_28,B_29] :
      ( r2_hidden(D_263,B_264)
      | ~ r1_tarski(k1_xboole_0,B_264)
      | r2_hidden(D_263,k2_xboole_0(A_28,B_29))
      | ~ r2_hidden(D_263,A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_3462])).

tff(c_3503,plain,(
    ! [D_263,B_264,A_28,B_29] :
      ( r2_hidden(D_263,B_264)
      | r2_hidden(D_263,k2_xboole_0(A_28,B_29))
      | ~ r2_hidden(D_263,A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_3483])).

tff(c_3865,plain,(
    ! [D_279,A_280,B_281] :
      ( ~ r2_hidden(D_279,A_280)
      | r2_hidden(D_279,k2_xboole_0(A_280,B_281)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3503])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6327,plain,(
    ! [A_357,A_358,B_359] :
      ( r1_tarski(A_357,k2_xboole_0(A_358,B_359))
      | ~ r2_hidden('#skF_1'(A_357,k2_xboole_0(A_358,B_359)),A_358) ) ),
    inference(resolution,[status(thm)],[c_3865,c_6])).

tff(c_6448,plain,(
    ! [A_360,B_361] : r1_tarski(A_360,k2_xboole_0(A_360,B_361)) ),
    inference(resolution,[status(thm)],[c_8,c_6327])).

tff(c_50,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7853,plain,(
    ! [A_415,B_416] : k2_xboole_0(A_415,k2_xboole_0(A_415,B_416)) = k2_xboole_0(A_415,B_416) ),
    inference(resolution,[status(thm)],[c_6448,c_50])).

tff(c_7941,plain,(
    ! [A_35,B_36] : k2_xboole_0(k1_tarski(A_35),k2_tarski(A_35,B_36)) = k2_xboole_0(k1_tarski(A_35),k1_tarski(B_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_7853])).

tff(c_14511,plain,(
    ! [A_579,B_580] : k2_xboole_0(k1_tarski(A_579),k2_tarski(A_579,B_580)) = k2_tarski(A_579,B_580) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_7941])).

tff(c_1124,plain,(
    ! [A_28,B_29] : k2_xboole_0(k2_xboole_0(A_28,B_29),A_28) = k2_xboole_0(A_28,B_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_326])).

tff(c_14543,plain,(
    ! [A_579,B_580] : k2_xboole_0(k2_tarski(A_579,B_580),k1_tarski(A_579)) = k2_xboole_0(k1_tarski(A_579),k2_tarski(A_579,B_580)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14511,c_1124])).

tff(c_14567,plain,(
    ! [A_579,B_580] : k1_enumset1(A_579,A_579,B_580) = k2_tarski(A_579,B_580) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1172,c_64,c_14543])).

tff(c_68,plain,(
    k1_enumset1('#skF_6','#skF_6','#skF_7') != k2_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14567,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.97/3.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/3.00  
% 7.97/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/3.01  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_1
% 7.97/3.01  
% 7.97/3.01  %Foreground sorts:
% 7.97/3.01  
% 7.97/3.01  
% 7.97/3.01  %Background operators:
% 7.97/3.01  
% 7.97/3.01  
% 7.97/3.01  %Foreground operators:
% 7.97/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.97/3.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.97/3.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.97/3.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.97/3.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.97/3.01  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.97/3.01  tff('#skF_7', type, '#skF_7': $i).
% 7.97/3.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.97/3.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.97/3.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.97/3.01  tff('#skF_6', type, '#skF_6': $i).
% 7.97/3.01  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.97/3.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.97/3.01  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.97/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.97/3.01  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.97/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.97/3.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.97/3.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.97/3.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.97/3.01  
% 7.97/3.02  tff(f_73, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 7.97/3.02  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 7.97/3.02  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 7.97/3.02  tff(f_71, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.97/3.02  tff(f_75, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 7.97/3.02  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.97/3.02  tff(f_65, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.97/3.02  tff(f_53, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.97/3.02  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.97/3.02  tff(f_80, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.97/3.02  tff(c_62, plain, (![A_35, B_36]: (k2_xboole_0(k1_tarski(A_35), k1_tarski(B_36))=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.97/3.02  tff(c_46, plain, (![A_20]: (k2_xboole_0(A_20, A_20)=A_20)), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.97/3.02  tff(c_148, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k2_xboole_0(A_47, B_48))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.97/3.02  tff(c_155, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_148])).
% 7.97/3.02  tff(c_311, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k4_xboole_0(B_80, A_79))=k2_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.97/3.02  tff(c_323, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=k2_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_155, c_311])).
% 7.97/3.02  tff(c_332, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_323])).
% 7.97/3.02  tff(c_56, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k2_xboole_0(A_28, B_29))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.97/3.02  tff(c_326, plain, (![A_28, B_29]: (k5_xboole_0(k2_xboole_0(A_28, B_29), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_28, B_29), A_28))), inference(superposition, [status(thm), theory('equality')], [c_56, c_311])).
% 7.97/3.02  tff(c_1125, plain, (![A_128, B_129]: (k2_xboole_0(k2_xboole_0(A_128, B_129), A_128)=k2_xboole_0(A_128, B_129))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_326])).
% 7.97/3.02  tff(c_1153, plain, (![A_35, B_36]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(A_35))=k2_xboole_0(k1_tarski(A_35), k1_tarski(B_36)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1125])).
% 7.97/3.02  tff(c_1172, plain, (![A_35, B_36]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(A_35))=k2_tarski(A_35, B_36))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1153])).
% 7.97/3.02  tff(c_64, plain, (![A_37, B_38, C_39]: (k2_xboole_0(k1_tarski(A_37), k2_tarski(B_38, C_39))=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.97/3.02  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.97/3.02  tff(c_54, plain, (![A_27]: (k4_xboole_0(A_27, k1_xboole_0)=A_27)), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.97/3.02  tff(c_213, plain, (![D_62, B_63, A_64]: (~r2_hidden(D_62, B_63) | ~r2_hidden(D_62, k4_xboole_0(A_64, B_63)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.97/3.02  tff(c_228, plain, (![D_65, A_66]: (~r2_hidden(D_65, k1_xboole_0) | ~r2_hidden(D_65, A_66))), inference(superposition, [status(thm), theory('equality')], [c_54, c_213])).
% 7.97/3.02  tff(c_647, plain, (![B_105, A_106]: (~r2_hidden('#skF_1'(k1_xboole_0, B_105), A_106) | r1_tarski(k1_xboole_0, B_105))), inference(resolution, [status(thm)], [c_8, c_228])).
% 7.97/3.02  tff(c_657, plain, (![B_4]: (r1_tarski(k1_xboole_0, B_4))), inference(resolution, [status(thm)], [c_8, c_647])).
% 7.97/3.02  tff(c_664, plain, (![D_108, A_109, B_110]: (r2_hidden(D_108, k4_xboole_0(A_109, B_110)) | r2_hidden(D_108, B_110) | ~r2_hidden(D_108, A_109))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.97/3.02  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.97/3.02  tff(c_3462, plain, (![D_263, B_264, A_265, B_266]: (r2_hidden(D_263, B_264) | ~r1_tarski(k4_xboole_0(A_265, B_266), B_264) | r2_hidden(D_263, B_266) | ~r2_hidden(D_263, A_265))), inference(resolution, [status(thm)], [c_664, c_4])).
% 7.97/3.02  tff(c_3483, plain, (![D_263, B_264, A_28, B_29]: (r2_hidden(D_263, B_264) | ~r1_tarski(k1_xboole_0, B_264) | r2_hidden(D_263, k2_xboole_0(A_28, B_29)) | ~r2_hidden(D_263, A_28))), inference(superposition, [status(thm), theory('equality')], [c_56, c_3462])).
% 7.97/3.02  tff(c_3503, plain, (![D_263, B_264, A_28, B_29]: (r2_hidden(D_263, B_264) | r2_hidden(D_263, k2_xboole_0(A_28, B_29)) | ~r2_hidden(D_263, A_28))), inference(demodulation, [status(thm), theory('equality')], [c_657, c_3483])).
% 7.97/3.02  tff(c_3865, plain, (![D_279, A_280, B_281]: (~r2_hidden(D_279, A_280) | r2_hidden(D_279, k2_xboole_0(A_280, B_281)))), inference(factorization, [status(thm), theory('equality')], [c_3503])).
% 7.97/3.02  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.97/3.02  tff(c_6327, plain, (![A_357, A_358, B_359]: (r1_tarski(A_357, k2_xboole_0(A_358, B_359)) | ~r2_hidden('#skF_1'(A_357, k2_xboole_0(A_358, B_359)), A_358))), inference(resolution, [status(thm)], [c_3865, c_6])).
% 7.97/3.02  tff(c_6448, plain, (![A_360, B_361]: (r1_tarski(A_360, k2_xboole_0(A_360, B_361)))), inference(resolution, [status(thm)], [c_8, c_6327])).
% 7.97/3.02  tff(c_50, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=B_25 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.97/3.02  tff(c_7853, plain, (![A_415, B_416]: (k2_xboole_0(A_415, k2_xboole_0(A_415, B_416))=k2_xboole_0(A_415, B_416))), inference(resolution, [status(thm)], [c_6448, c_50])).
% 7.97/3.02  tff(c_7941, plain, (![A_35, B_36]: (k2_xboole_0(k1_tarski(A_35), k2_tarski(A_35, B_36))=k2_xboole_0(k1_tarski(A_35), k1_tarski(B_36)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_7853])).
% 7.97/3.02  tff(c_14511, plain, (![A_579, B_580]: (k2_xboole_0(k1_tarski(A_579), k2_tarski(A_579, B_580))=k2_tarski(A_579, B_580))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_7941])).
% 7.97/3.02  tff(c_1124, plain, (![A_28, B_29]: (k2_xboole_0(k2_xboole_0(A_28, B_29), A_28)=k2_xboole_0(A_28, B_29))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_326])).
% 7.97/3.02  tff(c_14543, plain, (![A_579, B_580]: (k2_xboole_0(k2_tarski(A_579, B_580), k1_tarski(A_579))=k2_xboole_0(k1_tarski(A_579), k2_tarski(A_579, B_580)))), inference(superposition, [status(thm), theory('equality')], [c_14511, c_1124])).
% 7.97/3.02  tff(c_14567, plain, (![A_579, B_580]: (k1_enumset1(A_579, A_579, B_580)=k2_tarski(A_579, B_580))), inference(demodulation, [status(thm), theory('equality')], [c_1172, c_64, c_14543])).
% 7.97/3.02  tff(c_68, plain, (k1_enumset1('#skF_6', '#skF_6', '#skF_7')!=k2_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.97/3.02  tff(c_14573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14567, c_68])).
% 7.97/3.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/3.02  
% 7.97/3.02  Inference rules
% 7.97/3.02  ----------------------
% 7.97/3.02  #Ref     : 0
% 7.97/3.02  #Sup     : 3436
% 7.97/3.02  #Fact    : 2
% 7.97/3.02  #Define  : 0
% 7.97/3.02  #Split   : 0
% 7.97/3.02  #Chain   : 0
% 7.97/3.02  #Close   : 0
% 7.97/3.02  
% 7.97/3.02  Ordering : KBO
% 7.97/3.02  
% 7.97/3.02  Simplification rules
% 7.97/3.02  ----------------------
% 7.97/3.02  #Subsume      : 444
% 7.97/3.02  #Demod        : 2577
% 7.97/3.02  #Tautology    : 1715
% 7.97/3.02  #SimpNegUnit  : 0
% 7.97/3.02  #BackRed      : 4
% 7.97/3.02  
% 7.97/3.02  #Partial instantiations: 0
% 7.97/3.02  #Strategies tried      : 1
% 7.97/3.02  
% 7.97/3.02  Timing (in seconds)
% 7.97/3.02  ----------------------
% 7.97/3.02  Preprocessing        : 0.32
% 7.97/3.02  Parsing              : 0.16
% 7.97/3.02  CNF conversion       : 0.02
% 7.97/3.02  Main loop            : 1.91
% 7.97/3.02  Inferencing          : 0.55
% 7.97/3.02  Reduction            : 0.74
% 7.97/3.02  Demodulation         : 0.61
% 7.97/3.02  BG Simplification    : 0.07
% 7.97/3.02  Subsumption          : 0.44
% 7.97/3.02  Abstraction          : 0.08
% 7.97/3.02  MUC search           : 0.00
% 7.97/3.02  Cooper               : 0.00
% 7.97/3.02  Total                : 2.26
% 7.97/3.02  Index Insertion      : 0.00
% 7.97/3.02  Index Deletion       : 0.00
% 7.97/3.02  Index Matching       : 0.00
% 7.97/3.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
