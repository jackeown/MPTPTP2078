%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:01 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   65 (  89 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 129 expanded)
%              Number of equality atoms :   21 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_60,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_292,plain,(
    ! [A_59,B_60] :
      ( r1_xboole_0(A_59,B_60)
      | k3_xboole_0(A_59,B_60) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( r1_xboole_0(B_16,A_15)
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_302,plain,(
    ! [B_60,A_59] :
      ( r1_xboole_0(B_60,A_59)
      | k3_xboole_0(A_59,B_60) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_292,c_30])).

tff(c_58,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_164,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_180,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_164])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1285,plain,(
    ! [A_126,B_127,C_128] :
      ( k3_xboole_0(A_126,k2_xboole_0(B_127,C_128)) = k3_xboole_0(A_126,C_128)
      | ~ r1_xboole_0(A_126,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_300,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_292,c_56])).

tff(c_304,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_300])).

tff(c_1324,plain,
    ( k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1285,c_304])).

tff(c_1367,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_4,c_1324])).

tff(c_1385,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_302,c_1367])).

tff(c_305,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(k1_tarski(A_61),B_62)
      | r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1579,plain,(
    ! [A_141,B_142] :
      ( k3_xboole_0(k1_tarski(A_141),B_142) = k1_xboole_0
      | r2_hidden(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_305,c_24])).

tff(c_62,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_313,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_317,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_313])).

tff(c_366,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_4])).

tff(c_1619,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | r2_hidden('#skF_7',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1579,c_366])).

tff(c_1679,plain,(
    r2_hidden('#skF_7',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1385,c_1619])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1712,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_1679,c_8])).

tff(c_415,plain,(
    ! [A_80,B_81,C_82] :
      ( ~ r1_xboole_0(A_80,B_81)
      | ~ r2_hidden(C_82,k3_xboole_0(A_80,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_427,plain,(
    ! [C_82] :
      ( ~ r1_xboole_0('#skF_6','#skF_5')
      | ~ r2_hidden(C_82,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_415])).

tff(c_445,plain,(
    ! [C_82] : ~ r2_hidden(C_82,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_427])).

tff(c_962,plain,(
    ! [D_114,A_115,B_116] :
      ( r2_hidden(D_114,k3_xboole_0(A_115,B_116))
      | ~ r2_hidden(D_114,B_116)
      | ~ r2_hidden(D_114,A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_996,plain,(
    ! [D_114] :
      ( r2_hidden(D_114,k1_xboole_0)
      | ~ r2_hidden(D_114,'#skF_5')
      | ~ r2_hidden(D_114,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_962])).

tff(c_1017,plain,(
    ! [D_114] :
      ( ~ r2_hidden(D_114,'#skF_5')
      | ~ r2_hidden(D_114,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_445,c_996])).

tff(c_1759,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_1712,c_1017])).

tff(c_1766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1759])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.73  
% 3.68/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.73  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.68/1.73  
% 3.68/1.73  %Foreground sorts:
% 3.68/1.73  
% 3.68/1.73  
% 3.68/1.73  %Background operators:
% 3.68/1.73  
% 3.68/1.73  
% 3.68/1.73  %Foreground operators:
% 3.68/1.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.68/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.68/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.68/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.68/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.68/1.73  tff('#skF_7', type, '#skF_7': $i).
% 3.68/1.73  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.68/1.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.68/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.68/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.68/1.73  tff('#skF_5', type, '#skF_5': $i).
% 3.68/1.73  tff('#skF_6', type, '#skF_6': $i).
% 3.68/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.68/1.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.68/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.68/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.68/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.68/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.68/1.73  
% 3.68/1.75  tff(f_102, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.68/1.75  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.68/1.75  tff(f_48, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.68/1.75  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.68/1.75  tff(f_80, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 3.68/1.75  tff(f_93, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.68/1.75  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.68/1.75  tff(f_38, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.68/1.75  tff(f_62, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.68/1.75  tff(c_60, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.68/1.75  tff(c_292, plain, (![A_59, B_60]: (r1_xboole_0(A_59, B_60) | k3_xboole_0(A_59, B_60)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.68/1.75  tff(c_30, plain, (![B_16, A_15]: (r1_xboole_0(B_16, A_15) | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.68/1.75  tff(c_302, plain, (![B_60, A_59]: (r1_xboole_0(B_60, A_59) | k3_xboole_0(A_59, B_60)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_292, c_30])).
% 3.68/1.75  tff(c_58, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.68/1.75  tff(c_164, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.68/1.75  tff(c_180, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_164])).
% 3.68/1.75  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.68/1.75  tff(c_1285, plain, (![A_126, B_127, C_128]: (k3_xboole_0(A_126, k2_xboole_0(B_127, C_128))=k3_xboole_0(A_126, C_128) | ~r1_xboole_0(A_126, B_127))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.68/1.75  tff(c_56, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.68/1.75  tff(c_300, plain, (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_292, c_56])).
% 3.68/1.75  tff(c_304, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_300])).
% 3.68/1.75  tff(c_1324, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0 | ~r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1285, c_304])).
% 3.68/1.75  tff(c_1367, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_4, c_1324])).
% 3.68/1.75  tff(c_1385, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_302, c_1367])).
% 3.68/1.75  tff(c_305, plain, (![A_61, B_62]: (r1_xboole_0(k1_tarski(A_61), B_62) | r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.68/1.75  tff(c_24, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.68/1.75  tff(c_1579, plain, (![A_141, B_142]: (k3_xboole_0(k1_tarski(A_141), B_142)=k1_xboole_0 | r2_hidden(A_141, B_142))), inference(resolution, [status(thm)], [c_305, c_24])).
% 3.68/1.75  tff(c_62, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.68/1.75  tff(c_313, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.68/1.75  tff(c_317, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_313])).
% 3.68/1.75  tff(c_366, plain, (k3_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5'))=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_317, c_4])).
% 3.68/1.75  tff(c_1619, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | r2_hidden('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1579, c_366])).
% 3.68/1.75  tff(c_1679, plain, (r2_hidden('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1385, c_1619])).
% 3.68/1.75  tff(c_8, plain, (![D_10, B_6, A_5]: (r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.68/1.75  tff(c_1712, plain, (r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_1679, c_8])).
% 3.68/1.75  tff(c_415, plain, (![A_80, B_81, C_82]: (~r1_xboole_0(A_80, B_81) | ~r2_hidden(C_82, k3_xboole_0(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.68/1.75  tff(c_427, plain, (![C_82]: (~r1_xboole_0('#skF_6', '#skF_5') | ~r2_hidden(C_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_180, c_415])).
% 3.68/1.75  tff(c_445, plain, (![C_82]: (~r2_hidden(C_82, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_427])).
% 3.68/1.75  tff(c_962, plain, (![D_114, A_115, B_116]: (r2_hidden(D_114, k3_xboole_0(A_115, B_116)) | ~r2_hidden(D_114, B_116) | ~r2_hidden(D_114, A_115))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.68/1.75  tff(c_996, plain, (![D_114]: (r2_hidden(D_114, k1_xboole_0) | ~r2_hidden(D_114, '#skF_5') | ~r2_hidden(D_114, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_180, c_962])).
% 3.68/1.75  tff(c_1017, plain, (![D_114]: (~r2_hidden(D_114, '#skF_5') | ~r2_hidden(D_114, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_445, c_996])).
% 3.68/1.75  tff(c_1759, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_1712, c_1017])).
% 3.68/1.75  tff(c_1766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_1759])).
% 3.68/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.75  
% 3.68/1.75  Inference rules
% 3.68/1.75  ----------------------
% 3.68/1.75  #Ref     : 0
% 3.68/1.75  #Sup     : 448
% 3.68/1.75  #Fact    : 0
% 3.68/1.75  #Define  : 0
% 3.68/1.75  #Split   : 0
% 3.68/1.75  #Chain   : 0
% 3.68/1.75  #Close   : 0
% 3.68/1.75  
% 3.68/1.75  Ordering : KBO
% 3.68/1.75  
% 3.68/1.75  Simplification rules
% 3.68/1.75  ----------------------
% 3.68/1.75  #Subsume      : 136
% 3.68/1.75  #Demod        : 98
% 3.68/1.75  #Tautology    : 162
% 3.68/1.75  #SimpNegUnit  : 22
% 3.68/1.75  #BackRed      : 0
% 3.68/1.75  
% 3.68/1.75  #Partial instantiations: 0
% 3.68/1.75  #Strategies tried      : 1
% 3.68/1.75  
% 3.68/1.75  Timing (in seconds)
% 3.68/1.75  ----------------------
% 3.68/1.75  Preprocessing        : 0.41
% 3.68/1.75  Parsing              : 0.19
% 3.68/1.75  CNF conversion       : 0.04
% 3.68/1.75  Main loop            : 0.50
% 3.68/1.75  Inferencing          : 0.17
% 3.68/1.75  Reduction            : 0.19
% 3.68/1.75  Demodulation         : 0.14
% 3.68/1.75  BG Simplification    : 0.03
% 3.68/1.75  Subsumption          : 0.09
% 3.68/1.75  Abstraction          : 0.03
% 3.68/1.75  MUC search           : 0.00
% 3.68/1.75  Cooper               : 0.00
% 3.68/1.75  Total                : 0.95
% 3.68/1.75  Index Insertion      : 0.00
% 3.68/1.75  Index Deletion       : 0.00
% 3.68/1.75  Index Matching       : 0.00
% 3.68/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
