%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:35 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 131 expanded)
%              Number of leaves         :   34 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :   82 ( 214 expanded)
%              Number of equality atoms :   18 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_102,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_112,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_65,axiom,(
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

tff(c_64,plain,(
    ! [C_36] : r2_hidden(C_36,k1_tarski(C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_91,plain,(
    ! [B_53,A_54] :
      ( ~ r2_hidden(B_53,A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [C_36] : ~ v1_xboole_0(k1_tarski(C_36)) ),
    inference(resolution,[status(thm)],[c_64,c_91])).

tff(c_146,plain,(
    ! [A_63] :
      ( v1_xboole_0(A_63)
      | r2_hidden('#skF_1'(A_63),A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [C_36,A_32] :
      ( C_36 = A_32
      | ~ r2_hidden(C_36,k1_tarski(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_150,plain,(
    ! [A_32] :
      ( '#skF_1'(k1_tarski(A_32)) = A_32
      | v1_xboole_0(k1_tarski(A_32)) ) ),
    inference(resolution,[status(thm)],[c_146,c_62])).

tff(c_156,plain,(
    ! [A_32] : '#skF_1'(k1_tarski(A_32)) = A_32 ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_150])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_60,plain,(
    ! [B_31,A_30] : k2_tarski(B_31,A_30) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_181,plain,(
    ! [A_67,B_68] : k3_tarski(k2_tarski(A_67,B_68)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_233,plain,(
    ! [A_74,B_75] : k3_tarski(k2_tarski(A_74,B_75)) = k2_xboole_0(B_75,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_181])).

tff(c_82,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_239,plain,(
    ! [B_75,A_74] : k2_xboole_0(B_75,A_74) = k2_xboole_0(A_74,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_82])).

tff(c_86,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_7'),'#skF_8'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_268,plain,(
    r1_tarski(k2_xboole_0('#skF_8',k1_tarski('#skF_7')),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_86])).

tff(c_360,plain,(
    ! [B_90,A_91] :
      ( B_90 = A_91
      | ~ r1_tarski(B_90,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_362,plain,
    ( k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = '#skF_8'
    | ~ r1_tarski('#skF_8',k2_xboole_0('#skF_8',k1_tarski('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_268,c_360])).

tff(c_373,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_362])).

tff(c_427,plain,(
    ! [A_96,C_97,B_98] :
      ( r1_xboole_0(A_96,C_97)
      | ~ r1_xboole_0(A_96,k2_xboole_0(B_98,C_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_434,plain,(
    ! [A_96] :
      ( r1_xboole_0(A_96,k1_tarski('#skF_7'))
      | ~ r1_xboole_0(A_96,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_427])).

tff(c_559,plain,(
    ! [A_120,B_121,C_122] :
      ( ~ r1_xboole_0(A_120,B_121)
      | ~ r2_hidden(C_122,B_121)
      | ~ r2_hidden(C_122,A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1010,plain,(
    ! [C_175,A_176] :
      ( ~ r2_hidden(C_175,k1_tarski('#skF_7'))
      | ~ r2_hidden(C_175,A_176)
      | ~ r1_xboole_0(A_176,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_434,c_559])).

tff(c_1019,plain,(
    ! [A_176] :
      ( ~ r2_hidden('#skF_1'(k1_tarski('#skF_7')),A_176)
      | ~ r1_xboole_0(A_176,'#skF_8')
      | v1_xboole_0(k1_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_4,c_1010])).

tff(c_1026,plain,(
    ! [A_176] :
      ( ~ r2_hidden('#skF_7',A_176)
      | ~ r1_xboole_0(A_176,'#skF_8')
      | v1_xboole_0(k1_tarski('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_1019])).

tff(c_1029,plain,(
    ! [A_177] :
      ( ~ r2_hidden('#skF_7',A_177)
      | ~ r1_xboole_0(A_177,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_1026])).

tff(c_1039,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_1029])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_463,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_4'(A_100,B_101),A_100)
      | r1_xboole_0(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_476,plain,(
    ! [A_32,B_101] :
      ( '#skF_4'(k1_tarski(A_32),B_101) = A_32
      | r1_xboole_0(k1_tarski(A_32),B_101) ) ),
    inference(resolution,[status(thm)],[c_463,c_62])).

tff(c_1049,plain,(
    '#skF_4'(k1_tarski('#skF_7'),'#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_476,c_1039])).

tff(c_38,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_4'(A_14,B_15),B_15)
      | r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1055,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r1_xboole_0(k1_tarski('#skF_7'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_38])).

tff(c_1062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1039,c_84,c_1055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n019.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 10:41:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.54  
% 3.17/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.54  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.17/1.54  
% 3.17/1.54  %Foreground sorts:
% 3.17/1.54  
% 3.17/1.54  
% 3.17/1.54  %Background operators:
% 3.17/1.54  
% 3.17/1.54  
% 3.17/1.54  %Foreground operators:
% 3.17/1.54  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.17/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.17/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.17/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.17/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.17/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.17/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.17/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.17/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.17/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.17/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.17/1.54  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.17/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.17/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.17/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.54  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.17/1.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.17/1.54  
% 3.17/1.55  tff(f_102, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.17/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.17/1.55  tff(f_93, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.17/1.55  tff(f_95, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.17/1.55  tff(f_112, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.17/1.55  tff(f_117, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 3.17/1.55  tff(f_71, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.17/1.55  tff(f_89, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.17/1.55  tff(f_65, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.17/1.55  tff(c_64, plain, (![C_36]: (r2_hidden(C_36, k1_tarski(C_36)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.17/1.55  tff(c_91, plain, (![B_53, A_54]: (~r2_hidden(B_53, A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.17/1.55  tff(c_95, plain, (![C_36]: (~v1_xboole_0(k1_tarski(C_36)))), inference(resolution, [status(thm)], [c_64, c_91])).
% 3.17/1.55  tff(c_146, plain, (![A_63]: (v1_xboole_0(A_63) | r2_hidden('#skF_1'(A_63), A_63))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.17/1.55  tff(c_62, plain, (![C_36, A_32]: (C_36=A_32 | ~r2_hidden(C_36, k1_tarski(A_32)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.17/1.55  tff(c_150, plain, (![A_32]: ('#skF_1'(k1_tarski(A_32))=A_32 | v1_xboole_0(k1_tarski(A_32)))), inference(resolution, [status(thm)], [c_146, c_62])).
% 3.17/1.55  tff(c_156, plain, (![A_32]: ('#skF_1'(k1_tarski(A_32))=A_32)), inference(negUnitSimplification, [status(thm)], [c_95, c_150])).
% 3.17/1.55  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.17/1.55  tff(c_58, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.17/1.55  tff(c_60, plain, (![B_31, A_30]: (k2_tarski(B_31, A_30)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.17/1.55  tff(c_181, plain, (![A_67, B_68]: (k3_tarski(k2_tarski(A_67, B_68))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.17/1.55  tff(c_233, plain, (![A_74, B_75]: (k3_tarski(k2_tarski(A_74, B_75))=k2_xboole_0(B_75, A_74))), inference(superposition, [status(thm), theory('equality')], [c_60, c_181])).
% 3.17/1.55  tff(c_82, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.17/1.55  tff(c_239, plain, (![B_75, A_74]: (k2_xboole_0(B_75, A_74)=k2_xboole_0(A_74, B_75))), inference(superposition, [status(thm), theory('equality')], [c_233, c_82])).
% 3.17/1.55  tff(c_86, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_7'), '#skF_8'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.17/1.55  tff(c_268, plain, (r1_tarski(k2_xboole_0('#skF_8', k1_tarski('#skF_7')), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_86])).
% 3.17/1.55  tff(c_360, plain, (![B_90, A_91]: (B_90=A_91 | ~r1_tarski(B_90, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.17/1.55  tff(c_362, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))='#skF_8' | ~r1_tarski('#skF_8', k2_xboole_0('#skF_8', k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_268, c_360])).
% 3.17/1.55  tff(c_373, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_362])).
% 3.17/1.55  tff(c_427, plain, (![A_96, C_97, B_98]: (r1_xboole_0(A_96, C_97) | ~r1_xboole_0(A_96, k2_xboole_0(B_98, C_97)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.17/1.55  tff(c_434, plain, (![A_96]: (r1_xboole_0(A_96, k1_tarski('#skF_7')) | ~r1_xboole_0(A_96, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_373, c_427])).
% 3.17/1.55  tff(c_559, plain, (![A_120, B_121, C_122]: (~r1_xboole_0(A_120, B_121) | ~r2_hidden(C_122, B_121) | ~r2_hidden(C_122, A_120))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.17/1.55  tff(c_1010, plain, (![C_175, A_176]: (~r2_hidden(C_175, k1_tarski('#skF_7')) | ~r2_hidden(C_175, A_176) | ~r1_xboole_0(A_176, '#skF_8'))), inference(resolution, [status(thm)], [c_434, c_559])).
% 3.17/1.55  tff(c_1019, plain, (![A_176]: (~r2_hidden('#skF_1'(k1_tarski('#skF_7')), A_176) | ~r1_xboole_0(A_176, '#skF_8') | v1_xboole_0(k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_4, c_1010])).
% 3.17/1.55  tff(c_1026, plain, (![A_176]: (~r2_hidden('#skF_7', A_176) | ~r1_xboole_0(A_176, '#skF_8') | v1_xboole_0(k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_1019])).
% 3.17/1.55  tff(c_1029, plain, (![A_177]: (~r2_hidden('#skF_7', A_177) | ~r1_xboole_0(A_177, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_95, c_1026])).
% 3.17/1.55  tff(c_1039, plain, (~r1_xboole_0(k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_64, c_1029])).
% 3.17/1.55  tff(c_84, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.17/1.55  tff(c_463, plain, (![A_100, B_101]: (r2_hidden('#skF_4'(A_100, B_101), A_100) | r1_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.17/1.55  tff(c_476, plain, (![A_32, B_101]: ('#skF_4'(k1_tarski(A_32), B_101)=A_32 | r1_xboole_0(k1_tarski(A_32), B_101))), inference(resolution, [status(thm)], [c_463, c_62])).
% 3.17/1.55  tff(c_1049, plain, ('#skF_4'(k1_tarski('#skF_7'), '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_476, c_1039])).
% 3.17/1.55  tff(c_38, plain, (![A_14, B_15]: (r2_hidden('#skF_4'(A_14, B_15), B_15) | r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.17/1.55  tff(c_1055, plain, (r2_hidden('#skF_7', '#skF_8') | r1_xboole_0(k1_tarski('#skF_7'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1049, c_38])).
% 3.17/1.55  tff(c_1062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1039, c_84, c_1055])).
% 3.17/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.55  
% 3.17/1.55  Inference rules
% 3.17/1.55  ----------------------
% 3.17/1.55  #Ref     : 0
% 3.17/1.55  #Sup     : 232
% 3.17/1.55  #Fact    : 0
% 3.17/1.55  #Define  : 0
% 3.17/1.55  #Split   : 2
% 3.17/1.55  #Chain   : 0
% 3.17/1.55  #Close   : 0
% 3.17/1.55  
% 3.17/1.55  Ordering : KBO
% 3.17/1.55  
% 3.17/1.55  Simplification rules
% 3.17/1.55  ----------------------
% 3.17/1.55  #Subsume      : 28
% 3.17/1.55  #Demod        : 47
% 3.17/1.55  #Tautology    : 86
% 3.17/1.55  #SimpNegUnit  : 4
% 3.17/1.55  #BackRed      : 2
% 3.17/1.55  
% 3.17/1.55  #Partial instantiations: 0
% 3.17/1.55  #Strategies tried      : 1
% 3.17/1.55  
% 3.17/1.55  Timing (in seconds)
% 3.17/1.55  ----------------------
% 3.17/1.56  Preprocessing        : 0.36
% 3.17/1.56  Parsing              : 0.19
% 3.17/1.56  CNF conversion       : 0.03
% 3.17/1.56  Main loop            : 0.40
% 3.17/1.56  Inferencing          : 0.13
% 3.17/1.56  Reduction            : 0.14
% 3.17/1.56  Demodulation         : 0.11
% 3.17/1.56  BG Simplification    : 0.02
% 3.17/1.56  Subsumption          : 0.07
% 3.17/1.56  Abstraction          : 0.02
% 3.17/1.56  MUC search           : 0.00
% 3.17/1.56  Cooper               : 0.00
% 3.17/1.56  Total                : 0.79
% 3.17/1.56  Index Insertion      : 0.00
% 3.17/1.56  Index Deletion       : 0.00
% 3.17/1.56  Index Matching       : 0.00
% 3.17/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
