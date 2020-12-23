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
% DateTime   : Thu Dec  3 09:49:25 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   71 (  88 expanded)
%              Number of leaves         :   37 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 119 expanded)
%              Number of equality atoms :   25 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_82,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_76,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_74,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_62,plain,(
    ! [A_60,B_61] :
      ( r1_xboole_0(k1_tarski(A_60),B_61)
      | r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | r2_hidden('#skF_1'(A_5),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_428,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r1_xboole_0(A_112,B_113)
      | ~ r2_hidden(C_114,k3_xboole_0(A_112,B_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_745,plain,(
    ! [A_132,B_133] :
      ( ~ r1_xboole_0(A_132,B_133)
      | v1_xboole_0(k3_xboole_0(A_132,B_133)) ) ),
    inference(resolution,[status(thm)],[c_8,c_428])).

tff(c_754,plain,(
    ! [A_3,B_4] :
      ( ~ r1_xboole_0(A_3,B_4)
      | v1_xboole_0(k3_xboole_0(B_4,A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_745])).

tff(c_824,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_2'(A_140,B_141),k3_xboole_0(A_140,B_141))
      | r1_xboole_0(A_140,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [B_8,A_5] :
      ( ~ r2_hidden(B_8,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_876,plain,(
    ! [A_144,B_145] :
      ( ~ v1_xboole_0(k3_xboole_0(A_144,B_145))
      | r1_xboole_0(A_144,B_145) ) ),
    inference(resolution,[status(thm)],[c_824,c_6])).

tff(c_928,plain,(
    ! [B_147,A_148] :
      ( r1_xboole_0(B_147,A_148)
      | ~ r1_xboole_0(A_148,B_147) ) ),
    inference(resolution,[status(thm)],[c_754,c_876])).

tff(c_942,plain,(
    ! [B_61,A_60] :
      ( r1_xboole_0(B_61,k1_tarski(A_60))
      | r2_hidden(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_62,c_928])).

tff(c_50,plain,(
    ! [A_39] : k2_tarski(A_39,A_39) = k1_tarski(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_127,plain,(
    ! [D_72,B_73] : r2_hidden(D_72,k2_tarski(D_72,B_73)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_130,plain,(
    ! [A_39] : r2_hidden(A_39,k1_tarski(A_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_127])).

tff(c_132,plain,(
    ! [B_75,A_76] :
      ( ~ r2_hidden(B_75,A_76)
      | ~ v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_139,plain,(
    ! [A_39] : ~ v1_xboole_0(k1_tarski(A_39)) ),
    inference(resolution,[status(thm)],[c_130,c_132])).

tff(c_70,plain,(
    ! [B_63,C_64] : r1_tarski(k1_tarski(B_63),k2_tarski(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_78,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_304,plain,(
    ! [A_95,B_96] :
      ( k3_xboole_0(A_95,B_96) = A_95
      | ~ r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_332,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_304])).

tff(c_379,plain,(
    ! [A_105,B_106,C_107] :
      ( r1_tarski(A_105,B_106)
      | ~ r1_tarski(A_105,k3_xboole_0(B_106,C_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1227,plain,(
    ! [A_175,B_176,A_177] :
      ( r1_tarski(A_175,B_176)
      | ~ r1_tarski(A_175,k3_xboole_0(A_177,B_176)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_379])).

tff(c_1304,plain,(
    ! [A_180] :
      ( r1_tarski(A_180,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_180,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_1227])).

tff(c_20,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1559,plain,(
    ! [A_212] :
      ( k3_xboole_0(A_212,k2_tarski('#skF_7','#skF_8')) = A_212
      | ~ r1_tarski(A_212,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1304,c_20])).

tff(c_1588,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_1559])).

tff(c_1613,plain,
    ( ~ r1_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5'))
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1588,c_754])).

tff(c_1628,plain,(
    ~ r1_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_1613])).

tff(c_1635,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_942,c_1628])).

tff(c_30,plain,(
    ! [D_34,B_30,A_29] :
      ( D_34 = B_30
      | D_34 = A_29
      | ~ r2_hidden(D_34,k2_tarski(A_29,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1638,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1635,c_30])).

tff(c_1645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_1638])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:56:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.58  
% 3.45/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2
% 3.45/1.58  
% 3.45/1.58  %Foreground sorts:
% 3.45/1.58  
% 3.45/1.58  
% 3.45/1.58  %Background operators:
% 3.45/1.58  
% 3.45/1.58  
% 3.45/1.58  %Foreground operators:
% 3.45/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.45/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.45/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.45/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.45/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.45/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.45/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.45/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.45/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.45/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.45/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.45/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.45/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.45/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.45/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.45/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.45/1.58  tff('#skF_8', type, '#skF_8': $i).
% 3.45/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.45/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.45/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.45/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.45/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.45/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.45/1.58  
% 3.45/1.59  tff(f_122, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.45/1.59  tff(f_97, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.45/1.59  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.45/1.59  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.45/1.59  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.45/1.59  tff(f_82, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.45/1.59  tff(f_78, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.45/1.59  tff(f_112, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.45/1.59  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.45/1.59  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.45/1.59  tff(c_76, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.45/1.59  tff(c_74, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.45/1.59  tff(c_62, plain, (![A_60, B_61]: (r1_xboole_0(k1_tarski(A_60), B_61) | r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.45/1.59  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.45/1.59  tff(c_8, plain, (![A_5]: (v1_xboole_0(A_5) | r2_hidden('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.45/1.59  tff(c_428, plain, (![A_112, B_113, C_114]: (~r1_xboole_0(A_112, B_113) | ~r2_hidden(C_114, k3_xboole_0(A_112, B_113)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.45/1.59  tff(c_745, plain, (![A_132, B_133]: (~r1_xboole_0(A_132, B_133) | v1_xboole_0(k3_xboole_0(A_132, B_133)))), inference(resolution, [status(thm)], [c_8, c_428])).
% 3.45/1.59  tff(c_754, plain, (![A_3, B_4]: (~r1_xboole_0(A_3, B_4) | v1_xboole_0(k3_xboole_0(B_4, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_745])).
% 3.45/1.59  tff(c_824, plain, (![A_140, B_141]: (r2_hidden('#skF_2'(A_140, B_141), k3_xboole_0(A_140, B_141)) | r1_xboole_0(A_140, B_141))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.45/1.59  tff(c_6, plain, (![B_8, A_5]: (~r2_hidden(B_8, A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.45/1.59  tff(c_876, plain, (![A_144, B_145]: (~v1_xboole_0(k3_xboole_0(A_144, B_145)) | r1_xboole_0(A_144, B_145))), inference(resolution, [status(thm)], [c_824, c_6])).
% 3.45/1.59  tff(c_928, plain, (![B_147, A_148]: (r1_xboole_0(B_147, A_148) | ~r1_xboole_0(A_148, B_147))), inference(resolution, [status(thm)], [c_754, c_876])).
% 3.45/1.59  tff(c_942, plain, (![B_61, A_60]: (r1_xboole_0(B_61, k1_tarski(A_60)) | r2_hidden(A_60, B_61))), inference(resolution, [status(thm)], [c_62, c_928])).
% 3.45/1.59  tff(c_50, plain, (![A_39]: (k2_tarski(A_39, A_39)=k1_tarski(A_39))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.45/1.59  tff(c_127, plain, (![D_72, B_73]: (r2_hidden(D_72, k2_tarski(D_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.45/1.59  tff(c_130, plain, (![A_39]: (r2_hidden(A_39, k1_tarski(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_127])).
% 3.45/1.59  tff(c_132, plain, (![B_75, A_76]: (~r2_hidden(B_75, A_76) | ~v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.45/1.59  tff(c_139, plain, (![A_39]: (~v1_xboole_0(k1_tarski(A_39)))), inference(resolution, [status(thm)], [c_130, c_132])).
% 3.45/1.59  tff(c_70, plain, (![B_63, C_64]: (r1_tarski(k1_tarski(B_63), k2_tarski(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.45/1.59  tff(c_78, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.45/1.59  tff(c_304, plain, (![A_95, B_96]: (k3_xboole_0(A_95, B_96)=A_95 | ~r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.45/1.59  tff(c_332, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_78, c_304])).
% 3.45/1.59  tff(c_379, plain, (![A_105, B_106, C_107]: (r1_tarski(A_105, B_106) | ~r1_tarski(A_105, k3_xboole_0(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.45/1.59  tff(c_1227, plain, (![A_175, B_176, A_177]: (r1_tarski(A_175, B_176) | ~r1_tarski(A_175, k3_xboole_0(A_177, B_176)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_379])).
% 3.45/1.59  tff(c_1304, plain, (![A_180]: (r1_tarski(A_180, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_180, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_332, c_1227])).
% 3.45/1.59  tff(c_20, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.45/1.59  tff(c_1559, plain, (![A_212]: (k3_xboole_0(A_212, k2_tarski('#skF_7', '#skF_8'))=A_212 | ~r1_tarski(A_212, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_1304, c_20])).
% 3.45/1.59  tff(c_1588, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_70, c_1559])).
% 3.45/1.59  tff(c_1613, plain, (~r1_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5')) | v1_xboole_0(k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1588, c_754])).
% 3.45/1.59  tff(c_1628, plain, (~r1_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_139, c_1613])).
% 3.45/1.59  tff(c_1635, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_942, c_1628])).
% 3.45/1.59  tff(c_30, plain, (![D_34, B_30, A_29]: (D_34=B_30 | D_34=A_29 | ~r2_hidden(D_34, k2_tarski(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.45/1.59  tff(c_1638, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1635, c_30])).
% 3.45/1.59  tff(c_1645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_74, c_1638])).
% 3.45/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.59  
% 3.45/1.59  Inference rules
% 3.45/1.59  ----------------------
% 3.45/1.59  #Ref     : 0
% 3.45/1.59  #Sup     : 375
% 3.45/1.59  #Fact    : 0
% 3.45/1.59  #Define  : 0
% 3.45/1.60  #Split   : 2
% 3.45/1.60  #Chain   : 0
% 3.45/1.60  #Close   : 0
% 3.45/1.60  
% 3.45/1.60  Ordering : KBO
% 3.45/1.60  
% 3.45/1.60  Simplification rules
% 3.45/1.60  ----------------------
% 3.45/1.60  #Subsume      : 47
% 3.45/1.60  #Demod        : 133
% 3.45/1.60  #Tautology    : 222
% 3.45/1.60  #SimpNegUnit  : 22
% 3.45/1.60  #BackRed      : 1
% 3.45/1.60  
% 3.45/1.60  #Partial instantiations: 0
% 3.45/1.60  #Strategies tried      : 1
% 3.45/1.60  
% 3.45/1.60  Timing (in seconds)
% 3.45/1.60  ----------------------
% 3.45/1.60  Preprocessing        : 0.34
% 3.45/1.60  Parsing              : 0.18
% 3.45/1.60  CNF conversion       : 0.03
% 3.45/1.60  Main loop            : 0.46
% 3.45/1.60  Inferencing          : 0.16
% 3.45/1.60  Reduction            : 0.16
% 3.45/1.60  Demodulation         : 0.12
% 3.45/1.60  BG Simplification    : 0.02
% 3.45/1.60  Subsumption          : 0.08
% 3.45/1.60  Abstraction          : 0.02
% 3.45/1.60  MUC search           : 0.00
% 3.45/1.60  Cooper               : 0.00
% 3.45/1.60  Total                : 0.83
% 3.45/1.60  Index Insertion      : 0.00
% 3.45/1.60  Index Deletion       : 0.00
% 3.45/1.60  Index Matching       : 0.00
% 3.45/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
