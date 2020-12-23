%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:49 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 519 expanded)
%              Number of leaves         :   24 ( 166 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 (1375 expanded)
%              Number of equality atoms :   24 ( 384 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_972,plain,(
    ! [B_125,C_126] :
      ( r2_hidden('#skF_2'(B_125,B_125,C_126),C_126)
      | k2_xboole_0(B_125,B_125) = C_126
      | r2_hidden('#skF_1'(B_125,B_125,C_126),B_125) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_20])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1049,plain,(
    ! [B_127] :
      ( r2_hidden('#skF_2'(B_127,B_127,B_127),B_127)
      | k2_xboole_0(B_127,B_127) = B_127 ) ),
    inference(resolution,[status(thm)],[c_972,c_18])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_671,plain,(
    ! [B_113,C_114] :
      ( ~ r2_hidden('#skF_2'(B_113,B_113,C_114),B_113)
      | k2_xboole_0(B_113,B_113) = C_114
      | r2_hidden('#skF_1'(B_113,B_113,C_114),B_113) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_16])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_707,plain,(
    ! [B_113] :
      ( ~ r2_hidden('#skF_2'(B_113,B_113,B_113),B_113)
      | k2_xboole_0(B_113,B_113) = B_113 ) ),
    inference(resolution,[status(thm)],[c_671,c_14])).

tff(c_1083,plain,(
    ! [B_127] : k2_xboole_0(B_127,B_127) = B_127 ),
    inference(resolution,[status(thm)],[c_1049,c_707])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_121,plain,(
    ! [D_34,B_35,A_36] :
      ( ~ r2_hidden(D_34,B_35)
      | r2_hidden(D_34,k2_xboole_0(A_36,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_133,plain,(
    ! [D_34] :
      ( ~ r2_hidden(D_34,'#skF_6')
      | r2_hidden(D_34,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_121])).

tff(c_391,plain,(
    ! [A_85,B_86,C_87] :
      ( ~ r2_hidden('#skF_1'(A_85,B_86,C_87),C_87)
      | r2_hidden('#skF_2'(A_85,B_86,C_87),C_87)
      | k2_xboole_0(A_85,B_86) = C_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_410,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_2'(A_85,B_86,k1_xboole_0),k1_xboole_0)
      | k2_xboole_0(A_85,B_86) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(A_85,B_86,k1_xboole_0),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_133,c_391])).

tff(c_1042,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_6',k1_xboole_0),k1_xboole_0)
    | k2_xboole_0('#skF_6','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_972,c_410])).

tff(c_1170,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_6',k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_1042])).

tff(c_1171,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1170])).

tff(c_28,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1185,plain,(
    ! [A_14] : r1_tarski('#skF_6',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1171,c_28])).

tff(c_850,plain,(
    ! [A_3,C_5] :
      ( r2_hidden('#skF_2'(A_3,A_3,C_5),C_5)
      | k2_xboole_0(A_3,A_3) = C_5
      | r2_hidden('#skF_1'(A_3,A_3,C_5),A_3) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_20])).

tff(c_1380,plain,(
    ! [A_3,C_5] :
      ( r2_hidden('#skF_2'(A_3,A_3,C_5),C_5)
      | C_5 = A_3
      | r2_hidden('#skF_1'(A_3,A_3,C_5),A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_850])).

tff(c_1381,plain,(
    ! [A_135,C_136] :
      ( r2_hidden('#skF_2'(A_135,A_135,C_136),C_136)
      | C_136 = A_135
      | r2_hidden('#skF_1'(A_135,A_135,C_136),A_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_850])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( ~ r2_hidden(D_8,A_3)
      | r2_hidden(D_8,k2_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_163,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,B_53)
      | ~ r2_hidden(C_54,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_167,plain,(
    ! [C_55,A_56] :
      ( ~ r2_hidden(C_55,k1_xboole_0)
      | ~ r2_hidden(C_55,A_56) ) ),
    inference(resolution,[status(thm)],[c_30,c_163])).

tff(c_180,plain,(
    ! [D_57,A_58] :
      ( ~ r2_hidden(D_57,A_58)
      | ~ r2_hidden(D_57,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_133,c_167])).

tff(c_191,plain,(
    ! [D_8,A_3] :
      ( ~ r2_hidden(D_8,'#skF_6')
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_180])).

tff(c_1531,plain,(
    ! [C_141,A_142] :
      ( ~ r2_hidden('#skF_1'('#skF_6','#skF_6',C_141),A_142)
      | r2_hidden('#skF_2'('#skF_6','#skF_6',C_141),C_141)
      | C_141 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_1381,c_191])).

tff(c_1560,plain,(
    ! [C_143] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_6',C_143),C_143)
      | C_143 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_1380,c_1531])).

tff(c_138,plain,(
    ! [D_45,A_46,B_47] :
      ( ~ r2_hidden(D_45,A_46)
      | r2_hidden(D_45,k2_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_150,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_tarski('#skF_4','#skF_5'))
      | r2_hidden(D_45,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_138])).

tff(c_1181,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_tarski('#skF_4','#skF_5'))
      | r2_hidden(D_45,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1171,c_150])).

tff(c_1585,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_6',k2_tarski('#skF_4','#skF_5')),'#skF_6')
    | k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1560,c_1181])).

tff(c_1613,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1585])).

tff(c_40,plain,(
    ! [B_24,C_25,A_23] :
      ( r2_hidden(B_24,C_25)
      | ~ r1_tarski(k2_tarski(A_23,B_24),C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1631,plain,(
    ! [C_25] :
      ( r2_hidden('#skF_5',C_25)
      | ~ r1_tarski('#skF_6',C_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1613,c_40])).

tff(c_1642,plain,(
    ! [C_25] : r2_hidden('#skF_5',C_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_1631])).

tff(c_1646,plain,(
    ! [C_146] : r2_hidden('#skF_5',C_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_1631])).

tff(c_1657,plain,(
    ! [A_3] : ~ r2_hidden('#skF_5',A_3) ),
    inference(resolution,[status(thm)],[c_1646,c_191])).

tff(c_1665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1642,c_1657])).

tff(c_1666,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_6',k2_tarski('#skF_4','#skF_5')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1585])).

tff(c_1719,plain,(
    ! [A_3] : ~ r2_hidden('#skF_2'('#skF_6','#skF_6',k2_tarski('#skF_4','#skF_5')),A_3) ),
    inference(resolution,[status(thm)],[c_1666,c_191])).

tff(c_1721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1719,c_1666])).

tff(c_1722,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_6',k1_xboole_0),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1170])).

tff(c_166,plain,(
    ! [C_54,A_15] :
      ( ~ r2_hidden(C_54,k1_xboole_0)
      | ~ r2_hidden(C_54,A_15) ) ),
    inference(resolution,[status(thm)],[c_30,c_163])).

tff(c_1726,plain,(
    ! [A_15] : ~ r2_hidden('#skF_2'('#skF_6','#skF_6',k1_xboole_0),A_15) ),
    inference(resolution,[status(thm)],[c_1722,c_166])).

tff(c_1835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1726,c_1722])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n002.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 12:30:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.77  
% 4.16/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.78  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.16/1.78  
% 4.16/1.78  %Foreground sorts:
% 4.16/1.78  
% 4.16/1.78  
% 4.16/1.78  %Background operators:
% 4.16/1.78  
% 4.16/1.78  
% 4.16/1.78  %Foreground operators:
% 4.16/1.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.16/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.16/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.16/1.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.16/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.16/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.16/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.16/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.16/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.16/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.16/1.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.16/1.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.16/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.16/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.16/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.16/1.78  
% 4.24/1.79  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.24/1.79  tff(f_74, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 4.24/1.79  tff(f_56, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.24/1.79  tff(f_58, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.24/1.79  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.24/1.79  tff(f_70, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.24/1.79  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.24/1.79  tff(c_972, plain, (![B_125, C_126]: (r2_hidden('#skF_2'(B_125, B_125, C_126), C_126) | k2_xboole_0(B_125, B_125)=C_126 | r2_hidden('#skF_1'(B_125, B_125, C_126), B_125))), inference(factorization, [status(thm), theory('equality')], [c_20])).
% 4.24/1.79  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.24/1.79  tff(c_1049, plain, (![B_127]: (r2_hidden('#skF_2'(B_127, B_127, B_127), B_127) | k2_xboole_0(B_127, B_127)=B_127)), inference(resolution, [status(thm)], [c_972, c_18])).
% 4.24/1.79  tff(c_16, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.24/1.79  tff(c_671, plain, (![B_113, C_114]: (~r2_hidden('#skF_2'(B_113, B_113, C_114), B_113) | k2_xboole_0(B_113, B_113)=C_114 | r2_hidden('#skF_1'(B_113, B_113, C_114), B_113))), inference(factorization, [status(thm), theory('equality')], [c_16])).
% 4.24/1.79  tff(c_14, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.24/1.79  tff(c_707, plain, (![B_113]: (~r2_hidden('#skF_2'(B_113, B_113, B_113), B_113) | k2_xboole_0(B_113, B_113)=B_113)), inference(resolution, [status(thm)], [c_671, c_14])).
% 4.24/1.79  tff(c_1083, plain, (![B_127]: (k2_xboole_0(B_127, B_127)=B_127)), inference(resolution, [status(thm)], [c_1049, c_707])).
% 4.24/1.79  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.24/1.79  tff(c_121, plain, (![D_34, B_35, A_36]: (~r2_hidden(D_34, B_35) | r2_hidden(D_34, k2_xboole_0(A_36, B_35)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.24/1.79  tff(c_133, plain, (![D_34]: (~r2_hidden(D_34, '#skF_6') | r2_hidden(D_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_121])).
% 4.24/1.79  tff(c_391, plain, (![A_85, B_86, C_87]: (~r2_hidden('#skF_1'(A_85, B_86, C_87), C_87) | r2_hidden('#skF_2'(A_85, B_86, C_87), C_87) | k2_xboole_0(A_85, B_86)=C_87)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.24/1.79  tff(c_410, plain, (![A_85, B_86]: (r2_hidden('#skF_2'(A_85, B_86, k1_xboole_0), k1_xboole_0) | k2_xboole_0(A_85, B_86)=k1_xboole_0 | ~r2_hidden('#skF_1'(A_85, B_86, k1_xboole_0), '#skF_6'))), inference(resolution, [status(thm)], [c_133, c_391])).
% 4.24/1.79  tff(c_1042, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_6', k1_xboole_0), k1_xboole_0) | k2_xboole_0('#skF_6', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_972, c_410])).
% 4.24/1.79  tff(c_1170, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_6', k1_xboole_0), k1_xboole_0) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_1042])).
% 4.24/1.79  tff(c_1171, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_1170])).
% 4.24/1.79  tff(c_28, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.24/1.79  tff(c_1185, plain, (![A_14]: (r1_tarski('#skF_6', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_1171, c_28])).
% 4.24/1.79  tff(c_850, plain, (![A_3, C_5]: (r2_hidden('#skF_2'(A_3, A_3, C_5), C_5) | k2_xboole_0(A_3, A_3)=C_5 | r2_hidden('#skF_1'(A_3, A_3, C_5), A_3))), inference(factorization, [status(thm), theory('equality')], [c_20])).
% 4.24/1.79  tff(c_1380, plain, (![A_3, C_5]: (r2_hidden('#skF_2'(A_3, A_3, C_5), C_5) | C_5=A_3 | r2_hidden('#skF_1'(A_3, A_3, C_5), A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_850])).
% 4.24/1.79  tff(c_1381, plain, (![A_135, C_136]: (r2_hidden('#skF_2'(A_135, A_135, C_136), C_136) | C_136=A_135 | r2_hidden('#skF_1'(A_135, A_135, C_136), A_135))), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_850])).
% 4.24/1.79  tff(c_8, plain, (![D_8, A_3, B_4]: (~r2_hidden(D_8, A_3) | r2_hidden(D_8, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.24/1.79  tff(c_30, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.24/1.79  tff(c_163, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, B_53) | ~r2_hidden(C_54, A_52))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.24/1.79  tff(c_167, plain, (![C_55, A_56]: (~r2_hidden(C_55, k1_xboole_0) | ~r2_hidden(C_55, A_56))), inference(resolution, [status(thm)], [c_30, c_163])).
% 4.24/1.79  tff(c_180, plain, (![D_57, A_58]: (~r2_hidden(D_57, A_58) | ~r2_hidden(D_57, '#skF_6'))), inference(resolution, [status(thm)], [c_133, c_167])).
% 4.24/1.79  tff(c_191, plain, (![D_8, A_3]: (~r2_hidden(D_8, '#skF_6') | ~r2_hidden(D_8, A_3))), inference(resolution, [status(thm)], [c_8, c_180])).
% 4.24/1.79  tff(c_1531, plain, (![C_141, A_142]: (~r2_hidden('#skF_1'('#skF_6', '#skF_6', C_141), A_142) | r2_hidden('#skF_2'('#skF_6', '#skF_6', C_141), C_141) | C_141='#skF_6')), inference(resolution, [status(thm)], [c_1381, c_191])).
% 4.24/1.79  tff(c_1560, plain, (![C_143]: (r2_hidden('#skF_2'('#skF_6', '#skF_6', C_143), C_143) | C_143='#skF_6')), inference(resolution, [status(thm)], [c_1380, c_1531])).
% 4.24/1.79  tff(c_138, plain, (![D_45, A_46, B_47]: (~r2_hidden(D_45, A_46) | r2_hidden(D_45, k2_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.24/1.79  tff(c_150, plain, (![D_45]: (~r2_hidden(D_45, k2_tarski('#skF_4', '#skF_5')) | r2_hidden(D_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_138])).
% 4.24/1.79  tff(c_1181, plain, (![D_45]: (~r2_hidden(D_45, k2_tarski('#skF_4', '#skF_5')) | r2_hidden(D_45, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1171, c_150])).
% 4.24/1.79  tff(c_1585, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_6', k2_tarski('#skF_4', '#skF_5')), '#skF_6') | k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_1560, c_1181])).
% 4.24/1.79  tff(c_1613, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_1585])).
% 4.24/1.79  tff(c_40, plain, (![B_24, C_25, A_23]: (r2_hidden(B_24, C_25) | ~r1_tarski(k2_tarski(A_23, B_24), C_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.24/1.79  tff(c_1631, plain, (![C_25]: (r2_hidden('#skF_5', C_25) | ~r1_tarski('#skF_6', C_25))), inference(superposition, [status(thm), theory('equality')], [c_1613, c_40])).
% 4.24/1.79  tff(c_1642, plain, (![C_25]: (r2_hidden('#skF_5', C_25))), inference(demodulation, [status(thm), theory('equality')], [c_1185, c_1631])).
% 4.24/1.79  tff(c_1646, plain, (![C_146]: (r2_hidden('#skF_5', C_146))), inference(demodulation, [status(thm), theory('equality')], [c_1185, c_1631])).
% 4.24/1.79  tff(c_1657, plain, (![A_3]: (~r2_hidden('#skF_5', A_3))), inference(resolution, [status(thm)], [c_1646, c_191])).
% 4.24/1.79  tff(c_1665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1642, c_1657])).
% 4.24/1.79  tff(c_1666, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_6', k2_tarski('#skF_4', '#skF_5')), '#skF_6')), inference(splitRight, [status(thm)], [c_1585])).
% 4.24/1.79  tff(c_1719, plain, (![A_3]: (~r2_hidden('#skF_2'('#skF_6', '#skF_6', k2_tarski('#skF_4', '#skF_5')), A_3))), inference(resolution, [status(thm)], [c_1666, c_191])).
% 4.24/1.79  tff(c_1721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1719, c_1666])).
% 4.24/1.79  tff(c_1722, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_6', k1_xboole_0), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1170])).
% 4.24/1.79  tff(c_166, plain, (![C_54, A_15]: (~r2_hidden(C_54, k1_xboole_0) | ~r2_hidden(C_54, A_15))), inference(resolution, [status(thm)], [c_30, c_163])).
% 4.24/1.79  tff(c_1726, plain, (![A_15]: (~r2_hidden('#skF_2'('#skF_6', '#skF_6', k1_xboole_0), A_15))), inference(resolution, [status(thm)], [c_1722, c_166])).
% 4.24/1.79  tff(c_1835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1726, c_1722])).
% 4.24/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.79  
% 4.24/1.79  Inference rules
% 4.24/1.79  ----------------------
% 4.24/1.79  #Ref     : 0
% 4.24/1.79  #Sup     : 361
% 4.24/1.79  #Fact    : 8
% 4.24/1.79  #Define  : 0
% 4.24/1.79  #Split   : 3
% 4.24/1.79  #Chain   : 0
% 4.24/1.79  #Close   : 0
% 4.24/1.79  
% 4.24/1.79  Ordering : KBO
% 4.24/1.79  
% 4.24/1.79  Simplification rules
% 4.24/1.79  ----------------------
% 4.24/1.79  #Subsume      : 86
% 4.24/1.79  #Demod        : 141
% 4.24/1.79  #Tautology    : 111
% 4.24/1.79  #SimpNegUnit  : 3
% 4.24/1.79  #BackRed      : 23
% 4.24/1.79  
% 4.24/1.79  #Partial instantiations: 0
% 4.24/1.79  #Strategies tried      : 1
% 4.24/1.79  
% 4.24/1.79  Timing (in seconds)
% 4.24/1.79  ----------------------
% 4.24/1.79  Preprocessing        : 0.33
% 4.24/1.79  Parsing              : 0.16
% 4.24/1.79  CNF conversion       : 0.02
% 4.24/1.79  Main loop            : 0.69
% 4.24/1.79  Inferencing          : 0.22
% 4.24/1.79  Reduction            : 0.21
% 4.24/1.79  Demodulation         : 0.16
% 4.24/1.79  BG Simplification    : 0.03
% 4.24/1.79  Subsumption          : 0.18
% 4.24/1.79  Abstraction          : 0.03
% 4.24/1.79  MUC search           : 0.00
% 4.24/1.79  Cooper               : 0.00
% 4.24/1.79  Total                : 1.06
% 4.24/1.79  Index Insertion      : 0.00
% 4.24/1.79  Index Deletion       : 0.00
% 4.24/1.79  Index Matching       : 0.00
% 4.24/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
