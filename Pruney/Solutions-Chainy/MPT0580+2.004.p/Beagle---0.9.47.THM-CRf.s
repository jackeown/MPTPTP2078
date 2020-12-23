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
% DateTime   : Thu Dec  3 10:01:57 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   74 (  99 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 165 expanded)
%              Number of equality atoms :   20 (  36 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_relat_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v3_relat_1,type,(
    v3_relat_1: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v3_relat_1(A)
        <=> ! [B] :
              ( r2_hidden(B,k2_relat_1(A))
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v3_relat_1(A)
      <=> r1_tarski(k2_relat_1(A),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).

tff(f_61,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_50,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_82,plain,(
    ~ v3_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_146,plain,(
    ! [B_50,C_51,A_52] :
      ( r2_hidden(B_50,C_51)
      | ~ r1_tarski(k2_tarski(A_52,B_50),C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_166,plain,(
    ! [B_53,A_54] : r2_hidden(B_53,k2_tarski(A_54,B_53)) ),
    inference(resolution,[status(thm)],[c_12,c_146])).

tff(c_169,plain,(
    ! [A_10] : r2_hidden(A_10,k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_166])).

tff(c_357,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_1'(A_76,B_77),A_76)
      | r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [B_37] :
      ( v3_relat_1('#skF_2')
      | k1_xboole_0 = B_37
      | ~ r2_hidden(B_37,k2_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_202,plain,(
    ! [B_37] :
      ( k1_xboole_0 = B_37
      | ~ r2_hidden(B_37,k2_relat_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_60])).

tff(c_367,plain,(
    ! [B_77] :
      ( '#skF_1'(k2_relat_1('#skF_2'),B_77) = k1_xboole_0
      | r1_tarski(k2_relat_1('#skF_2'),B_77) ) ),
    inference(resolution,[status(thm)],[c_357,c_202])).

tff(c_818,plain,(
    ! [A_126] :
      ( v3_relat_1(A_126)
      | ~ r1_tarski(k2_relat_1(A_126),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_825,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_367,c_818])).

tff(c_829,plain,
    ( v3_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_825])).

tff(c_830,plain,(
    '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_829])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_834,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_4])).

tff(c_841,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_834])).

tff(c_44,plain,(
    ! [A_34] :
      ( v3_relat_1(A_34)
      | ~ r1_tarski(k2_relat_1(A_34),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_846,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_841,c_44])).

tff(c_851,plain,(
    v3_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_846])).

tff(c_853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_851])).

tff(c_854,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_855,plain,(
    v3_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1333,plain,(
    ! [A_184] :
      ( r1_tarski(k2_relat_1(A_184),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(A_184)
      | ~ v1_relat_1(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_52,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_2'))
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_886,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_52])).

tff(c_1253,plain,(
    ! [C_177,B_178,A_179] :
      ( r2_hidden(C_177,B_178)
      | ~ r2_hidden(C_177,A_179)
      | ~ r1_tarski(A_179,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1286,plain,(
    ! [B_178] :
      ( r2_hidden('#skF_3',B_178)
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_178) ) ),
    inference(resolution,[status(thm)],[c_886,c_1253])).

tff(c_1337,plain,
    ( r2_hidden('#skF_3',k1_tarski(k1_xboole_0))
    | ~ v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1333,c_1286])).

tff(c_1342,plain,(
    r2_hidden('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_855,c_1337])).

tff(c_34,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    ! [A_33] : k3_tarski(k1_zfmisc_1(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_859,plain,(
    k3_tarski(k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_930,plain,(
    ! [A_132,B_133] :
      ( r1_tarski(A_132,k3_tarski(B_133))
      | ~ r2_hidden(A_132,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_939,plain,(
    ! [A_132] :
      ( r1_tarski(A_132,k1_xboole_0)
      | ~ r2_hidden(A_132,k1_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_859,c_930])).

tff(c_1350,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1342,c_939])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_967,plain,(
    ! [B_140,A_141] :
      ( B_140 = A_141
      | ~ r1_tarski(B_140,A_141)
      | ~ r1_tarski(A_141,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_985,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_967])).

tff(c_1353,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1350,c_985])).

tff(c_1359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_854,c_1353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:51:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.48  
% 3.15/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.49  %$ r2_hidden > r1_tarski > v3_relat_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.15/1.49  
% 3.15/1.49  %Foreground sorts:
% 3.15/1.49  
% 3.15/1.49  
% 3.15/1.49  %Background operators:
% 3.15/1.49  
% 3.15/1.49  
% 3.15/1.49  %Foreground operators:
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.49  tff(v3_relat_1, type, v3_relat_1: $i > $o).
% 3.15/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.15/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.15/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.49  
% 3.15/1.50  tff(f_85, negated_conjecture, ~(![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> (![B]: (r2_hidden(B, k2_relat_1(A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_relat_1)).
% 3.15/1.50  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.15/1.50  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/1.50  tff(f_67, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.15/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.15/1.50  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> r1_tarski(k2_relat_1(A), k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_relat_1)).
% 3.15/1.50  tff(f_61, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 3.15/1.50  tff(f_69, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.15/1.50  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.15/1.50  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.15/1.50  tff(c_50, plain, (k1_xboole_0!='#skF_3' | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.15/1.50  tff(c_82, plain, (~v3_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 3.15/1.50  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.15/1.50  tff(c_18, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.15/1.50  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.15/1.50  tff(c_146, plain, (![B_50, C_51, A_52]: (r2_hidden(B_50, C_51) | ~r1_tarski(k2_tarski(A_52, B_50), C_51))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.15/1.50  tff(c_166, plain, (![B_53, A_54]: (r2_hidden(B_53, k2_tarski(A_54, B_53)))), inference(resolution, [status(thm)], [c_12, c_146])).
% 3.15/1.50  tff(c_169, plain, (![A_10]: (r2_hidden(A_10, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_166])).
% 3.15/1.50  tff(c_357, plain, (![A_76, B_77]: (r2_hidden('#skF_1'(A_76, B_77), A_76) | r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.50  tff(c_60, plain, (![B_37]: (v3_relat_1('#skF_2') | k1_xboole_0=B_37 | ~r2_hidden(B_37, k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.15/1.50  tff(c_202, plain, (![B_37]: (k1_xboole_0=B_37 | ~r2_hidden(B_37, k2_relat_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_82, c_60])).
% 3.15/1.50  tff(c_367, plain, (![B_77]: ('#skF_1'(k2_relat_1('#skF_2'), B_77)=k1_xboole_0 | r1_tarski(k2_relat_1('#skF_2'), B_77))), inference(resolution, [status(thm)], [c_357, c_202])).
% 3.15/1.50  tff(c_818, plain, (![A_126]: (v3_relat_1(A_126) | ~r1_tarski(k2_relat_1(A_126), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.15/1.50  tff(c_825, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_367, c_818])).
% 3.15/1.50  tff(c_829, plain, (v3_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_825])).
% 3.15/1.50  tff(c_830, plain, ('#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_82, c_829])).
% 3.15/1.50  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.50  tff(c_834, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_830, c_4])).
% 3.15/1.50  tff(c_841, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_834])).
% 3.15/1.50  tff(c_44, plain, (![A_34]: (v3_relat_1(A_34) | ~r1_tarski(k2_relat_1(A_34), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.15/1.50  tff(c_846, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_841, c_44])).
% 3.15/1.50  tff(c_851, plain, (v3_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_846])).
% 3.15/1.50  tff(c_853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_851])).
% 3.15/1.50  tff(c_854, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 3.15/1.50  tff(c_855, plain, (v3_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 3.15/1.50  tff(c_1333, plain, (![A_184]: (r1_tarski(k2_relat_1(A_184), k1_tarski(k1_xboole_0)) | ~v3_relat_1(A_184) | ~v1_relat_1(A_184))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.15/1.50  tff(c_52, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2')) | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.15/1.50  tff(c_886, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_855, c_52])).
% 3.15/1.50  tff(c_1253, plain, (![C_177, B_178, A_179]: (r2_hidden(C_177, B_178) | ~r2_hidden(C_177, A_179) | ~r1_tarski(A_179, B_178))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.50  tff(c_1286, plain, (![B_178]: (r2_hidden('#skF_3', B_178) | ~r1_tarski(k2_relat_1('#skF_2'), B_178))), inference(resolution, [status(thm)], [c_886, c_1253])).
% 3.15/1.50  tff(c_1337, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0)) | ~v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1333, c_1286])).
% 3.15/1.50  tff(c_1342, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_855, c_1337])).
% 3.15/1.50  tff(c_34, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.15/1.50  tff(c_42, plain, (![A_33]: (k3_tarski(k1_zfmisc_1(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.15/1.50  tff(c_859, plain, (k3_tarski(k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34, c_42])).
% 3.15/1.50  tff(c_930, plain, (![A_132, B_133]: (r1_tarski(A_132, k3_tarski(B_133)) | ~r2_hidden(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.15/1.50  tff(c_939, plain, (![A_132]: (r1_tarski(A_132, k1_xboole_0) | ~r2_hidden(A_132, k1_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_859, c_930])).
% 3.15/1.50  tff(c_1350, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_1342, c_939])).
% 3.15/1.50  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.15/1.50  tff(c_967, plain, (![B_140, A_141]: (B_140=A_141 | ~r1_tarski(B_140, A_141) | ~r1_tarski(A_141, B_140))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.15/1.50  tff(c_985, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_967])).
% 3.15/1.50  tff(c_1353, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1350, c_985])).
% 3.15/1.50  tff(c_1359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_854, c_1353])).
% 3.15/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.50  
% 3.15/1.50  Inference rules
% 3.15/1.50  ----------------------
% 3.15/1.50  #Ref     : 0
% 3.15/1.50  #Sup     : 283
% 3.15/1.50  #Fact    : 0
% 3.15/1.50  #Define  : 0
% 3.15/1.50  #Split   : 4
% 3.15/1.50  #Chain   : 0
% 3.15/1.50  #Close   : 0
% 3.15/1.50  
% 3.15/1.50  Ordering : KBO
% 3.15/1.50  
% 3.15/1.50  Simplification rules
% 3.15/1.50  ----------------------
% 3.15/1.50  #Subsume      : 10
% 3.15/1.50  #Demod        : 131
% 3.15/1.50  #Tautology    : 148
% 3.15/1.50  #SimpNegUnit  : 6
% 3.15/1.50  #BackRed      : 4
% 3.15/1.50  
% 3.15/1.50  #Partial instantiations: 0
% 3.15/1.50  #Strategies tried      : 1
% 3.15/1.50  
% 3.15/1.50  Timing (in seconds)
% 3.15/1.50  ----------------------
% 3.31/1.50  Preprocessing        : 0.32
% 3.31/1.50  Parsing              : 0.17
% 3.31/1.50  CNF conversion       : 0.02
% 3.31/1.50  Main loop            : 0.41
% 3.31/1.50  Inferencing          : 0.15
% 3.31/1.50  Reduction            : 0.14
% 3.31/1.50  Demodulation         : 0.10
% 3.31/1.50  BG Simplification    : 0.02
% 3.31/1.50  Subsumption          : 0.06
% 3.31/1.50  Abstraction          : 0.02
% 3.31/1.50  MUC search           : 0.00
% 3.31/1.50  Cooper               : 0.00
% 3.31/1.50  Total                : 0.76
% 3.31/1.50  Index Insertion      : 0.00
% 3.31/1.50  Index Deletion       : 0.00
% 3.31/1.50  Index Matching       : 0.00
% 3.31/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
