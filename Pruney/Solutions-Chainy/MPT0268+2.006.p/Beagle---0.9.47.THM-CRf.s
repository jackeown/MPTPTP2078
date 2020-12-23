%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:34 EST 2020

% Result     : Theorem 9.99s
% Output     : CNFRefutation 10.02s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 121 expanded)
%              Number of leaves         :   38 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :  112 ( 165 expanded)
%              Number of equality atoms :   47 (  71 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_103,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_105,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_86,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_102,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_166,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_34,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_170,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = k1_xboole_0
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_186,plain,(
    ! [B_17] : k4_xboole_0(B_17,B_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_170])).

tff(c_44,plain,(
    ! [A_24,B_25] : r1_tarski(k4_xboole_0(A_24,B_25),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1055,plain,(
    ! [B_147,A_148] :
      ( k1_tarski(B_147) = A_148
      | k1_xboole_0 = A_148
      | ~ r1_tarski(A_148,k1_tarski(B_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_7761,plain,(
    ! [B_361,B_362] :
      ( k4_xboole_0(k1_tarski(B_361),B_362) = k1_tarski(B_361)
      | k4_xboole_0(k1_tarski(B_361),B_362) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_1055])).

tff(c_46,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7840,plain,(
    ! [B_361,B_362] :
      ( k4_xboole_0(k1_tarski(B_361),k1_tarski(B_361)) = k3_xboole_0(k1_tarski(B_361),B_362)
      | k4_xboole_0(k1_tarski(B_361),B_362) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7761,c_46])).

tff(c_15940,plain,(
    ! [B_533,B_534] :
      ( k3_xboole_0(k1_tarski(B_533),B_534) = k1_xboole_0
      | k4_xboole_0(k1_tarski(B_533),B_534) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_7840])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,(
    ! [A_38] : k2_tarski(A_38,A_38) = k1_tarski(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_534,plain,(
    ! [A_107,C_108,B_109] :
      ( r2_hidden(A_107,C_108)
      | ~ r1_tarski(k2_tarski(A_107,B_109),C_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_549,plain,(
    ! [A_110,C_111] :
      ( r2_hidden(A_110,C_111)
      | ~ r1_tarski(k1_tarski(A_110),C_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_534])).

tff(c_558,plain,(
    ! [A_110,B_19] :
      ( r2_hidden(A_110,B_19)
      | k4_xboole_0(k1_tarski(A_110),B_19) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_549])).

tff(c_16165,plain,(
    ! [B_535,B_536] :
      ( r2_hidden(B_535,B_536)
      | k3_xboole_0(k1_tarski(B_535),B_536) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15940,c_558])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16738,plain,(
    ! [B_539,B_540] :
      ( k3_xboole_0(B_539,k1_tarski(B_540)) = k1_xboole_0
      | r2_hidden(B_540,B_539) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16165,c_2])).

tff(c_493,plain,(
    ! [B_104,A_105] :
      ( B_104 = A_105
      | ~ r1_tarski(B_104,A_105)
      | ~ r1_tarski(A_105,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4210,plain,(
    ! [A_272,B_273] :
      ( k4_xboole_0(A_272,B_273) = A_272
      | ~ r1_tarski(A_272,k4_xboole_0(A_272,B_273)) ) ),
    inference(resolution,[status(thm)],[c_44,c_493])).

tff(c_4255,plain,(
    ! [A_18,B_273] :
      ( k4_xboole_0(A_18,B_273) = A_18
      | k4_xboole_0(A_18,k4_xboole_0(A_18,B_273)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_4210])).

tff(c_4275,plain,(
    ! [A_274,B_275] :
      ( k4_xboole_0(A_274,B_275) = A_274
      | k3_xboole_0(A_274,B_275) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4255])).

tff(c_100,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_209,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_4427,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_8')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4275,c_209])).

tff(c_16911,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_16738,c_4427])).

tff(c_17128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_16911])).

tff(c_17129,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_17166,plain,(
    ! [A_543,B_544] : k1_enumset1(A_543,A_543,B_544) = k2_tarski(A_543,B_544) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_56,plain,(
    ! [E_37,A_31,C_33] : r2_hidden(E_37,k1_enumset1(A_31,E_37,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_17185,plain,(
    ! [A_545,B_546] : r2_hidden(A_545,k2_tarski(A_545,B_546)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17166,c_56])).

tff(c_17188,plain,(
    ! [A_38] : r2_hidden(A_38,k1_tarski(A_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_17185])).

tff(c_17130,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_104,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_17334,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17130,c_104])).

tff(c_50,plain,(
    ! [A_29,B_30] : r1_xboole_0(k4_xboole_0(A_29,B_30),B_30) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_17344,plain,(
    r1_xboole_0('#skF_9',k1_tarski('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17334,c_50])).

tff(c_18564,plain,(
    ! [A_618,B_619,C_620] :
      ( ~ r1_xboole_0(A_618,B_619)
      | ~ r2_hidden(C_620,B_619)
      | ~ r2_hidden(C_620,A_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18707,plain,(
    ! [C_628] :
      ( ~ r2_hidden(C_628,k1_tarski('#skF_10'))
      | ~ r2_hidden(C_628,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_17344,c_18564])).

tff(c_18719,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_17188,c_18707])).

tff(c_18729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17129,c_18719])).

tff(c_18730,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_18854,plain,(
    ! [A_646,B_647] : k1_enumset1(A_646,A_646,B_647) = k2_tarski(A_646,B_647) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_58,plain,(
    ! [E_37,B_32,C_33] : r2_hidden(E_37,k1_enumset1(E_37,B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_18966,plain,(
    ! [A_650,B_651] : r2_hidden(A_650,k2_tarski(A_650,B_651)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18854,c_58])).

tff(c_18969,plain,(
    ! [A_38] : r2_hidden(A_38,k1_tarski(A_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_18966])).

tff(c_18731,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_106,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_18948,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18731,c_106])).

tff(c_18958,plain,(
    r1_xboole_0('#skF_9',k1_tarski('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18948,c_50])).

tff(c_19899,plain,(
    ! [A_706,B_707,C_708] :
      ( ~ r1_xboole_0(A_706,B_707)
      | ~ r2_hidden(C_708,B_707)
      | ~ r2_hidden(C_708,A_706) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20031,plain,(
    ! [C_716] :
      ( ~ r2_hidden(C_716,k1_tarski('#skF_10'))
      | ~ r2_hidden(C_716,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_18958,c_19899])).

tff(c_20043,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_18969,c_20031])).

tff(c_20053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18730,c_20043])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.37  % Computer   : n022.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 14:38:40 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.38  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.99/3.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.02/3.82  
% 10.02/3.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.02/3.82  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5
% 10.02/3.82  
% 10.02/3.82  %Foreground sorts:
% 10.02/3.82  
% 10.02/3.82  
% 10.02/3.82  %Background operators:
% 10.02/3.82  
% 10.02/3.82  
% 10.02/3.82  %Foreground operators:
% 10.02/3.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.02/3.82  tff('#skF_4', type, '#skF_4': $i > $i).
% 10.02/3.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.02/3.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.02/3.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.02/3.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.02/3.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.02/3.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.02/3.82  tff('#skF_7', type, '#skF_7': $i).
% 10.02/3.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.02/3.82  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.02/3.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.02/3.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.02/3.82  tff('#skF_10', type, '#skF_10': $i).
% 10.02/3.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.02/3.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.02/3.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.02/3.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.02/3.82  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 10.02/3.82  tff('#skF_9', type, '#skF_9': $i).
% 10.02/3.82  tff('#skF_8', type, '#skF_8': $i).
% 10.02/3.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.02/3.82  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 10.02/3.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.02/3.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.02/3.82  
% 10.02/3.83  tff(f_132, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 10.02/3.83  tff(f_68, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.02/3.83  tff(f_72, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.02/3.83  tff(f_80, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.02/3.83  tff(f_115, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 10.02/3.83  tff(f_82, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.02/3.83  tff(f_103, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.02/3.83  tff(f_126, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 10.02/3.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.02/3.83  tff(f_105, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 10.02/3.83  tff(f_101, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 10.02/3.83  tff(f_86, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 10.02/3.83  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.02/3.83  tff(c_102, plain, (~r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.02/3.83  tff(c_166, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_102])).
% 10.02/3.83  tff(c_34, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.02/3.83  tff(c_170, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=k1_xboole_0 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.02/3.83  tff(c_186, plain, (![B_17]: (k4_xboole_0(B_17, B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_170])).
% 10.02/3.83  tff(c_44, plain, (![A_24, B_25]: (r1_tarski(k4_xboole_0(A_24, B_25), A_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.02/3.83  tff(c_1055, plain, (![B_147, A_148]: (k1_tarski(B_147)=A_148 | k1_xboole_0=A_148 | ~r1_tarski(A_148, k1_tarski(B_147)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.02/3.83  tff(c_7761, plain, (![B_361, B_362]: (k4_xboole_0(k1_tarski(B_361), B_362)=k1_tarski(B_361) | k4_xboole_0(k1_tarski(B_361), B_362)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_1055])).
% 10.02/3.83  tff(c_46, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.02/3.83  tff(c_7840, plain, (![B_361, B_362]: (k4_xboole_0(k1_tarski(B_361), k1_tarski(B_361))=k3_xboole_0(k1_tarski(B_361), B_362) | k4_xboole_0(k1_tarski(B_361), B_362)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7761, c_46])).
% 10.02/3.83  tff(c_15940, plain, (![B_533, B_534]: (k3_xboole_0(k1_tarski(B_533), B_534)=k1_xboole_0 | k4_xboole_0(k1_tarski(B_533), B_534)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_7840])).
% 10.02/3.83  tff(c_36, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | k4_xboole_0(A_18, B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.02/3.83  tff(c_76, plain, (![A_38]: (k2_tarski(A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.02/3.83  tff(c_534, plain, (![A_107, C_108, B_109]: (r2_hidden(A_107, C_108) | ~r1_tarski(k2_tarski(A_107, B_109), C_108))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.02/3.83  tff(c_549, plain, (![A_110, C_111]: (r2_hidden(A_110, C_111) | ~r1_tarski(k1_tarski(A_110), C_111))), inference(superposition, [status(thm), theory('equality')], [c_76, c_534])).
% 10.02/3.83  tff(c_558, plain, (![A_110, B_19]: (r2_hidden(A_110, B_19) | k4_xboole_0(k1_tarski(A_110), B_19)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_549])).
% 10.02/3.83  tff(c_16165, plain, (![B_535, B_536]: (r2_hidden(B_535, B_536) | k3_xboole_0(k1_tarski(B_535), B_536)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15940, c_558])).
% 10.02/3.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.02/3.83  tff(c_16738, plain, (![B_539, B_540]: (k3_xboole_0(B_539, k1_tarski(B_540))=k1_xboole_0 | r2_hidden(B_540, B_539))), inference(superposition, [status(thm), theory('equality')], [c_16165, c_2])).
% 10.02/3.83  tff(c_493, plain, (![B_104, A_105]: (B_104=A_105 | ~r1_tarski(B_104, A_105) | ~r1_tarski(A_105, B_104))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.02/3.83  tff(c_4210, plain, (![A_272, B_273]: (k4_xboole_0(A_272, B_273)=A_272 | ~r1_tarski(A_272, k4_xboole_0(A_272, B_273)))), inference(resolution, [status(thm)], [c_44, c_493])).
% 10.02/3.83  tff(c_4255, plain, (![A_18, B_273]: (k4_xboole_0(A_18, B_273)=A_18 | k4_xboole_0(A_18, k4_xboole_0(A_18, B_273))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_4210])).
% 10.02/3.83  tff(c_4275, plain, (![A_274, B_275]: (k4_xboole_0(A_274, B_275)=A_274 | k3_xboole_0(A_274, B_275)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4255])).
% 10.02/3.83  tff(c_100, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.02/3.83  tff(c_209, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_100])).
% 10.02/3.83  tff(c_4427, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_8'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4275, c_209])).
% 10.02/3.83  tff(c_16911, plain, (r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_16738, c_4427])).
% 10.02/3.83  tff(c_17128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_16911])).
% 10.02/3.83  tff(c_17129, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_100])).
% 10.02/3.83  tff(c_17166, plain, (![A_543, B_544]: (k1_enumset1(A_543, A_543, B_544)=k2_tarski(A_543, B_544))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.02/3.83  tff(c_56, plain, (![E_37, A_31, C_33]: (r2_hidden(E_37, k1_enumset1(A_31, E_37, C_33)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.02/3.83  tff(c_17185, plain, (![A_545, B_546]: (r2_hidden(A_545, k2_tarski(A_545, B_546)))), inference(superposition, [status(thm), theory('equality')], [c_17166, c_56])).
% 10.02/3.83  tff(c_17188, plain, (![A_38]: (r2_hidden(A_38, k1_tarski(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_17185])).
% 10.02/3.83  tff(c_17130, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_100])).
% 10.02/3.83  tff(c_104, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.02/3.83  tff(c_17334, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_17130, c_104])).
% 10.02/3.83  tff(c_50, plain, (![A_29, B_30]: (r1_xboole_0(k4_xboole_0(A_29, B_30), B_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.02/3.83  tff(c_17344, plain, (r1_xboole_0('#skF_9', k1_tarski('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_17334, c_50])).
% 10.02/3.83  tff(c_18564, plain, (![A_618, B_619, C_620]: (~r1_xboole_0(A_618, B_619) | ~r2_hidden(C_620, B_619) | ~r2_hidden(C_620, A_618))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.02/3.83  tff(c_18707, plain, (![C_628]: (~r2_hidden(C_628, k1_tarski('#skF_10')) | ~r2_hidden(C_628, '#skF_9'))), inference(resolution, [status(thm)], [c_17344, c_18564])).
% 10.02/3.83  tff(c_18719, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_17188, c_18707])).
% 10.02/3.83  tff(c_18729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17129, c_18719])).
% 10.02/3.83  tff(c_18730, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_102])).
% 10.02/3.83  tff(c_18854, plain, (![A_646, B_647]: (k1_enumset1(A_646, A_646, B_647)=k2_tarski(A_646, B_647))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.02/3.83  tff(c_58, plain, (![E_37, B_32, C_33]: (r2_hidden(E_37, k1_enumset1(E_37, B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.02/3.83  tff(c_18966, plain, (![A_650, B_651]: (r2_hidden(A_650, k2_tarski(A_650, B_651)))), inference(superposition, [status(thm), theory('equality')], [c_18854, c_58])).
% 10.02/3.83  tff(c_18969, plain, (![A_38]: (r2_hidden(A_38, k1_tarski(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_18966])).
% 10.02/3.83  tff(c_18731, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_102])).
% 10.02/3.83  tff(c_106, plain, (~r2_hidden('#skF_8', '#skF_7') | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.02/3.83  tff(c_18948, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_18731, c_106])).
% 10.02/3.83  tff(c_18958, plain, (r1_xboole_0('#skF_9', k1_tarski('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_18948, c_50])).
% 10.02/3.83  tff(c_19899, plain, (![A_706, B_707, C_708]: (~r1_xboole_0(A_706, B_707) | ~r2_hidden(C_708, B_707) | ~r2_hidden(C_708, A_706))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.02/3.83  tff(c_20031, plain, (![C_716]: (~r2_hidden(C_716, k1_tarski('#skF_10')) | ~r2_hidden(C_716, '#skF_9'))), inference(resolution, [status(thm)], [c_18958, c_19899])).
% 10.02/3.83  tff(c_20043, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_18969, c_20031])).
% 10.02/3.83  tff(c_20053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18730, c_20043])).
% 10.02/3.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.02/3.83  
% 10.02/3.83  Inference rules
% 10.02/3.83  ----------------------
% 10.02/3.83  #Ref     : 1
% 10.02/3.83  #Sup     : 4905
% 10.02/3.83  #Fact    : 3
% 10.02/3.83  #Define  : 0
% 10.02/3.83  #Split   : 3
% 10.02/3.83  #Chain   : 0
% 10.02/3.83  #Close   : 0
% 10.02/3.83  
% 10.02/3.83  Ordering : KBO
% 10.02/3.83  
% 10.02/3.83  Simplification rules
% 10.02/3.83  ----------------------
% 10.02/3.83  #Subsume      : 1428
% 10.02/3.83  #Demod        : 3125
% 10.02/3.83  #Tautology    : 1867
% 10.02/3.83  #SimpNegUnit  : 155
% 10.02/3.83  #BackRed      : 1
% 10.02/3.83  
% 10.02/3.83  #Partial instantiations: 0
% 10.02/3.83  #Strategies tried      : 1
% 10.02/3.83  
% 10.02/3.83  Timing (in seconds)
% 10.02/3.83  ----------------------
% 10.02/3.84  Preprocessing        : 0.36
% 10.02/3.84  Parsing              : 0.18
% 10.02/3.84  CNF conversion       : 0.03
% 10.02/3.84  Main loop            : 2.65
% 10.02/3.84  Inferencing          : 0.63
% 10.02/3.84  Reduction            : 1.21
% 10.02/3.84  Demodulation         : 0.99
% 10.02/3.84  BG Simplification    : 0.08
% 10.02/3.84  Subsumption          : 0.58
% 10.02/3.84  Abstraction          : 0.13
% 10.02/3.84  MUC search           : 0.00
% 10.02/3.84  Cooper               : 0.00
% 10.02/3.84  Total                : 3.05
% 10.02/3.84  Index Insertion      : 0.00
% 10.02/3.84  Index Deletion       : 0.00
% 10.02/3.84  Index Matching       : 0.00
% 10.02/3.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
