%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:11 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 209 expanded)
%              Number of leaves         :   20 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  171 ( 504 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => r1_ordinal1(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).

tff(f_37,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( ~ v1_xboole_0(k1_ordinal1(A))
        & v3_ordinal1(k1_ordinal1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_74,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_88,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_83,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_30,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_ordinal1(A_6,A_6)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_736,plain,(
    ! [B_7] : ~ v3_ordinal1(B_7) ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_28,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_736,c_28])).

tff(c_741,plain,(
    ! [A_6] :
      ( r1_ordinal1(A_6,A_6)
      | ~ v3_ordinal1(A_6) ) ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_4,plain,(
    ! [A_3] :
      ( v3_ordinal1(k1_ordinal1(A_3))
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ r1_ordinal1(A_4,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_284,plain,(
    ! [B_59,A_60] :
      ( r2_hidden(B_59,A_60)
      | B_59 = A_60
      | r2_hidden(A_60,B_59)
      | ~ v3_ordinal1(B_59)
      | ~ v3_ordinal1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_499,plain,(
    ! [B_68,A_69] :
      ( ~ r1_tarski(B_68,A_69)
      | r2_hidden(B_68,A_69)
      | B_68 = A_69
      | ~ v3_ordinal1(B_68)
      | ~ v3_ordinal1(A_69) ) ),
    inference(resolution,[status(thm)],[c_284,c_26])).

tff(c_38,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_54,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_32,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_56,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32])).

tff(c_555,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_499,c_56])).

tff(c_581,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_555])).

tff(c_585,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_581])).

tff(c_588,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_585])).

tff(c_591,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_588])).

tff(c_24,plain,(
    ! [B_16,A_14] :
      ( r2_hidden(B_16,A_14)
      | r1_ordinal1(A_14,B_16)
      | ~ v3_ordinal1(B_16)
      | ~ v3_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_213,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ r1_ordinal1(A_50,B_51)
      | ~ v3_ordinal1(B_51)
      | ~ v3_ordinal1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    ! [A_29,B_30] :
      ( ~ r2_hidden(A_29,B_30)
      | r2_hidden(A_29,k1_ordinal1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(k1_ordinal1(B_30),A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_57,c_26])).

tff(c_604,plain,(
    ! [B_74,B_75] :
      ( ~ r2_hidden(B_74,B_75)
      | ~ r1_ordinal1(k1_ordinal1(B_75),B_74)
      | ~ v3_ordinal1(B_74)
      | ~ v3_ordinal1(k1_ordinal1(B_75)) ) ),
    inference(resolution,[status(thm)],[c_213,c_67])).

tff(c_631,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_604])).

tff(c_640,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_631])).

tff(c_641,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_640])).

tff(c_644,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_641])).

tff(c_648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_644])).

tff(c_649,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_640])).

tff(c_662,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_649])).

tff(c_676,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_662])).

tff(c_678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_591,c_676])).

tff(c_679,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_581])).

tff(c_683,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_54])).

tff(c_18,plain,(
    ! [B_10] : r2_hidden(B_10,k1_ordinal1(B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    ! [B_26,A_27] :
      ( ~ r1_tarski(B_26,A_27)
      | ~ r2_hidden(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_52,plain,(
    ! [B_10] : ~ r1_tarski(k1_ordinal1(B_10),B_10) ),
    inference(resolution,[status(thm)],[c_18,c_48])).

tff(c_223,plain,(
    ! [B_51] :
      ( ~ r1_ordinal1(k1_ordinal1(B_51),B_51)
      | ~ v3_ordinal1(B_51)
      | ~ v3_ordinal1(k1_ordinal1(B_51)) ) ),
    inference(resolution,[status(thm)],[c_213,c_52])).

tff(c_714,plain,
    ( ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_683,c_223])).

tff(c_717,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_714])).

tff(c_722,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_717])).

tff(c_726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_722])).

tff(c_727,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_735,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_727,c_2])).

tff(c_807,plain,(
    ! [B_90,A_91] :
      ( r2_hidden(B_90,A_91)
      | r1_ordinal1(A_91,B_90)
      | ~ v3_ordinal1(B_90)
      | ~ v3_ordinal1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1060,plain,(
    ! [A_104,B_105] :
      ( ~ r2_hidden(A_104,B_105)
      | r1_ordinal1(A_104,B_105)
      | ~ v3_ordinal1(B_105)
      | ~ v3_ordinal1(A_104) ) ),
    inference(resolution,[status(thm)],[c_807,c_2])).

tff(c_1101,plain,(
    ! [B_106,A_107] :
      ( r1_ordinal1(B_106,A_107)
      | r1_ordinal1(A_107,B_106)
      | ~ v3_ordinal1(B_106)
      | ~ v3_ordinal1(A_107) ) ),
    inference(resolution,[status(thm)],[c_24,c_1060])).

tff(c_728,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1111,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1101,c_728])).

tff(c_1128,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1111])).

tff(c_1136,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1128])).

tff(c_1139,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_1136])).

tff(c_1143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1139])).

tff(c_1145,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1128])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | r2_hidden(A_9,B_10)
      | ~ r2_hidden(A_9,k1_ordinal1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1324,plain,(
    ! [B_118,B_117] :
      ( B_118 = B_117
      | r2_hidden(B_117,B_118)
      | r1_ordinal1(k1_ordinal1(B_118),B_117)
      | ~ v3_ordinal1(B_117)
      | ~ v3_ordinal1(k1_ordinal1(B_118)) ) ),
    inference(resolution,[status(thm)],[c_807,c_16])).

tff(c_1331,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1324,c_728])).

tff(c_1336,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1145,c_28,c_1331])).

tff(c_1337,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_735,c_1336])).

tff(c_895,plain,(
    ! [A_99,B_100] :
      ( r1_tarski(A_99,B_100)
      | ~ r1_ordinal1(A_99,B_100)
      | ~ v3_ordinal1(B_100)
      | ~ v3_ordinal1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_734,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_727,c_26])).

tff(c_905,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_895,c_734])).

tff(c_914,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_905])).

tff(c_1339,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_914])).

tff(c_1355,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_741,c_1339])).

tff(c_1359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:56:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.49  
% 3.14/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.49  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k1_ordinal1 > #skF_2 > #skF_1
% 3.14/1.49  
% 3.14/1.49  %Foreground sorts:
% 3.14/1.49  
% 3.14/1.49  
% 3.14/1.49  %Background operators:
% 3.14/1.49  
% 3.14/1.49  
% 3.14/1.49  %Foreground operators:
% 3.14/1.49  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.14/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.49  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.14/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.49  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.14/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.49  
% 3.14/1.50  tff(f_98, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 3.14/1.50  tff(f_51, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => r1_ordinal1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_ordinal1)).
% 3.14/1.50  tff(f_37, axiom, (![A]: (v3_ordinal1(A) => (~v1_xboole_0(k1_ordinal1(A)) & v3_ordinal1(k1_ordinal1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_ordinal1)).
% 3.14/1.50  tff(f_45, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.14/1.50  tff(f_74, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.14/1.50  tff(f_88, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.14/1.50  tff(f_83, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.14/1.50  tff(f_59, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.14/1.50  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.14/1.50  tff(c_30, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.14/1.50  tff(c_12, plain, (![A_6, B_7]: (r1_ordinal1(A_6, A_6) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.14/1.50  tff(c_736, plain, (![B_7]: (~v3_ordinal1(B_7))), inference(splitLeft, [status(thm)], [c_12])).
% 3.14/1.50  tff(c_28, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.14/1.50  tff(c_740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_736, c_28])).
% 3.14/1.50  tff(c_741, plain, (![A_6]: (r1_ordinal1(A_6, A_6) | ~v3_ordinal1(A_6))), inference(splitRight, [status(thm)], [c_12])).
% 3.14/1.50  tff(c_4, plain, (![A_3]: (v3_ordinal1(k1_ordinal1(A_3)) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.14/1.50  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~r1_ordinal1(A_4, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.50  tff(c_284, plain, (![B_59, A_60]: (r2_hidden(B_59, A_60) | B_59=A_60 | r2_hidden(A_60, B_59) | ~v3_ordinal1(B_59) | ~v3_ordinal1(A_60))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.14/1.50  tff(c_26, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.14/1.50  tff(c_499, plain, (![B_68, A_69]: (~r1_tarski(B_68, A_69) | r2_hidden(B_68, A_69) | B_68=A_69 | ~v3_ordinal1(B_68) | ~v3_ordinal1(A_69))), inference(resolution, [status(thm)], [c_284, c_26])).
% 3.14/1.50  tff(c_38, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.14/1.50  tff(c_54, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 3.14/1.50  tff(c_32, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.14/1.50  tff(c_56, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_32])).
% 3.14/1.50  tff(c_555, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1' | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_499, c_56])).
% 3.14/1.50  tff(c_581, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_555])).
% 3.14/1.50  tff(c_585, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_581])).
% 3.14/1.50  tff(c_588, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_585])).
% 3.14/1.50  tff(c_591, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_588])).
% 3.14/1.50  tff(c_24, plain, (![B_16, A_14]: (r2_hidden(B_16, A_14) | r1_ordinal1(A_14, B_16) | ~v3_ordinal1(B_16) | ~v3_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.50  tff(c_213, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~r1_ordinal1(A_50, B_51) | ~v3_ordinal1(B_51) | ~v3_ordinal1(A_50))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.50  tff(c_57, plain, (![A_29, B_30]: (~r2_hidden(A_29, B_30) | r2_hidden(A_29, k1_ordinal1(B_30)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.50  tff(c_67, plain, (![B_30, A_29]: (~r1_tarski(k1_ordinal1(B_30), A_29) | ~r2_hidden(A_29, B_30))), inference(resolution, [status(thm)], [c_57, c_26])).
% 3.14/1.50  tff(c_604, plain, (![B_74, B_75]: (~r2_hidden(B_74, B_75) | ~r1_ordinal1(k1_ordinal1(B_75), B_74) | ~v3_ordinal1(B_74) | ~v3_ordinal1(k1_ordinal1(B_75)))), inference(resolution, [status(thm)], [c_213, c_67])).
% 3.14/1.50  tff(c_631, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_604])).
% 3.14/1.50  tff(c_640, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_631])).
% 3.14/1.50  tff(c_641, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_640])).
% 3.14/1.50  tff(c_644, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_641])).
% 3.14/1.50  tff(c_648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_644])).
% 3.14/1.50  tff(c_649, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_640])).
% 3.14/1.50  tff(c_662, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_649])).
% 3.14/1.50  tff(c_676, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_662])).
% 3.14/1.50  tff(c_678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_591, c_676])).
% 3.14/1.50  tff(c_679, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_581])).
% 3.14/1.50  tff(c_683, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_679, c_54])).
% 3.14/1.50  tff(c_18, plain, (![B_10]: (r2_hidden(B_10, k1_ordinal1(B_10)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.50  tff(c_48, plain, (![B_26, A_27]: (~r1_tarski(B_26, A_27) | ~r2_hidden(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.14/1.50  tff(c_52, plain, (![B_10]: (~r1_tarski(k1_ordinal1(B_10), B_10))), inference(resolution, [status(thm)], [c_18, c_48])).
% 3.14/1.50  tff(c_223, plain, (![B_51]: (~r1_ordinal1(k1_ordinal1(B_51), B_51) | ~v3_ordinal1(B_51) | ~v3_ordinal1(k1_ordinal1(B_51)))), inference(resolution, [status(thm)], [c_213, c_52])).
% 3.14/1.50  tff(c_714, plain, (~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_683, c_223])).
% 3.14/1.50  tff(c_717, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_714])).
% 3.14/1.50  tff(c_722, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_717])).
% 3.14/1.50  tff(c_726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_722])).
% 3.14/1.50  tff(c_727, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 3.14/1.50  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.14/1.50  tff(c_735, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_727, c_2])).
% 3.14/1.50  tff(c_807, plain, (![B_90, A_91]: (r2_hidden(B_90, A_91) | r1_ordinal1(A_91, B_90) | ~v3_ordinal1(B_90) | ~v3_ordinal1(A_91))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.50  tff(c_1060, plain, (![A_104, B_105]: (~r2_hidden(A_104, B_105) | r1_ordinal1(A_104, B_105) | ~v3_ordinal1(B_105) | ~v3_ordinal1(A_104))), inference(resolution, [status(thm)], [c_807, c_2])).
% 3.14/1.50  tff(c_1101, plain, (![B_106, A_107]: (r1_ordinal1(B_106, A_107) | r1_ordinal1(A_107, B_106) | ~v3_ordinal1(B_106) | ~v3_ordinal1(A_107))), inference(resolution, [status(thm)], [c_24, c_1060])).
% 3.14/1.50  tff(c_728, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 3.14/1.50  tff(c_1111, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_1101, c_728])).
% 3.14/1.50  tff(c_1128, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1111])).
% 3.14/1.50  tff(c_1136, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1128])).
% 3.14/1.50  tff(c_1139, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_1136])).
% 3.14/1.50  tff(c_1143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1139])).
% 3.14/1.50  tff(c_1145, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_1128])).
% 3.14/1.50  tff(c_16, plain, (![B_10, A_9]: (B_10=A_9 | r2_hidden(A_9, B_10) | ~r2_hidden(A_9, k1_ordinal1(B_10)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.50  tff(c_1324, plain, (![B_118, B_117]: (B_118=B_117 | r2_hidden(B_117, B_118) | r1_ordinal1(k1_ordinal1(B_118), B_117) | ~v3_ordinal1(B_117) | ~v3_ordinal1(k1_ordinal1(B_118)))), inference(resolution, [status(thm)], [c_807, c_16])).
% 3.14/1.50  tff(c_1331, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_1324, c_728])).
% 3.14/1.50  tff(c_1336, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1145, c_28, c_1331])).
% 3.14/1.50  tff(c_1337, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_735, c_1336])).
% 3.14/1.50  tff(c_895, plain, (![A_99, B_100]: (r1_tarski(A_99, B_100) | ~r1_ordinal1(A_99, B_100) | ~v3_ordinal1(B_100) | ~v3_ordinal1(A_99))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.50  tff(c_734, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_727, c_26])).
% 3.14/1.50  tff(c_905, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_895, c_734])).
% 3.14/1.50  tff(c_914, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_905])).
% 3.14/1.50  tff(c_1339, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_914])).
% 3.14/1.50  tff(c_1355, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_741, c_1339])).
% 3.14/1.50  tff(c_1359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1355])).
% 3.14/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.50  
% 3.14/1.50  Inference rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Ref     : 0
% 3.14/1.50  #Sup     : 238
% 3.14/1.50  #Fact    : 8
% 3.14/1.50  #Define  : 0
% 3.14/1.50  #Split   : 6
% 3.14/1.50  #Chain   : 0
% 3.14/1.50  #Close   : 0
% 3.14/1.50  
% 3.14/1.50  Ordering : KBO
% 3.14/1.50  
% 3.14/1.50  Simplification rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Subsume      : 55
% 3.14/1.50  #Demod        : 75
% 3.14/1.50  #Tautology    : 37
% 3.14/1.50  #SimpNegUnit  : 10
% 3.14/1.50  #BackRed      : 16
% 3.14/1.50  
% 3.14/1.50  #Partial instantiations: 0
% 3.14/1.50  #Strategies tried      : 1
% 3.14/1.50  
% 3.14/1.50  Timing (in seconds)
% 3.14/1.50  ----------------------
% 3.14/1.51  Preprocessing        : 0.27
% 3.14/1.51  Parsing              : 0.15
% 3.14/1.51  CNF conversion       : 0.02
% 3.14/1.51  Main loop            : 0.43
% 3.14/1.51  Inferencing          : 0.16
% 3.14/1.51  Reduction            : 0.11
% 3.14/1.51  Demodulation         : 0.07
% 3.14/1.51  BG Simplification    : 0.03
% 3.14/1.51  Subsumption          : 0.10
% 3.14/1.51  Abstraction          : 0.02
% 3.14/1.51  MUC search           : 0.00
% 3.14/1.51  Cooper               : 0.00
% 3.14/1.51  Total                : 0.74
% 3.14/1.51  Index Insertion      : 0.00
% 3.14/1.51  Index Deletion       : 0.00
% 3.14/1.51  Index Matching       : 0.00
% 3.14/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
