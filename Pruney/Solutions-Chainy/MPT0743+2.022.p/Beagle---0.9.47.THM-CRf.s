%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:11 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 263 expanded)
%              Number of leaves         :   20 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  164 ( 640 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_76,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_63,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_72,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_48,axiom,(
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

tff(c_28,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22,plain,(
    ! [A_15] :
      ( v3_ordinal1(k1_ordinal1(A_15))
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ r1_ordinal1(A_4,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_245,plain,(
    ! [B_53,A_54] :
      ( r2_hidden(B_53,A_54)
      | B_53 = A_54
      | r2_hidden(A_54,B_53)
      | ~ v3_ordinal1(B_53)
      | ~ v3_ordinal1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_430,plain,(
    ! [A_62,B_63] :
      ( ~ r1_tarski(A_62,B_63)
      | B_63 = A_62
      | r2_hidden(A_62,B_63)
      | ~ v3_ordinal1(B_63)
      | ~ v3_ordinal1(A_62) ) ),
    inference(resolution,[status(thm)],[c_245,c_24])).

tff(c_36,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_60,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_30,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_30])).

tff(c_474,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_430,c_62])).

tff(c_497,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_474])).

tff(c_501,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_497])).

tff(c_504,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_501])).

tff(c_507,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_504])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( r2_hidden(B_14,A_12)
      | r1_ordinal1(A_12,B_14)
      | ~ v3_ordinal1(B_14)
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_212,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ r1_ordinal1(A_49,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_63,plain,(
    ! [A_28,B_29] :
      ( ~ r2_hidden(A_28,B_29)
      | r2_hidden(A_28,k1_ordinal1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_74,plain,(
    ! [B_29,A_28] :
      ( ~ r1_tarski(k1_ordinal1(B_29),A_28)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_63,c_24])).

tff(c_594,plain,(
    ! [B_69,B_70] :
      ( ~ r2_hidden(B_69,B_70)
      | ~ r1_ordinal1(k1_ordinal1(B_70),B_69)
      | ~ v3_ordinal1(B_69)
      | ~ v3_ordinal1(k1_ordinal1(B_70)) ) ),
    inference(resolution,[status(thm)],[c_212,c_74])).

tff(c_617,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_594])).

tff(c_625,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_617])).

tff(c_637,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_625])).

tff(c_640,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_637])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_640])).

tff(c_645,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_625])).

tff(c_658,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_645])).

tff(c_672,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_658])).

tff(c_674,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_507,c_672])).

tff(c_675,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_497])).

tff(c_679,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_60])).

tff(c_14,plain,(
    ! [B_8] : r2_hidden(B_8,k1_ordinal1(B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    ! [B_23,A_24] :
      ( ~ r1_tarski(B_23,A_24)
      | ~ r2_hidden(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    ! [B_8] : ~ r1_tarski(k1_ordinal1(B_8),B_8) ),
    inference(resolution,[status(thm)],[c_14,c_44])).

tff(c_226,plain,(
    ! [B_50] :
      ( ~ r1_ordinal1(k1_ordinal1(B_50),B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(k1_ordinal1(B_50)) ) ),
    inference(resolution,[status(thm)],[c_212,c_48])).

tff(c_711,plain,
    ( ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_679,c_226])).

tff(c_714,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_711])).

tff(c_717,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_714])).

tff(c_721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_717])).

tff(c_722,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_730,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_722,c_2])).

tff(c_841,plain,(
    ! [B_95,A_96] :
      ( r2_hidden(B_95,A_96)
      | r1_ordinal1(A_96,B_95)
      | ~ v3_ordinal1(B_95)
      | ~ v3_ordinal1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_905,plain,(
    ! [A_98,B_99] :
      ( ~ r2_hidden(A_98,B_99)
      | r1_ordinal1(A_98,B_99)
      | ~ v3_ordinal1(B_99)
      | ~ v3_ordinal1(A_98) ) ),
    inference(resolution,[status(thm)],[c_841,c_2])).

tff(c_938,plain,(
    ! [B_100,A_101] :
      ( r1_ordinal1(B_100,A_101)
      | r1_ordinal1(A_101,B_100)
      | ~ v3_ordinal1(B_100)
      | ~ v3_ordinal1(A_101) ) ),
    inference(resolution,[status(thm)],[c_20,c_905])).

tff(c_732,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_30])).

tff(c_948,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_938,c_732])).

tff(c_965,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_948])).

tff(c_1125,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_965])).

tff(c_1128,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1125])).

tff(c_1132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1128])).

tff(c_1134,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_965])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | r2_hidden(A_7,B_8)
      | ~ r2_hidden(A_7,k1_ordinal1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1415,plain,(
    ! [B_127,B_126] :
      ( B_127 = B_126
      | r2_hidden(B_126,B_127)
      | r1_ordinal1(k1_ordinal1(B_127),B_126)
      | ~ v3_ordinal1(B_126)
      | ~ v3_ordinal1(k1_ordinal1(B_127)) ) ),
    inference(resolution,[status(thm)],[c_841,c_12])).

tff(c_1427,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1415,c_732])).

tff(c_1434,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1134,c_26,c_1427])).

tff(c_1435,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_730,c_1434])).

tff(c_879,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_841,c_730])).

tff(c_900,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_879])).

tff(c_1437,plain,(
    r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1435,c_900])).

tff(c_819,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(A_92,B_93)
      | ~ r1_ordinal1(A_92,B_93)
      | ~ v3_ordinal1(B_93)
      | ~ v3_ordinal1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_729,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_722,c_24])).

tff(c_829,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_819,c_729])).

tff(c_838,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_829])).

tff(c_1438,plain,(
    ~ r1_ordinal1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1435,c_838])).

tff(c_1456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_1438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.56  
% 3.19/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.56  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 3.19/1.56  
% 3.19/1.56  %Foreground sorts:
% 3.19/1.56  
% 3.19/1.56  
% 3.19/1.56  %Background operators:
% 3.19/1.56  
% 3.19/1.56  
% 3.19/1.56  %Foreground operators:
% 3.19/1.56  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.19/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.56  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.19/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.19/1.56  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.19/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.19/1.56  
% 3.19/1.58  tff(f_91, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 3.19/1.58  tff(f_76, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 3.19/1.58  tff(f_40, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.19/1.58  tff(f_63, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.19/1.58  tff(f_81, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.19/1.58  tff(f_72, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 3.19/1.58  tff(f_48, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.19/1.58  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.19/1.58  tff(c_28, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.19/1.58  tff(c_22, plain, (![A_15]: (v3_ordinal1(k1_ordinal1(A_15)) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.19/1.58  tff(c_26, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.19/1.58  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~r1_ordinal1(A_4, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.19/1.58  tff(c_245, plain, (![B_53, A_54]: (r2_hidden(B_53, A_54) | B_53=A_54 | r2_hidden(A_54, B_53) | ~v3_ordinal1(B_53) | ~v3_ordinal1(A_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.19/1.58  tff(c_24, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.19/1.58  tff(c_430, plain, (![A_62, B_63]: (~r1_tarski(A_62, B_63) | B_63=A_62 | r2_hidden(A_62, B_63) | ~v3_ordinal1(B_63) | ~v3_ordinal1(A_62))), inference(resolution, [status(thm)], [c_245, c_24])).
% 3.19/1.58  tff(c_36, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.19/1.58  tff(c_60, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_36])).
% 3.19/1.58  tff(c_30, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.19/1.58  tff(c_62, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_30])).
% 3.19/1.58  tff(c_474, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1' | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_430, c_62])).
% 3.19/1.58  tff(c_497, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_474])).
% 3.19/1.58  tff(c_501, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_497])).
% 3.19/1.58  tff(c_504, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_501])).
% 3.19/1.58  tff(c_507, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_504])).
% 3.19/1.58  tff(c_20, plain, (![B_14, A_12]: (r2_hidden(B_14, A_12) | r1_ordinal1(A_12, B_14) | ~v3_ordinal1(B_14) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.19/1.58  tff(c_212, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~r1_ordinal1(A_49, B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_49))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.19/1.58  tff(c_63, plain, (![A_28, B_29]: (~r2_hidden(A_28, B_29) | r2_hidden(A_28, k1_ordinal1(B_29)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.19/1.58  tff(c_74, plain, (![B_29, A_28]: (~r1_tarski(k1_ordinal1(B_29), A_28) | ~r2_hidden(A_28, B_29))), inference(resolution, [status(thm)], [c_63, c_24])).
% 3.19/1.58  tff(c_594, plain, (![B_69, B_70]: (~r2_hidden(B_69, B_70) | ~r1_ordinal1(k1_ordinal1(B_70), B_69) | ~v3_ordinal1(B_69) | ~v3_ordinal1(k1_ordinal1(B_70)))), inference(resolution, [status(thm)], [c_212, c_74])).
% 3.19/1.58  tff(c_617, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_594])).
% 3.19/1.58  tff(c_625, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_617])).
% 3.19/1.58  tff(c_637, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_625])).
% 3.19/1.58  tff(c_640, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_637])).
% 3.19/1.58  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_640])).
% 3.19/1.58  tff(c_645, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_625])).
% 3.19/1.58  tff(c_658, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_645])).
% 3.19/1.58  tff(c_672, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_658])).
% 3.19/1.58  tff(c_674, plain, $false, inference(negUnitSimplification, [status(thm)], [c_507, c_672])).
% 3.19/1.58  tff(c_675, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_497])).
% 3.19/1.58  tff(c_679, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_675, c_60])).
% 3.19/1.58  tff(c_14, plain, (![B_8]: (r2_hidden(B_8, k1_ordinal1(B_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.19/1.58  tff(c_44, plain, (![B_23, A_24]: (~r1_tarski(B_23, A_24) | ~r2_hidden(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.19/1.58  tff(c_48, plain, (![B_8]: (~r1_tarski(k1_ordinal1(B_8), B_8))), inference(resolution, [status(thm)], [c_14, c_44])).
% 3.19/1.58  tff(c_226, plain, (![B_50]: (~r1_ordinal1(k1_ordinal1(B_50), B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(k1_ordinal1(B_50)))), inference(resolution, [status(thm)], [c_212, c_48])).
% 3.19/1.58  tff(c_711, plain, (~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_679, c_226])).
% 3.19/1.58  tff(c_714, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_711])).
% 3.19/1.58  tff(c_717, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_714])).
% 3.19/1.58  tff(c_721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_717])).
% 3.19/1.58  tff(c_722, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 3.19/1.58  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.19/1.58  tff(c_730, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_722, c_2])).
% 3.19/1.58  tff(c_841, plain, (![B_95, A_96]: (r2_hidden(B_95, A_96) | r1_ordinal1(A_96, B_95) | ~v3_ordinal1(B_95) | ~v3_ordinal1(A_96))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.19/1.58  tff(c_905, plain, (![A_98, B_99]: (~r2_hidden(A_98, B_99) | r1_ordinal1(A_98, B_99) | ~v3_ordinal1(B_99) | ~v3_ordinal1(A_98))), inference(resolution, [status(thm)], [c_841, c_2])).
% 3.19/1.58  tff(c_938, plain, (![B_100, A_101]: (r1_ordinal1(B_100, A_101) | r1_ordinal1(A_101, B_100) | ~v3_ordinal1(B_100) | ~v3_ordinal1(A_101))), inference(resolution, [status(thm)], [c_20, c_905])).
% 3.19/1.58  tff(c_732, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_722, c_30])).
% 3.19/1.58  tff(c_948, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_938, c_732])).
% 3.19/1.58  tff(c_965, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_948])).
% 3.19/1.58  tff(c_1125, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_965])).
% 3.19/1.58  tff(c_1128, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1125])).
% 3.19/1.58  tff(c_1132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1128])).
% 3.19/1.58  tff(c_1134, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_965])).
% 3.19/1.58  tff(c_12, plain, (![B_8, A_7]: (B_8=A_7 | r2_hidden(A_7, B_8) | ~r2_hidden(A_7, k1_ordinal1(B_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.19/1.58  tff(c_1415, plain, (![B_127, B_126]: (B_127=B_126 | r2_hidden(B_126, B_127) | r1_ordinal1(k1_ordinal1(B_127), B_126) | ~v3_ordinal1(B_126) | ~v3_ordinal1(k1_ordinal1(B_127)))), inference(resolution, [status(thm)], [c_841, c_12])).
% 3.19/1.58  tff(c_1427, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_1415, c_732])).
% 3.19/1.58  tff(c_1434, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1134, c_26, c_1427])).
% 3.19/1.58  tff(c_1435, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_730, c_1434])).
% 3.19/1.58  tff(c_879, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_841, c_730])).
% 3.19/1.58  tff(c_900, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_879])).
% 3.19/1.58  tff(c_1437, plain, (r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1435, c_900])).
% 3.19/1.58  tff(c_819, plain, (![A_92, B_93]: (r1_tarski(A_92, B_93) | ~r1_ordinal1(A_92, B_93) | ~v3_ordinal1(B_93) | ~v3_ordinal1(A_92))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.19/1.58  tff(c_729, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_722, c_24])).
% 3.19/1.58  tff(c_829, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_819, c_729])).
% 3.19/1.58  tff(c_838, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_829])).
% 3.19/1.58  tff(c_1438, plain, (~r1_ordinal1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1435, c_838])).
% 3.19/1.58  tff(c_1456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1437, c_1438])).
% 3.19/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.58  
% 3.19/1.58  Inference rules
% 3.19/1.58  ----------------------
% 3.19/1.58  #Ref     : 0
% 3.19/1.58  #Sup     : 264
% 3.19/1.58  #Fact    : 8
% 3.19/1.58  #Define  : 0
% 3.19/1.58  #Split   : 4
% 3.19/1.58  #Chain   : 0
% 3.19/1.58  #Close   : 0
% 3.19/1.58  
% 3.19/1.58  Ordering : KBO
% 3.19/1.58  
% 3.19/1.58  Simplification rules
% 3.19/1.58  ----------------------
% 3.19/1.58  #Subsume      : 57
% 3.19/1.58  #Demod        : 81
% 3.19/1.58  #Tautology    : 46
% 3.19/1.58  #SimpNegUnit  : 4
% 3.19/1.58  #BackRed      : 12
% 3.19/1.58  
% 3.19/1.58  #Partial instantiations: 0
% 3.19/1.58  #Strategies tried      : 1
% 3.19/1.58  
% 3.19/1.58  Timing (in seconds)
% 3.19/1.58  ----------------------
% 3.19/1.58  Preprocessing        : 0.27
% 3.19/1.58  Parsing              : 0.15
% 3.19/1.58  CNF conversion       : 0.02
% 3.19/1.59  Main loop            : 0.47
% 3.19/1.59  Inferencing          : 0.17
% 3.19/1.59  Reduction            : 0.12
% 3.19/1.59  Demodulation         : 0.08
% 3.19/1.59  BG Simplification    : 0.02
% 3.19/1.59  Subsumption          : 0.12
% 3.19/1.59  Abstraction          : 0.02
% 3.19/1.59  MUC search           : 0.00
% 3.19/1.59  Cooper               : 0.00
% 3.19/1.59  Total                : 0.78
% 3.19/1.59  Index Insertion      : 0.00
% 3.19/1.59  Index Deletion       : 0.00
% 3.19/1.59  Index Matching       : 0.00
% 3.19/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
