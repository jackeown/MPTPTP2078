%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:13 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 309 expanded)
%              Number of leaves         :   21 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  174 ( 782 expanded)
%              Number of equality atoms :   17 (  40 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_71,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_67,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_58,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_493,plain,(
    ! [B_82,A_83] :
      ( r1_ordinal1(B_82,A_83)
      | r1_ordinal1(A_83,B_82)
      | ~ v3_ordinal1(B_82)
      | ~ v3_ordinal1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_442,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(A_75,B_76)
      | ~ r1_ordinal1(A_75,B_76)
      | ~ v3_ordinal1(B_76)
      | ~ v3_ordinal1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_14] :
      ( v3_ordinal1(k1_ordinal1(A_14))
      | ~ v3_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_61,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_181,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ r1_ordinal1(A_46,B_47)
      | ~ v3_ordinal1(B_47)
      | ~ v3_ordinal1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden(A_26,B_27)
      | r2_hidden(A_26,k1_ordinal1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_68,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(k1_ordinal1(B_27),A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_64,c_28])).

tff(c_265,plain,(
    ! [B_58,B_59] :
      ( ~ r2_hidden(B_58,B_59)
      | ~ r1_ordinal1(k1_ordinal1(B_59),B_58)
      | ~ v3_ordinal1(B_58)
      | ~ v3_ordinal1(k1_ordinal1(B_59)) ) ),
    inference(resolution,[status(thm)],[c_181,c_68])).

tff(c_291,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_61,c_265])).

tff(c_300,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_291])).

tff(c_301,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_304,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_301])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_304])).

tff(c_310,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_128,plain,(
    ! [B_40,A_41] :
      ( r2_hidden(B_40,A_41)
      | r1_ordinal1(A_41,B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v3_ordinal1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69,plain,(
    ! [B_28,A_29] :
      ( ~ r1_tarski(k1_ordinal1(B_28),A_29)
      | ~ r2_hidden(A_29,B_28) ) ),
    inference(resolution,[status(thm)],[c_64,c_28])).

tff(c_74,plain,(
    ! [B_28] : ~ r2_hidden(k1_ordinal1(B_28),B_28) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_169,plain,(
    ! [A_41] :
      ( r1_ordinal1(A_41,k1_ordinal1(A_41))
      | ~ v3_ordinal1(k1_ordinal1(A_41))
      | ~ v3_ordinal1(A_41) ) ),
    inference(resolution,[status(thm)],[c_128,c_74])).

tff(c_22,plain,(
    ! [A_10] : k1_ordinal1(A_10) != A_10 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [B_13,A_11] :
      ( r2_hidden(B_13,A_11)
      | r1_ordinal1(A_11,B_13)
      | ~ v3_ordinal1(B_13)
      | ~ v3_ordinal1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_309,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_313,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_309])).

tff(c_316,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_313])).

tff(c_34,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_63,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_34])).

tff(c_159,plain,
    ( r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_128,c_63])).

tff(c_172,plain,(
    r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_159])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ r1_ordinal1(A_6,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_248,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_ordinal1(A_55,B_54)
      | ~ v3_ordinal1(B_54)
      | ~ v3_ordinal1(A_55) ) ),
    inference(resolution,[status(thm)],[c_181,c_2])).

tff(c_317,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_ordinal1(B_60,A_61)
      | ~ r1_ordinal1(A_61,B_60)
      | ~ v3_ordinal1(B_60)
      | ~ v3_ordinal1(A_61) ) ),
    inference(resolution,[status(thm)],[c_14,c_248])).

tff(c_333,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_172,c_317])).

tff(c_349,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_316,c_333])).

tff(c_335,plain,
    ( k1_ordinal1('#skF_1') = '#skF_2'
    | ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_61,c_317])).

tff(c_352,plain,
    ( k1_ordinal1('#skF_1') = '#skF_2'
    | ~ r1_ordinal1('#skF_2',k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_310,c_335])).

tff(c_365,plain,
    ( k1_ordinal1('#skF_1') = '#skF_1'
    | ~ r1_ordinal1('#skF_1',k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_349,c_352])).

tff(c_366,plain,(
    ~ r1_ordinal1('#skF_1',k1_ordinal1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_365])).

tff(c_371,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_169,c_366])).

tff(c_375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_310,c_371])).

tff(c_376,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_381,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_376,c_28])).

tff(c_451,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_442,c_381])).

tff(c_460,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_451])).

tff(c_500,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_493,c_460])).

tff(c_517,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_500])).

tff(c_377,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_513,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_493,c_377])).

tff(c_527,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_513])).

tff(c_529,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_527])).

tff(c_533,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_529])).

tff(c_537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_533])).

tff(c_539,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_527])).

tff(c_543,plain,(
    ! [B_85,A_86] :
      ( r2_hidden(B_85,A_86)
      | r1_ordinal1(A_86,B_85)
      | ~ v3_ordinal1(B_85)
      | ~ v3_ordinal1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | r2_hidden(A_8,B_9)
      | ~ r2_hidden(A_8,k1_ordinal1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_684,plain,(
    ! [B_99,B_98] :
      ( B_99 = B_98
      | r2_hidden(B_99,B_98)
      | r1_ordinal1(k1_ordinal1(B_98),B_99)
      | ~ v3_ordinal1(B_99)
      | ~ v3_ordinal1(k1_ordinal1(B_98)) ) ),
    inference(resolution,[status(thm)],[c_543,c_16])).

tff(c_696,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_684,c_377])).

tff(c_703,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_30,c_696])).

tff(c_704,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_703])).

tff(c_708,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_704,c_28])).

tff(c_711,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_708])).

tff(c_715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_517,c_711])).

tff(c_716,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_703])).

tff(c_722,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_381])).

tff(c_727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_722])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:23:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.38  
% 2.31/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.38  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 2.75/1.38  
% 2.75/1.38  %Foreground sorts:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Background operators:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Foreground operators:
% 2.75/1.38  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.38  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.75/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.38  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.75/1.38  
% 2.83/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.83/1.40  tff(f_86, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 2.83/1.40  tff(f_39, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 2.83/1.40  tff(f_49, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.83/1.40  tff(f_71, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 2.83/1.40  tff(f_55, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.83/1.40  tff(f_76, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.83/1.40  tff(f_67, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.83/1.40  tff(f_58, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 2.83/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.40  tff(c_32, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.40  tff(c_30, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.40  tff(c_493, plain, (![B_82, A_83]: (r1_ordinal1(B_82, A_83) | r1_ordinal1(A_83, B_82) | ~v3_ordinal1(B_82) | ~v3_ordinal1(A_83))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.83/1.40  tff(c_442, plain, (![A_75, B_76]: (r1_tarski(A_75, B_76) | ~r1_ordinal1(A_75, B_76) | ~v3_ordinal1(B_76) | ~v3_ordinal1(A_75))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.40  tff(c_26, plain, (![A_14]: (v3_ordinal1(k1_ordinal1(A_14)) | ~v3_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.83/1.40  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.40  tff(c_61, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 2.83/1.40  tff(c_181, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~r1_ordinal1(A_46, B_47) | ~v3_ordinal1(B_47) | ~v3_ordinal1(A_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.40  tff(c_64, plain, (![A_26, B_27]: (~r2_hidden(A_26, B_27) | r2_hidden(A_26, k1_ordinal1(B_27)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.83/1.40  tff(c_28, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.83/1.40  tff(c_68, plain, (![B_27, A_26]: (~r1_tarski(k1_ordinal1(B_27), A_26) | ~r2_hidden(A_26, B_27))), inference(resolution, [status(thm)], [c_64, c_28])).
% 2.83/1.40  tff(c_265, plain, (![B_58, B_59]: (~r2_hidden(B_58, B_59) | ~r1_ordinal1(k1_ordinal1(B_59), B_58) | ~v3_ordinal1(B_58) | ~v3_ordinal1(k1_ordinal1(B_59)))), inference(resolution, [status(thm)], [c_181, c_68])).
% 2.83/1.40  tff(c_291, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_61, c_265])).
% 2.83/1.40  tff(c_300, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_291])).
% 2.83/1.40  tff(c_301, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_300])).
% 2.83/1.40  tff(c_304, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_301])).
% 2.83/1.40  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_304])).
% 2.83/1.40  tff(c_310, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_300])).
% 2.83/1.40  tff(c_128, plain, (![B_40, A_41]: (r2_hidden(B_40, A_41) | r1_ordinal1(A_41, B_40) | ~v3_ordinal1(B_40) | ~v3_ordinal1(A_41))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.83/1.40  tff(c_69, plain, (![B_28, A_29]: (~r1_tarski(k1_ordinal1(B_28), A_29) | ~r2_hidden(A_29, B_28))), inference(resolution, [status(thm)], [c_64, c_28])).
% 2.83/1.40  tff(c_74, plain, (![B_28]: (~r2_hidden(k1_ordinal1(B_28), B_28))), inference(resolution, [status(thm)], [c_6, c_69])).
% 2.83/1.40  tff(c_169, plain, (![A_41]: (r1_ordinal1(A_41, k1_ordinal1(A_41)) | ~v3_ordinal1(k1_ordinal1(A_41)) | ~v3_ordinal1(A_41))), inference(resolution, [status(thm)], [c_128, c_74])).
% 2.83/1.40  tff(c_22, plain, (![A_10]: (k1_ordinal1(A_10)!=A_10)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.40  tff(c_24, plain, (![B_13, A_11]: (r2_hidden(B_13, A_11) | r1_ordinal1(A_11, B_13) | ~v3_ordinal1(B_13) | ~v3_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.83/1.40  tff(c_309, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_300])).
% 2.83/1.40  tff(c_313, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_309])).
% 2.83/1.40  tff(c_316, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_313])).
% 2.83/1.40  tff(c_34, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.40  tff(c_63, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_34])).
% 2.83/1.40  tff(c_159, plain, (r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_128, c_63])).
% 2.83/1.40  tff(c_172, plain, (r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_159])).
% 2.83/1.40  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~r1_ordinal1(A_6, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.40  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.40  tff(c_248, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_ordinal1(A_55, B_54) | ~v3_ordinal1(B_54) | ~v3_ordinal1(A_55))), inference(resolution, [status(thm)], [c_181, c_2])).
% 2.83/1.40  tff(c_317, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_ordinal1(B_60, A_61) | ~r1_ordinal1(A_61, B_60) | ~v3_ordinal1(B_60) | ~v3_ordinal1(A_61))), inference(resolution, [status(thm)], [c_14, c_248])).
% 2.83/1.40  tff(c_333, plain, ('#skF_2'='#skF_1' | ~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_172, c_317])).
% 2.83/1.40  tff(c_349, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_316, c_333])).
% 2.83/1.40  tff(c_335, plain, (k1_ordinal1('#skF_1')='#skF_2' | ~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_61, c_317])).
% 2.83/1.40  tff(c_352, plain, (k1_ordinal1('#skF_1')='#skF_2' | ~r1_ordinal1('#skF_2', k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_310, c_335])).
% 2.83/1.40  tff(c_365, plain, (k1_ordinal1('#skF_1')='#skF_1' | ~r1_ordinal1('#skF_1', k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_349, c_349, c_352])).
% 2.83/1.40  tff(c_366, plain, (~r1_ordinal1('#skF_1', k1_ordinal1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_22, c_365])).
% 2.83/1.40  tff(c_371, plain, (~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_169, c_366])).
% 2.83/1.40  tff(c_375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_310, c_371])).
% 2.83/1.40  tff(c_376, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.83/1.40  tff(c_381, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_376, c_28])).
% 2.83/1.40  tff(c_451, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_442, c_381])).
% 2.83/1.40  tff(c_460, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_451])).
% 2.83/1.40  tff(c_500, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_493, c_460])).
% 2.83/1.40  tff(c_517, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_500])).
% 2.83/1.40  tff(c_377, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.83/1.40  tff(c_513, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_493, c_377])).
% 2.83/1.40  tff(c_527, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_513])).
% 2.83/1.40  tff(c_529, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_527])).
% 2.83/1.40  tff(c_533, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_529])).
% 2.83/1.40  tff(c_537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_533])).
% 2.83/1.40  tff(c_539, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_527])).
% 2.83/1.40  tff(c_543, plain, (![B_85, A_86]: (r2_hidden(B_85, A_86) | r1_ordinal1(A_86, B_85) | ~v3_ordinal1(B_85) | ~v3_ordinal1(A_86))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.83/1.40  tff(c_16, plain, (![B_9, A_8]: (B_9=A_8 | r2_hidden(A_8, B_9) | ~r2_hidden(A_8, k1_ordinal1(B_9)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.83/1.40  tff(c_684, plain, (![B_99, B_98]: (B_99=B_98 | r2_hidden(B_99, B_98) | r1_ordinal1(k1_ordinal1(B_98), B_99) | ~v3_ordinal1(B_99) | ~v3_ordinal1(k1_ordinal1(B_98)))), inference(resolution, [status(thm)], [c_543, c_16])).
% 2.83/1.40  tff(c_696, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_684, c_377])).
% 2.83/1.40  tff(c_703, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_539, c_30, c_696])).
% 2.83/1.40  tff(c_704, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_703])).
% 2.83/1.40  tff(c_708, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_704, c_28])).
% 2.83/1.40  tff(c_711, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_708])).
% 2.83/1.40  tff(c_715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_517, c_711])).
% 2.83/1.40  tff(c_716, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_703])).
% 2.83/1.40  tff(c_722, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_716, c_381])).
% 2.83/1.40  tff(c_727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_722])).
% 2.83/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.40  
% 2.83/1.40  Inference rules
% 2.83/1.40  ----------------------
% 2.83/1.40  #Ref     : 0
% 2.83/1.40  #Sup     : 118
% 2.83/1.40  #Fact    : 4
% 2.83/1.40  #Define  : 0
% 2.83/1.40  #Split   : 5
% 2.83/1.40  #Chain   : 0
% 2.83/1.40  #Close   : 0
% 2.83/1.40  
% 2.83/1.40  Ordering : KBO
% 2.83/1.40  
% 2.83/1.40  Simplification rules
% 2.83/1.40  ----------------------
% 2.83/1.40  #Subsume      : 24
% 2.83/1.40  #Demod        : 60
% 2.83/1.40  #Tautology    : 31
% 2.83/1.40  #SimpNegUnit  : 3
% 2.83/1.40  #BackRed      : 13
% 2.83/1.40  
% 2.83/1.40  #Partial instantiations: 0
% 2.83/1.40  #Strategies tried      : 1
% 2.83/1.40  
% 2.83/1.40  Timing (in seconds)
% 2.83/1.40  ----------------------
% 2.83/1.40  Preprocessing        : 0.29
% 2.83/1.40  Parsing              : 0.16
% 2.83/1.40  CNF conversion       : 0.02
% 2.83/1.40  Main loop            : 0.34
% 2.83/1.40  Inferencing          : 0.14
% 2.83/1.40  Reduction            : 0.09
% 2.83/1.40  Demodulation         : 0.06
% 2.83/1.40  BG Simplification    : 0.02
% 2.83/1.40  Subsumption          : 0.08
% 2.83/1.40  Abstraction          : 0.01
% 2.83/1.40  MUC search           : 0.00
% 2.83/1.40  Cooper               : 0.00
% 2.83/1.40  Total                : 0.67
% 2.83/1.40  Index Insertion      : 0.00
% 2.83/1.40  Index Deletion       : 0.00
% 2.83/1.40  Index Matching       : 0.00
% 2.83/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
