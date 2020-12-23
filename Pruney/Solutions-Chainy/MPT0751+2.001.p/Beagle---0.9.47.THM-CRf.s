%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:25 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   68 (  98 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  163 ( 282 expanded)
%              Number of equality atoms :   19 (  41 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ( ~ ( ~ v4_ordinal1(A)
              & ! [B] :
                  ( v3_ordinal1(B)
                 => A != k1_ordinal1(B) ) )
          & ~ ( ? [B] :
                  ( v3_ordinal1(B)
                  & A = k1_ordinal1(B) )
              & v4_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).

tff(f_86,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v4_ordinal1(A)
      <=> ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(B,A)
             => r2_hidden(k1_ordinal1(B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

tff(f_66,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_43,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_75,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
          <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_53,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_36,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_34,plain,(
    ! [A_16] :
      ( v3_ordinal1('#skF_1'(A_16))
      | v4_ordinal1(A_16)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_1'(A_16),A_16)
      | v4_ordinal1(A_16)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_62,plain,(
    ! [A_27] :
      ( v3_ordinal1(k1_ordinal1(A_27))
      | ~ v3_ordinal1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_5] :
      ( v1_ordinal1(A_5)
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_69,plain,(
    ! [A_27] :
      ( v1_ordinal1(k1_ordinal1(A_27))
      | ~ v3_ordinal1(A_27) ) ),
    inference(resolution,[status(thm)],[c_62,c_12])).

tff(c_22,plain,(
    ! [A_12] :
      ( v3_ordinal1(k1_ordinal1(A_12))
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_13,B_15] :
      ( r1_ordinal1(k1_ordinal1(A_13),B_15)
      | ~ r2_hidden(A_13,B_15)
      | ~ v3_ordinal1(B_15)
      | ~ v3_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ r1_ordinal1(A_6,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_xboole_0(A_3,B_4)
      | B_4 = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_129,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(A_50,B_51)
      | ~ r2_xboole_0(A_50,B_51)
      | ~ v3_ordinal1(B_51)
      | ~ v1_ordinal1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_140,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,B_57)
      | ~ v3_ordinal1(B_57)
      | ~ v1_ordinal1(A_56)
      | B_57 = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_4,c_129])).

tff(c_30,plain,(
    ! [A_16] :
      ( ~ r2_hidden(k1_ordinal1('#skF_1'(A_16)),A_16)
      | v4_ordinal1(A_16)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_289,plain,(
    ! [B_79] :
      ( v4_ordinal1(B_79)
      | ~ v3_ordinal1(B_79)
      | ~ v1_ordinal1(k1_ordinal1('#skF_1'(B_79)))
      | k1_ordinal1('#skF_1'(B_79)) = B_79
      | ~ r1_tarski(k1_ordinal1('#skF_1'(B_79)),B_79) ) ),
    inference(resolution,[status(thm)],[c_140,c_30])).

tff(c_312,plain,(
    ! [B_83] :
      ( v4_ordinal1(B_83)
      | ~ v1_ordinal1(k1_ordinal1('#skF_1'(B_83)))
      | k1_ordinal1('#skF_1'(B_83)) = B_83
      | ~ r1_ordinal1(k1_ordinal1('#skF_1'(B_83)),B_83)
      | ~ v3_ordinal1(B_83)
      | ~ v3_ordinal1(k1_ordinal1('#skF_1'(B_83))) ) ),
    inference(resolution,[status(thm)],[c_16,c_289])).

tff(c_330,plain,(
    ! [B_88] :
      ( v4_ordinal1(B_88)
      | ~ v1_ordinal1(k1_ordinal1('#skF_1'(B_88)))
      | k1_ordinal1('#skF_1'(B_88)) = B_88
      | ~ v3_ordinal1(k1_ordinal1('#skF_1'(B_88)))
      | ~ r2_hidden('#skF_1'(B_88),B_88)
      | ~ v3_ordinal1(B_88)
      | ~ v3_ordinal1('#skF_1'(B_88)) ) ),
    inference(resolution,[status(thm)],[c_26,c_312])).

tff(c_335,plain,(
    ! [B_89] :
      ( v4_ordinal1(B_89)
      | ~ v1_ordinal1(k1_ordinal1('#skF_1'(B_89)))
      | k1_ordinal1('#skF_1'(B_89)) = B_89
      | ~ r2_hidden('#skF_1'(B_89),B_89)
      | ~ v3_ordinal1(B_89)
      | ~ v3_ordinal1('#skF_1'(B_89)) ) ),
    inference(resolution,[status(thm)],[c_22,c_330])).

tff(c_340,plain,(
    ! [B_90] :
      ( v4_ordinal1(B_90)
      | k1_ordinal1('#skF_1'(B_90)) = B_90
      | ~ r2_hidden('#skF_1'(B_90),B_90)
      | ~ v3_ordinal1(B_90)
      | ~ v3_ordinal1('#skF_1'(B_90)) ) ),
    inference(resolution,[status(thm)],[c_69,c_335])).

tff(c_350,plain,(
    ! [A_91] :
      ( k1_ordinal1('#skF_1'(A_91)) = A_91
      | ~ v3_ordinal1('#skF_1'(A_91))
      | v4_ordinal1(A_91)
      | ~ v3_ordinal1(A_91) ) ),
    inference(resolution,[status(thm)],[c_32,c_340])).

tff(c_355,plain,(
    ! [A_92] :
      ( k1_ordinal1('#skF_1'(A_92)) = A_92
      | v4_ordinal1(A_92)
      | ~ v3_ordinal1(A_92) ) ),
    inference(resolution,[status(thm)],[c_34,c_350])).

tff(c_48,plain,
    ( ~ v4_ordinal1('#skF_2')
    | v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_60,plain,(
    ~ v4_ordinal1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_38,plain,(
    ! [B_22] :
      ( k1_ordinal1(B_22) != '#skF_2'
      | ~ v3_ordinal1(B_22)
      | v4_ordinal1('#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_89,plain,(
    ! [B_36] :
      ( k1_ordinal1(B_36) != '#skF_2'
      | ~ v3_ordinal1(B_36) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_38])).

tff(c_99,plain,(
    ! [A_16] :
      ( k1_ordinal1('#skF_1'(A_16)) != '#skF_2'
      | v4_ordinal1(A_16)
      | ~ v3_ordinal1(A_16) ) ),
    inference(resolution,[status(thm)],[c_34,c_89])).

tff(c_397,plain,(
    ! [A_92] :
      ( A_92 != '#skF_2'
      | v4_ordinal1(A_92)
      | ~ v3_ordinal1(A_92)
      | v4_ordinal1(A_92)
      | ~ v3_ordinal1(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_99])).

tff(c_447,plain,(
    ! [A_95] :
      ( A_95 != '#skF_2'
      | ~ v3_ordinal1(A_95)
      | v4_ordinal1(A_95) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_397])).

tff(c_453,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_447,c_60])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_453])).

tff(c_460,plain,(
    v4_ordinal1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_44,plain,
    ( ~ v4_ordinal1('#skF_2')
    | k1_ordinal1('#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_470,plain,(
    k1_ordinal1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_44])).

tff(c_459,plain,(
    v3_ordinal1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_18,plain,(
    ! [A_8] : r2_hidden(A_8,k1_ordinal1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [B_19,A_16] :
      ( r2_hidden(k1_ordinal1(B_19),A_16)
      | ~ r2_hidden(B_19,A_16)
      | ~ v3_ordinal1(B_19)
      | ~ v4_ordinal1(A_16)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_627,plain,(
    ! [B_126,A_127] :
      ( r2_hidden(k1_ordinal1(B_126),A_127)
      | ~ r2_hidden(B_126,A_127)
      | ~ v3_ordinal1(B_126)
      | ~ v4_ordinal1(A_127)
      | ~ v3_ordinal1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_505,plain,(
    ! [B_100,A_101] :
      ( ~ r2_hidden(B_100,A_101)
      | ~ r2_hidden(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_511,plain,(
    ! [A_8] : ~ r2_hidden(k1_ordinal1(A_8),A_8) ),
    inference(resolution,[status(thm)],[c_18,c_505])).

tff(c_658,plain,(
    ! [A_128] :
      ( ~ r2_hidden(A_128,A_128)
      | ~ v4_ordinal1(A_128)
      | ~ v3_ordinal1(A_128) ) ),
    inference(resolution,[status(thm)],[c_627,c_511])).

tff(c_662,plain,(
    ! [B_19] :
      ( ~ r2_hidden(B_19,k1_ordinal1(B_19))
      | ~ v3_ordinal1(B_19)
      | ~ v4_ordinal1(k1_ordinal1(B_19))
      | ~ v3_ordinal1(k1_ordinal1(B_19)) ) ),
    inference(resolution,[status(thm)],[c_28,c_658])).

tff(c_673,plain,(
    ! [B_129] :
      ( ~ v3_ordinal1(B_129)
      | ~ v4_ordinal1(k1_ordinal1(B_129))
      | ~ v3_ordinal1(k1_ordinal1(B_129)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_662])).

tff(c_676,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v4_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_673])).

tff(c_679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_470,c_460,c_459,c_676])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:30:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.51  
% 3.01/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.52  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3
% 3.01/1.52  
% 3.01/1.52  %Foreground sorts:
% 3.01/1.52  
% 3.01/1.52  
% 3.01/1.52  %Background operators:
% 3.01/1.52  
% 3.01/1.52  
% 3.01/1.52  %Foreground operators:
% 3.01/1.52  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.01/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.52  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 3.01/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.01/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.52  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.01/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.01/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.52  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.01/1.52  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 3.01/1.52  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.01/1.52  tff(v4_ordinal1, type, v4_ordinal1: $i > $o).
% 3.01/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.52  
% 3.17/1.53  tff(f_107, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (~(~v4_ordinal1(A) & (![B]: (v3_ordinal1(B) => ~(A = k1_ordinal1(B))))) & ~((?[B]: (v3_ordinal1(B) & (A = k1_ordinal1(B)))) & v4_ordinal1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_ordinal1)).
% 3.17/1.53  tff(f_86, axiom, (![A]: (v3_ordinal1(A) => (v4_ordinal1(A) <=> (![B]: (v3_ordinal1(B) => (r2_hidden(B, A) => r2_hidden(k1_ordinal1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 3.17/1.53  tff(f_66, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 3.17/1.53  tff(f_43, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 3.17/1.53  tff(f_75, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 3.17/1.53  tff(f_51, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.17/1.53  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.17/1.53  tff(f_62, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 3.17/1.53  tff(f_53, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 3.17/1.53  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.17/1.53  tff(c_36, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.17/1.53  tff(c_34, plain, (![A_16]: (v3_ordinal1('#skF_1'(A_16)) | v4_ordinal1(A_16) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.53  tff(c_32, plain, (![A_16]: (r2_hidden('#skF_1'(A_16), A_16) | v4_ordinal1(A_16) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.53  tff(c_62, plain, (![A_27]: (v3_ordinal1(k1_ordinal1(A_27)) | ~v3_ordinal1(A_27))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.17/1.53  tff(c_12, plain, (![A_5]: (v1_ordinal1(A_5) | ~v3_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.17/1.53  tff(c_69, plain, (![A_27]: (v1_ordinal1(k1_ordinal1(A_27)) | ~v3_ordinal1(A_27))), inference(resolution, [status(thm)], [c_62, c_12])).
% 3.17/1.53  tff(c_22, plain, (![A_12]: (v3_ordinal1(k1_ordinal1(A_12)) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.17/1.53  tff(c_26, plain, (![A_13, B_15]: (r1_ordinal1(k1_ordinal1(A_13), B_15) | ~r2_hidden(A_13, B_15) | ~v3_ordinal1(B_15) | ~v3_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.17/1.53  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~r1_ordinal1(A_6, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.17/1.53  tff(c_4, plain, (![A_3, B_4]: (r2_xboole_0(A_3, B_4) | B_4=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.17/1.53  tff(c_129, plain, (![A_50, B_51]: (r2_hidden(A_50, B_51) | ~r2_xboole_0(A_50, B_51) | ~v3_ordinal1(B_51) | ~v1_ordinal1(A_50))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.17/1.53  tff(c_140, plain, (![A_56, B_57]: (r2_hidden(A_56, B_57) | ~v3_ordinal1(B_57) | ~v1_ordinal1(A_56) | B_57=A_56 | ~r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_4, c_129])).
% 3.17/1.53  tff(c_30, plain, (![A_16]: (~r2_hidden(k1_ordinal1('#skF_1'(A_16)), A_16) | v4_ordinal1(A_16) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.53  tff(c_289, plain, (![B_79]: (v4_ordinal1(B_79) | ~v3_ordinal1(B_79) | ~v1_ordinal1(k1_ordinal1('#skF_1'(B_79))) | k1_ordinal1('#skF_1'(B_79))=B_79 | ~r1_tarski(k1_ordinal1('#skF_1'(B_79)), B_79))), inference(resolution, [status(thm)], [c_140, c_30])).
% 3.17/1.53  tff(c_312, plain, (![B_83]: (v4_ordinal1(B_83) | ~v1_ordinal1(k1_ordinal1('#skF_1'(B_83))) | k1_ordinal1('#skF_1'(B_83))=B_83 | ~r1_ordinal1(k1_ordinal1('#skF_1'(B_83)), B_83) | ~v3_ordinal1(B_83) | ~v3_ordinal1(k1_ordinal1('#skF_1'(B_83))))), inference(resolution, [status(thm)], [c_16, c_289])).
% 3.17/1.53  tff(c_330, plain, (![B_88]: (v4_ordinal1(B_88) | ~v1_ordinal1(k1_ordinal1('#skF_1'(B_88))) | k1_ordinal1('#skF_1'(B_88))=B_88 | ~v3_ordinal1(k1_ordinal1('#skF_1'(B_88))) | ~r2_hidden('#skF_1'(B_88), B_88) | ~v3_ordinal1(B_88) | ~v3_ordinal1('#skF_1'(B_88)))), inference(resolution, [status(thm)], [c_26, c_312])).
% 3.17/1.53  tff(c_335, plain, (![B_89]: (v4_ordinal1(B_89) | ~v1_ordinal1(k1_ordinal1('#skF_1'(B_89))) | k1_ordinal1('#skF_1'(B_89))=B_89 | ~r2_hidden('#skF_1'(B_89), B_89) | ~v3_ordinal1(B_89) | ~v3_ordinal1('#skF_1'(B_89)))), inference(resolution, [status(thm)], [c_22, c_330])).
% 3.17/1.53  tff(c_340, plain, (![B_90]: (v4_ordinal1(B_90) | k1_ordinal1('#skF_1'(B_90))=B_90 | ~r2_hidden('#skF_1'(B_90), B_90) | ~v3_ordinal1(B_90) | ~v3_ordinal1('#skF_1'(B_90)))), inference(resolution, [status(thm)], [c_69, c_335])).
% 3.17/1.53  tff(c_350, plain, (![A_91]: (k1_ordinal1('#skF_1'(A_91))=A_91 | ~v3_ordinal1('#skF_1'(A_91)) | v4_ordinal1(A_91) | ~v3_ordinal1(A_91))), inference(resolution, [status(thm)], [c_32, c_340])).
% 3.17/1.53  tff(c_355, plain, (![A_92]: (k1_ordinal1('#skF_1'(A_92))=A_92 | v4_ordinal1(A_92) | ~v3_ordinal1(A_92))), inference(resolution, [status(thm)], [c_34, c_350])).
% 3.17/1.53  tff(c_48, plain, (~v4_ordinal1('#skF_2') | v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.17/1.53  tff(c_60, plain, (~v4_ordinal1('#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 3.17/1.53  tff(c_38, plain, (![B_22]: (k1_ordinal1(B_22)!='#skF_2' | ~v3_ordinal1(B_22) | v4_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.17/1.53  tff(c_89, plain, (![B_36]: (k1_ordinal1(B_36)!='#skF_2' | ~v3_ordinal1(B_36))), inference(negUnitSimplification, [status(thm)], [c_60, c_38])).
% 3.17/1.53  tff(c_99, plain, (![A_16]: (k1_ordinal1('#skF_1'(A_16))!='#skF_2' | v4_ordinal1(A_16) | ~v3_ordinal1(A_16))), inference(resolution, [status(thm)], [c_34, c_89])).
% 3.17/1.53  tff(c_397, plain, (![A_92]: (A_92!='#skF_2' | v4_ordinal1(A_92) | ~v3_ordinal1(A_92) | v4_ordinal1(A_92) | ~v3_ordinal1(A_92))), inference(superposition, [status(thm), theory('equality')], [c_355, c_99])).
% 3.17/1.53  tff(c_447, plain, (![A_95]: (A_95!='#skF_2' | ~v3_ordinal1(A_95) | v4_ordinal1(A_95))), inference(factorization, [status(thm), theory('equality')], [c_397])).
% 3.17/1.53  tff(c_453, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_447, c_60])).
% 3.17/1.53  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_453])).
% 3.17/1.53  tff(c_460, plain, (v4_ordinal1('#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 3.17/1.53  tff(c_44, plain, (~v4_ordinal1('#skF_2') | k1_ordinal1('#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.17/1.53  tff(c_470, plain, (k1_ordinal1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_460, c_44])).
% 3.17/1.53  tff(c_459, plain, (v3_ordinal1('#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 3.17/1.53  tff(c_18, plain, (![A_8]: (r2_hidden(A_8, k1_ordinal1(A_8)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.17/1.53  tff(c_28, plain, (![B_19, A_16]: (r2_hidden(k1_ordinal1(B_19), A_16) | ~r2_hidden(B_19, A_16) | ~v3_ordinal1(B_19) | ~v4_ordinal1(A_16) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.53  tff(c_627, plain, (![B_126, A_127]: (r2_hidden(k1_ordinal1(B_126), A_127) | ~r2_hidden(B_126, A_127) | ~v3_ordinal1(B_126) | ~v4_ordinal1(A_127) | ~v3_ordinal1(A_127))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.53  tff(c_505, plain, (![B_100, A_101]: (~r2_hidden(B_100, A_101) | ~r2_hidden(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.17/1.53  tff(c_511, plain, (![A_8]: (~r2_hidden(k1_ordinal1(A_8), A_8))), inference(resolution, [status(thm)], [c_18, c_505])).
% 3.17/1.53  tff(c_658, plain, (![A_128]: (~r2_hidden(A_128, A_128) | ~v4_ordinal1(A_128) | ~v3_ordinal1(A_128))), inference(resolution, [status(thm)], [c_627, c_511])).
% 3.17/1.53  tff(c_662, plain, (![B_19]: (~r2_hidden(B_19, k1_ordinal1(B_19)) | ~v3_ordinal1(B_19) | ~v4_ordinal1(k1_ordinal1(B_19)) | ~v3_ordinal1(k1_ordinal1(B_19)))), inference(resolution, [status(thm)], [c_28, c_658])).
% 3.17/1.53  tff(c_673, plain, (![B_129]: (~v3_ordinal1(B_129) | ~v4_ordinal1(k1_ordinal1(B_129)) | ~v3_ordinal1(k1_ordinal1(B_129)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_662])).
% 3.17/1.53  tff(c_676, plain, (~v3_ordinal1('#skF_3') | ~v4_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_470, c_673])).
% 3.17/1.53  tff(c_679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_470, c_460, c_459, c_676])).
% 3.17/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.53  
% 3.17/1.53  Inference rules
% 3.17/1.53  ----------------------
% 3.17/1.53  #Ref     : 0
% 3.17/1.53  #Sup     : 122
% 3.17/1.53  #Fact    : 2
% 3.17/1.53  #Define  : 0
% 3.17/1.53  #Split   : 2
% 3.17/1.53  #Chain   : 0
% 3.17/1.53  #Close   : 0
% 3.17/1.53  
% 3.17/1.53  Ordering : KBO
% 3.17/1.53  
% 3.17/1.53  Simplification rules
% 3.17/1.53  ----------------------
% 3.17/1.53  #Subsume      : 27
% 3.17/1.53  #Demod        : 33
% 3.17/1.53  #Tautology    : 27
% 3.17/1.53  #SimpNegUnit  : 1
% 3.17/1.53  #BackRed      : 0
% 3.17/1.53  
% 3.17/1.53  #Partial instantiations: 0
% 3.17/1.53  #Strategies tried      : 1
% 3.17/1.53  
% 3.17/1.53  Timing (in seconds)
% 3.17/1.53  ----------------------
% 3.17/1.54  Preprocessing        : 0.31
% 3.17/1.54  Parsing              : 0.17
% 3.17/1.54  CNF conversion       : 0.02
% 3.17/1.54  Main loop            : 0.38
% 3.17/1.54  Inferencing          : 0.16
% 3.17/1.54  Reduction            : 0.09
% 3.17/1.54  Demodulation         : 0.05
% 3.17/1.54  BG Simplification    : 0.02
% 3.17/1.54  Subsumption          : 0.10
% 3.17/1.54  Abstraction          : 0.01
% 3.17/1.54  MUC search           : 0.00
% 3.17/1.54  Cooper               : 0.00
% 3.17/1.54  Total                : 0.73
% 3.17/1.54  Index Insertion      : 0.00
% 3.17/1.54  Index Deletion       : 0.00
% 3.17/1.54  Index Matching       : 0.00
% 3.17/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
