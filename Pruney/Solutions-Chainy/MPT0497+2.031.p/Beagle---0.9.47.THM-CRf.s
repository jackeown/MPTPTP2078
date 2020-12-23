%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:43 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   67 (  86 expanded)
%              Number of leaves         :   33 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 136 expanded)
%              Number of equality atoms :   21 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_68,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
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

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_71,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_48,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_96,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_125,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_54])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_128,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_26,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    ! [A_36] : k2_relat_1(k6_relat_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_236,plain,(
    ! [A_85,B_86] :
      ( k5_relat_1(A_85,B_86) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_85),k1_relat_1(B_86))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_239,plain,(
    ! [A_36,B_86] :
      ( k5_relat_1(k6_relat_1(A_36),B_86) = k1_xboole_0
      | ~ r1_xboole_0(A_36,k1_relat_1(B_86))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_236])).

tff(c_258,plain,(
    ! [A_87,B_88] :
      ( k5_relat_1(k6_relat_1(A_87),B_88) = k1_xboole_0
      | ~ r1_xboole_0(A_87,k1_relat_1(B_88))
      | ~ v1_relat_1(B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_239])).

tff(c_261,plain,
    ( k5_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_258])).

tff(c_274,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_261])).

tff(c_44,plain,(
    ! [A_40,B_41] :
      ( k5_relat_1(k6_relat_1(A_40),B_41) = k7_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_292,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_44])).

tff(c_299,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_292])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_299])).

tff(c_302,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_315,plain,(
    ! [A_96,B_97] :
      ( ~ r2_hidden(A_96,B_97)
      | ~ r1_xboole_0(k1_tarski(A_96),B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_320,plain,(
    ! [A_96] : ~ r2_hidden(A_96,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_315])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_309,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_54])).

tff(c_467,plain,(
    ! [A_138,C_139,B_140] :
      ( r2_hidden(A_138,k1_relat_1(k7_relat_1(C_139,B_140)))
      | ~ r2_hidden(A_138,k1_relat_1(C_139))
      | ~ r2_hidden(A_138,B_140)
      | ~ v1_relat_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_476,plain,(
    ! [A_138] :
      ( r2_hidden(A_138,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_138,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_138,'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_467])).

tff(c_480,plain,(
    ! [A_138] :
      ( r2_hidden(A_138,k1_xboole_0)
      | ~ r2_hidden(A_138,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_138,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_30,c_476])).

tff(c_482,plain,(
    ! [A_141] :
      ( ~ r2_hidden(A_141,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_141,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_480])).

tff(c_649,plain,(
    ! [A_149] :
      ( ~ r2_hidden('#skF_1'(A_149,k1_relat_1('#skF_3')),'#skF_2')
      | r1_xboole_0(A_149,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6,c_482])).

tff(c_654,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_649])).

tff(c_661,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_654,c_2])).

tff(c_669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_661])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.47  
% 2.80/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.47  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.80/1.47  
% 2.80/1.47  %Foreground sorts:
% 2.80/1.47  
% 2.80/1.47  
% 2.80/1.47  %Background operators:
% 2.80/1.47  
% 2.80/1.47  
% 2.80/1.47  %Foreground operators:
% 2.80/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.80/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.80/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.80/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.80/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.80/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.80/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.80/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.80/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.80/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.80/1.47  
% 2.80/1.48  tff(f_103, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.80/1.48  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.80/1.48  tff(f_68, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.80/1.48  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.80/1.48  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_relat_1)).
% 2.80/1.48  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.80/1.48  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.80/1.48  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.80/1.48  tff(f_66, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.80/1.48  tff(f_71, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.80/1.48  tff(f_92, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 2.80/1.48  tff(c_48, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.80/1.48  tff(c_96, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.80/1.48  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.80/1.48  tff(c_54, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.80/1.48  tff(c_125, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_96, c_54])).
% 2.80/1.48  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.48  tff(c_128, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_125, c_2])).
% 2.80/1.48  tff(c_26, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.48  tff(c_36, plain, (![A_36]: (k2_relat_1(k6_relat_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.80/1.48  tff(c_236, plain, (![A_85, B_86]: (k5_relat_1(A_85, B_86)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_85), k1_relat_1(B_86)) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.80/1.48  tff(c_239, plain, (![A_36, B_86]: (k5_relat_1(k6_relat_1(A_36), B_86)=k1_xboole_0 | ~r1_xboole_0(A_36, k1_relat_1(B_86)) | ~v1_relat_1(B_86) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_236])).
% 2.80/1.48  tff(c_258, plain, (![A_87, B_88]: (k5_relat_1(k6_relat_1(A_87), B_88)=k1_xboole_0 | ~r1_xboole_0(A_87, k1_relat_1(B_88)) | ~v1_relat_1(B_88))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_239])).
% 2.80/1.48  tff(c_261, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_128, c_258])).
% 2.80/1.48  tff(c_274, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_261])).
% 2.80/1.48  tff(c_44, plain, (![A_40, B_41]: (k5_relat_1(k6_relat_1(A_40), B_41)=k7_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.80/1.48  tff(c_292, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_274, c_44])).
% 2.80/1.48  tff(c_299, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_292])).
% 2.80/1.48  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_299])).
% 2.80/1.48  tff(c_302, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 2.80/1.48  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.80/1.48  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.80/1.48  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.80/1.48  tff(c_315, plain, (![A_96, B_97]: (~r2_hidden(A_96, B_97) | ~r1_xboole_0(k1_tarski(A_96), B_97))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.80/1.48  tff(c_320, plain, (![A_96]: (~r2_hidden(A_96, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_315])).
% 2.80/1.48  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.80/1.48  tff(c_309, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_302, c_54])).
% 2.80/1.48  tff(c_467, plain, (![A_138, C_139, B_140]: (r2_hidden(A_138, k1_relat_1(k7_relat_1(C_139, B_140))) | ~r2_hidden(A_138, k1_relat_1(C_139)) | ~r2_hidden(A_138, B_140) | ~v1_relat_1(C_139))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.80/1.48  tff(c_476, plain, (![A_138]: (r2_hidden(A_138, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_138, k1_relat_1('#skF_3')) | ~r2_hidden(A_138, '#skF_2') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_309, c_467])).
% 2.80/1.48  tff(c_480, plain, (![A_138]: (r2_hidden(A_138, k1_xboole_0) | ~r2_hidden(A_138, k1_relat_1('#skF_3')) | ~r2_hidden(A_138, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_30, c_476])).
% 2.80/1.48  tff(c_482, plain, (![A_141]: (~r2_hidden(A_141, k1_relat_1('#skF_3')) | ~r2_hidden(A_141, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_320, c_480])).
% 2.80/1.48  tff(c_649, plain, (![A_149]: (~r2_hidden('#skF_1'(A_149, k1_relat_1('#skF_3')), '#skF_2') | r1_xboole_0(A_149, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_6, c_482])).
% 2.80/1.48  tff(c_654, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_649])).
% 2.80/1.48  tff(c_661, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_654, c_2])).
% 2.80/1.48  tff(c_669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_302, c_661])).
% 2.80/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.48  
% 2.80/1.48  Inference rules
% 2.80/1.48  ----------------------
% 2.80/1.48  #Ref     : 0
% 2.80/1.48  #Sup     : 127
% 2.80/1.48  #Fact    : 0
% 2.80/1.48  #Define  : 0
% 2.80/1.48  #Split   : 3
% 2.80/1.48  #Chain   : 0
% 2.80/1.48  #Close   : 0
% 2.80/1.48  
% 2.80/1.48  Ordering : KBO
% 2.80/1.48  
% 2.80/1.48  Simplification rules
% 2.80/1.48  ----------------------
% 2.80/1.48  #Subsume      : 22
% 2.80/1.48  #Demod        : 66
% 2.80/1.48  #Tautology    : 66
% 2.80/1.48  #SimpNegUnit  : 11
% 2.80/1.48  #BackRed      : 0
% 2.80/1.48  
% 2.80/1.48  #Partial instantiations: 0
% 2.80/1.48  #Strategies tried      : 1
% 2.80/1.48  
% 2.80/1.48  Timing (in seconds)
% 2.80/1.48  ----------------------
% 2.86/1.49  Preprocessing        : 0.37
% 2.86/1.49  Parsing              : 0.19
% 2.86/1.49  CNF conversion       : 0.03
% 2.86/1.49  Main loop            : 0.29
% 2.86/1.49  Inferencing          : 0.12
% 2.86/1.49  Reduction            : 0.09
% 2.86/1.49  Demodulation         : 0.06
% 2.86/1.49  BG Simplification    : 0.02
% 2.86/1.49  Subsumption          : 0.05
% 2.86/1.49  Abstraction          : 0.02
% 2.86/1.49  MUC search           : 0.00
% 2.86/1.49  Cooper               : 0.00
% 2.86/1.49  Total                : 0.69
% 2.86/1.49  Index Insertion      : 0.00
% 2.86/1.49  Index Deletion       : 0.00
% 2.86/1.49  Index Matching       : 0.00
% 2.86/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
