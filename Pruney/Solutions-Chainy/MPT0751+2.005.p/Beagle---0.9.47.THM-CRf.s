%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:26 EST 2020

% Result     : Theorem 10.97s
% Output     : CNFRefutation 10.97s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 140 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  184 ( 424 expanded)
%              Number of equality atoms :   26 (  79 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3

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

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_112,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v4_ordinal1(A)
      <=> ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(B,A)
             => r2_hidden(k1_ordinal1(B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

tff(f_62,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_71,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
          <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_80,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,k1_ordinal1(B))
          <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_58,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_42,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_40,plain,(
    ! [A_18] :
      ( v3_ordinal1('#skF_1'(A_18))
      | v4_ordinal1(A_18)
      | ~ v3_ordinal1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_38,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_1'(A_18),A_18)
      | v4_ordinal1(A_18)
      | ~ v3_ordinal1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    ! [A_11] :
      ( v3_ordinal1(k1_ordinal1(A_11))
      | ~ v3_ordinal1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [A_12,B_14] :
      ( r1_ordinal1(k1_ordinal1(A_12),B_14)
      | ~ r2_hidden(A_12,B_14)
      | ~ v3_ordinal1(B_14)
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5375,plain,(
    ! [A_245,B_246] :
      ( r2_hidden(A_245,k1_ordinal1(B_246))
      | ~ r1_ordinal1(A_245,B_246)
      | ~ v3_ordinal1(B_246)
      | ~ v3_ordinal1(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | r2_hidden(A_8,B_9)
      | ~ r2_hidden(A_8,k1_ordinal1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5466,plain,(
    ! [B_255,A_256] :
      ( B_255 = A_256
      | r2_hidden(A_256,B_255)
      | ~ r1_ordinal1(A_256,B_255)
      | ~ v3_ordinal1(B_255)
      | ~ v3_ordinal1(A_256) ) ),
    inference(resolution,[status(thm)],[c_5375,c_16])).

tff(c_36,plain,(
    ! [A_18] :
      ( ~ r2_hidden(k1_ordinal1('#skF_1'(A_18)),A_18)
      | v4_ordinal1(A_18)
      | ~ v3_ordinal1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6442,plain,(
    ! [B_310] :
      ( v4_ordinal1(B_310)
      | k1_ordinal1('#skF_1'(B_310)) = B_310
      | ~ r1_ordinal1(k1_ordinal1('#skF_1'(B_310)),B_310)
      | ~ v3_ordinal1(B_310)
      | ~ v3_ordinal1(k1_ordinal1('#skF_1'(B_310))) ) ),
    inference(resolution,[status(thm)],[c_5466,c_36])).

tff(c_11365,plain,(
    ! [B_435] :
      ( v4_ordinal1(B_435)
      | k1_ordinal1('#skF_1'(B_435)) = B_435
      | ~ v3_ordinal1(k1_ordinal1('#skF_1'(B_435)))
      | ~ r2_hidden('#skF_1'(B_435),B_435)
      | ~ v3_ordinal1(B_435)
      | ~ v3_ordinal1('#skF_1'(B_435)) ) ),
    inference(resolution,[status(thm)],[c_28,c_6442])).

tff(c_11372,plain,(
    ! [B_436] :
      ( v4_ordinal1(B_436)
      | k1_ordinal1('#skF_1'(B_436)) = B_436
      | ~ r2_hidden('#skF_1'(B_436),B_436)
      | ~ v3_ordinal1(B_436)
      | ~ v3_ordinal1('#skF_1'(B_436)) ) ),
    inference(resolution,[status(thm)],[c_24,c_11365])).

tff(c_11457,plain,(
    ! [A_437] :
      ( k1_ordinal1('#skF_1'(A_437)) = A_437
      | ~ v3_ordinal1('#skF_1'(A_437))
      | v4_ordinal1(A_437)
      | ~ v3_ordinal1(A_437) ) ),
    inference(resolution,[status(thm)],[c_38,c_11372])).

tff(c_11465,plain,(
    ! [A_438] :
      ( k1_ordinal1('#skF_1'(A_438)) = A_438
      | v4_ordinal1(A_438)
      | ~ v3_ordinal1(A_438) ) ),
    inference(resolution,[status(thm)],[c_40,c_11457])).

tff(c_5280,plain,(
    ! [A_221] :
      ( v3_ordinal1('#skF_1'(A_221))
      | v4_ordinal1(A_221)
      | ~ v3_ordinal1(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_54,plain,
    ( ~ v4_ordinal1('#skF_2')
    | v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_59,plain,(
    ~ v4_ordinal1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_44,plain,(
    ! [B_24] :
      ( k1_ordinal1(B_24) != '#skF_2'
      | ~ v3_ordinal1(B_24)
      | v4_ordinal1('#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5265,plain,(
    ! [B_24] :
      ( k1_ordinal1(B_24) != '#skF_2'
      | ~ v3_ordinal1(B_24) ) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_44])).

tff(c_5284,plain,(
    ! [A_221] :
      ( k1_ordinal1('#skF_1'(A_221)) != '#skF_2'
      | v4_ordinal1(A_221)
      | ~ v3_ordinal1(A_221) ) ),
    inference(resolution,[status(thm)],[c_5280,c_5265])).

tff(c_11721,plain,(
    ! [A_438] :
      ( A_438 != '#skF_2'
      | v4_ordinal1(A_438)
      | ~ v3_ordinal1(A_438)
      | v4_ordinal1(A_438)
      | ~ v3_ordinal1(A_438) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11465,c_5284])).

tff(c_11775,plain,(
    ! [A_441] :
      ( A_441 != '#skF_2'
      | ~ v3_ordinal1(A_441)
      | v4_ordinal1(A_441) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_11721])).

tff(c_11781,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_11775,c_59])).

tff(c_11786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_11781])).

tff(c_11788,plain,(
    v4_ordinal1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_50,plain,
    ( ~ v4_ordinal1('#skF_2')
    | k1_ordinal1('#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_11791,plain,(
    k1_ordinal1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11788,c_50])).

tff(c_22,plain,(
    ! [A_10] : k1_ordinal1(A_10) != A_10 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_11801,plain,(
    '#skF_2' != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_11791,c_22])).

tff(c_11787,plain,(
    v3_ordinal1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_18,plain,(
    ! [B_9] : r2_hidden(B_9,k1_ordinal1(B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_11798,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11791,c_18])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden(A_8,B_9)
      | r2_hidden(A_8,k1_ordinal1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_11910,plain,(
    ! [A_462,B_463] :
      ( r1_ordinal1(A_462,B_463)
      | ~ r2_hidden(A_462,k1_ordinal1(B_463))
      | ~ v3_ordinal1(B_463)
      | ~ v3_ordinal1(A_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_11962,plain,(
    ! [A_466,B_467] :
      ( r1_ordinal1(A_466,B_467)
      | ~ v3_ordinal1(B_467)
      | ~ v3_ordinal1(A_466)
      | ~ r2_hidden(A_466,B_467) ) ),
    inference(resolution,[status(thm)],[c_20,c_11910])).

tff(c_11974,plain,
    ( r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11798,c_11962])).

tff(c_11985,plain,(
    r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11787,c_42,c_11974])).

tff(c_12277,plain,(
    ! [B_483,A_484] :
      ( r2_hidden(k1_ordinal1(B_483),A_484)
      | ~ r2_hidden(B_483,A_484)
      | ~ v3_ordinal1(B_483)
      | ~ v4_ordinal1(A_484)
      | ~ v3_ordinal1(A_484) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12311,plain,(
    ! [A_484] :
      ( r2_hidden('#skF_2',A_484)
      | ~ r2_hidden('#skF_3',A_484)
      | ~ v3_ordinal1('#skF_3')
      | ~ v4_ordinal1(A_484)
      | ~ v3_ordinal1(A_484) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11791,c_12277])).

tff(c_12345,plain,(
    ! [A_486] :
      ( r2_hidden('#skF_2',A_486)
      | ~ r2_hidden('#skF_3',A_486)
      | ~ v4_ordinal1(A_486)
      | ~ v3_ordinal1(A_486) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11787,c_12311])).

tff(c_11920,plain,(
    ! [A_462] :
      ( r1_ordinal1(A_462,'#skF_3')
      | ~ r2_hidden(A_462,'#skF_2')
      | ~ v3_ordinal1('#skF_3')
      | ~ v3_ordinal1(A_462) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11791,c_11910])).

tff(c_11927,plain,(
    ! [A_462] :
      ( r1_ordinal1(A_462,'#skF_3')
      | ~ r2_hidden(A_462,'#skF_2')
      | ~ v3_ordinal1(A_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11787,c_11920])).

tff(c_12360,plain,
    ( r1_ordinal1('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_2')
    | ~ v4_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12345,c_11927])).

tff(c_12384,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_11788,c_11798,c_12360])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ r1_ordinal1(A_6,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_11897,plain,(
    ! [A_458,B_459] :
      ( r1_tarski(A_458,B_459)
      | ~ r1_ordinal1(A_458,B_459)
      | ~ v3_ordinal1(B_459)
      | ~ v3_ordinal1(A_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12420,plain,(
    ! [B_487,A_488] :
      ( B_487 = A_488
      | ~ r1_tarski(B_487,A_488)
      | ~ r1_ordinal1(A_488,B_487)
      | ~ v3_ordinal1(B_487)
      | ~ v3_ordinal1(A_488) ) ),
    inference(resolution,[status(thm)],[c_11897,c_2])).

tff(c_13857,plain,(
    ! [B_529,A_530] :
      ( B_529 = A_530
      | ~ r1_ordinal1(B_529,A_530)
      | ~ r1_ordinal1(A_530,B_529)
      | ~ v3_ordinal1(B_529)
      | ~ v3_ordinal1(A_530) ) ),
    inference(resolution,[status(thm)],[c_14,c_12420])).

tff(c_13893,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12384,c_13857])).

tff(c_13966,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11787,c_42,c_11985,c_13893])).

tff(c_13968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11801,c_13966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:54:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.97/3.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.97/3.71  
% 10.97/3.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.97/3.71  %$ r2_hidden > r1_tarski > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3
% 10.97/3.71  
% 10.97/3.71  %Foreground sorts:
% 10.97/3.71  
% 10.97/3.71  
% 10.97/3.71  %Background operators:
% 10.97/3.71  
% 10.97/3.71  
% 10.97/3.71  %Foreground operators:
% 10.97/3.71  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 10.97/3.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.97/3.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.97/3.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.97/3.71  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.97/3.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.97/3.71  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 10.97/3.71  tff('#skF_2', type, '#skF_2': $i).
% 10.97/3.71  tff('#skF_3', type, '#skF_3': $i).
% 10.97/3.71  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 10.97/3.71  tff(v4_ordinal1, type, v4_ordinal1: $i > $o).
% 10.97/3.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.97/3.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.97/3.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.97/3.71  
% 10.97/3.72  tff(f_112, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (~(~v4_ordinal1(A) & (![B]: (v3_ordinal1(B) => ~(A = k1_ordinal1(B))))) & ~((?[B]: (v3_ordinal1(B) & (A = k1_ordinal1(B)))) & v4_ordinal1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_ordinal1)).
% 10.97/3.72  tff(f_91, axiom, (![A]: (v3_ordinal1(A) => (v4_ordinal1(A) <=> (![B]: (v3_ordinal1(B) => (r2_hidden(B, A) => r2_hidden(k1_ordinal1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 10.97/3.72  tff(f_62, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 10.97/3.72  tff(f_71, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 10.97/3.72  tff(f_80, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 10.97/3.72  tff(f_55, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 10.97/3.72  tff(f_58, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 10.97/3.72  tff(f_49, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 10.97/3.72  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.97/3.72  tff(c_42, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.97/3.72  tff(c_40, plain, (![A_18]: (v3_ordinal1('#skF_1'(A_18)) | v4_ordinal1(A_18) | ~v3_ordinal1(A_18))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.97/3.72  tff(c_38, plain, (![A_18]: (r2_hidden('#skF_1'(A_18), A_18) | v4_ordinal1(A_18) | ~v3_ordinal1(A_18))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.97/3.72  tff(c_24, plain, (![A_11]: (v3_ordinal1(k1_ordinal1(A_11)) | ~v3_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.97/3.72  tff(c_28, plain, (![A_12, B_14]: (r1_ordinal1(k1_ordinal1(A_12), B_14) | ~r2_hidden(A_12, B_14) | ~v3_ordinal1(B_14) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.97/3.72  tff(c_5375, plain, (![A_245, B_246]: (r2_hidden(A_245, k1_ordinal1(B_246)) | ~r1_ordinal1(A_245, B_246) | ~v3_ordinal1(B_246) | ~v3_ordinal1(A_245))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.97/3.72  tff(c_16, plain, (![B_9, A_8]: (B_9=A_8 | r2_hidden(A_8, B_9) | ~r2_hidden(A_8, k1_ordinal1(B_9)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.97/3.72  tff(c_5466, plain, (![B_255, A_256]: (B_255=A_256 | r2_hidden(A_256, B_255) | ~r1_ordinal1(A_256, B_255) | ~v3_ordinal1(B_255) | ~v3_ordinal1(A_256))), inference(resolution, [status(thm)], [c_5375, c_16])).
% 10.97/3.72  tff(c_36, plain, (![A_18]: (~r2_hidden(k1_ordinal1('#skF_1'(A_18)), A_18) | v4_ordinal1(A_18) | ~v3_ordinal1(A_18))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.97/3.72  tff(c_6442, plain, (![B_310]: (v4_ordinal1(B_310) | k1_ordinal1('#skF_1'(B_310))=B_310 | ~r1_ordinal1(k1_ordinal1('#skF_1'(B_310)), B_310) | ~v3_ordinal1(B_310) | ~v3_ordinal1(k1_ordinal1('#skF_1'(B_310))))), inference(resolution, [status(thm)], [c_5466, c_36])).
% 10.97/3.72  tff(c_11365, plain, (![B_435]: (v4_ordinal1(B_435) | k1_ordinal1('#skF_1'(B_435))=B_435 | ~v3_ordinal1(k1_ordinal1('#skF_1'(B_435))) | ~r2_hidden('#skF_1'(B_435), B_435) | ~v3_ordinal1(B_435) | ~v3_ordinal1('#skF_1'(B_435)))), inference(resolution, [status(thm)], [c_28, c_6442])).
% 10.97/3.72  tff(c_11372, plain, (![B_436]: (v4_ordinal1(B_436) | k1_ordinal1('#skF_1'(B_436))=B_436 | ~r2_hidden('#skF_1'(B_436), B_436) | ~v3_ordinal1(B_436) | ~v3_ordinal1('#skF_1'(B_436)))), inference(resolution, [status(thm)], [c_24, c_11365])).
% 10.97/3.72  tff(c_11457, plain, (![A_437]: (k1_ordinal1('#skF_1'(A_437))=A_437 | ~v3_ordinal1('#skF_1'(A_437)) | v4_ordinal1(A_437) | ~v3_ordinal1(A_437))), inference(resolution, [status(thm)], [c_38, c_11372])).
% 10.97/3.72  tff(c_11465, plain, (![A_438]: (k1_ordinal1('#skF_1'(A_438))=A_438 | v4_ordinal1(A_438) | ~v3_ordinal1(A_438))), inference(resolution, [status(thm)], [c_40, c_11457])).
% 10.97/3.72  tff(c_5280, plain, (![A_221]: (v3_ordinal1('#skF_1'(A_221)) | v4_ordinal1(A_221) | ~v3_ordinal1(A_221))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.97/3.72  tff(c_54, plain, (~v4_ordinal1('#skF_2') | v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.97/3.72  tff(c_59, plain, (~v4_ordinal1('#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 10.97/3.72  tff(c_44, plain, (![B_24]: (k1_ordinal1(B_24)!='#skF_2' | ~v3_ordinal1(B_24) | v4_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.97/3.72  tff(c_5265, plain, (![B_24]: (k1_ordinal1(B_24)!='#skF_2' | ~v3_ordinal1(B_24))), inference(negUnitSimplification, [status(thm)], [c_59, c_44])).
% 10.97/3.72  tff(c_5284, plain, (![A_221]: (k1_ordinal1('#skF_1'(A_221))!='#skF_2' | v4_ordinal1(A_221) | ~v3_ordinal1(A_221))), inference(resolution, [status(thm)], [c_5280, c_5265])).
% 10.97/3.72  tff(c_11721, plain, (![A_438]: (A_438!='#skF_2' | v4_ordinal1(A_438) | ~v3_ordinal1(A_438) | v4_ordinal1(A_438) | ~v3_ordinal1(A_438))), inference(superposition, [status(thm), theory('equality')], [c_11465, c_5284])).
% 10.97/3.72  tff(c_11775, plain, (![A_441]: (A_441!='#skF_2' | ~v3_ordinal1(A_441) | v4_ordinal1(A_441))), inference(factorization, [status(thm), theory('equality')], [c_11721])).
% 10.97/3.72  tff(c_11781, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_11775, c_59])).
% 10.97/3.72  tff(c_11786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_11781])).
% 10.97/3.72  tff(c_11788, plain, (v4_ordinal1('#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 10.97/3.72  tff(c_50, plain, (~v4_ordinal1('#skF_2') | k1_ordinal1('#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.97/3.72  tff(c_11791, plain, (k1_ordinal1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11788, c_50])).
% 10.97/3.72  tff(c_22, plain, (![A_10]: (k1_ordinal1(A_10)!=A_10)), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.97/3.72  tff(c_11801, plain, ('#skF_2'!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_11791, c_22])).
% 10.97/3.72  tff(c_11787, plain, (v3_ordinal1('#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 10.97/3.72  tff(c_18, plain, (![B_9]: (r2_hidden(B_9, k1_ordinal1(B_9)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.97/3.72  tff(c_11798, plain, (r2_hidden('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11791, c_18])).
% 10.97/3.72  tff(c_20, plain, (![A_8, B_9]: (~r2_hidden(A_8, B_9) | r2_hidden(A_8, k1_ordinal1(B_9)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.97/3.72  tff(c_11910, plain, (![A_462, B_463]: (r1_ordinal1(A_462, B_463) | ~r2_hidden(A_462, k1_ordinal1(B_463)) | ~v3_ordinal1(B_463) | ~v3_ordinal1(A_462))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.97/3.72  tff(c_11962, plain, (![A_466, B_467]: (r1_ordinal1(A_466, B_467) | ~v3_ordinal1(B_467) | ~v3_ordinal1(A_466) | ~r2_hidden(A_466, B_467))), inference(resolution, [status(thm)], [c_20, c_11910])).
% 10.97/3.72  tff(c_11974, plain, (r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_11798, c_11962])).
% 10.97/3.72  tff(c_11985, plain, (r1_ordinal1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11787, c_42, c_11974])).
% 10.97/3.72  tff(c_12277, plain, (![B_483, A_484]: (r2_hidden(k1_ordinal1(B_483), A_484) | ~r2_hidden(B_483, A_484) | ~v3_ordinal1(B_483) | ~v4_ordinal1(A_484) | ~v3_ordinal1(A_484))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.97/3.72  tff(c_12311, plain, (![A_484]: (r2_hidden('#skF_2', A_484) | ~r2_hidden('#skF_3', A_484) | ~v3_ordinal1('#skF_3') | ~v4_ordinal1(A_484) | ~v3_ordinal1(A_484))), inference(superposition, [status(thm), theory('equality')], [c_11791, c_12277])).
% 10.97/3.72  tff(c_12345, plain, (![A_486]: (r2_hidden('#skF_2', A_486) | ~r2_hidden('#skF_3', A_486) | ~v4_ordinal1(A_486) | ~v3_ordinal1(A_486))), inference(demodulation, [status(thm), theory('equality')], [c_11787, c_12311])).
% 10.97/3.72  tff(c_11920, plain, (![A_462]: (r1_ordinal1(A_462, '#skF_3') | ~r2_hidden(A_462, '#skF_2') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(A_462))), inference(superposition, [status(thm), theory('equality')], [c_11791, c_11910])).
% 10.97/3.72  tff(c_11927, plain, (![A_462]: (r1_ordinal1(A_462, '#skF_3') | ~r2_hidden(A_462, '#skF_2') | ~v3_ordinal1(A_462))), inference(demodulation, [status(thm), theory('equality')], [c_11787, c_11920])).
% 10.97/3.72  tff(c_12360, plain, (r1_ordinal1('#skF_2', '#skF_3') | ~r2_hidden('#skF_3', '#skF_2') | ~v4_ordinal1('#skF_2') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_12345, c_11927])).
% 10.97/3.72  tff(c_12384, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_11788, c_11798, c_12360])).
% 10.97/3.72  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~r1_ordinal1(A_6, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.97/3.72  tff(c_11897, plain, (![A_458, B_459]: (r1_tarski(A_458, B_459) | ~r1_ordinal1(A_458, B_459) | ~v3_ordinal1(B_459) | ~v3_ordinal1(A_458))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.97/3.72  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.97/3.72  tff(c_12420, plain, (![B_487, A_488]: (B_487=A_488 | ~r1_tarski(B_487, A_488) | ~r1_ordinal1(A_488, B_487) | ~v3_ordinal1(B_487) | ~v3_ordinal1(A_488))), inference(resolution, [status(thm)], [c_11897, c_2])).
% 10.97/3.72  tff(c_13857, plain, (![B_529, A_530]: (B_529=A_530 | ~r1_ordinal1(B_529, A_530) | ~r1_ordinal1(A_530, B_529) | ~v3_ordinal1(B_529) | ~v3_ordinal1(A_530))), inference(resolution, [status(thm)], [c_14, c_12420])).
% 10.97/3.72  tff(c_13893, plain, ('#skF_2'='#skF_3' | ~r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_12384, c_13857])).
% 10.97/3.72  tff(c_13966, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11787, c_42, c_11985, c_13893])).
% 10.97/3.72  tff(c_13968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11801, c_13966])).
% 10.97/3.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.97/3.72  
% 10.97/3.72  Inference rules
% 10.97/3.72  ----------------------
% 10.97/3.72  #Ref     : 0
% 10.97/3.72  #Sup     : 2893
% 10.97/3.72  #Fact    : 32
% 10.97/3.72  #Define  : 0
% 10.97/3.72  #Split   : 8
% 10.97/3.72  #Chain   : 0
% 10.97/3.72  #Close   : 0
% 10.97/3.72  
% 10.97/3.72  Ordering : KBO
% 10.97/3.72  
% 10.97/3.72  Simplification rules
% 10.97/3.72  ----------------------
% 10.97/3.72  #Subsume      : 1243
% 10.97/3.72  #Demod        : 595
% 10.97/3.72  #Tautology    : 357
% 10.97/3.72  #SimpNegUnit  : 123
% 10.97/3.72  #BackRed      : 0
% 10.97/3.72  
% 10.97/3.72  #Partial instantiations: 0
% 10.97/3.72  #Strategies tried      : 1
% 10.97/3.72  
% 10.97/3.72  Timing (in seconds)
% 10.97/3.72  ----------------------
% 10.97/3.73  Preprocessing        : 0.30
% 10.97/3.73  Parsing              : 0.17
% 10.97/3.73  CNF conversion       : 0.02
% 10.97/3.73  Main loop            : 2.66
% 10.97/3.73  Inferencing          : 0.67
% 10.97/3.73  Reduction            : 0.51
% 10.97/3.73  Demodulation         : 0.30
% 10.97/3.73  BG Simplification    : 0.07
% 10.97/3.73  Subsumption          : 1.27
% 10.97/3.73  Abstraction          : 0.11
% 10.97/3.73  MUC search           : 0.00
% 10.97/3.73  Cooper               : 0.00
% 10.97/3.73  Total                : 3.00
% 10.97/3.73  Index Insertion      : 0.00
% 10.97/3.73  Index Deletion       : 0.00
% 10.97/3.73  Index Matching       : 0.00
% 10.97/3.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
