%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:24 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 201 expanded)
%              Number of leaves         :   35 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 329 expanded)
%              Number of equality atoms :   26 ( 127 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_18,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_tarski(A_50),B_51)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_54,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_72,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_24])).

tff(c_323,plain,(
    ! [B_99,A_100] :
      ( B_99 = A_100
      | ~ r1_tarski(B_99,A_100)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_342,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_323])).

tff(c_385,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_342])).

tff(c_389,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_385])).

tff(c_44,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),B_53)
      | r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_124,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,B_71) = A_70
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_138,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_72,c_124])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_299,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ r1_xboole_0(A_96,B_97)
      | ~ r2_hidden(C_98,k3_xboole_0(A_96,B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_354,plain,(
    ! [A_103,B_104] :
      ( ~ r1_xboole_0(A_103,B_104)
      | v1_xboole_0(k3_xboole_0(A_103,B_104)) ) ),
    inference(resolution,[status(thm)],[c_6,c_299])).

tff(c_391,plain,(
    ! [B_106,A_107] :
      ( ~ r1_xboole_0(B_106,A_107)
      | v1_xboole_0(k3_xboole_0(A_107,B_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_354])).

tff(c_403,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_391])).

tff(c_423,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_403])).

tff(c_426,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_423])).

tff(c_430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_426])).

tff(c_431,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_435,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_431,c_8])).

tff(c_439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_435])).

tff(c_440,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_342])).

tff(c_207,plain,(
    ! [A_87,C_88,B_89] :
      ( r1_tarski(A_87,k2_xboole_0(C_88,B_89))
      | ~ r1_tarski(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_217,plain,(
    ! [A_87] :
      ( r1_tarski(A_87,k1_tarski('#skF_3'))
      | ~ r1_tarski(A_87,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_207])).

tff(c_574,plain,(
    ! [A_116] :
      ( r1_tarski(A_116,'#skF_4')
      | ~ r1_tarski(A_116,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_217])).

tff(c_584,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_574])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( B_14 = A_13
      | ~ r1_tarski(B_14,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_586,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_584,c_14])).

tff(c_592,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_586])).

tff(c_513,plain,(
    ! [B_53] :
      ( r1_xboole_0('#skF_4',B_53)
      | r2_hidden('#skF_3',B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_44])).

tff(c_795,plain,(
    ! [B_134] :
      ( r1_tarski('#skF_4',B_134)
      | ~ r2_hidden('#skF_3',B_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_42])).

tff(c_876,plain,(
    ! [B_137] :
      ( r1_tarski('#skF_4',B_137)
      | r1_xboole_0('#skF_4',B_137) ) ),
    inference(resolution,[status(thm)],[c_513,c_795])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_593,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_584,c_22])).

tff(c_603,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_2])).

tff(c_322,plain,(
    ! [A_96,B_97] :
      ( ~ r1_xboole_0(A_96,B_97)
      | v1_xboole_0(k3_xboole_0(A_96,B_97)) ) ),
    inference(resolution,[status(thm)],[c_6,c_299])).

tff(c_619,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_322])).

tff(c_711,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_619])).

tff(c_882,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_876,c_711])).

tff(c_895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_592,c_882])).

tff(c_896,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_619])).

tff(c_900,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_896,c_8])).

tff(c_904,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.39  
% 3.01/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.01/1.39  
% 3.01/1.39  %Foreground sorts:
% 3.01/1.39  
% 3.01/1.39  
% 3.01/1.39  %Background operators:
% 3.01/1.39  
% 3.01/1.39  
% 3.01/1.39  %Foreground operators:
% 3.01/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.01/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.01/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.01/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.01/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.01/1.39  tff('#skF_5', type, '#skF_5': $i).
% 3.01/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.01/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.01/1.39  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.01/1.39  tff('#skF_4', type, '#skF_4': $i).
% 3.01/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.01/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.01/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.01/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.01/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.01/1.39  
% 3.01/1.41  tff(f_105, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.01/1.41  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.01/1.41  tff(f_85, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.01/1.41  tff(f_67, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.01/1.41  tff(f_90, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.01/1.41  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.01/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.01/1.41  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.01/1.41  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.01/1.41  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.01/1.41  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.01/1.41  tff(c_48, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.01/1.41  tff(c_52, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.01/1.41  tff(c_18, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.01/1.41  tff(c_50, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.01/1.41  tff(c_42, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), B_51) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.01/1.41  tff(c_54, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.01/1.41  tff(c_24, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.01/1.41  tff(c_72, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_24])).
% 3.01/1.41  tff(c_323, plain, (![B_99, A_100]: (B_99=A_100 | ~r1_tarski(B_99, A_100) | ~r1_tarski(A_100, B_99))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.01/1.41  tff(c_342, plain, (k1_tarski('#skF_3')='#skF_4' | ~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_72, c_323])).
% 3.01/1.41  tff(c_385, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_342])).
% 3.01/1.41  tff(c_389, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_385])).
% 3.01/1.41  tff(c_44, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), B_53) | r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.01/1.41  tff(c_124, plain, (![A_70, B_71]: (k3_xboole_0(A_70, B_71)=A_70 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.01/1.41  tff(c_138, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(resolution, [status(thm)], [c_72, c_124])).
% 3.01/1.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.01/1.41  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.01/1.41  tff(c_299, plain, (![A_96, B_97, C_98]: (~r1_xboole_0(A_96, B_97) | ~r2_hidden(C_98, k3_xboole_0(A_96, B_97)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.01/1.41  tff(c_354, plain, (![A_103, B_104]: (~r1_xboole_0(A_103, B_104) | v1_xboole_0(k3_xboole_0(A_103, B_104)))), inference(resolution, [status(thm)], [c_6, c_299])).
% 3.01/1.41  tff(c_391, plain, (![B_106, A_107]: (~r1_xboole_0(B_106, A_107) | v1_xboole_0(k3_xboole_0(A_107, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_354])).
% 3.01/1.41  tff(c_403, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_138, c_391])).
% 3.01/1.41  tff(c_423, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_403])).
% 3.01/1.41  tff(c_426, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_423])).
% 3.01/1.41  tff(c_430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_389, c_426])).
% 3.01/1.41  tff(c_431, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_403])).
% 3.01/1.41  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.01/1.41  tff(c_435, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_431, c_8])).
% 3.01/1.41  tff(c_439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_435])).
% 3.01/1.41  tff(c_440, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_342])).
% 3.01/1.41  tff(c_207, plain, (![A_87, C_88, B_89]: (r1_tarski(A_87, k2_xboole_0(C_88, B_89)) | ~r1_tarski(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.01/1.41  tff(c_217, plain, (![A_87]: (r1_tarski(A_87, k1_tarski('#skF_3')) | ~r1_tarski(A_87, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_207])).
% 3.01/1.41  tff(c_574, plain, (![A_116]: (r1_tarski(A_116, '#skF_4') | ~r1_tarski(A_116, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_217])).
% 3.01/1.41  tff(c_584, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_574])).
% 3.01/1.41  tff(c_14, plain, (![B_14, A_13]: (B_14=A_13 | ~r1_tarski(B_14, A_13) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.01/1.41  tff(c_586, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_584, c_14])).
% 3.01/1.41  tff(c_592, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_586])).
% 3.01/1.41  tff(c_513, plain, (![B_53]: (r1_xboole_0('#skF_4', B_53) | r2_hidden('#skF_3', B_53))), inference(superposition, [status(thm), theory('equality')], [c_440, c_44])).
% 3.01/1.41  tff(c_795, plain, (![B_134]: (r1_tarski('#skF_4', B_134) | ~r2_hidden('#skF_3', B_134))), inference(superposition, [status(thm), theory('equality')], [c_440, c_42])).
% 3.01/1.41  tff(c_876, plain, (![B_137]: (r1_tarski('#skF_4', B_137) | r1_xboole_0('#skF_4', B_137))), inference(resolution, [status(thm)], [c_513, c_795])).
% 3.01/1.41  tff(c_22, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.01/1.41  tff(c_593, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_584, c_22])).
% 3.01/1.41  tff(c_603, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_593, c_2])).
% 3.01/1.41  tff(c_322, plain, (![A_96, B_97]: (~r1_xboole_0(A_96, B_97) | v1_xboole_0(k3_xboole_0(A_96, B_97)))), inference(resolution, [status(thm)], [c_6, c_299])).
% 3.01/1.41  tff(c_619, plain, (~r1_xboole_0('#skF_4', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_603, c_322])).
% 3.01/1.41  tff(c_711, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_619])).
% 3.01/1.41  tff(c_882, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_876, c_711])).
% 3.01/1.41  tff(c_895, plain, $false, inference(negUnitSimplification, [status(thm)], [c_592, c_882])).
% 3.01/1.41  tff(c_896, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_619])).
% 3.01/1.41  tff(c_900, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_896, c_8])).
% 3.01/1.41  tff(c_904, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_900])).
% 3.01/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.41  
% 3.01/1.41  Inference rules
% 3.01/1.41  ----------------------
% 3.01/1.41  #Ref     : 0
% 3.01/1.41  #Sup     : 204
% 3.01/1.41  #Fact    : 0
% 3.01/1.41  #Define  : 0
% 3.01/1.41  #Split   : 5
% 3.01/1.41  #Chain   : 0
% 3.01/1.41  #Close   : 0
% 3.01/1.41  
% 3.01/1.41  Ordering : KBO
% 3.01/1.41  
% 3.01/1.41  Simplification rules
% 3.01/1.41  ----------------------
% 3.01/1.41  #Subsume      : 20
% 3.01/1.41  #Demod        : 49
% 3.01/1.41  #Tautology    : 87
% 3.01/1.41  #SimpNegUnit  : 10
% 3.01/1.41  #BackRed      : 5
% 3.01/1.41  
% 3.01/1.41  #Partial instantiations: 0
% 3.01/1.41  #Strategies tried      : 1
% 3.01/1.41  
% 3.01/1.41  Timing (in seconds)
% 3.01/1.41  ----------------------
% 3.01/1.41  Preprocessing        : 0.32
% 3.01/1.41  Parsing              : 0.17
% 3.01/1.41  CNF conversion       : 0.02
% 3.01/1.41  Main loop            : 0.33
% 3.01/1.41  Inferencing          : 0.12
% 3.01/1.41  Reduction            : 0.11
% 3.01/1.41  Demodulation         : 0.08
% 3.01/1.41  BG Simplification    : 0.02
% 3.01/1.41  Subsumption          : 0.06
% 3.01/1.41  Abstraction          : 0.01
% 3.01/1.41  MUC search           : 0.00
% 3.01/1.41  Cooper               : 0.00
% 3.01/1.41  Total                : 0.68
% 3.01/1.41  Index Insertion      : 0.00
% 3.01/1.41  Index Deletion       : 0.00
% 3.01/1.41  Index Matching       : 0.00
% 3.01/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
