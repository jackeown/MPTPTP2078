%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:37 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 100 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 ( 123 expanded)
%              Number of equality atoms :   37 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_94,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_62,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    ! [C_27] : r2_hidden(C_27,k1_tarski(C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    ! [B_69,A_70] :
      ( ~ r2_hidden(B_69,A_70)
      | ~ v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [C_27] : ~ v1_xboole_0(k1_tarski(C_27)) ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [C_77,A_78] :
      ( C_77 = A_78
      | ~ r2_hidden(C_77,k1_tarski(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_110,plain,(
    ! [A_78] :
      ( '#skF_1'(k1_tarski(A_78)) = A_78
      | v1_xboole_0(k1_tarski(A_78)) ) ),
    inference(resolution,[status(thm)],[c_4,c_106])).

tff(c_116,plain,(
    ! [A_78] : '#skF_1'(k1_tarski(A_78)) = A_78 ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_110])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_60,plain,(
    ! [B_65] : r1_tarski(k1_xboole_0,k1_tarski(B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_141,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = A_84
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_153,plain,(
    ! [B_65] : k3_xboole_0(k1_xboole_0,k1_tarski(B_65)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_141])).

tff(c_188,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k3_xboole_0(A_92,B_93)) = k4_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_203,plain,(
    ! [B_65] : k4_xboole_0(k1_xboole_0,k1_tarski(B_65)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_188])).

tff(c_209,plain,(
    ! [B_65] : k4_xboole_0(k1_xboole_0,k1_tarski(B_65)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_203])).

tff(c_235,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k4_xboole_0(B_97,A_96)) = k2_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_244,plain,(
    ! [B_65] : k5_xboole_0(k1_tarski(B_65),k1_xboole_0) = k2_xboole_0(k1_tarski(B_65),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_235])).

tff(c_270,plain,(
    ! [B_101] : k2_xboole_0(k1_tarski(B_101),k1_xboole_0) = k1_tarski(B_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_244])).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_276,plain,(
    ! [B_101] : k4_xboole_0(k1_tarski(B_101),k1_tarski(B_101)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_16])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k4_xboole_0(A_19,B_20) != A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58,plain,(
    ! [B_65] : r1_tarski(k1_tarski(B_65),k1_tarski(B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_151,plain,(
    ! [B_65] : k3_xboole_0(k1_tarski(B_65),k1_tarski(B_65)) = k1_tarski(B_65) ),
    inference(resolution,[status(thm)],[c_58,c_141])).

tff(c_252,plain,(
    ! [A_98,B_99,C_100] :
      ( ~ r1_xboole_0(A_98,B_99)
      | ~ r2_hidden(C_100,k3_xboole_0(A_98,B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_297,plain,(
    ! [A_103,B_104] :
      ( ~ r1_xboole_0(A_103,B_104)
      | v1_xboole_0(k3_xboole_0(A_103,B_104)) ) ),
    inference(resolution,[status(thm)],[c_4,c_252])).

tff(c_300,plain,(
    ! [B_65] :
      ( ~ r1_xboole_0(k1_tarski(B_65),k1_tarski(B_65))
      | v1_xboole_0(k1_tarski(B_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_297])).

tff(c_317,plain,(
    ! [B_105] : ~ r1_xboole_0(k1_tarski(B_105),k1_tarski(B_105)) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_300])).

tff(c_320,plain,(
    ! [B_105] : k4_xboole_0(k1_tarski(B_105),k1_tarski(B_105)) != k1_tarski(B_105) ),
    inference(resolution,[status(thm)],[c_22,c_317])).

tff(c_322,plain,(
    ! [B_105] : k1_tarski(B_105) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_320])).

tff(c_64,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_325,plain,(
    ! [B_107,A_108] :
      ( k1_tarski(B_107) = A_108
      | k1_xboole_0 = A_108
      | ~ r1_tarski(A_108,k1_tarski(B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_331,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_6')
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_325])).

tff(c_341,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_322,c_331])).

tff(c_384,plain,(
    '#skF_1'(k1_tarski('#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_116])).

tff(c_413,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_384])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:55:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.35  
% 2.27/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.27/1.35  
% 2.27/1.35  %Foreground sorts:
% 2.27/1.35  
% 2.27/1.35  
% 2.27/1.35  %Background operators:
% 2.27/1.35  
% 2.27/1.35  
% 2.27/1.35  %Foreground operators:
% 2.27/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.27/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.27/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.27/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.27/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.27/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.27/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.27/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.27/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.27/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.27/1.35  
% 2.27/1.37  tff(f_99, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.27/1.37  tff(f_70, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.27/1.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.27/1.37  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.27/1.37  tff(f_94, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.27/1.37  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.27/1.37  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.27/1.37  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.27/1.37  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.27/1.37  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.27/1.37  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.27/1.37  tff(c_62, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.27/1.37  tff(c_28, plain, (![C_27]: (r2_hidden(C_27, k1_tarski(C_27)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.27/1.37  tff(c_76, plain, (![B_69, A_70]: (~r2_hidden(B_69, A_70) | ~v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.37  tff(c_80, plain, (![C_27]: (~v1_xboole_0(k1_tarski(C_27)))), inference(resolution, [status(thm)], [c_28, c_76])).
% 2.27/1.37  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.37  tff(c_106, plain, (![C_77, A_78]: (C_77=A_78 | ~r2_hidden(C_77, k1_tarski(A_78)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.27/1.37  tff(c_110, plain, (![A_78]: ('#skF_1'(k1_tarski(A_78))=A_78 | v1_xboole_0(k1_tarski(A_78)))), inference(resolution, [status(thm)], [c_4, c_106])).
% 2.27/1.37  tff(c_116, plain, (![A_78]: ('#skF_1'(k1_tarski(A_78))=A_78)), inference(negUnitSimplification, [status(thm)], [c_80, c_110])).
% 2.27/1.37  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.27/1.37  tff(c_60, plain, (![B_65]: (r1_tarski(k1_xboole_0, k1_tarski(B_65)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.27/1.37  tff(c_141, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=A_84 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.57/1.37  tff(c_153, plain, (![B_65]: (k3_xboole_0(k1_xboole_0, k1_tarski(B_65))=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_141])).
% 2.57/1.37  tff(c_188, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k3_xboole_0(A_92, B_93))=k4_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.57/1.37  tff(c_203, plain, (![B_65]: (k4_xboole_0(k1_xboole_0, k1_tarski(B_65))=k5_xboole_0(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_153, c_188])).
% 2.57/1.37  tff(c_209, plain, (![B_65]: (k4_xboole_0(k1_xboole_0, k1_tarski(B_65))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_203])).
% 2.57/1.37  tff(c_235, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k4_xboole_0(B_97, A_96))=k2_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.57/1.37  tff(c_244, plain, (![B_65]: (k5_xboole_0(k1_tarski(B_65), k1_xboole_0)=k2_xboole_0(k1_tarski(B_65), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_209, c_235])).
% 2.57/1.37  tff(c_270, plain, (![B_101]: (k2_xboole_0(k1_tarski(B_101), k1_xboole_0)=k1_tarski(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_244])).
% 2.57/1.37  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.37  tff(c_276, plain, (![B_101]: (k4_xboole_0(k1_tarski(B_101), k1_tarski(B_101))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_270, c_16])).
% 2.57/1.37  tff(c_22, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k4_xboole_0(A_19, B_20)!=A_19)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.57/1.37  tff(c_58, plain, (![B_65]: (r1_tarski(k1_tarski(B_65), k1_tarski(B_65)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.57/1.37  tff(c_151, plain, (![B_65]: (k3_xboole_0(k1_tarski(B_65), k1_tarski(B_65))=k1_tarski(B_65))), inference(resolution, [status(thm)], [c_58, c_141])).
% 2.57/1.37  tff(c_252, plain, (![A_98, B_99, C_100]: (~r1_xboole_0(A_98, B_99) | ~r2_hidden(C_100, k3_xboole_0(A_98, B_99)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.57/1.37  tff(c_297, plain, (![A_103, B_104]: (~r1_xboole_0(A_103, B_104) | v1_xboole_0(k3_xboole_0(A_103, B_104)))), inference(resolution, [status(thm)], [c_4, c_252])).
% 2.57/1.37  tff(c_300, plain, (![B_65]: (~r1_xboole_0(k1_tarski(B_65), k1_tarski(B_65)) | v1_xboole_0(k1_tarski(B_65)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_297])).
% 2.57/1.37  tff(c_317, plain, (![B_105]: (~r1_xboole_0(k1_tarski(B_105), k1_tarski(B_105)))), inference(negUnitSimplification, [status(thm)], [c_80, c_300])).
% 2.57/1.37  tff(c_320, plain, (![B_105]: (k4_xboole_0(k1_tarski(B_105), k1_tarski(B_105))!=k1_tarski(B_105))), inference(resolution, [status(thm)], [c_22, c_317])).
% 2.57/1.37  tff(c_322, plain, (![B_105]: (k1_tarski(B_105)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_276, c_320])).
% 2.57/1.37  tff(c_64, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.57/1.37  tff(c_325, plain, (![B_107, A_108]: (k1_tarski(B_107)=A_108 | k1_xboole_0=A_108 | ~r1_tarski(A_108, k1_tarski(B_107)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.57/1.37  tff(c_331, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6') | k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_325])).
% 2.57/1.37  tff(c_341, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_322, c_331])).
% 2.57/1.37  tff(c_384, plain, ('#skF_1'(k1_tarski('#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_341, c_116])).
% 2.57/1.37  tff(c_413, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_384])).
% 2.57/1.37  tff(c_415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_413])).
% 2.57/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.37  
% 2.57/1.37  Inference rules
% 2.57/1.37  ----------------------
% 2.57/1.37  #Ref     : 0
% 2.57/1.37  #Sup     : 84
% 2.57/1.37  #Fact    : 0
% 2.57/1.37  #Define  : 0
% 2.57/1.37  #Split   : 2
% 2.57/1.37  #Chain   : 0
% 2.57/1.37  #Close   : 0
% 2.57/1.37  
% 2.57/1.37  Ordering : KBO
% 2.57/1.37  
% 2.57/1.37  Simplification rules
% 2.57/1.37  ----------------------
% 2.57/1.37  #Subsume      : 6
% 2.57/1.37  #Demod        : 32
% 2.57/1.37  #Tautology    : 49
% 2.57/1.37  #SimpNegUnit  : 8
% 2.57/1.37  #BackRed      : 3
% 2.57/1.37  
% 2.57/1.37  #Partial instantiations: 0
% 2.57/1.37  #Strategies tried      : 1
% 2.57/1.37  
% 2.57/1.37  Timing (in seconds)
% 2.57/1.37  ----------------------
% 2.57/1.37  Preprocessing        : 0.34
% 2.57/1.37  Parsing              : 0.17
% 2.57/1.37  CNF conversion       : 0.02
% 2.57/1.37  Main loop            : 0.24
% 2.57/1.38  Inferencing          : 0.08
% 2.57/1.38  Reduction            : 0.09
% 2.57/1.38  Demodulation         : 0.06
% 2.57/1.38  BG Simplification    : 0.02
% 2.57/1.38  Subsumption          : 0.04
% 2.57/1.38  Abstraction          : 0.01
% 2.57/1.38  MUC search           : 0.00
% 2.57/1.38  Cooper               : 0.00
% 2.57/1.38  Total                : 0.62
% 2.57/1.38  Index Insertion      : 0.00
% 2.57/1.38  Index Deletion       : 0.00
% 2.57/1.38  Index Matching       : 0.00
% 2.57/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
