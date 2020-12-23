%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:17 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   65 (  87 expanded)
%              Number of leaves         :   33 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 134 expanded)
%              Number of equality atoms :   40 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_48,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_89,plain,(
    k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_22,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(k1_tarski(A_32),B_33)
      | r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_129,plain,(
    ! [A_74,B_75] :
      ( k7_relat_1(A_74,B_75) = k1_xboole_0
      | ~ r1_xboole_0(B_75,k1_relat_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_196,plain,(
    ! [A_88,A_89] :
      ( k7_relat_1(A_88,k1_tarski(A_89)) = k1_xboole_0
      | ~ v1_relat_1(A_88)
      | r2_hidden(A_89,k1_relat_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_22,c_129])).

tff(c_42,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_42])).

tff(c_199,plain,
    ( k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_196,c_90])).

tff(c_202,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_199])).

tff(c_111,plain,(
    ! [B_70,A_71] :
      ( r1_xboole_0(k1_relat_1(B_70),A_71)
      | k7_relat_1(B_70,A_71) != k1_xboole_0
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [B_40,A_39] :
      ( k9_relat_1(B_40,A_39) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_40),A_39)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_154,plain,(
    ! [B_80,A_81] :
      ( k9_relat_1(B_80,A_81) = k1_xboole_0
      | k7_relat_1(B_80,A_81) != k1_xboole_0
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_111,c_28])).

tff(c_158,plain,(
    ! [A_82] :
      ( k9_relat_1('#skF_2',A_82) = k1_xboole_0
      | k7_relat_1('#skF_2',A_82) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_154])).

tff(c_26,plain,(
    ! [A_36,B_38] :
      ( k9_relat_1(A_36,k1_tarski(B_38)) = k11_relat_1(A_36,B_38)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_165,plain,(
    ! [B_38] :
      ( k11_relat_1('#skF_2',B_38) = k1_xboole_0
      | ~ v1_relat_1('#skF_2')
      | k7_relat_1('#skF_2',k1_tarski(B_38)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_26])).

tff(c_175,plain,(
    ! [B_38] :
      ( k11_relat_1('#skF_2',B_38) = k1_xboole_0
      | k7_relat_1('#skF_2',k1_tarski(B_38)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_165])).

tff(c_206,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_175])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_206])).

tff(c_213,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_216,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_42])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    ! [A_49,B_50] : k2_xboole_0(k1_tarski(A_49),B_50) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,(
    ! [A_49] : k1_tarski(A_49) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_20,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_tarski(A_30),B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_320,plain,(
    ! [B_117,A_118] :
      ( k9_relat_1(B_117,A_118) != k1_xboole_0
      | ~ r1_tarski(A_118,k1_relat_1(B_117))
      | k1_xboole_0 = A_118
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_324,plain,(
    ! [B_117,A_30] :
      ( k9_relat_1(B_117,k1_tarski(A_30)) != k1_xboole_0
      | k1_tarski(A_30) = k1_xboole_0
      | ~ v1_relat_1(B_117)
      | ~ r2_hidden(A_30,k1_relat_1(B_117)) ) ),
    inference(resolution,[status(thm)],[c_20,c_320])).

tff(c_328,plain,(
    ! [B_119,A_120] :
      ( k9_relat_1(B_119,k1_tarski(A_120)) != k1_xboole_0
      | ~ v1_relat_1(B_119)
      | ~ r2_hidden(A_120,k1_relat_1(B_119)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_324])).

tff(c_334,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_213,c_328])).

tff(c_338,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_334])).

tff(c_344,plain,
    ( k11_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_338])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_216,c_344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:56:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.30  
% 2.18/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.18/1.30  
% 2.18/1.30  %Foreground sorts:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Background operators:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Foreground operators:
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.18/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.30  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.18/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.18/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.18/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.30  
% 2.18/1.32  tff(f_95, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.18/1.32  tff(f_50, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.18/1.32  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.18/1.32  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.18/1.32  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.18/1.32  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.18/1.32  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.18/1.32  tff(f_53, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.18/1.32  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.18/1.32  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 2.18/1.32  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.18/1.32  tff(c_48, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2')) | k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.18/1.32  tff(c_89, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.18/1.32  tff(c_22, plain, (![A_32, B_33]: (r1_xboole_0(k1_tarski(A_32), B_33) | r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.32  tff(c_129, plain, (![A_74, B_75]: (k7_relat_1(A_74, B_75)=k1_xboole_0 | ~r1_xboole_0(B_75, k1_relat_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.18/1.32  tff(c_196, plain, (![A_88, A_89]: (k7_relat_1(A_88, k1_tarski(A_89))=k1_xboole_0 | ~v1_relat_1(A_88) | r2_hidden(A_89, k1_relat_1(A_88)))), inference(resolution, [status(thm)], [c_22, c_129])).
% 2.18/1.32  tff(c_42, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.18/1.32  tff(c_90, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_89, c_42])).
% 2.18/1.32  tff(c_199, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_196, c_90])).
% 2.18/1.32  tff(c_202, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_199])).
% 2.18/1.32  tff(c_111, plain, (![B_70, A_71]: (r1_xboole_0(k1_relat_1(B_70), A_71) | k7_relat_1(B_70, A_71)!=k1_xboole_0 | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.18/1.32  tff(c_28, plain, (![B_40, A_39]: (k9_relat_1(B_40, A_39)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_40), A_39) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.32  tff(c_154, plain, (![B_80, A_81]: (k9_relat_1(B_80, A_81)=k1_xboole_0 | k7_relat_1(B_80, A_81)!=k1_xboole_0 | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_111, c_28])).
% 2.18/1.32  tff(c_158, plain, (![A_82]: (k9_relat_1('#skF_2', A_82)=k1_xboole_0 | k7_relat_1('#skF_2', A_82)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_154])).
% 2.18/1.32  tff(c_26, plain, (![A_36, B_38]: (k9_relat_1(A_36, k1_tarski(B_38))=k11_relat_1(A_36, B_38) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.32  tff(c_165, plain, (![B_38]: (k11_relat_1('#skF_2', B_38)=k1_xboole_0 | ~v1_relat_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski(B_38))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_158, c_26])).
% 2.18/1.32  tff(c_175, plain, (![B_38]: (k11_relat_1('#skF_2', B_38)=k1_xboole_0 | k7_relat_1('#skF_2', k1_tarski(B_38))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_165])).
% 2.18/1.32  tff(c_206, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_202, c_175])).
% 2.18/1.32  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_206])).
% 2.18/1.32  tff(c_213, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 2.18/1.32  tff(c_216, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_213, c_42])).
% 2.18/1.32  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.32  tff(c_58, plain, (![A_49, B_50]: (k2_xboole_0(k1_tarski(A_49), B_50)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.18/1.32  tff(c_62, plain, (![A_49]: (k1_tarski(A_49)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_58])).
% 2.18/1.32  tff(c_20, plain, (![A_30, B_31]: (r1_tarski(k1_tarski(A_30), B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.32  tff(c_320, plain, (![B_117, A_118]: (k9_relat_1(B_117, A_118)!=k1_xboole_0 | ~r1_tarski(A_118, k1_relat_1(B_117)) | k1_xboole_0=A_118 | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.32  tff(c_324, plain, (![B_117, A_30]: (k9_relat_1(B_117, k1_tarski(A_30))!=k1_xboole_0 | k1_tarski(A_30)=k1_xboole_0 | ~v1_relat_1(B_117) | ~r2_hidden(A_30, k1_relat_1(B_117)))), inference(resolution, [status(thm)], [c_20, c_320])).
% 2.18/1.32  tff(c_328, plain, (![B_119, A_120]: (k9_relat_1(B_119, k1_tarski(A_120))!=k1_xboole_0 | ~v1_relat_1(B_119) | ~r2_hidden(A_120, k1_relat_1(B_119)))), inference(negUnitSimplification, [status(thm)], [c_62, c_324])).
% 2.18/1.32  tff(c_334, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_213, c_328])).
% 2.18/1.32  tff(c_338, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_334])).
% 2.18/1.32  tff(c_344, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_338])).
% 2.18/1.32  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_216, c_344])).
% 2.18/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.32  
% 2.18/1.32  Inference rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Ref     : 0
% 2.18/1.32  #Sup     : 60
% 2.18/1.32  #Fact    : 0
% 2.18/1.32  #Define  : 0
% 2.18/1.32  #Split   : 1
% 2.18/1.32  #Chain   : 0
% 2.18/1.32  #Close   : 0
% 2.18/1.32  
% 2.18/1.32  Ordering : KBO
% 2.18/1.32  
% 2.18/1.32  Simplification rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Subsume      : 3
% 2.18/1.32  #Demod        : 12
% 2.18/1.32  #Tautology    : 35
% 2.18/1.32  #SimpNegUnit  : 4
% 2.18/1.32  #BackRed      : 0
% 2.18/1.32  
% 2.18/1.32  #Partial instantiations: 0
% 2.18/1.32  #Strategies tried      : 1
% 2.18/1.32  
% 2.18/1.32  Timing (in seconds)
% 2.18/1.32  ----------------------
% 2.48/1.32  Preprocessing        : 0.34
% 2.48/1.32  Parsing              : 0.18
% 2.48/1.32  CNF conversion       : 0.02
% 2.48/1.32  Main loop            : 0.22
% 2.48/1.32  Inferencing          : 0.09
% 2.48/1.32  Reduction            : 0.06
% 2.48/1.32  Demodulation         : 0.03
% 2.48/1.32  BG Simplification    : 0.02
% 2.48/1.32  Subsumption          : 0.03
% 2.48/1.32  Abstraction          : 0.01
% 2.48/1.32  MUC search           : 0.00
% 2.48/1.32  Cooper               : 0.00
% 2.48/1.32  Total                : 0.59
% 2.48/1.32  Index Insertion      : 0.00
% 2.48/1.32  Index Deletion       : 0.00
% 2.48/1.32  Index Matching       : 0.00
% 2.48/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
