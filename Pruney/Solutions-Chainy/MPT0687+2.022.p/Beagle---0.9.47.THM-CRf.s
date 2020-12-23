%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:36 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   64 (  81 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 113 expanded)
%              Number of equality atoms :   34 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_99,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_182,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_46])).

tff(c_73,plain,(
    ! [A_48,B_49] :
      ( r1_xboole_0(k1_tarski(A_48),B_49)
      | r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [B_49,A_48] :
      ( r1_xboole_0(B_49,k1_tarski(A_48))
      | r2_hidden(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_73,c_6])).

tff(c_331,plain,(
    ! [B_85,A_86] :
      ( k10_relat_1(B_85,A_86) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_85),A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_493,plain,(
    ! [B_105,A_106] :
      ( k10_relat_1(B_105,k1_tarski(A_106)) = k1_xboole_0
      | ~ v1_relat_1(B_105)
      | r2_hidden(A_106,k2_relat_1(B_105)) ) ),
    inference(resolution,[status(thm)],[c_76,c_331])).

tff(c_496,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_493,c_99])).

tff(c_499,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_496])).

tff(c_501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_499])).

tff(c_502,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_504,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_504])).

tff(c_512,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_503,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_549,plain,(
    ! [A_115,B_116] : k5_xboole_0(A_115,k3_xboole_0(A_115,B_116)) = k4_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_558,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_549])).

tff(c_561,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_558])).

tff(c_666,plain,(
    ! [B_128,A_129] :
      ( r1_xboole_0(k2_relat_1(B_128),A_129)
      | k10_relat_1(B_128,A_129) != k1_xboole_0
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_791,plain,(
    ! [B_144,A_145] :
      ( k3_xboole_0(k2_relat_1(B_144),A_145) = k1_xboole_0
      | k10_relat_1(B_144,A_145) != k1_xboole_0
      | ~ v1_relat_1(B_144) ) ),
    inference(resolution,[status(thm)],[c_666,c_2])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_803,plain,(
    ! [B_144,A_145] :
      ( k5_xboole_0(k2_relat_1(B_144),k1_xboole_0) = k4_xboole_0(k2_relat_1(B_144),A_145)
      | k10_relat_1(B_144,A_145) != k1_xboole_0
      | ~ v1_relat_1(B_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_8])).

tff(c_979,plain,(
    ! [B_175,A_176] :
      ( k4_xboole_0(k2_relat_1(B_175),A_176) = k2_relat_1(B_175)
      | k10_relat_1(B_175,A_176) != k1_xboole_0
      | ~ v1_relat_1(B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_803])).

tff(c_30,plain,(
    ! [B_40,A_39] :
      ( ~ r2_hidden(B_40,A_39)
      | k4_xboole_0(A_39,k1_tarski(B_40)) != A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1023,plain,(
    ! [B_177,B_178] :
      ( ~ r2_hidden(B_177,k2_relat_1(B_178))
      | k10_relat_1(B_178,k1_tarski(B_177)) != k1_xboole_0
      | ~ v1_relat_1(B_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_30])).

tff(c_1029,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_503,c_1023])).

tff(c_1034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_512,c_1029])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:26:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.63  
% 3.00/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.63  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.00/1.63  
% 3.00/1.63  %Foreground sorts:
% 3.00/1.63  
% 3.00/1.63  
% 3.00/1.63  %Background operators:
% 3.00/1.63  
% 3.00/1.63  
% 3.00/1.63  %Foreground operators:
% 3.00/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.00/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.00/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.00/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.00/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.00/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.00/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.00/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.00/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.00/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.00/1.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.63  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.63  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.00/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.00/1.63  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.00/1.63  
% 3.00/1.64  tff(f_77, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 3.00/1.64  tff(f_58, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.00/1.64  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.00/1.64  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 3.00/1.64  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.00/1.64  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.00/1.64  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.00/1.64  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.00/1.64  tff(f_63, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.00/1.64  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.00/1.64  tff(c_40, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.00/1.64  tff(c_99, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_40])).
% 3.00/1.64  tff(c_46, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.00/1.64  tff(c_182, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_99, c_46])).
% 3.00/1.64  tff(c_73, plain, (![A_48, B_49]: (r1_xboole_0(k1_tarski(A_48), B_49) | r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.00/1.64  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.00/1.64  tff(c_76, plain, (![B_49, A_48]: (r1_xboole_0(B_49, k1_tarski(A_48)) | r2_hidden(A_48, B_49))), inference(resolution, [status(thm)], [c_73, c_6])).
% 3.00/1.64  tff(c_331, plain, (![B_85, A_86]: (k10_relat_1(B_85, A_86)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_85), A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.00/1.64  tff(c_493, plain, (![B_105, A_106]: (k10_relat_1(B_105, k1_tarski(A_106))=k1_xboole_0 | ~v1_relat_1(B_105) | r2_hidden(A_106, k2_relat_1(B_105)))), inference(resolution, [status(thm)], [c_76, c_331])).
% 3.00/1.64  tff(c_496, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_493, c_99])).
% 3.00/1.64  tff(c_499, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_496])).
% 3.00/1.64  tff(c_501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_499])).
% 3.00/1.64  tff(c_502, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.00/1.64  tff(c_504, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 3.00/1.64  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_502, c_504])).
% 3.00/1.64  tff(c_512, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 3.00/1.64  tff(c_503, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_40])).
% 3.00/1.64  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.00/1.64  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.00/1.64  tff(c_549, plain, (![A_115, B_116]: (k5_xboole_0(A_115, k3_xboole_0(A_115, B_116))=k4_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.64  tff(c_558, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_549])).
% 3.00/1.64  tff(c_561, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_558])).
% 3.00/1.64  tff(c_666, plain, (![B_128, A_129]: (r1_xboole_0(k2_relat_1(B_128), A_129) | k10_relat_1(B_128, A_129)!=k1_xboole_0 | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.00/1.64  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.00/1.64  tff(c_791, plain, (![B_144, A_145]: (k3_xboole_0(k2_relat_1(B_144), A_145)=k1_xboole_0 | k10_relat_1(B_144, A_145)!=k1_xboole_0 | ~v1_relat_1(B_144))), inference(resolution, [status(thm)], [c_666, c_2])).
% 3.00/1.64  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.64  tff(c_803, plain, (![B_144, A_145]: (k5_xboole_0(k2_relat_1(B_144), k1_xboole_0)=k4_xboole_0(k2_relat_1(B_144), A_145) | k10_relat_1(B_144, A_145)!=k1_xboole_0 | ~v1_relat_1(B_144))), inference(superposition, [status(thm), theory('equality')], [c_791, c_8])).
% 3.00/1.64  tff(c_979, plain, (![B_175, A_176]: (k4_xboole_0(k2_relat_1(B_175), A_176)=k2_relat_1(B_175) | k10_relat_1(B_175, A_176)!=k1_xboole_0 | ~v1_relat_1(B_175))), inference(demodulation, [status(thm), theory('equality')], [c_561, c_803])).
% 3.00/1.64  tff(c_30, plain, (![B_40, A_39]: (~r2_hidden(B_40, A_39) | k4_xboole_0(A_39, k1_tarski(B_40))!=A_39)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.64  tff(c_1023, plain, (![B_177, B_178]: (~r2_hidden(B_177, k2_relat_1(B_178)) | k10_relat_1(B_178, k1_tarski(B_177))!=k1_xboole_0 | ~v1_relat_1(B_178))), inference(superposition, [status(thm), theory('equality')], [c_979, c_30])).
% 3.00/1.64  tff(c_1029, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_503, c_1023])).
% 3.00/1.64  tff(c_1034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_512, c_1029])).
% 3.00/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.64  
% 3.00/1.64  Inference rules
% 3.00/1.64  ----------------------
% 3.00/1.64  #Ref     : 0
% 3.00/1.64  #Sup     : 216
% 3.00/1.64  #Fact    : 0
% 3.00/1.64  #Define  : 0
% 3.00/1.64  #Split   : 2
% 3.00/1.64  #Chain   : 0
% 3.00/1.65  #Close   : 0
% 3.00/1.65  
% 3.00/1.65  Ordering : KBO
% 3.00/1.65  
% 3.00/1.65  Simplification rules
% 3.00/1.65  ----------------------
% 3.00/1.65  #Subsume      : 18
% 3.00/1.65  #Demod        : 20
% 3.00/1.65  #Tautology    : 153
% 3.00/1.65  #SimpNegUnit  : 10
% 3.00/1.65  #BackRed      : 0
% 3.00/1.65  
% 3.00/1.65  #Partial instantiations: 0
% 3.00/1.65  #Strategies tried      : 1
% 3.00/1.65  
% 3.00/1.65  Timing (in seconds)
% 3.00/1.65  ----------------------
% 3.00/1.65  Preprocessing        : 0.41
% 3.00/1.65  Parsing              : 0.22
% 3.00/1.65  CNF conversion       : 0.02
% 3.00/1.65  Main loop            : 0.35
% 3.00/1.65  Inferencing          : 0.15
% 3.00/1.65  Reduction            : 0.09
% 3.00/1.65  Demodulation         : 0.06
% 3.00/1.65  BG Simplification    : 0.02
% 3.00/1.65  Subsumption          : 0.06
% 3.00/1.65  Abstraction          : 0.02
% 3.00/1.65  MUC search           : 0.00
% 3.00/1.65  Cooper               : 0.00
% 3.00/1.65  Total                : 0.79
% 3.00/1.65  Index Insertion      : 0.00
% 3.00/1.65  Index Deletion       : 0.00
% 3.00/1.65  Index Matching       : 0.00
% 3.00/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
