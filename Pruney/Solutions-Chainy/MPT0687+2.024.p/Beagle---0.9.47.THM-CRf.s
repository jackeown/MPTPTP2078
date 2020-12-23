%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:36 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   66 (  79 expanded)
%              Number of leaves         :   35 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 101 expanded)
%              Number of equality atoms :   34 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_123,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_191,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_54])).

tff(c_125,plain,(
    ! [A_63,B_64] :
      ( r1_xboole_0(k1_tarski(A_63),B_64)
      | r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [B_64,A_63] :
      ( r1_xboole_0(B_64,k1_tarski(A_63))
      | r2_hidden(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_125,c_4])).

tff(c_299,plain,(
    ! [B_88,A_89] :
      ( k10_relat_1(B_88,A_89) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_88),A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_352,plain,(
    ! [B_98,A_99] :
      ( k10_relat_1(B_98,k1_tarski(A_99)) = k1_xboole_0
      | ~ v1_relat_1(B_98)
      | r2_hidden(A_99,k2_relat_1(B_98)) ) ),
    inference(resolution,[status(thm)],[c_128,c_299])).

tff(c_355,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_352,c_123])).

tff(c_358,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_355])).

tff(c_360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_358])).

tff(c_361,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_362,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_392,plain,(
    ! [A_110,B_111] : k5_xboole_0(A_110,k3_xboole_0(A_110,B_111)) = k4_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_404,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_392])).

tff(c_407,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_404])).

tff(c_436,plain,(
    ! [A_114,B_115] : k4_xboole_0(A_114,k4_xboole_0(A_114,B_115)) = k3_xboole_0(A_114,B_115) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_451,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_436])).

tff(c_454,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_451])).

tff(c_34,plain,(
    ! [B_44] : k4_xboole_0(k1_tarski(B_44),k1_tarski(B_44)) != k1_tarski(B_44) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_465,plain,(
    ! [B_44] : k1_tarski(B_44) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_34])).

tff(c_30,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_tarski(A_39),B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_616,plain,(
    ! [B_140,A_141] :
      ( k10_relat_1(B_140,A_141) != k1_xboole_0
      | ~ r1_tarski(A_141,k2_relat_1(B_140))
      | k1_xboole_0 = A_141
      | ~ v1_relat_1(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_620,plain,(
    ! [B_140,A_39] :
      ( k10_relat_1(B_140,k1_tarski(A_39)) != k1_xboole_0
      | k1_tarski(A_39) = k1_xboole_0
      | ~ v1_relat_1(B_140)
      | ~ r2_hidden(A_39,k2_relat_1(B_140)) ) ),
    inference(resolution,[status(thm)],[c_30,c_616])).

tff(c_633,plain,(
    ! [B_147,A_148] :
      ( k10_relat_1(B_147,k1_tarski(A_148)) != k1_xboole_0
      | ~ v1_relat_1(B_147)
      | ~ r2_hidden(A_148,k2_relat_1(B_147)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_465,c_620])).

tff(c_639,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_362,c_633])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_361,c_639])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:55:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.66/1.37  
% 2.66/1.37  %Foreground sorts:
% 2.66/1.37  
% 2.66/1.37  
% 2.66/1.37  %Background operators:
% 2.66/1.37  
% 2.66/1.37  
% 2.66/1.37  %Foreground operators:
% 2.66/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.66/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.66/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.66/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.66/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.66/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.66/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.66/1.37  
% 2.66/1.38  tff(f_93, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 2.66/1.38  tff(f_62, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.66/1.38  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.66/1.38  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 2.66/1.38  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.66/1.38  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.66/1.38  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.66/1.38  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.66/1.38  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.66/1.38  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.66/1.38  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 2.66/1.38  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.66/1.38  tff(c_48, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.66/1.38  tff(c_123, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.66/1.38  tff(c_54, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.66/1.38  tff(c_191, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_123, c_54])).
% 2.66/1.38  tff(c_125, plain, (![A_63, B_64]: (r1_xboole_0(k1_tarski(A_63), B_64) | r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.38  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.38  tff(c_128, plain, (![B_64, A_63]: (r1_xboole_0(B_64, k1_tarski(A_63)) | r2_hidden(A_63, B_64))), inference(resolution, [status(thm)], [c_125, c_4])).
% 2.66/1.38  tff(c_299, plain, (![B_88, A_89]: (k10_relat_1(B_88, A_89)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_88), A_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.66/1.38  tff(c_352, plain, (![B_98, A_99]: (k10_relat_1(B_98, k1_tarski(A_99))=k1_xboole_0 | ~v1_relat_1(B_98) | r2_hidden(A_99, k2_relat_1(B_98)))), inference(resolution, [status(thm)], [c_128, c_299])).
% 2.66/1.38  tff(c_355, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_352, c_123])).
% 2.66/1.38  tff(c_358, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_355])).
% 2.66/1.38  tff(c_360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_358])).
% 2.66/1.38  tff(c_361, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.66/1.38  tff(c_362, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 2.66/1.38  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.38  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.66/1.38  tff(c_392, plain, (![A_110, B_111]: (k5_xboole_0(A_110, k3_xboole_0(A_110, B_111))=k4_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.66/1.38  tff(c_404, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_392])).
% 2.66/1.38  tff(c_407, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_404])).
% 2.66/1.38  tff(c_436, plain, (![A_114, B_115]: (k4_xboole_0(A_114, k4_xboole_0(A_114, B_115))=k3_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.66/1.38  tff(c_451, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_407, c_436])).
% 2.66/1.38  tff(c_454, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_451])).
% 2.66/1.38  tff(c_34, plain, (![B_44]: (k4_xboole_0(k1_tarski(B_44), k1_tarski(B_44))!=k1_tarski(B_44))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.66/1.38  tff(c_465, plain, (![B_44]: (k1_tarski(B_44)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_454, c_34])).
% 2.66/1.38  tff(c_30, plain, (![A_39, B_40]: (r1_tarski(k1_tarski(A_39), B_40) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.66/1.38  tff(c_616, plain, (![B_140, A_141]: (k10_relat_1(B_140, A_141)!=k1_xboole_0 | ~r1_tarski(A_141, k2_relat_1(B_140)) | k1_xboole_0=A_141 | ~v1_relat_1(B_140))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.66/1.38  tff(c_620, plain, (![B_140, A_39]: (k10_relat_1(B_140, k1_tarski(A_39))!=k1_xboole_0 | k1_tarski(A_39)=k1_xboole_0 | ~v1_relat_1(B_140) | ~r2_hidden(A_39, k2_relat_1(B_140)))), inference(resolution, [status(thm)], [c_30, c_616])).
% 2.66/1.38  tff(c_633, plain, (![B_147, A_148]: (k10_relat_1(B_147, k1_tarski(A_148))!=k1_xboole_0 | ~v1_relat_1(B_147) | ~r2_hidden(A_148, k2_relat_1(B_147)))), inference(negUnitSimplification, [status(thm)], [c_465, c_620])).
% 2.66/1.38  tff(c_639, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_362, c_633])).
% 2.66/1.38  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_361, c_639])).
% 2.66/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.38  
% 2.66/1.38  Inference rules
% 2.66/1.38  ----------------------
% 2.66/1.38  #Ref     : 0
% 2.66/1.38  #Sup     : 127
% 2.66/1.38  #Fact    : 0
% 2.66/1.38  #Define  : 0
% 2.66/1.38  #Split   : 1
% 2.66/1.38  #Chain   : 0
% 2.66/1.38  #Close   : 0
% 2.66/1.38  
% 2.66/1.38  Ordering : KBO
% 2.66/1.38  
% 2.66/1.38  Simplification rules
% 2.66/1.38  ----------------------
% 2.66/1.38  #Subsume      : 6
% 2.66/1.38  #Demod        : 40
% 2.66/1.38  #Tautology    : 98
% 2.66/1.38  #SimpNegUnit  : 11
% 2.66/1.38  #BackRed      : 3
% 2.66/1.38  
% 2.66/1.38  #Partial instantiations: 0
% 2.66/1.38  #Strategies tried      : 1
% 2.66/1.38  
% 2.66/1.38  Timing (in seconds)
% 2.66/1.38  ----------------------
% 2.66/1.39  Preprocessing        : 0.34
% 2.66/1.39  Parsing              : 0.18
% 2.66/1.39  CNF conversion       : 0.02
% 2.66/1.39  Main loop            : 0.27
% 2.66/1.39  Inferencing          : 0.11
% 2.66/1.39  Reduction            : 0.08
% 2.66/1.39  Demodulation         : 0.06
% 2.66/1.39  BG Simplification    : 0.02
% 2.66/1.39  Subsumption          : 0.04
% 2.66/1.39  Abstraction          : 0.02
% 2.66/1.39  MUC search           : 0.00
% 2.66/1.39  Cooper               : 0.00
% 2.66/1.39  Total                : 0.65
% 2.66/1.39  Index Insertion      : 0.00
% 2.66/1.39  Index Deletion       : 0.00
% 2.66/1.39  Index Matching       : 0.00
% 2.66/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
