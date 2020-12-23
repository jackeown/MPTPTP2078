%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:33 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   72 (  91 expanded)
%              Number of leaves         :   33 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   92 ( 129 expanded)
%              Number of equality atoms :   39 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_168,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_172,plain,(
    ! [A_50,B_51] :
      ( r1_xboole_0(k1_tarski(A_50),B_51)
      | r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_175,plain,(
    ! [B_51,A_50] :
      ( r1_xboole_0(B_51,k1_tarski(A_50))
      | r2_hidden(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_172,c_8])).

tff(c_607,plain,(
    ! [B_99,A_100] :
      ( k10_relat_1(B_99,A_100) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_99),A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_863,plain,(
    ! [B_123,A_124] :
      ( k10_relat_1(B_123,k1_tarski(A_124)) = k1_xboole_0
      | ~ v1_relat_1(B_123)
      | r2_hidden(A_124,k2_relat_1(B_123)) ) ),
    inference(resolution,[status(thm)],[c_175,c_607])).

tff(c_46,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_216,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_46])).

tff(c_866,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_863,c_216])).

tff(c_869,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_866])).

tff(c_871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_869])).

tff(c_873,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_872,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_20,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1016,plain,(
    ! [A_147,B_148,C_149] :
      ( ~ r1_xboole_0(A_147,B_148)
      | ~ r2_hidden(C_149,k3_xboole_0(A_147,B_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1028,plain,(
    ! [A_14,C_149] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | ~ r2_hidden(C_149,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1016])).

tff(c_1032,plain,(
    ! [C_149] : ~ r2_hidden(C_149,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1028])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_984,plain,(
    ! [A_141,B_142] :
      ( r2_hidden(A_141,B_142)
      | k4_xboole_0(k1_tarski(A_141),B_142) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_988,plain,(
    ! [A_141] :
      ( r2_hidden(A_141,k1_xboole_0)
      | k1_tarski(A_141) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_984])).

tff(c_1042,plain,(
    ! [A_141] : k1_tarski(A_141) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1032,c_988])).

tff(c_38,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(k1_tarski(A_36),B_37) = k1_xboole_0
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_927,plain,(
    ! [A_135,B_136] : k5_xboole_0(A_135,k3_xboole_0(A_135,B_136)) = k4_xboole_0(A_135,B_136) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_945,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k4_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_927])).

tff(c_948,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_945])).

tff(c_1165,plain,(
    ! [B_164,A_165] :
      ( r1_xboole_0(k2_relat_1(B_164),A_165)
      | k10_relat_1(B_164,A_165) != k1_xboole_0
      | ~ v1_relat_1(B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1503,plain,(
    ! [B_198,A_199] :
      ( k3_xboole_0(k2_relat_1(B_198),A_199) = k1_xboole_0
      | k10_relat_1(B_198,A_199) != k1_xboole_0
      | ~ v1_relat_1(B_198) ) ),
    inference(resolution,[status(thm)],[c_1165,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_939,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_927])).

tff(c_1527,plain,(
    ! [A_199,B_198] :
      ( k4_xboole_0(A_199,k2_relat_1(B_198)) = k5_xboole_0(A_199,k1_xboole_0)
      | k10_relat_1(B_198,A_199) != k1_xboole_0
      | ~ v1_relat_1(B_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1503,c_939])).

tff(c_1695,plain,(
    ! [A_206,B_207] :
      ( k4_xboole_0(A_206,k2_relat_1(B_207)) = A_206
      | k10_relat_1(B_207,A_206) != k1_xboole_0
      | ~ v1_relat_1(B_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_1527])).

tff(c_1725,plain,(
    ! [A_36,B_207] :
      ( k1_tarski(A_36) = k1_xboole_0
      | k10_relat_1(B_207,k1_tarski(A_36)) != k1_xboole_0
      | ~ v1_relat_1(B_207)
      | ~ r2_hidden(A_36,k2_relat_1(B_207)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1695])).

tff(c_1738,plain,(
    ! [B_208,A_209] :
      ( k10_relat_1(B_208,k1_tarski(A_209)) != k1_xboole_0
      | ~ v1_relat_1(B_208)
      | ~ r2_hidden(A_209,k2_relat_1(B_208)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1042,c_1725])).

tff(c_1744,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_872,c_1738])).

tff(c_1749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_873,c_1744])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:27:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.48  
% 3.18/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.49  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.18/1.49  
% 3.18/1.49  %Foreground sorts:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Background operators:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Foreground operators:
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.18/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.18/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.18/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.18/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.18/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.18/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.18/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.18/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.18/1.49  
% 3.18/1.50  tff(f_94, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 3.18/1.50  tff(f_72, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.18/1.50  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.18/1.50  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 3.18/1.50  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.18/1.50  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.18/1.50  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.18/1.50  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.18/1.50  tff(f_80, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 3.18/1.50  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.18/1.50  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.18/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.18/1.50  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.18/1.50  tff(c_52, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.18/1.50  tff(c_168, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 3.18/1.50  tff(c_172, plain, (![A_50, B_51]: (r1_xboole_0(k1_tarski(A_50), B_51) | r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.18/1.50  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.18/1.50  tff(c_175, plain, (![B_51, A_50]: (r1_xboole_0(B_51, k1_tarski(A_50)) | r2_hidden(A_50, B_51))), inference(resolution, [status(thm)], [c_172, c_8])).
% 3.18/1.50  tff(c_607, plain, (![B_99, A_100]: (k10_relat_1(B_99, A_100)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_99), A_100) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.18/1.50  tff(c_863, plain, (![B_123, A_124]: (k10_relat_1(B_123, k1_tarski(A_124))=k1_xboole_0 | ~v1_relat_1(B_123) | r2_hidden(A_124, k2_relat_1(B_123)))), inference(resolution, [status(thm)], [c_175, c_607])).
% 3.18/1.50  tff(c_46, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.18/1.50  tff(c_216, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_168, c_46])).
% 3.18/1.50  tff(c_866, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_863, c_216])).
% 3.18/1.50  tff(c_869, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_866])).
% 3.18/1.50  tff(c_871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_869])).
% 3.18/1.50  tff(c_873, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.18/1.50  tff(c_872, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_52])).
% 3.18/1.50  tff(c_20, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.18/1.50  tff(c_16, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.18/1.50  tff(c_1016, plain, (![A_147, B_148, C_149]: (~r1_xboole_0(A_147, B_148) | ~r2_hidden(C_149, k3_xboole_0(A_147, B_148)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.50  tff(c_1028, plain, (![A_14, C_149]: (~r1_xboole_0(A_14, k1_xboole_0) | ~r2_hidden(C_149, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1016])).
% 3.18/1.50  tff(c_1032, plain, (![C_149]: (~r2_hidden(C_149, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1028])).
% 3.18/1.50  tff(c_18, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.18/1.50  tff(c_984, plain, (![A_141, B_142]: (r2_hidden(A_141, B_142) | k4_xboole_0(k1_tarski(A_141), B_142)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.18/1.50  tff(c_988, plain, (![A_141]: (r2_hidden(A_141, k1_xboole_0) | k1_tarski(A_141)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_984])).
% 3.18/1.50  tff(c_1042, plain, (![A_141]: (k1_tarski(A_141)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1032, c_988])).
% 3.18/1.50  tff(c_38, plain, (![A_36, B_37]: (k4_xboole_0(k1_tarski(A_36), B_37)=k1_xboole_0 | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.18/1.50  tff(c_927, plain, (![A_135, B_136]: (k5_xboole_0(A_135, k3_xboole_0(A_135, B_136))=k4_xboole_0(A_135, B_136))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.50  tff(c_945, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k4_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_927])).
% 3.18/1.50  tff(c_948, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_945])).
% 3.18/1.50  tff(c_1165, plain, (![B_164, A_165]: (r1_xboole_0(k2_relat_1(B_164), A_165) | k10_relat_1(B_164, A_165)!=k1_xboole_0 | ~v1_relat_1(B_164))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.18/1.50  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.50  tff(c_1503, plain, (![B_198, A_199]: (k3_xboole_0(k2_relat_1(B_198), A_199)=k1_xboole_0 | k10_relat_1(B_198, A_199)!=k1_xboole_0 | ~v1_relat_1(B_198))), inference(resolution, [status(thm)], [c_1165, c_4])).
% 3.18/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.18/1.50  tff(c_939, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_927])).
% 3.18/1.50  tff(c_1527, plain, (![A_199, B_198]: (k4_xboole_0(A_199, k2_relat_1(B_198))=k5_xboole_0(A_199, k1_xboole_0) | k10_relat_1(B_198, A_199)!=k1_xboole_0 | ~v1_relat_1(B_198))), inference(superposition, [status(thm), theory('equality')], [c_1503, c_939])).
% 3.18/1.50  tff(c_1695, plain, (![A_206, B_207]: (k4_xboole_0(A_206, k2_relat_1(B_207))=A_206 | k10_relat_1(B_207, A_206)!=k1_xboole_0 | ~v1_relat_1(B_207))), inference(demodulation, [status(thm), theory('equality')], [c_948, c_1527])).
% 3.18/1.50  tff(c_1725, plain, (![A_36, B_207]: (k1_tarski(A_36)=k1_xboole_0 | k10_relat_1(B_207, k1_tarski(A_36))!=k1_xboole_0 | ~v1_relat_1(B_207) | ~r2_hidden(A_36, k2_relat_1(B_207)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1695])).
% 3.18/1.50  tff(c_1738, plain, (![B_208, A_209]: (k10_relat_1(B_208, k1_tarski(A_209))!=k1_xboole_0 | ~v1_relat_1(B_208) | ~r2_hidden(A_209, k2_relat_1(B_208)))), inference(negUnitSimplification, [status(thm)], [c_1042, c_1725])).
% 3.18/1.50  tff(c_1744, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_872, c_1738])).
% 3.18/1.50  tff(c_1749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_873, c_1744])).
% 3.18/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.50  
% 3.18/1.50  Inference rules
% 3.18/1.50  ----------------------
% 3.18/1.50  #Ref     : 0
% 3.18/1.50  #Sup     : 394
% 3.18/1.50  #Fact    : 0
% 3.18/1.50  #Define  : 0
% 3.18/1.50  #Split   : 1
% 3.18/1.50  #Chain   : 0
% 3.18/1.50  #Close   : 0
% 3.18/1.50  
% 3.18/1.50  Ordering : KBO
% 3.18/1.50  
% 3.18/1.50  Simplification rules
% 3.18/1.50  ----------------------
% 3.18/1.50  #Subsume      : 129
% 3.18/1.50  #Demod        : 72
% 3.18/1.50  #Tautology    : 197
% 3.18/1.50  #SimpNegUnit  : 56
% 3.18/1.50  #BackRed      : 1
% 3.18/1.50  
% 3.18/1.50  #Partial instantiations: 0
% 3.18/1.50  #Strategies tried      : 1
% 3.18/1.50  
% 3.18/1.50  Timing (in seconds)
% 3.18/1.50  ----------------------
% 3.18/1.50  Preprocessing        : 0.31
% 3.18/1.50  Parsing              : 0.17
% 3.18/1.50  CNF conversion       : 0.02
% 3.18/1.50  Main loop            : 0.42
% 3.18/1.50  Inferencing          : 0.16
% 3.18/1.50  Reduction            : 0.13
% 3.18/1.50  Demodulation         : 0.09
% 3.18/1.50  BG Simplification    : 0.02
% 3.18/1.50  Subsumption          : 0.07
% 3.18/1.50  Abstraction          : 0.02
% 3.18/1.50  MUC search           : 0.00
% 3.18/1.50  Cooper               : 0.00
% 3.18/1.50  Total                : 0.76
% 3.18/1.50  Index Insertion      : 0.00
% 3.18/1.50  Index Deletion       : 0.00
% 3.18/1.50  Index Matching       : 0.00
% 3.18/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
