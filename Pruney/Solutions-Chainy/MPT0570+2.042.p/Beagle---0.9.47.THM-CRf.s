%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:47 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   63 (  86 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 119 expanded)
%              Number of equality atoms :   39 (  62 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_57,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(C,B)
     => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    k10_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_13] : k7_relat_1(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_107,plain,(
    ! [B_29,A_30] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_29,A_30)),A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_110,plain,(
    ! [A_13] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_13)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_107])).

tff(c_111,plain,(
    ! [A_13] :
      ( r1_tarski(k1_xboole_0,A_13)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_110])).

tff(c_112,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_4,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_113,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_113])).

tff(c_145,plain,(
    ! [A_35] : k4_xboole_0(A_35,A_35) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_131])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k4_xboole_0(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_153,plain,(
    ! [A_35] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_18])).

tff(c_166,plain,(
    ! [A_35] : ~ v1_relat_1(A_35) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_153])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_38])).

tff(c_173,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_387,plain,(
    ! [A_51,B_52,C_53] :
      ( k2_xboole_0(k4_xboole_0(A_51,B_52),k3_xboole_0(A_51,k4_xboole_0(B_52,C_53))) = k4_xboole_0(A_51,C_53)
      | ~ r1_tarski(C_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_421,plain,(
    ! [A_51,A_5] :
      ( k2_xboole_0(k4_xboole_0(A_51,A_5),k3_xboole_0(A_51,A_5)) = k4_xboole_0(A_51,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_387])).

tff(c_427,plain,(
    ! [A_51,A_5] : k2_xboole_0(k4_xboole_0(A_51,A_5),k3_xboole_0(A_51,A_5)) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_6,c_421])).

tff(c_262,plain,(
    ! [B_45,A_46] :
      ( r1_xboole_0(k2_relat_1(B_45),A_46)
      | k10_relat_1(B_45,A_46) != k1_xboole_0
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_814,plain,(
    ! [B_74,A_75] :
      ( k4_xboole_0(k2_relat_1(B_74),A_75) = k2_relat_1(B_74)
      | k10_relat_1(B_74,A_75) != k1_xboole_0
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_262,c_14])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k2_xboole_0(k4_xboole_0(A_1,B_2),k3_xboole_0(A_1,k4_xboole_0(B_2,C_3))) = k4_xboole_0(A_1,C_3)
      | ~ r1_tarski(C_3,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_839,plain,(
    ! [A_1,A_75,B_74] :
      ( k4_xboole_0(A_1,A_75) = k2_xboole_0(k4_xboole_0(A_1,k2_relat_1(B_74)),k3_xboole_0(A_1,k2_relat_1(B_74)))
      | ~ r1_tarski(A_75,k2_relat_1(B_74))
      | k10_relat_1(B_74,A_75) != k1_xboole_0
      | ~ v1_relat_1(B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_2])).

tff(c_3092,plain,(
    ! [A_119,A_120,B_121] :
      ( k4_xboole_0(A_119,A_120) = A_119
      | ~ r1_tarski(A_120,k2_relat_1(B_121))
      | k10_relat_1(B_121,A_120) != k1_xboole_0
      | ~ v1_relat_1(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_839])).

tff(c_3100,plain,(
    ! [A_119] :
      ( k4_xboole_0(A_119,'#skF_1') = A_119
      | k10_relat_1('#skF_2','#skF_1') != k1_xboole_0
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_3092])).

tff(c_3111,plain,(
    ! [A_122] : k4_xboole_0(A_122,'#skF_1') = A_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_3100])).

tff(c_176,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_176])).

tff(c_197,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_194])).

tff(c_3226,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3111,c_197])).

tff(c_3279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_3226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:50:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.54  
% 3.79/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.55  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.79/1.55  
% 3.79/1.55  %Foreground sorts:
% 3.79/1.55  
% 3.79/1.55  
% 3.79/1.55  %Background operators:
% 3.79/1.55  
% 3.79/1.55  
% 3.79/1.55  %Foreground operators:
% 3.79/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.79/1.55  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.79/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.79/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.79/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.79/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.79/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.79/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.79/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/1.55  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.79/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.79/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.79/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.79/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.79/1.55  
% 3.79/1.56  tff(f_81, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 3.79/1.56  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.79/1.56  tff(f_57, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 3.79/1.56  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.79/1.56  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.79/1.56  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.79/1.56  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.79/1.56  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 3.79/1.56  tff(f_29, axiom, (![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_xboole_1)).
% 3.79/1.56  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 3.79/1.56  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.79/1.56  tff(c_36, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.79/1.56  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.79/1.56  tff(c_32, plain, (k10_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.79/1.56  tff(c_34, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.79/1.56  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.79/1.56  tff(c_20, plain, (![A_13]: (k7_relat_1(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.79/1.56  tff(c_107, plain, (![B_29, A_30]: (r1_tarski(k1_relat_1(k7_relat_1(B_29, A_30)), A_30) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.79/1.56  tff(c_110, plain, (![A_13]: (r1_tarski(k1_relat_1(k1_xboole_0), A_13) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_107])).
% 3.79/1.56  tff(c_111, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13) | ~v1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_110])).
% 3.79/1.56  tff(c_112, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_111])).
% 3.79/1.56  tff(c_4, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/1.56  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.79/1.56  tff(c_113, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.79/1.56  tff(c_131, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_113])).
% 3.79/1.56  tff(c_145, plain, (![A_35]: (k4_xboole_0(A_35, A_35)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_131])).
% 3.79/1.56  tff(c_18, plain, (![A_11, B_12]: (v1_relat_1(k4_xboole_0(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.79/1.56  tff(c_153, plain, (![A_35]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_145, c_18])).
% 3.79/1.56  tff(c_166, plain, (![A_35]: (~v1_relat_1(A_35))), inference(negUnitSimplification, [status(thm)], [c_112, c_153])).
% 3.79/1.56  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_38])).
% 3.79/1.56  tff(c_173, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(splitRight, [status(thm)], [c_111])).
% 3.79/1.56  tff(c_387, plain, (![A_51, B_52, C_53]: (k2_xboole_0(k4_xboole_0(A_51, B_52), k3_xboole_0(A_51, k4_xboole_0(B_52, C_53)))=k4_xboole_0(A_51, C_53) | ~r1_tarski(C_53, B_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.79/1.56  tff(c_421, plain, (![A_51, A_5]: (k2_xboole_0(k4_xboole_0(A_51, A_5), k3_xboole_0(A_51, A_5))=k4_xboole_0(A_51, k1_xboole_0) | ~r1_tarski(k1_xboole_0, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_387])).
% 3.79/1.56  tff(c_427, plain, (![A_51, A_5]: (k2_xboole_0(k4_xboole_0(A_51, A_5), k3_xboole_0(A_51, A_5))=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_173, c_6, c_421])).
% 3.79/1.56  tff(c_262, plain, (![B_45, A_46]: (r1_xboole_0(k2_relat_1(B_45), A_46) | k10_relat_1(B_45, A_46)!=k1_xboole_0 | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.79/1.56  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.79/1.56  tff(c_814, plain, (![B_74, A_75]: (k4_xboole_0(k2_relat_1(B_74), A_75)=k2_relat_1(B_74) | k10_relat_1(B_74, A_75)!=k1_xboole_0 | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_262, c_14])).
% 3.79/1.56  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k3_xboole_0(A_1, k4_xboole_0(B_2, C_3)))=k4_xboole_0(A_1, C_3) | ~r1_tarski(C_3, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.79/1.56  tff(c_839, plain, (![A_1, A_75, B_74]: (k4_xboole_0(A_1, A_75)=k2_xboole_0(k4_xboole_0(A_1, k2_relat_1(B_74)), k3_xboole_0(A_1, k2_relat_1(B_74))) | ~r1_tarski(A_75, k2_relat_1(B_74)) | k10_relat_1(B_74, A_75)!=k1_xboole_0 | ~v1_relat_1(B_74))), inference(superposition, [status(thm), theory('equality')], [c_814, c_2])).
% 3.79/1.56  tff(c_3092, plain, (![A_119, A_120, B_121]: (k4_xboole_0(A_119, A_120)=A_119 | ~r1_tarski(A_120, k2_relat_1(B_121)) | k10_relat_1(B_121, A_120)!=k1_xboole_0 | ~v1_relat_1(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_427, c_839])).
% 3.79/1.56  tff(c_3100, plain, (![A_119]: (k4_xboole_0(A_119, '#skF_1')=A_119 | k10_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_3092])).
% 3.79/1.56  tff(c_3111, plain, (![A_122]: (k4_xboole_0(A_122, '#skF_1')=A_122)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_3100])).
% 3.79/1.56  tff(c_176, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.79/1.56  tff(c_194, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_176])).
% 3.79/1.56  tff(c_197, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_194])).
% 3.79/1.56  tff(c_3226, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3111, c_197])).
% 3.79/1.56  tff(c_3279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_3226])).
% 3.79/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.56  
% 3.79/1.56  Inference rules
% 3.79/1.56  ----------------------
% 3.79/1.56  #Ref     : 0
% 3.79/1.56  #Sup     : 758
% 3.79/1.56  #Fact    : 0
% 3.79/1.56  #Define  : 0
% 3.79/1.56  #Split   : 1
% 3.79/1.56  #Chain   : 0
% 3.79/1.56  #Close   : 0
% 3.79/1.56  
% 3.79/1.56  Ordering : KBO
% 3.79/1.56  
% 3.79/1.56  Simplification rules
% 3.79/1.56  ----------------------
% 3.79/1.56  #Subsume      : 158
% 3.79/1.56  #Demod        : 676
% 3.79/1.56  #Tautology    : 344
% 3.79/1.56  #SimpNegUnit  : 4
% 3.79/1.56  #BackRed      : 1
% 3.79/1.56  
% 3.79/1.56  #Partial instantiations: 0
% 3.79/1.56  #Strategies tried      : 1
% 3.79/1.56  
% 3.79/1.56  Timing (in seconds)
% 3.79/1.56  ----------------------
% 3.79/1.56  Preprocessing        : 0.27
% 3.79/1.56  Parsing              : 0.14
% 3.79/1.56  CNF conversion       : 0.02
% 3.79/1.56  Main loop            : 0.63
% 3.79/1.56  Inferencing          : 0.22
% 3.79/1.56  Reduction            : 0.22
% 3.79/1.56  Demodulation         : 0.17
% 3.79/1.56  BG Simplification    : 0.03
% 3.79/1.56  Subsumption          : 0.11
% 3.79/1.56  Abstraction          : 0.03
% 3.79/1.56  MUC search           : 0.00
% 3.79/1.56  Cooper               : 0.00
% 3.79/1.56  Total                : 0.93
% 3.79/1.56  Index Insertion      : 0.00
% 3.79/1.56  Index Deletion       : 0.00
% 3.79/1.56  Index Matching       : 0.00
% 3.79/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
