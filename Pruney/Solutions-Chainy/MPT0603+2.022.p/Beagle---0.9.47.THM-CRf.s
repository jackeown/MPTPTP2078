%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:26 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   58 (  76 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :   71 ( 116 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k7_relat_1(A_18,B_19))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    ! [A_37,B_38] :
      ( ~ r1_xboole_0(A_37,B_38)
      | k3_xboole_0(A_37,B_38) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_73,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_69])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    ! [C_5] :
      ( ~ r1_xboole_0('#skF_3','#skF_4')
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_4])).

tff(c_81,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_77])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_21,A_20)),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_99,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_90])).

tff(c_102,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_99])).

tff(c_107,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_xboole_0(A_42,C_43)
      | ~ r1_tarski(A_42,k4_xboole_0(B_44,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_126,plain,(
    ! [A_47] :
      ( r1_xboole_0(A_47,'#skF_4')
      | ~ r1_tarski(A_47,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_107])).

tff(c_68,plain,(
    ! [A_34,B_35] :
      ( ~ r1_xboole_0(A_34,B_35)
      | k3_xboole_0(A_34,B_35) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_131,plain,(
    ! [A_48] :
      ( k3_xboole_0(A_48,'#skF_4') = k1_xboole_0
      | ~ r1_tarski(A_48,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_126,c_68])).

tff(c_136,plain,(
    ! [B_21] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_21,'#skF_3')),'#skF_4') = k1_xboole_0
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_22,c_131])).

tff(c_208,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_1'(A_61,B_62),k3_xboole_0(A_61,B_62))
      | r1_xboole_0(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_217,plain,(
    ! [B_21] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(B_21,'#skF_3')),'#skF_4'),k1_xboole_0)
      | r1_xboole_0(k1_relat_1(k7_relat_1(B_21,'#skF_3')),'#skF_4')
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_208])).

tff(c_226,plain,(
    ! [B_63] :
      ( r1_xboole_0(k1_relat_1(k7_relat_1(B_63,'#skF_3')),'#skF_4')
      | ~ v1_relat_1(B_63) ) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_217])).

tff(c_24,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_23),A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_945,plain,(
    ! [B_117] :
      ( k7_relat_1(k7_relat_1(B_117,'#skF_3'),'#skF_4') = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(B_117,'#skF_3'))
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_226,c_24])).

tff(c_1029,plain,(
    ! [A_125] :
      ( k7_relat_1(k7_relat_1(A_125,'#skF_3'),'#skF_4') = k1_xboole_0
      | ~ v1_relat_1(A_125) ) ),
    inference(resolution,[status(thm)],[c_20,c_945])).

tff(c_28,plain,(
    k7_relat_1(k7_relat_1('#skF_5','#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1056,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_28])).

tff(c_1065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1056])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:03:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.44  
% 2.77/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.77/1.45  
% 2.77/1.45  %Foreground sorts:
% 2.77/1.45  
% 2.77/1.45  
% 2.77/1.45  %Background operators:
% 2.77/1.45  
% 2.77/1.45  
% 2.77/1.45  %Foreground operators:
% 2.77/1.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.77/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.77/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.77/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.77/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.77/1.45  
% 3.01/1.46  tff(f_82, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 3.01/1.46  tff(f_65, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.01/1.46  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.01/1.46  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.01/1.46  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.01/1.46  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.01/1.46  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.01/1.46  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.01/1.46  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.01/1.46  tff(c_32, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.01/1.46  tff(c_20, plain, (![A_18, B_19]: (v1_relat_1(k7_relat_1(A_18, B_19)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.01/1.46  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.01/1.46  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.01/1.46  tff(c_63, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.01/1.46  tff(c_69, plain, (![A_37, B_38]: (~r1_xboole_0(A_37, B_38) | k3_xboole_0(A_37, B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_63])).
% 3.01/1.46  tff(c_73, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_69])).
% 3.01/1.46  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.01/1.46  tff(c_77, plain, (![C_5]: (~r1_xboole_0('#skF_3', '#skF_4') | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_73, c_4])).
% 3.01/1.46  tff(c_81, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_77])).
% 3.01/1.46  tff(c_22, plain, (![B_21, A_20]: (r1_tarski(k1_relat_1(k7_relat_1(B_21, A_20)), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.01/1.46  tff(c_12, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.01/1.46  tff(c_90, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k3_xboole_0(A_40, B_41))=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.01/1.46  tff(c_99, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_73, c_90])).
% 3.01/1.46  tff(c_102, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_99])).
% 3.01/1.46  tff(c_107, plain, (![A_42, C_43, B_44]: (r1_xboole_0(A_42, C_43) | ~r1_tarski(A_42, k4_xboole_0(B_44, C_43)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.01/1.46  tff(c_126, plain, (![A_47]: (r1_xboole_0(A_47, '#skF_4') | ~r1_tarski(A_47, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_107])).
% 3.01/1.46  tff(c_68, plain, (![A_34, B_35]: (~r1_xboole_0(A_34, B_35) | k3_xboole_0(A_34, B_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_63])).
% 3.01/1.46  tff(c_131, plain, (![A_48]: (k3_xboole_0(A_48, '#skF_4')=k1_xboole_0 | ~r1_tarski(A_48, '#skF_3'))), inference(resolution, [status(thm)], [c_126, c_68])).
% 3.01/1.46  tff(c_136, plain, (![B_21]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_21, '#skF_3')), '#skF_4')=k1_xboole_0 | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_22, c_131])).
% 3.01/1.46  tff(c_208, plain, (![A_61, B_62]: (r2_hidden('#skF_1'(A_61, B_62), k3_xboole_0(A_61, B_62)) | r1_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.01/1.46  tff(c_217, plain, (![B_21]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(B_21, '#skF_3')), '#skF_4'), k1_xboole_0) | r1_xboole_0(k1_relat_1(k7_relat_1(B_21, '#skF_3')), '#skF_4') | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_136, c_208])).
% 3.01/1.46  tff(c_226, plain, (![B_63]: (r1_xboole_0(k1_relat_1(k7_relat_1(B_63, '#skF_3')), '#skF_4') | ~v1_relat_1(B_63))), inference(negUnitSimplification, [status(thm)], [c_81, c_217])).
% 3.01/1.46  tff(c_24, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_23), A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.01/1.46  tff(c_945, plain, (![B_117]: (k7_relat_1(k7_relat_1(B_117, '#skF_3'), '#skF_4')=k1_xboole_0 | ~v1_relat_1(k7_relat_1(B_117, '#skF_3')) | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_226, c_24])).
% 3.01/1.46  tff(c_1029, plain, (![A_125]: (k7_relat_1(k7_relat_1(A_125, '#skF_3'), '#skF_4')=k1_xboole_0 | ~v1_relat_1(A_125))), inference(resolution, [status(thm)], [c_20, c_945])).
% 3.01/1.46  tff(c_28, plain, (k7_relat_1(k7_relat_1('#skF_5', '#skF_3'), '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.01/1.46  tff(c_1056, plain, (~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1029, c_28])).
% 3.01/1.46  tff(c_1065, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1056])).
% 3.01/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.46  
% 3.01/1.46  Inference rules
% 3.01/1.46  ----------------------
% 3.01/1.46  #Ref     : 0
% 3.01/1.46  #Sup     : 257
% 3.01/1.46  #Fact    : 0
% 3.01/1.46  #Define  : 0
% 3.01/1.46  #Split   : 1
% 3.01/1.46  #Chain   : 0
% 3.01/1.46  #Close   : 0
% 3.01/1.46  
% 3.01/1.46  Ordering : KBO
% 3.01/1.46  
% 3.01/1.46  Simplification rules
% 3.01/1.46  ----------------------
% 3.01/1.46  #Subsume      : 105
% 3.01/1.46  #Demod        : 30
% 3.01/1.46  #Tautology    : 72
% 3.01/1.46  #SimpNegUnit  : 10
% 3.01/1.46  #BackRed      : 1
% 3.01/1.46  
% 3.01/1.46  #Partial instantiations: 0
% 3.01/1.46  #Strategies tried      : 1
% 3.01/1.46  
% 3.01/1.46  Timing (in seconds)
% 3.01/1.46  ----------------------
% 3.01/1.46  Preprocessing        : 0.30
% 3.01/1.46  Parsing              : 0.16
% 3.01/1.46  CNF conversion       : 0.02
% 3.01/1.46  Main loop            : 0.38
% 3.01/1.46  Inferencing          : 0.16
% 3.01/1.46  Reduction            : 0.11
% 3.01/1.46  Demodulation         : 0.07
% 3.01/1.46  BG Simplification    : 0.02
% 3.01/1.46  Subsumption          : 0.07
% 3.01/1.46  Abstraction          : 0.02
% 3.01/1.46  MUC search           : 0.00
% 3.01/1.46  Cooper               : 0.00
% 3.01/1.46  Total                : 0.72
% 3.01/1.46  Index Insertion      : 0.00
% 3.01/1.46  Index Deletion       : 0.00
% 3.01/1.46  Index Matching       : 0.00
% 3.01/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
