%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:11 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   61 (  80 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 134 expanded)
%              Number of equality atoms :   28 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_139,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | k4_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_151,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_28])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_40])).

tff(c_75,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_152,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_164,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_152])).

tff(c_168,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_164])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_369,plain,(
    ! [B_56,A_57] :
      ( k9_relat_1(B_56,k10_relat_1(B_56,A_57)) = A_57
      | ~ r1_tarski(A_57,k2_relat_1(B_56))
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_380,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_369])).

tff(c_389,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_380])).

tff(c_464,plain,(
    ! [C_63,A_64,B_65] :
      ( k3_xboole_0(k10_relat_1(C_63,A_64),k10_relat_1(C_63,B_65)) = k10_relat_1(C_63,k3_xboole_0(A_64,B_65))
      | ~ v1_funct_1(C_63)
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_88,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_75])).

tff(c_476,plain,
    ( k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_88])).

tff(c_505,plain,(
    k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_476])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,k10_relat_1(B_19,A_18)),A_18)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_523,plain,
    ( r1_tarski(k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_24])).

tff(c_533,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_389,c_523])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_185,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_198,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,k3_xboole_0(A_7,B_8)) ) ),
    inference(resolution,[status(thm)],[c_14,c_185])).

tff(c_549,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_533,c_198])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_573,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_12])).

tff(c_587,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_573])).

tff(c_589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:58:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.33  
% 2.53/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.34  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.53/1.34  
% 2.53/1.34  %Foreground sorts:
% 2.53/1.34  
% 2.53/1.34  
% 2.53/1.34  %Background operators:
% 2.53/1.34  
% 2.53/1.34  
% 2.53/1.34  %Foreground operators:
% 2.53/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.53/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.53/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.53/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.53/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.53/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.53/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.53/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.53/1.34  
% 2.53/1.35  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.53/1.35  tff(f_78, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 2.53/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.53/1.35  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.53/1.35  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.53/1.35  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.53/1.35  tff(f_53, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_funct_1)).
% 2.53/1.35  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 2.53/1.35  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.53/1.35  tff(c_139, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | k4_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.35  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.35  tff(c_151, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_139, c_28])).
% 2.53/1.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.35  tff(c_40, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.35  tff(c_52, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_40])).
% 2.53/1.35  tff(c_75, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.53/1.35  tff(c_91, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_75])).
% 2.53/1.35  tff(c_152, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.35  tff(c_164, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_91, c_152])).
% 2.53/1.35  tff(c_168, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_164])).
% 2.53/1.35  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.35  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.35  tff(c_30, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.35  tff(c_369, plain, (![B_56, A_57]: (k9_relat_1(B_56, k10_relat_1(B_56, A_57))=A_57 | ~r1_tarski(A_57, k2_relat_1(B_56)) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.35  tff(c_380, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_369])).
% 2.53/1.35  tff(c_389, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_380])).
% 2.53/1.35  tff(c_464, plain, (![C_63, A_64, B_65]: (k3_xboole_0(k10_relat_1(C_63, A_64), k10_relat_1(C_63, B_65))=k10_relat_1(C_63, k3_xboole_0(A_64, B_65)) | ~v1_funct_1(C_63) | ~v1_relat_1(C_63))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.35  tff(c_32, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.35  tff(c_88, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_75])).
% 2.53/1.35  tff(c_476, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_464, c_88])).
% 2.53/1.35  tff(c_505, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_476])).
% 2.53/1.35  tff(c_24, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, k10_relat_1(B_19, A_18)), A_18) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.53/1.35  tff(c_523, plain, (r1_tarski(k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_505, c_24])).
% 2.53/1.35  tff(c_533, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_389, c_523])).
% 2.53/1.35  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.53/1.35  tff(c_185, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.35  tff(c_198, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, k3_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_14, c_185])).
% 2.53/1.35  tff(c_549, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_533, c_198])).
% 2.53/1.35  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.35  tff(c_573, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_549, c_12])).
% 2.53/1.35  tff(c_587, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_168, c_573])).
% 2.53/1.35  tff(c_589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_587])).
% 2.53/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.35  
% 2.53/1.35  Inference rules
% 2.53/1.35  ----------------------
% 2.53/1.35  #Ref     : 0
% 2.53/1.35  #Sup     : 135
% 2.53/1.35  #Fact    : 0
% 2.53/1.35  #Define  : 0
% 2.53/1.35  #Split   : 2
% 2.53/1.35  #Chain   : 0
% 2.53/1.35  #Close   : 0
% 2.53/1.35  
% 2.53/1.35  Ordering : KBO
% 2.53/1.35  
% 2.53/1.35  Simplification rules
% 2.53/1.35  ----------------------
% 2.53/1.35  #Subsume      : 4
% 2.53/1.35  #Demod        : 87
% 2.53/1.35  #Tautology    : 81
% 2.53/1.35  #SimpNegUnit  : 1
% 2.53/1.35  #BackRed      : 1
% 2.53/1.35  
% 2.53/1.35  #Partial instantiations: 0
% 2.53/1.35  #Strategies tried      : 1
% 2.53/1.35  
% 2.53/1.35  Timing (in seconds)
% 2.53/1.35  ----------------------
% 2.53/1.35  Preprocessing        : 0.31
% 2.53/1.35  Parsing              : 0.17
% 2.53/1.35  CNF conversion       : 0.02
% 2.53/1.35  Main loop            : 0.28
% 2.53/1.35  Inferencing          : 0.10
% 2.53/1.35  Reduction            : 0.09
% 2.53/1.36  Demodulation         : 0.07
% 2.53/1.36  BG Simplification    : 0.02
% 2.53/1.36  Subsumption          : 0.05
% 2.53/1.36  Abstraction          : 0.02
% 2.53/1.36  MUC search           : 0.00
% 2.53/1.36  Cooper               : 0.00
% 2.53/1.36  Total                : 0.62
% 2.53/1.36  Index Insertion      : 0.00
% 2.53/1.36  Index Deletion       : 0.00
% 2.53/1.36  Index Matching       : 0.00
% 2.53/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
