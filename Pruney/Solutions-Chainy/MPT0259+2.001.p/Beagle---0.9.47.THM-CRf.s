%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:08 EST 2020

% Result     : Theorem 9.19s
% Output     : CNFRefutation 9.19s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 243 expanded)
%              Number of leaves         :   27 (  93 expanded)
%              Depth                    :   17
%              Number of atoms          :   73 ( 275 expanded)
%              Number of equality atoms :   43 ( 178 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),B)
          & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_57,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
        & r1_xboole_0(A,B)
        & r1_xboole_0(C,B) )
     => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_36,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [A_38,B_39] : r1_tarski(k3_xboole_0(A_38,B_39),A_38) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_69])).

tff(c_108,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_119,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_108])).

tff(c_155,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_180,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_155])).

tff(c_190,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_180])).

tff(c_38,plain,(
    r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_266,plain,(
    ! [A_57] : k4_xboole_0(A_57,k1_xboole_0) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_180])).

tff(c_276,plain,(
    ! [A_57] : k4_xboole_0(A_57,A_57) = k3_xboole_0(A_57,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_14])).

tff(c_309,plain,(
    ! [A_57] : k3_xboole_0(A_57,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_276])).

tff(c_847,plain,(
    ! [A_90,B_91,C_92] : k2_xboole_0(k4_xboole_0(A_90,B_91),k4_xboole_0(A_90,C_92)) = k4_xboole_0(A_90,k3_xboole_0(B_91,C_92)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_865,plain,(
    ! [A_3,B_91] : k4_xboole_0(A_3,k3_xboole_0(B_91,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_3,B_91),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_847])).

tff(c_910,plain,(
    ! [A_93,B_94] : k2_xboole_0(k4_xboole_0(A_93,B_94),A_93) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_309,c_865])).

tff(c_928,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_xboole_0(A_11,B_12),A_11) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_910])).

tff(c_494,plain,(
    ! [C_70,A_71,B_72] :
      ( r1_xboole_0(k3_xboole_0(C_70,A_71),k3_xboole_0(C_70,B_72))
      | ~ r1_xboole_0(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_512,plain,(
    ! [A_3,A_71] :
      ( r1_xboole_0(k3_xboole_0(A_3,A_71),A_3)
      | ~ r1_xboole_0(A_71,A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_494])).

tff(c_934,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_910])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    ! [A_34,B_35] : r1_xboole_0(k4_xboole_0(A_34,B_35),B_35) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,(
    ! [A_13] : r1_xboole_0(k1_xboole_0,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_55])).

tff(c_942,plain,(
    ! [C_95,A_96,B_97] :
      ( C_95 = A_96
      | ~ r1_xboole_0(C_95,B_97)
      | ~ r1_xboole_0(A_96,B_97)
      | k2_xboole_0(C_95,B_97) != k2_xboole_0(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_972,plain,(
    ! [A_96,A_13] :
      ( k1_xboole_0 = A_96
      | ~ r1_xboole_0(A_96,A_13)
      | k2_xboole_0(k1_xboole_0,A_13) != k2_xboole_0(A_96,A_13) ) ),
    inference(resolution,[status(thm)],[c_58,c_942])).

tff(c_17950,plain,(
    ! [A_381,A_382] :
      ( k1_xboole_0 = A_381
      | ~ r1_xboole_0(A_381,A_382)
      | k2_xboole_0(A_381,A_382) != A_382 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_972])).

tff(c_18028,plain,(
    ! [A_3,A_71] :
      ( k3_xboole_0(A_3,A_71) = k1_xboole_0
      | k2_xboole_0(k3_xboole_0(A_3,A_71),A_3) != A_3
      | ~ r1_xboole_0(A_71,A_3) ) ),
    inference(resolution,[status(thm)],[c_512,c_17950])).

tff(c_18110,plain,(
    ! [A_383,A_384] :
      ( k3_xboole_0(A_383,A_384) = k1_xboole_0
      | ~ r1_xboole_0(A_384,A_383) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_18028])).

tff(c_18258,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_18110])).

tff(c_168,plain,(
    ! [B_51] : k3_xboole_0(k1_xboole_0,B_51) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_16])).

tff(c_862,plain,(
    ! [A_3,C_92] : k4_xboole_0(A_3,k3_xboole_0(k1_xboole_0,C_92)) = k2_xboole_0(A_3,k4_xboole_0(A_3,C_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_847])).

tff(c_1017,plain,(
    ! [A_100,C_101] : k2_xboole_0(A_100,k4_xboole_0(A_100,C_101)) = A_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_168,c_862])).

tff(c_1049,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_1017])).

tff(c_889,plain,(
    ! [A_3,B_91] : k4_xboole_0(A_3,k3_xboole_0(B_91,A_3)) = k2_xboole_0(k4_xboole_0(A_3,B_91),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_847])).

tff(c_2781,plain,(
    ! [A_3,B_91] : k4_xboole_0(A_3,k3_xboole_0(B_91,A_3)) = k4_xboole_0(A_3,B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_889])).

tff(c_18425,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18258,c_2781])).

tff(c_18551,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_18425])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden(A_30,B_31)
      | k4_xboole_0(k1_tarski(A_30),B_31) != k1_tarski(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20000,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18551,c_32])).

tff(c_20073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_20000])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.19/3.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.19/3.50  
% 9.19/3.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.19/3.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 9.19/3.51  
% 9.19/3.51  %Foreground sorts:
% 9.19/3.51  
% 9.19/3.51  
% 9.19/3.51  %Background operators:
% 9.19/3.51  
% 9.19/3.51  
% 9.19/3.51  %Foreground operators:
% 9.19/3.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.19/3.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.19/3.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.19/3.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.19/3.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.19/3.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.19/3.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.19/3.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.19/3.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.19/3.51  tff('#skF_2', type, '#skF_2': $i).
% 9.19/3.51  tff('#skF_1', type, '#skF_1': $i).
% 9.19/3.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.19/3.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.19/3.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.19/3.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.19/3.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.19/3.51  
% 9.19/3.52  tff(f_74, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_zfmisc_1)).
% 9.19/3.52  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 9.19/3.52  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.19/3.52  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.19/3.52  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.19/3.52  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_xboole_1)).
% 9.19/3.52  tff(f_55, axiom, (![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 9.19/3.52  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 9.19/3.52  tff(f_57, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.19/3.52  tff(f_51, axiom, (![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 9.19/3.52  tff(f_68, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 9.19/3.52  tff(c_36, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.19/3.52  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.19/3.52  tff(c_69, plain, (![A_38, B_39]: (r1_tarski(k3_xboole_0(A_38, B_39), A_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.19/3.52  tff(c_72, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_69])).
% 9.19/3.52  tff(c_108, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.19/3.52  tff(c_119, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_108])).
% 9.19/3.52  tff(c_155, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.19/3.52  tff(c_180, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_119, c_155])).
% 9.19/3.52  tff(c_190, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_180])).
% 9.19/3.52  tff(c_38, plain, (r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.19/3.52  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.19/3.52  tff(c_266, plain, (![A_57]: (k4_xboole_0(A_57, k1_xboole_0)=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_180])).
% 9.19/3.52  tff(c_276, plain, (![A_57]: (k4_xboole_0(A_57, A_57)=k3_xboole_0(A_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_266, c_14])).
% 9.19/3.52  tff(c_309, plain, (![A_57]: (k3_xboole_0(A_57, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_276])).
% 9.19/3.52  tff(c_847, plain, (![A_90, B_91, C_92]: (k2_xboole_0(k4_xboole_0(A_90, B_91), k4_xboole_0(A_90, C_92))=k4_xboole_0(A_90, k3_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.19/3.52  tff(c_865, plain, (![A_3, B_91]: (k4_xboole_0(A_3, k3_xboole_0(B_91, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_3, B_91), A_3))), inference(superposition, [status(thm), theory('equality')], [c_190, c_847])).
% 9.19/3.52  tff(c_910, plain, (![A_93, B_94]: (k2_xboole_0(k4_xboole_0(A_93, B_94), A_93)=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_309, c_865])).
% 9.19/3.52  tff(c_928, plain, (![A_11, B_12]: (k2_xboole_0(k3_xboole_0(A_11, B_12), A_11)=A_11)), inference(superposition, [status(thm), theory('equality')], [c_14, c_910])).
% 9.19/3.52  tff(c_494, plain, (![C_70, A_71, B_72]: (r1_xboole_0(k3_xboole_0(C_70, A_71), k3_xboole_0(C_70, B_72)) | ~r1_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.19/3.52  tff(c_512, plain, (![A_3, A_71]: (r1_xboole_0(k3_xboole_0(A_3, A_71), A_3) | ~r1_xboole_0(A_71, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_494])).
% 9.19/3.52  tff(c_934, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_119, c_910])).
% 9.19/3.52  tff(c_16, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.19/3.52  tff(c_55, plain, (![A_34, B_35]: (r1_xboole_0(k4_xboole_0(A_34, B_35), B_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.19/3.52  tff(c_58, plain, (![A_13]: (r1_xboole_0(k1_xboole_0, A_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_55])).
% 9.19/3.52  tff(c_942, plain, (![C_95, A_96, B_97]: (C_95=A_96 | ~r1_xboole_0(C_95, B_97) | ~r1_xboole_0(A_96, B_97) | k2_xboole_0(C_95, B_97)!=k2_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.19/3.52  tff(c_972, plain, (![A_96, A_13]: (k1_xboole_0=A_96 | ~r1_xboole_0(A_96, A_13) | k2_xboole_0(k1_xboole_0, A_13)!=k2_xboole_0(A_96, A_13))), inference(resolution, [status(thm)], [c_58, c_942])).
% 9.19/3.52  tff(c_17950, plain, (![A_381, A_382]: (k1_xboole_0=A_381 | ~r1_xboole_0(A_381, A_382) | k2_xboole_0(A_381, A_382)!=A_382)), inference(demodulation, [status(thm), theory('equality')], [c_934, c_972])).
% 9.19/3.52  tff(c_18028, plain, (![A_3, A_71]: (k3_xboole_0(A_3, A_71)=k1_xboole_0 | k2_xboole_0(k3_xboole_0(A_3, A_71), A_3)!=A_3 | ~r1_xboole_0(A_71, A_3))), inference(resolution, [status(thm)], [c_512, c_17950])).
% 9.19/3.52  tff(c_18110, plain, (![A_383, A_384]: (k3_xboole_0(A_383, A_384)=k1_xboole_0 | ~r1_xboole_0(A_384, A_383))), inference(demodulation, [status(thm), theory('equality')], [c_928, c_18028])).
% 9.19/3.52  tff(c_18258, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_18110])).
% 9.19/3.52  tff(c_168, plain, (![B_51]: (k3_xboole_0(k1_xboole_0, B_51)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_155, c_16])).
% 9.19/3.52  tff(c_862, plain, (![A_3, C_92]: (k4_xboole_0(A_3, k3_xboole_0(k1_xboole_0, C_92))=k2_xboole_0(A_3, k4_xboole_0(A_3, C_92)))), inference(superposition, [status(thm), theory('equality')], [c_190, c_847])).
% 9.19/3.52  tff(c_1017, plain, (![A_100, C_101]: (k2_xboole_0(A_100, k4_xboole_0(A_100, C_101))=A_100)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_168, c_862])).
% 9.19/3.52  tff(c_1049, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_119, c_1017])).
% 9.19/3.52  tff(c_889, plain, (![A_3, B_91]: (k4_xboole_0(A_3, k3_xboole_0(B_91, A_3))=k2_xboole_0(k4_xboole_0(A_3, B_91), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_119, c_847])).
% 9.19/3.52  tff(c_2781, plain, (![A_3, B_91]: (k4_xboole_0(A_3, k3_xboole_0(B_91, A_3))=k4_xboole_0(A_3, B_91))), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_889])).
% 9.19/3.52  tff(c_18425, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18258, c_2781])).
% 9.19/3.52  tff(c_18551, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_18425])).
% 9.19/3.52  tff(c_32, plain, (![A_30, B_31]: (~r2_hidden(A_30, B_31) | k4_xboole_0(k1_tarski(A_30), B_31)!=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.19/3.52  tff(c_20000, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18551, c_32])).
% 9.19/3.52  tff(c_20073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_20000])).
% 9.19/3.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.19/3.52  
% 9.19/3.52  Inference rules
% 9.19/3.52  ----------------------
% 9.19/3.52  #Ref     : 5
% 9.19/3.52  #Sup     : 5038
% 9.19/3.52  #Fact    : 0
% 9.19/3.52  #Define  : 0
% 9.19/3.52  #Split   : 2
% 9.19/3.52  #Chain   : 0
% 9.19/3.52  #Close   : 0
% 9.19/3.52  
% 9.19/3.52  Ordering : KBO
% 9.19/3.52  
% 9.19/3.52  Simplification rules
% 9.19/3.52  ----------------------
% 9.19/3.52  #Subsume      : 835
% 9.19/3.52  #Demod        : 4560
% 9.19/3.52  #Tautology    : 2754
% 9.19/3.52  #SimpNegUnit  : 84
% 9.19/3.52  #BackRed      : 18
% 9.19/3.52  
% 9.19/3.52  #Partial instantiations: 0
% 9.19/3.52  #Strategies tried      : 1
% 9.19/3.52  
% 9.19/3.52  Timing (in seconds)
% 9.19/3.52  ----------------------
% 9.19/3.52  Preprocessing        : 0.35
% 9.19/3.52  Parsing              : 0.18
% 9.19/3.52  CNF conversion       : 0.02
% 9.19/3.52  Main loop            : 2.35
% 9.19/3.52  Inferencing          : 0.60
% 9.19/3.52  Reduction            : 1.11
% 9.19/3.52  Demodulation         : 0.91
% 9.19/3.52  BG Simplification    : 0.08
% 9.19/3.52  Subsumption          : 0.45
% 9.19/3.52  Abstraction          : 0.13
% 9.19/3.52  MUC search           : 0.00
% 9.19/3.52  Cooper               : 0.00
% 9.19/3.52  Total                : 2.74
% 9.19/3.52  Index Insertion      : 0.00
% 9.19/3.52  Index Deletion       : 0.00
% 9.19/3.52  Index Matching       : 0.00
% 9.19/3.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
