%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:52 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 131 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :   66 ( 128 expanded)
%              Number of equality atoms :   47 ( 107 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_164,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_201,plain,(
    ! [B_55,A_56] : k3_tarski(k2_tarski(B_55,A_56)) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_164])).

tff(c_36,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_229,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_36])).

tff(c_245,plain,(
    ! [A_58] : k2_xboole_0(k1_xboole_0,A_58) = A_58 ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_10])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_276,plain,(
    ! [A_59] : k2_xboole_0(k1_xboole_0,A_59) = A_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_10])).

tff(c_316,plain,(
    ! [B_11] : k4_xboole_0(B_11,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_276])).

tff(c_338,plain,(
    ! [B_11] : k4_xboole_0(B_11,k1_xboole_0) = B_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_316])).

tff(c_554,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k4_xboole_0(B_70,A_69)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_569,plain,(
    ! [B_11] : k5_xboole_0(k1_xboole_0,B_11) = k2_xboole_0(k1_xboole_0,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_554])).

tff(c_577,plain,(
    ! [B_11] : k5_xboole_0(k1_xboole_0,B_11) = B_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_569])).

tff(c_12,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_324,plain,(
    ! [B_7] : k3_xboole_0(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_276])).

tff(c_681,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_698,plain,(
    ! [B_7] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_681])).

tff(c_706,plain,(
    ! [B_7] : k4_xboole_0(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_698])).

tff(c_365,plain,(
    ! [A_61,B_62] : k4_xboole_0(k2_xboole_0(A_61,B_62),B_62) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_377,plain,(
    ! [A_58] : k4_xboole_0(k1_xboole_0,A_58) = k4_xboole_0(A_58,A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_365])).

tff(c_709,plain,(
    ! [A_58] : k4_xboole_0(A_58,A_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_377])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_114,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_701,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_681])).

tff(c_814,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_701])).

tff(c_146,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_tarski(A_46),B_47)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1012,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(k1_tarski(A_93),B_94) = k1_tarski(A_93)
      | ~ r2_hidden(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_146,c_14])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1021,plain,(
    ! [A_93,B_94] :
      ( k5_xboole_0(k1_tarski(A_93),k1_tarski(A_93)) = k4_xboole_0(k1_tarski(A_93),B_94)
      | ~ r2_hidden(A_93,B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_8])).

tff(c_1336,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(k1_tarski(A_105),B_106) = k1_xboole_0
      | ~ r2_hidden(A_105,B_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_1021])).

tff(c_1364,plain,(
    ! [B_106,A_105] :
      ( k2_xboole_0(B_106,k1_tarski(A_105)) = k2_xboole_0(B_106,k1_xboole_0)
      | ~ r2_hidden(A_105,B_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1336,c_16])).

tff(c_1501,plain,(
    ! [B_110,A_111] :
      ( k2_xboole_0(B_110,k1_tarski(A_111)) = B_110
      | ~ r2_hidden(A_111,B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1364])).

tff(c_207,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,A_56) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_36])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_228,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_38])).

tff(c_1532,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1501,c_228])).

tff(c_1572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:08:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.45  
% 2.66/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.45  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.66/1.45  
% 2.66/1.45  %Foreground sorts:
% 2.66/1.45  
% 2.66/1.45  
% 2.66/1.45  %Background operators:
% 2.66/1.45  
% 2.66/1.45  
% 2.66/1.45  %Foreground operators:
% 2.66/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.66/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.66/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.66/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.66/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.66/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.45  
% 2.98/1.47  tff(f_68, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.98/1.47  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.98/1.47  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.98/1.47  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.98/1.47  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.98/1.47  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.98/1.47  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.98/1.47  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.98/1.47  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.98/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.98/1.47  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.98/1.47  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.98/1.47  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.47  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.98/1.47  tff(c_22, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.98/1.47  tff(c_164, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.98/1.47  tff(c_201, plain, (![B_55, A_56]: (k3_tarski(k2_tarski(B_55, A_56))=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_22, c_164])).
% 2.98/1.47  tff(c_36, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.98/1.47  tff(c_229, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_201, c_36])).
% 2.98/1.47  tff(c_245, plain, (![A_58]: (k2_xboole_0(k1_xboole_0, A_58)=A_58)), inference(superposition, [status(thm), theory('equality')], [c_229, c_10])).
% 2.98/1.47  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.98/1.47  tff(c_276, plain, (![A_59]: (k2_xboole_0(k1_xboole_0, A_59)=A_59)), inference(superposition, [status(thm), theory('equality')], [c_229, c_10])).
% 2.98/1.47  tff(c_316, plain, (![B_11]: (k4_xboole_0(B_11, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_11))), inference(superposition, [status(thm), theory('equality')], [c_16, c_276])).
% 2.98/1.47  tff(c_338, plain, (![B_11]: (k4_xboole_0(B_11, k1_xboole_0)=B_11)), inference(demodulation, [status(thm), theory('equality')], [c_245, c_316])).
% 2.98/1.47  tff(c_554, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k4_xboole_0(B_70, A_69))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.98/1.47  tff(c_569, plain, (![B_11]: (k5_xboole_0(k1_xboole_0, B_11)=k2_xboole_0(k1_xboole_0, B_11))), inference(superposition, [status(thm), theory('equality')], [c_338, c_554])).
% 2.98/1.47  tff(c_577, plain, (![B_11]: (k5_xboole_0(k1_xboole_0, B_11)=B_11)), inference(demodulation, [status(thm), theory('equality')], [c_245, c_569])).
% 2.98/1.47  tff(c_12, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k3_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.98/1.47  tff(c_324, plain, (![B_7]: (k3_xboole_0(k1_xboole_0, B_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_276])).
% 2.98/1.47  tff(c_681, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.98/1.47  tff(c_698, plain, (![B_7]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_7))), inference(superposition, [status(thm), theory('equality')], [c_324, c_681])).
% 2.98/1.47  tff(c_706, plain, (![B_7]: (k4_xboole_0(k1_xboole_0, B_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_577, c_698])).
% 2.98/1.47  tff(c_365, plain, (![A_61, B_62]: (k4_xboole_0(k2_xboole_0(A_61, B_62), B_62)=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.98/1.47  tff(c_377, plain, (![A_58]: (k4_xboole_0(k1_xboole_0, A_58)=k4_xboole_0(A_58, A_58))), inference(superposition, [status(thm), theory('equality')], [c_245, c_365])).
% 2.98/1.47  tff(c_709, plain, (![A_58]: (k4_xboole_0(A_58, A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_706, c_377])).
% 2.98/1.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.47  tff(c_110, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.47  tff(c_114, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_110])).
% 2.98/1.47  tff(c_701, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_114, c_681])).
% 2.98/1.47  tff(c_814, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_709, c_701])).
% 2.98/1.47  tff(c_146, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), B_47) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.98/1.47  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.47  tff(c_1012, plain, (![A_93, B_94]: (k3_xboole_0(k1_tarski(A_93), B_94)=k1_tarski(A_93) | ~r2_hidden(A_93, B_94))), inference(resolution, [status(thm)], [c_146, c_14])).
% 2.98/1.47  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.98/1.47  tff(c_1021, plain, (![A_93, B_94]: (k5_xboole_0(k1_tarski(A_93), k1_tarski(A_93))=k4_xboole_0(k1_tarski(A_93), B_94) | ~r2_hidden(A_93, B_94))), inference(superposition, [status(thm), theory('equality')], [c_1012, c_8])).
% 2.98/1.47  tff(c_1336, plain, (![A_105, B_106]: (k4_xboole_0(k1_tarski(A_105), B_106)=k1_xboole_0 | ~r2_hidden(A_105, B_106))), inference(demodulation, [status(thm), theory('equality')], [c_814, c_1021])).
% 2.98/1.47  tff(c_1364, plain, (![B_106, A_105]: (k2_xboole_0(B_106, k1_tarski(A_105))=k2_xboole_0(B_106, k1_xboole_0) | ~r2_hidden(A_105, B_106))), inference(superposition, [status(thm), theory('equality')], [c_1336, c_16])).
% 2.98/1.47  tff(c_1501, plain, (![B_110, A_111]: (k2_xboole_0(B_110, k1_tarski(A_111))=B_110 | ~r2_hidden(A_111, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1364])).
% 2.98/1.47  tff(c_207, plain, (![B_55, A_56]: (k2_xboole_0(B_55, A_56)=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_201, c_36])).
% 2.98/1.47  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.47  tff(c_228, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_207, c_38])).
% 2.98/1.47  tff(c_1532, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1501, c_228])).
% 2.98/1.47  tff(c_1572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1532])).
% 2.98/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.47  
% 2.98/1.47  Inference rules
% 2.98/1.47  ----------------------
% 2.98/1.47  #Ref     : 0
% 2.98/1.47  #Sup     : 352
% 2.98/1.47  #Fact    : 0
% 2.98/1.47  #Define  : 0
% 2.98/1.47  #Split   : 0
% 2.98/1.47  #Chain   : 0
% 2.98/1.47  #Close   : 0
% 2.98/1.47  
% 2.98/1.47  Ordering : KBO
% 2.98/1.47  
% 2.98/1.47  Simplification rules
% 2.98/1.47  ----------------------
% 2.98/1.47  #Subsume      : 8
% 2.98/1.47  #Demod        : 276
% 2.98/1.47  #Tautology    : 293
% 2.98/1.47  #SimpNegUnit  : 0
% 2.98/1.47  #BackRed      : 6
% 2.98/1.47  
% 2.98/1.47  #Partial instantiations: 0
% 2.98/1.47  #Strategies tried      : 1
% 2.98/1.47  
% 2.98/1.47  Timing (in seconds)
% 2.98/1.47  ----------------------
% 2.98/1.47  Preprocessing        : 0.31
% 2.98/1.47  Parsing              : 0.17
% 2.98/1.47  CNF conversion       : 0.02
% 2.98/1.47  Main loop            : 0.37
% 2.98/1.47  Inferencing          : 0.14
% 2.98/1.47  Reduction            : 0.14
% 2.98/1.47  Demodulation         : 0.11
% 2.98/1.47  BG Simplification    : 0.02
% 2.98/1.47  Subsumption          : 0.05
% 2.98/1.47  Abstraction          : 0.02
% 2.98/1.47  MUC search           : 0.00
% 2.98/1.47  Cooper               : 0.00
% 2.98/1.47  Total                : 0.70
% 2.98/1.47  Index Insertion      : 0.00
% 2.98/1.47  Index Deletion       : 0.00
% 2.98/1.47  Index Matching       : 0.00
% 2.98/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
