%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:57 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 149 expanded)
%              Number of leaves         :   29 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :   65 ( 150 expanded)
%              Number of equality atoms :   47 ( 124 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_40,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_12])).

tff(c_557,plain,(
    ! [A_70,B_71] : k2_xboole_0(A_70,k4_xboole_0(B_71,A_70)) = k2_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_567,plain,(
    ! [B_71] : k4_xboole_0(B_71,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_78])).

tff(c_607,plain,(
    ! [B_72] : k4_xboole_0(B_72,k1_xboole_0) = B_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_567])).

tff(c_22,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_632,plain,(
    ! [B_72] : k5_xboole_0(k1_xboole_0,B_72) = k2_xboole_0(k1_xboole_0,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_22])).

tff(c_654,plain,(
    ! [B_72] : k5_xboole_0(k1_xboole_0,B_72) = B_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_632])).

tff(c_148,plain,(
    ! [A_38,B_39] : k2_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_155,plain,(
    ! [B_39] : k3_xboole_0(k1_xboole_0,B_39) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_78])).

tff(c_418,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_430,plain,(
    ! [B_39] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_418])).

tff(c_660,plain,(
    ! [B_39] : k4_xboole_0(k1_xboole_0,B_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_430])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_226,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_235,plain,(
    ! [B_53] : k3_xboole_0(B_53,B_53) = B_53 ),
    inference(resolution,[status(thm)],[c_8,c_226])).

tff(c_14,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_245,plain,(
    ! [B_53] : k2_xboole_0(B_53,B_53) = B_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_14])).

tff(c_296,plain,(
    ! [A_56,B_57] : k4_xboole_0(k2_xboole_0(A_56,B_57),B_57) = k4_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_311,plain,(
    ! [A_36] : k4_xboole_0(k1_xboole_0,A_36) = k4_xboole_0(A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_296])).

tff(c_343,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k4_xboole_0(B_60,A_59)) = k2_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_352,plain,(
    ! [A_36] : k5_xboole_0(A_36,k4_xboole_0(k1_xboole_0,A_36)) = k2_xboole_0(A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_343])).

tff(c_361,plain,(
    ! [A_36] : k5_xboole_0(A_36,k4_xboole_0(k1_xboole_0,A_36)) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_352])).

tff(c_731,plain,(
    ! [A_36] : k5_xboole_0(A_36,k1_xboole_0) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_361])).

tff(c_732,plain,(
    ! [A_36] : k4_xboole_0(A_36,A_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_311])).

tff(c_234,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_226])).

tff(c_427,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_418])).

tff(c_792,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_427])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_tarski(A_28),B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1267,plain,(
    ! [A_99,B_100] :
      ( k3_xboole_0(k1_tarski(A_99),B_100) = k1_tarski(A_99)
      | ~ r2_hidden(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_34,c_226])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1276,plain,(
    ! [A_99,B_100] :
      ( k5_xboole_0(k1_tarski(A_99),k1_tarski(A_99)) = k4_xboole_0(k1_tarski(A_99),B_100)
      | ~ r2_hidden(A_99,B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1267,c_10])).

tff(c_1604,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(k1_tarski(A_109),B_110) = k1_xboole_0
      | ~ r2_hidden(A_109,B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_1276])).

tff(c_1638,plain,(
    ! [B_110,A_109] :
      ( k2_xboole_0(B_110,k1_tarski(A_109)) = k5_xboole_0(B_110,k1_xboole_0)
      | ~ r2_hidden(A_109,B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1604,c_22])).

tff(c_1794,plain,(
    ! [B_114,A_115] :
      ( k2_xboole_0(B_114,k1_tarski(A_115)) = B_114
      | ~ r2_hidden(A_115,B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_1638])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_1841,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1794,c_42])).

tff(c_1875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1841])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.34  % CPULimit   : 60
% 0.18/0.34  % DateTime   : Tue Dec  1 11:06:07 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.47  
% 3.13/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.47  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.13/1.47  
% 3.13/1.47  %Foreground sorts:
% 3.13/1.47  
% 3.13/1.47  
% 3.13/1.47  %Background operators:
% 3.13/1.47  
% 3.13/1.47  
% 3.13/1.47  %Foreground operators:
% 3.13/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.13/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.13/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.13/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.13/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.13/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.13/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.13/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.13/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.13/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.13/1.47  
% 3.16/1.48  tff(f_68, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.16/1.48  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.16/1.48  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.16/1.48  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.16/1.48  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.16/1.48  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.16/1.48  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.16/1.48  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.16/1.48  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.16/1.48  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.16/1.48  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.16/1.48  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.16/1.48  tff(c_62, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.16/1.48  tff(c_12, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.16/1.48  tff(c_78, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_62, c_12])).
% 3.16/1.48  tff(c_557, plain, (![A_70, B_71]: (k2_xboole_0(A_70, k4_xboole_0(B_71, A_70))=k2_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.16/1.48  tff(c_567, plain, (![B_71]: (k4_xboole_0(B_71, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_71))), inference(superposition, [status(thm), theory('equality')], [c_557, c_78])).
% 3.16/1.48  tff(c_607, plain, (![B_72]: (k4_xboole_0(B_72, k1_xboole_0)=B_72)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_567])).
% 3.16/1.48  tff(c_22, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.48  tff(c_632, plain, (![B_72]: (k5_xboole_0(k1_xboole_0, B_72)=k2_xboole_0(k1_xboole_0, B_72))), inference(superposition, [status(thm), theory('equality')], [c_607, c_22])).
% 3.16/1.48  tff(c_654, plain, (![B_72]: (k5_xboole_0(k1_xboole_0, B_72)=B_72)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_632])).
% 3.16/1.48  tff(c_148, plain, (![A_38, B_39]: (k2_xboole_0(A_38, k3_xboole_0(A_38, B_39))=A_38)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.48  tff(c_155, plain, (![B_39]: (k3_xboole_0(k1_xboole_0, B_39)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_148, c_78])).
% 3.16/1.48  tff(c_418, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.48  tff(c_430, plain, (![B_39]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_39))), inference(superposition, [status(thm), theory('equality')], [c_155, c_418])).
% 3.16/1.48  tff(c_660, plain, (![B_39]: (k4_xboole_0(k1_xboole_0, B_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_654, c_430])).
% 3.16/1.48  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.48  tff(c_226, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.48  tff(c_235, plain, (![B_53]: (k3_xboole_0(B_53, B_53)=B_53)), inference(resolution, [status(thm)], [c_8, c_226])).
% 3.16/1.48  tff(c_14, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.48  tff(c_245, plain, (![B_53]: (k2_xboole_0(B_53, B_53)=B_53)), inference(superposition, [status(thm), theory('equality')], [c_235, c_14])).
% 3.16/1.48  tff(c_296, plain, (![A_56, B_57]: (k4_xboole_0(k2_xboole_0(A_56, B_57), B_57)=k4_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.16/1.48  tff(c_311, plain, (![A_36]: (k4_xboole_0(k1_xboole_0, A_36)=k4_xboole_0(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_78, c_296])).
% 3.16/1.48  tff(c_343, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k4_xboole_0(B_60, A_59))=k2_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.48  tff(c_352, plain, (![A_36]: (k5_xboole_0(A_36, k4_xboole_0(k1_xboole_0, A_36))=k2_xboole_0(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_311, c_343])).
% 3.16/1.48  tff(c_361, plain, (![A_36]: (k5_xboole_0(A_36, k4_xboole_0(k1_xboole_0, A_36))=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_245, c_352])).
% 3.16/1.48  tff(c_731, plain, (![A_36]: (k5_xboole_0(A_36, k1_xboole_0)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_660, c_361])).
% 3.16/1.48  tff(c_732, plain, (![A_36]: (k4_xboole_0(A_36, A_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_660, c_311])).
% 3.16/1.48  tff(c_234, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_226])).
% 3.16/1.48  tff(c_427, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_234, c_418])).
% 3.16/1.48  tff(c_792, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_732, c_427])).
% 3.16/1.48  tff(c_34, plain, (![A_28, B_29]: (r1_tarski(k1_tarski(A_28), B_29) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.16/1.48  tff(c_1267, plain, (![A_99, B_100]: (k3_xboole_0(k1_tarski(A_99), B_100)=k1_tarski(A_99) | ~r2_hidden(A_99, B_100))), inference(resolution, [status(thm)], [c_34, c_226])).
% 3.16/1.48  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.48  tff(c_1276, plain, (![A_99, B_100]: (k5_xboole_0(k1_tarski(A_99), k1_tarski(A_99))=k4_xboole_0(k1_tarski(A_99), B_100) | ~r2_hidden(A_99, B_100))), inference(superposition, [status(thm), theory('equality')], [c_1267, c_10])).
% 3.16/1.48  tff(c_1604, plain, (![A_109, B_110]: (k4_xboole_0(k1_tarski(A_109), B_110)=k1_xboole_0 | ~r2_hidden(A_109, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_792, c_1276])).
% 3.16/1.48  tff(c_1638, plain, (![B_110, A_109]: (k2_xboole_0(B_110, k1_tarski(A_109))=k5_xboole_0(B_110, k1_xboole_0) | ~r2_hidden(A_109, B_110))), inference(superposition, [status(thm), theory('equality')], [c_1604, c_22])).
% 3.16/1.48  tff(c_1794, plain, (![B_114, A_115]: (k2_xboole_0(B_114, k1_tarski(A_115))=B_114 | ~r2_hidden(A_115, B_114))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_1638])).
% 3.16/1.48  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.16/1.48  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.16/1.48  tff(c_42, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 3.16/1.48  tff(c_1841, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1794, c_42])).
% 3.16/1.48  tff(c_1875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1841])).
% 3.16/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.48  
% 3.16/1.48  Inference rules
% 3.16/1.48  ----------------------
% 3.16/1.48  #Ref     : 0
% 3.16/1.48  #Sup     : 438
% 3.16/1.48  #Fact    : 0
% 3.16/1.48  #Define  : 0
% 3.16/1.48  #Split   : 0
% 3.16/1.48  #Chain   : 0
% 3.16/1.48  #Close   : 0
% 3.16/1.48  
% 3.16/1.48  Ordering : KBO
% 3.16/1.48  
% 3.16/1.48  Simplification rules
% 3.16/1.48  ----------------------
% 3.16/1.48  #Subsume      : 25
% 3.16/1.48  #Demod        : 467
% 3.16/1.48  #Tautology    : 348
% 3.16/1.48  #SimpNegUnit  : 0
% 3.16/1.48  #BackRed      : 7
% 3.16/1.48  
% 3.16/1.48  #Partial instantiations: 0
% 3.16/1.48  #Strategies tried      : 1
% 3.16/1.48  
% 3.16/1.48  Timing (in seconds)
% 3.16/1.48  ----------------------
% 3.16/1.49  Preprocessing        : 0.30
% 3.16/1.49  Parsing              : 0.16
% 3.16/1.49  CNF conversion       : 0.02
% 3.16/1.49  Main loop            : 0.43
% 3.16/1.49  Inferencing          : 0.15
% 3.16/1.49  Reduction            : 0.19
% 3.16/1.49  Demodulation         : 0.15
% 3.16/1.49  BG Simplification    : 0.02
% 3.16/1.49  Subsumption          : 0.06
% 3.16/1.49  Abstraction          : 0.03
% 3.16/1.49  MUC search           : 0.00
% 3.16/1.49  Cooper               : 0.00
% 3.16/1.49  Total                : 0.76
% 3.16/1.49  Index Insertion      : 0.00
% 3.16/1.49  Index Deletion       : 0.00
% 3.16/1.49  Index Matching       : 0.00
% 3.16/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
