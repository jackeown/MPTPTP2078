%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:49 EST 2020

% Result     : Theorem 4.95s
% Output     : CNFRefutation 4.95s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 107 expanded)
%              Number of leaves         :   34 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 149 expanded)
%              Number of equality atoms :   34 (  53 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_82,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_62,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    ! [A_17] : k2_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_147,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_151,plain,(
    ! [B_14] : k3_xboole_0(B_14,B_14) = B_14 ),
    inference(resolution,[status(thm)],[c_30,c_147])).

tff(c_395,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_407,plain,(
    ! [B_14] : k5_xboole_0(B_14,B_14) = k4_xboole_0(B_14,B_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_395])).

tff(c_832,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_hidden(A_112,B_113)
      | r2_hidden(A_112,C_114)
      | ~ r2_hidden(A_112,k5_xboole_0(B_113,C_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1429,plain,(
    ! [A_171,B_172] :
      ( r2_hidden(A_171,B_172)
      | r2_hidden(A_171,B_172)
      | ~ r2_hidden(A_171,k4_xboole_0(B_172,B_172)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_832])).

tff(c_1465,plain,(
    ! [B_173] :
      ( r2_hidden('#skF_1'(k4_xboole_0(B_173,B_173)),B_173)
      | v1_xboole_0(k4_xboole_0(B_173,B_173)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1429])).

tff(c_1001,plain,(
    ! [A_135,C_136,B_137] :
      ( ~ r2_hidden(A_135,C_136)
      | ~ r2_hidden(A_135,B_137)
      | ~ r2_hidden(A_135,k5_xboole_0(B_137,C_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1351,plain,(
    ! [A_167,B_168] :
      ( ~ r2_hidden(A_167,B_168)
      | ~ r2_hidden(A_167,B_168)
      | ~ r2_hidden(A_167,k4_xboole_0(B_168,B_168)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_1001])).

tff(c_1384,plain,(
    ! [B_168] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(B_168,B_168)),B_168)
      | v1_xboole_0(k4_xboole_0(B_168,B_168)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1351])).

tff(c_1556,plain,(
    ! [B_177] : v1_xboole_0(k4_xboole_0(B_177,B_177)) ),
    inference(resolution,[status(thm)],[c_1465,c_1384])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_419,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_2'(A_78,B_79),A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_423,plain,(
    ! [A_78,B_79] :
      ( ~ v1_xboole_0(A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_419,c_2])).

tff(c_424,plain,(
    ! [A_80,B_81] :
      ( ~ v1_xboole_0(A_80)
      | r1_tarski(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_419,c_2])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( B_14 = A_13
      | ~ r1_tarski(B_14,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_818,plain,(
    ! [B_110,A_111] :
      ( B_110 = A_111
      | ~ r1_tarski(B_110,A_111)
      | ~ v1_xboole_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_424,c_26])).

tff(c_863,plain,(
    ! [B_115,A_116] :
      ( B_115 = A_116
      | ~ v1_xboole_0(B_115)
      | ~ v1_xboole_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_423,c_818])).

tff(c_866,plain,(
    ! [A_116] :
      ( k1_xboole_0 = A_116
      | ~ v1_xboole_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_12,c_863])).

tff(c_1571,plain,(
    ! [B_177] : k4_xboole_0(B_177,B_177) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1556,c_866])).

tff(c_211,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_tarski(A_64),B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_920,plain,(
    ! [A_124,B_125] :
      ( k3_xboole_0(k1_tarski(A_124),B_125) = k1_tarski(A_124)
      | ~ r2_hidden(A_124,B_125) ) ),
    inference(resolution,[status(thm)],[c_211,c_38])).

tff(c_32,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_926,plain,(
    ! [A_124,B_125] :
      ( k5_xboole_0(k1_tarski(A_124),k1_tarski(A_124)) = k4_xboole_0(k1_tarski(A_124),B_125)
      | ~ r2_hidden(A_124,B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_920,c_32])).

tff(c_942,plain,(
    ! [A_124,B_125] :
      ( k4_xboole_0(k1_tarski(A_124),k1_tarski(A_124)) = k4_xboole_0(k1_tarski(A_124),B_125)
      | ~ r2_hidden(A_124,B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_926])).

tff(c_4118,plain,(
    ! [A_289,B_290] :
      ( k4_xboole_0(k1_tarski(A_289),B_290) = k1_xboole_0
      | ~ r2_hidden(A_289,B_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1571,c_942])).

tff(c_40,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4169,plain,(
    ! [B_290,A_289] :
      ( k2_xboole_0(B_290,k1_tarski(A_289)) = k2_xboole_0(B_290,k1_xboole_0)
      | ~ r2_hidden(A_289,B_290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4118,c_40])).

tff(c_4204,plain,(
    ! [B_291,A_292] :
      ( k2_xboole_0(B_291,k1_tarski(A_292)) = B_291
      | ~ r2_hidden(A_292,B_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4169])).

tff(c_44,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_192,plain,(
    ! [A_62,B_63] : k3_tarski(k2_tarski(A_62,B_63)) = k2_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_229,plain,(
    ! [B_67,A_68] : k3_tarski(k2_tarski(B_67,A_68)) = k2_xboole_0(A_68,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_192])).

tff(c_58,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_235,plain,(
    ! [B_67,A_68] : k2_xboole_0(B_67,A_68) = k2_xboole_0(A_68,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_58])).

tff(c_60,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_256,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_60])).

tff(c_4229,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4204,c_256])).

tff(c_4271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.95/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.99  
% 4.95/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.99  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.95/1.99  
% 4.95/1.99  %Foreground sorts:
% 4.95/1.99  
% 4.95/1.99  
% 4.95/1.99  %Background operators:
% 4.95/1.99  
% 4.95/1.99  
% 4.95/1.99  %Foreground operators:
% 4.95/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.95/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.95/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.95/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.95/1.99  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.95/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.95/1.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.95/1.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.95/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.95/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.95/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.95/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.95/1.99  tff('#skF_3', type, '#skF_3': $i).
% 4.95/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.95/1.99  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.95/1.99  tff('#skF_4', type, '#skF_4': $i).
% 4.95/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.95/1.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.95/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.95/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.95/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.95/1.99  
% 4.95/2.01  tff(f_87, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.95/2.01  tff(f_56, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.95/2.01  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.95/2.01  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.95/2.01  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.95/2.01  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.95/2.01  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 4.95/2.01  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.95/2.01  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.95/2.01  tff(f_80, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.95/2.01  tff(f_64, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.95/2.01  tff(f_68, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.95/2.01  tff(f_82, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.95/2.01  tff(c_62, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.95/2.01  tff(c_34, plain, (![A_17]: (k2_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.95/2.01  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.95/2.01  tff(c_30, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.95/2.01  tff(c_147, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.95/2.01  tff(c_151, plain, (![B_14]: (k3_xboole_0(B_14, B_14)=B_14)), inference(resolution, [status(thm)], [c_30, c_147])).
% 4.95/2.01  tff(c_395, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.95/2.01  tff(c_407, plain, (![B_14]: (k5_xboole_0(B_14, B_14)=k4_xboole_0(B_14, B_14))), inference(superposition, [status(thm), theory('equality')], [c_151, c_395])).
% 4.95/2.01  tff(c_832, plain, (![A_112, B_113, C_114]: (r2_hidden(A_112, B_113) | r2_hidden(A_112, C_114) | ~r2_hidden(A_112, k5_xboole_0(B_113, C_114)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.95/2.01  tff(c_1429, plain, (![A_171, B_172]: (r2_hidden(A_171, B_172) | r2_hidden(A_171, B_172) | ~r2_hidden(A_171, k4_xboole_0(B_172, B_172)))), inference(superposition, [status(thm), theory('equality')], [c_407, c_832])).
% 4.95/2.01  tff(c_1465, plain, (![B_173]: (r2_hidden('#skF_1'(k4_xboole_0(B_173, B_173)), B_173) | v1_xboole_0(k4_xboole_0(B_173, B_173)))), inference(resolution, [status(thm)], [c_4, c_1429])).
% 4.95/2.01  tff(c_1001, plain, (![A_135, C_136, B_137]: (~r2_hidden(A_135, C_136) | ~r2_hidden(A_135, B_137) | ~r2_hidden(A_135, k5_xboole_0(B_137, C_136)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.95/2.01  tff(c_1351, plain, (![A_167, B_168]: (~r2_hidden(A_167, B_168) | ~r2_hidden(A_167, B_168) | ~r2_hidden(A_167, k4_xboole_0(B_168, B_168)))), inference(superposition, [status(thm), theory('equality')], [c_407, c_1001])).
% 4.95/2.01  tff(c_1384, plain, (![B_168]: (~r2_hidden('#skF_1'(k4_xboole_0(B_168, B_168)), B_168) | v1_xboole_0(k4_xboole_0(B_168, B_168)))), inference(resolution, [status(thm)], [c_4, c_1351])).
% 4.95/2.01  tff(c_1556, plain, (![B_177]: (v1_xboole_0(k4_xboole_0(B_177, B_177)))), inference(resolution, [status(thm)], [c_1465, c_1384])).
% 4.95/2.01  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.95/2.01  tff(c_419, plain, (![A_78, B_79]: (r2_hidden('#skF_2'(A_78, B_79), A_78) | r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.95/2.01  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.95/2.01  tff(c_423, plain, (![A_78, B_79]: (~v1_xboole_0(A_78) | r1_tarski(A_78, B_79))), inference(resolution, [status(thm)], [c_419, c_2])).
% 4.95/2.01  tff(c_424, plain, (![A_80, B_81]: (~v1_xboole_0(A_80) | r1_tarski(A_80, B_81))), inference(resolution, [status(thm)], [c_419, c_2])).
% 4.95/2.01  tff(c_26, plain, (![B_14, A_13]: (B_14=A_13 | ~r1_tarski(B_14, A_13) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.95/2.01  tff(c_818, plain, (![B_110, A_111]: (B_110=A_111 | ~r1_tarski(B_110, A_111) | ~v1_xboole_0(A_111))), inference(resolution, [status(thm)], [c_424, c_26])).
% 4.95/2.01  tff(c_863, plain, (![B_115, A_116]: (B_115=A_116 | ~v1_xboole_0(B_115) | ~v1_xboole_0(A_116))), inference(resolution, [status(thm)], [c_423, c_818])).
% 4.95/2.01  tff(c_866, plain, (![A_116]: (k1_xboole_0=A_116 | ~v1_xboole_0(A_116))), inference(resolution, [status(thm)], [c_12, c_863])).
% 4.95/2.01  tff(c_1571, plain, (![B_177]: (k4_xboole_0(B_177, B_177)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1556, c_866])).
% 4.95/2.01  tff(c_211, plain, (![A_64, B_65]: (r1_tarski(k1_tarski(A_64), B_65) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.95/2.01  tff(c_38, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.95/2.01  tff(c_920, plain, (![A_124, B_125]: (k3_xboole_0(k1_tarski(A_124), B_125)=k1_tarski(A_124) | ~r2_hidden(A_124, B_125))), inference(resolution, [status(thm)], [c_211, c_38])).
% 4.95/2.01  tff(c_32, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.95/2.01  tff(c_926, plain, (![A_124, B_125]: (k5_xboole_0(k1_tarski(A_124), k1_tarski(A_124))=k4_xboole_0(k1_tarski(A_124), B_125) | ~r2_hidden(A_124, B_125))), inference(superposition, [status(thm), theory('equality')], [c_920, c_32])).
% 4.95/2.01  tff(c_942, plain, (![A_124, B_125]: (k4_xboole_0(k1_tarski(A_124), k1_tarski(A_124))=k4_xboole_0(k1_tarski(A_124), B_125) | ~r2_hidden(A_124, B_125))), inference(demodulation, [status(thm), theory('equality')], [c_407, c_926])).
% 4.95/2.01  tff(c_4118, plain, (![A_289, B_290]: (k4_xboole_0(k1_tarski(A_289), B_290)=k1_xboole_0 | ~r2_hidden(A_289, B_290))), inference(demodulation, [status(thm), theory('equality')], [c_1571, c_942])).
% 4.95/2.01  tff(c_40, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.95/2.01  tff(c_4169, plain, (![B_290, A_289]: (k2_xboole_0(B_290, k1_tarski(A_289))=k2_xboole_0(B_290, k1_xboole_0) | ~r2_hidden(A_289, B_290))), inference(superposition, [status(thm), theory('equality')], [c_4118, c_40])).
% 4.95/2.01  tff(c_4204, plain, (![B_291, A_292]: (k2_xboole_0(B_291, k1_tarski(A_292))=B_291 | ~r2_hidden(A_292, B_291))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4169])).
% 4.95/2.01  tff(c_44, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.95/2.01  tff(c_192, plain, (![A_62, B_63]: (k3_tarski(k2_tarski(A_62, B_63))=k2_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.95/2.01  tff(c_229, plain, (![B_67, A_68]: (k3_tarski(k2_tarski(B_67, A_68))=k2_xboole_0(A_68, B_67))), inference(superposition, [status(thm), theory('equality')], [c_44, c_192])).
% 4.95/2.01  tff(c_58, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.95/2.01  tff(c_235, plain, (![B_67, A_68]: (k2_xboole_0(B_67, A_68)=k2_xboole_0(A_68, B_67))), inference(superposition, [status(thm), theory('equality')], [c_229, c_58])).
% 4.95/2.01  tff(c_60, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.95/2.01  tff(c_256, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_235, c_60])).
% 4.95/2.01  tff(c_4229, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4204, c_256])).
% 4.95/2.01  tff(c_4271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_4229])).
% 4.95/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/2.01  
% 4.95/2.01  Inference rules
% 4.95/2.01  ----------------------
% 4.95/2.01  #Ref     : 0
% 4.95/2.01  #Sup     : 980
% 4.95/2.01  #Fact    : 0
% 4.95/2.01  #Define  : 0
% 4.95/2.01  #Split   : 0
% 4.95/2.01  #Chain   : 0
% 4.95/2.01  #Close   : 0
% 4.95/2.01  
% 4.95/2.01  Ordering : KBO
% 4.95/2.01  
% 4.95/2.01  Simplification rules
% 4.95/2.01  ----------------------
% 4.95/2.01  #Subsume      : 358
% 4.95/2.01  #Demod        : 418
% 4.95/2.01  #Tautology    : 341
% 4.95/2.01  #SimpNegUnit  : 60
% 4.95/2.01  #BackRed      : 9
% 4.95/2.01  
% 4.95/2.01  #Partial instantiations: 0
% 4.95/2.01  #Strategies tried      : 1
% 4.95/2.01  
% 4.95/2.01  Timing (in seconds)
% 4.95/2.01  ----------------------
% 4.95/2.01  Preprocessing        : 0.32
% 4.95/2.01  Parsing              : 0.17
% 4.95/2.01  CNF conversion       : 0.02
% 4.95/2.01  Main loop            : 0.86
% 4.95/2.01  Inferencing          : 0.30
% 4.95/2.01  Reduction            : 0.29
% 4.95/2.01  Demodulation         : 0.21
% 4.95/2.01  BG Simplification    : 0.03
% 4.95/2.01  Subsumption          : 0.19
% 4.95/2.01  Abstraction          : 0.04
% 4.95/2.01  MUC search           : 0.00
% 4.95/2.01  Cooper               : 0.00
% 4.95/2.01  Total                : 1.22
% 4.95/2.01  Index Insertion      : 0.00
% 4.95/2.01  Index Deletion       : 0.00
% 4.95/2.01  Index Matching       : 0.00
% 4.95/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
