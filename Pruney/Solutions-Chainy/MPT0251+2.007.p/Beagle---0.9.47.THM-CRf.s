%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:47 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 172 expanded)
%              Number of leaves         :   41 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  110 ( 216 expanded)
%              Number of equality atoms :   45 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_83,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_91,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_74,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,(
    ! [A_22] : k2_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_54,plain,(
    ! [B_34,A_33] : k2_tarski(B_34,A_33) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_197,plain,(
    ! [A_74,B_75] : k3_tarski(k2_tarski(A_74,B_75)) = k2_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_261,plain,(
    ! [A_79,B_80] : k3_tarski(k2_tarski(A_79,B_80)) = k2_xboole_0(B_80,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_197])).

tff(c_301,plain,(
    ! [B_85,A_86] : k2_xboole_0(B_85,A_86) = k2_xboole_0(A_86,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_261])).

tff(c_360,plain,(
    ! [A_87] : k2_xboole_0(k1_xboole_0,A_87) = A_87 ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_40])).

tff(c_48,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_151,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_158,plain,(
    ! [A_29,B_30] : k3_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = A_29 ),
    inference(resolution,[status(thm)],[c_48,c_151])).

tff(c_372,plain,(
    ! [A_87] : k3_xboole_0(k1_xboole_0,A_87) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_158])).

tff(c_699,plain,(
    ! [D_121,B_122,A_123] :
      ( r2_hidden(D_121,B_122)
      | ~ r2_hidden(D_121,k3_xboole_0(A_123,B_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_836,plain,(
    ! [D_134,A_135] :
      ( r2_hidden(D_134,A_135)
      | ~ r2_hidden(D_134,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_699])).

tff(c_848,plain,(
    ! [A_135] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_135)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_836])).

tff(c_1130,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_848])).

tff(c_287,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_4'(A_81,B_82),A_81)
      | r1_xboole_0(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_295,plain,(
    ! [A_83,B_84] :
      ( ~ v1_xboole_0(A_83)
      | r1_xboole_0(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_287,c_4])).

tff(c_50,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = A_31
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_299,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,B_84) = A_83
      | ~ v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_295,c_50])).

tff(c_1137,plain,(
    ! [B_84] : k4_xboole_0(k1_xboole_0,B_84) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1130,c_299])).

tff(c_329,plain,(
    ! [A_86] : k2_xboole_0(k1_xboole_0,A_86) = A_86 ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_40])).

tff(c_610,plain,(
    ! [A_109,B_110] : k4_xboole_0(k2_xboole_0(A_109,B_110),B_110) = k4_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_619,plain,(
    ! [A_86] : k4_xboole_0(k1_xboole_0,A_86) = k4_xboole_0(A_86,A_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_610])).

tff(c_1140,plain,(
    ! [A_86] : k4_xboole_0(A_86,A_86) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1137,c_619])).

tff(c_36,plain,(
    ! [B_19] : r1_tarski(B_19,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_159,plain,(
    ! [B_19] : k3_xboole_0(B_19,B_19) = B_19 ),
    inference(resolution,[status(thm)],[c_36,c_151])).

tff(c_668,plain,(
    ! [A_116,B_117] : k5_xboole_0(A_116,k3_xboole_0(A_116,B_117)) = k4_xboole_0(A_116,B_117) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_686,plain,(
    ! [B_19] : k5_xboole_0(B_19,B_19) = k4_xboole_0(B_19,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_668])).

tff(c_1187,plain,(
    ! [B_19] : k5_xboole_0(B_19,B_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1140,c_686])).

tff(c_56,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1286,plain,(
    ! [A_159,B_160,C_161] :
      ( r1_tarski(k2_tarski(A_159,B_160),C_161)
      | ~ r2_hidden(B_160,C_161)
      | ~ r2_hidden(A_159,C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2589,plain,(
    ! [A_257,C_258] :
      ( r1_tarski(k1_tarski(A_257),C_258)
      | ~ r2_hidden(A_257,C_258)
      | ~ r2_hidden(A_257,C_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1286])).

tff(c_42,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10834,plain,(
    ! [A_554,C_555] :
      ( k3_xboole_0(k1_tarski(A_554),C_555) = k1_tarski(A_554)
      | ~ r2_hidden(A_554,C_555) ) ),
    inference(resolution,[status(thm)],[c_2589,c_42])).

tff(c_38,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10927,plain,(
    ! [A_554,C_555] :
      ( k5_xboole_0(k1_tarski(A_554),k1_tarski(A_554)) = k4_xboole_0(k1_tarski(A_554),C_555)
      | ~ r2_hidden(A_554,C_555) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10834,c_38])).

tff(c_11282,plain,(
    ! [A_562,C_563] :
      ( k4_xboole_0(k1_tarski(A_562),C_563) = k1_xboole_0
      | ~ r2_hidden(A_562,C_563) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_10927])).

tff(c_44,plain,(
    ! [A_25,B_26] : k2_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_11369,plain,(
    ! [C_563,A_562] :
      ( k2_xboole_0(C_563,k1_tarski(A_562)) = k2_xboole_0(C_563,k1_xboole_0)
      | ~ r2_hidden(A_562,C_563) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11282,c_44])).

tff(c_11484,plain,(
    ! [C_567,A_568] :
      ( k2_xboole_0(C_567,k1_tarski(A_568)) = C_567
      | ~ r2_hidden(A_568,C_567) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_11369])).

tff(c_273,plain,(
    ! [B_46,A_45] : k2_xboole_0(B_46,A_45) = k2_xboole_0(A_45,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_261])).

tff(c_72,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_300,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_72])).

tff(c_11806,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_11484,c_300])).

tff(c_11903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_11806])).

tff(c_11906,plain,(
    ! [A_569] : r2_hidden('#skF_1'(k1_xboole_0),A_569) ),
    inference(splitRight,[status(thm)],[c_848])).

tff(c_11935,plain,(
    ! [A_569] : ~ v1_xboole_0(A_569) ),
    inference(resolution,[status(thm)],[c_11906,c_4])).

tff(c_143,plain,(
    ! [B_60,A_61] :
      ( ~ r2_hidden(B_60,A_61)
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_148,plain,(
    ! [A_3] :
      ( ~ r2_hidden(A_3,'#skF_1'(A_3))
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_143])).

tff(c_11933,plain,(
    v1_xboole_0('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_11906,c_148])).

tff(c_11948,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11935,c_11933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.91/2.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.81  
% 7.91/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.81  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 7.91/2.81  
% 7.91/2.81  %Foreground sorts:
% 7.91/2.81  
% 7.91/2.81  
% 7.91/2.81  %Background operators:
% 7.91/2.81  
% 7.91/2.81  
% 7.91/2.81  %Foreground operators:
% 7.91/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.91/2.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.91/2.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.91/2.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.91/2.81  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.91/2.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.91/2.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.91/2.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.91/2.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.91/2.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.91/2.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.91/2.81  tff('#skF_5', type, '#skF_5': $i).
% 7.91/2.81  tff('#skF_6', type, '#skF_6': $i).
% 7.91/2.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.91/2.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.91/2.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.91/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.91/2.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.91/2.81  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.91/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.91/2.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.91/2.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.91/2.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.91/2.81  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.91/2.81  
% 7.91/2.83  tff(f_110, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 7.91/2.83  tff(f_73, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 7.91/2.83  tff(f_36, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.91/2.83  tff(f_99, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.91/2.83  tff(f_89, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.91/2.83  tff(f_83, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.91/2.83  tff(f_77, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.91/2.83  tff(f_45, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.91/2.83  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.91/2.83  tff(f_87, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 7.91/2.83  tff(f_81, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 7.91/2.83  tff(f_69, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.91/2.83  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.91/2.83  tff(f_91, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.91/2.83  tff(f_105, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 7.91/2.83  tff(f_79, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.91/2.83  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 7.91/2.83  tff(c_74, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.91/2.83  tff(c_40, plain, (![A_22]: (k2_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.91/2.83  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.91/2.83  tff(c_64, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.91/2.83  tff(c_54, plain, (![B_34, A_33]: (k2_tarski(B_34, A_33)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.91/2.83  tff(c_197, plain, (![A_74, B_75]: (k3_tarski(k2_tarski(A_74, B_75))=k2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.91/2.83  tff(c_261, plain, (![A_79, B_80]: (k3_tarski(k2_tarski(A_79, B_80))=k2_xboole_0(B_80, A_79))), inference(superposition, [status(thm), theory('equality')], [c_54, c_197])).
% 7.91/2.83  tff(c_301, plain, (![B_85, A_86]: (k2_xboole_0(B_85, A_86)=k2_xboole_0(A_86, B_85))), inference(superposition, [status(thm), theory('equality')], [c_64, c_261])).
% 7.91/2.83  tff(c_360, plain, (![A_87]: (k2_xboole_0(k1_xboole_0, A_87)=A_87)), inference(superposition, [status(thm), theory('equality')], [c_301, c_40])).
% 7.91/2.83  tff(c_48, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.91/2.83  tff(c_151, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.91/2.83  tff(c_158, plain, (![A_29, B_30]: (k3_xboole_0(A_29, k2_xboole_0(A_29, B_30))=A_29)), inference(resolution, [status(thm)], [c_48, c_151])).
% 7.91/2.83  tff(c_372, plain, (![A_87]: (k3_xboole_0(k1_xboole_0, A_87)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_360, c_158])).
% 7.91/2.83  tff(c_699, plain, (![D_121, B_122, A_123]: (r2_hidden(D_121, B_122) | ~r2_hidden(D_121, k3_xboole_0(A_123, B_122)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.91/2.83  tff(c_836, plain, (![D_134, A_135]: (r2_hidden(D_134, A_135) | ~r2_hidden(D_134, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_372, c_699])).
% 7.91/2.83  tff(c_848, plain, (![A_135]: (r2_hidden('#skF_1'(k1_xboole_0), A_135) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_836])).
% 7.91/2.83  tff(c_1130, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_848])).
% 7.91/2.83  tff(c_287, plain, (![A_81, B_82]: (r2_hidden('#skF_4'(A_81, B_82), A_81) | r1_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.91/2.83  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.91/2.83  tff(c_295, plain, (![A_83, B_84]: (~v1_xboole_0(A_83) | r1_xboole_0(A_83, B_84))), inference(resolution, [status(thm)], [c_287, c_4])).
% 7.91/2.83  tff(c_50, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=A_31 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.91/2.83  tff(c_299, plain, (![A_83, B_84]: (k4_xboole_0(A_83, B_84)=A_83 | ~v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_295, c_50])).
% 7.91/2.83  tff(c_1137, plain, (![B_84]: (k4_xboole_0(k1_xboole_0, B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1130, c_299])).
% 7.91/2.83  tff(c_329, plain, (![A_86]: (k2_xboole_0(k1_xboole_0, A_86)=A_86)), inference(superposition, [status(thm), theory('equality')], [c_301, c_40])).
% 7.91/2.83  tff(c_610, plain, (![A_109, B_110]: (k4_xboole_0(k2_xboole_0(A_109, B_110), B_110)=k4_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.91/2.83  tff(c_619, plain, (![A_86]: (k4_xboole_0(k1_xboole_0, A_86)=k4_xboole_0(A_86, A_86))), inference(superposition, [status(thm), theory('equality')], [c_329, c_610])).
% 7.91/2.83  tff(c_1140, plain, (![A_86]: (k4_xboole_0(A_86, A_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1137, c_619])).
% 7.91/2.83  tff(c_36, plain, (![B_19]: (r1_tarski(B_19, B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.91/2.83  tff(c_159, plain, (![B_19]: (k3_xboole_0(B_19, B_19)=B_19)), inference(resolution, [status(thm)], [c_36, c_151])).
% 7.91/2.83  tff(c_668, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k3_xboole_0(A_116, B_117))=k4_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.91/2.83  tff(c_686, plain, (![B_19]: (k5_xboole_0(B_19, B_19)=k4_xboole_0(B_19, B_19))), inference(superposition, [status(thm), theory('equality')], [c_159, c_668])).
% 7.91/2.83  tff(c_1187, plain, (![B_19]: (k5_xboole_0(B_19, B_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1140, c_686])).
% 7.91/2.83  tff(c_56, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.91/2.83  tff(c_1286, plain, (![A_159, B_160, C_161]: (r1_tarski(k2_tarski(A_159, B_160), C_161) | ~r2_hidden(B_160, C_161) | ~r2_hidden(A_159, C_161))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.91/2.83  tff(c_2589, plain, (![A_257, C_258]: (r1_tarski(k1_tarski(A_257), C_258) | ~r2_hidden(A_257, C_258) | ~r2_hidden(A_257, C_258))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1286])).
% 7.91/2.83  tff(c_42, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.91/2.83  tff(c_10834, plain, (![A_554, C_555]: (k3_xboole_0(k1_tarski(A_554), C_555)=k1_tarski(A_554) | ~r2_hidden(A_554, C_555))), inference(resolution, [status(thm)], [c_2589, c_42])).
% 7.91/2.83  tff(c_38, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.91/2.83  tff(c_10927, plain, (![A_554, C_555]: (k5_xboole_0(k1_tarski(A_554), k1_tarski(A_554))=k4_xboole_0(k1_tarski(A_554), C_555) | ~r2_hidden(A_554, C_555))), inference(superposition, [status(thm), theory('equality')], [c_10834, c_38])).
% 7.91/2.83  tff(c_11282, plain, (![A_562, C_563]: (k4_xboole_0(k1_tarski(A_562), C_563)=k1_xboole_0 | ~r2_hidden(A_562, C_563))), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_10927])).
% 7.91/2.83  tff(c_44, plain, (![A_25, B_26]: (k2_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.91/2.83  tff(c_11369, plain, (![C_563, A_562]: (k2_xboole_0(C_563, k1_tarski(A_562))=k2_xboole_0(C_563, k1_xboole_0) | ~r2_hidden(A_562, C_563))), inference(superposition, [status(thm), theory('equality')], [c_11282, c_44])).
% 7.91/2.83  tff(c_11484, plain, (![C_567, A_568]: (k2_xboole_0(C_567, k1_tarski(A_568))=C_567 | ~r2_hidden(A_568, C_567))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_11369])).
% 7.91/2.83  tff(c_273, plain, (![B_46, A_45]: (k2_xboole_0(B_46, A_45)=k2_xboole_0(A_45, B_46))), inference(superposition, [status(thm), theory('equality')], [c_64, c_261])).
% 7.91/2.83  tff(c_72, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.91/2.83  tff(c_300, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_273, c_72])).
% 7.91/2.83  tff(c_11806, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_11484, c_300])).
% 7.91/2.83  tff(c_11903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_11806])).
% 7.91/2.83  tff(c_11906, plain, (![A_569]: (r2_hidden('#skF_1'(k1_xboole_0), A_569))), inference(splitRight, [status(thm)], [c_848])).
% 7.91/2.83  tff(c_11935, plain, (![A_569]: (~v1_xboole_0(A_569))), inference(resolution, [status(thm)], [c_11906, c_4])).
% 7.91/2.83  tff(c_143, plain, (![B_60, A_61]: (~r2_hidden(B_60, A_61) | ~r2_hidden(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.91/2.83  tff(c_148, plain, (![A_3]: (~r2_hidden(A_3, '#skF_1'(A_3)) | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_143])).
% 7.91/2.83  tff(c_11933, plain, (v1_xboole_0('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_11906, c_148])).
% 7.91/2.83  tff(c_11948, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11935, c_11933])).
% 7.91/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.83  
% 7.91/2.83  Inference rules
% 7.91/2.83  ----------------------
% 7.91/2.83  #Ref     : 0
% 7.91/2.83  #Sup     : 3047
% 7.91/2.83  #Fact    : 0
% 7.91/2.83  #Define  : 0
% 7.91/2.83  #Split   : 2
% 7.91/2.83  #Chain   : 0
% 7.91/2.83  #Close   : 0
% 7.91/2.83  
% 7.91/2.83  Ordering : KBO
% 7.91/2.83  
% 7.91/2.83  Simplification rules
% 7.91/2.83  ----------------------
% 7.91/2.83  #Subsume      : 1200
% 7.91/2.83  #Demod        : 1731
% 7.91/2.83  #Tautology    : 1043
% 7.91/2.83  #SimpNegUnit  : 39
% 7.91/2.83  #BackRed      : 12
% 7.91/2.83  
% 7.91/2.83  #Partial instantiations: 0
% 7.91/2.83  #Strategies tried      : 1
% 7.91/2.83  
% 7.91/2.83  Timing (in seconds)
% 7.91/2.83  ----------------------
% 7.91/2.83  Preprocessing        : 0.34
% 7.91/2.83  Parsing              : 0.18
% 7.91/2.83  CNF conversion       : 0.02
% 7.91/2.83  Main loop            : 1.71
% 7.91/2.83  Inferencing          : 0.47
% 7.91/2.83  Reduction            : 0.74
% 7.91/2.83  Demodulation         : 0.58
% 7.91/2.83  BG Simplification    : 0.05
% 7.91/2.83  Subsumption          : 0.35
% 7.91/2.83  Abstraction          : 0.07
% 7.91/2.83  MUC search           : 0.00
% 7.91/2.83  Cooper               : 0.00
% 7.91/2.83  Total                : 2.09
% 7.91/2.83  Index Insertion      : 0.00
% 7.91/2.83  Index Deletion       : 0.00
% 7.91/2.83  Index Matching       : 0.00
% 7.91/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
