%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:55 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 126 expanded)
%              Number of leaves         :   39 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :   97 ( 148 expanded)
%              Number of equality atoms :   40 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_85,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_97,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_66,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    ! [A_22] : k2_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_200,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_209,plain,(
    ! [A_31] : k3_tarski(k1_tarski(A_31)) = k2_xboole_0(A_31,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_200])).

tff(c_46,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_340,plain,(
    ! [A_69,B_70] :
      ( r2_hidden(A_69,B_70)
      | ~ r1_tarski(k1_tarski(A_69),B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_367,plain,(
    ! [A_73,B_74] : r2_hidden(A_73,k2_xboole_0(k1_tarski(A_73),B_74)) ),
    inference(resolution,[status(thm)],[c_46,c_340])).

tff(c_374,plain,(
    ! [A_73] : r2_hidden(A_73,k3_tarski(k1_tarski(k1_tarski(A_73)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_367])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_98,plain,(
    ! [B_52,A_53] : k2_xboole_0(B_52,A_53) = k2_xboole_0(A_53,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_120,plain,(
    ! [A_53] : k2_xboole_0(k1_xboole_0,A_53) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_40])).

tff(c_635,plain,(
    ! [A_104,B_105] : k2_xboole_0(A_104,k4_xboole_0(B_105,A_104)) = k2_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_659,plain,(
    ! [B_105] : k4_xboole_0(B_105,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_120])).

tff(c_682,plain,(
    ! [B_105] : k4_xboole_0(B_105,k1_xboole_0) = B_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_659])).

tff(c_742,plain,(
    ! [D_108,B_109,A_110] :
      ( ~ r2_hidden(D_108,B_109)
      | ~ r2_hidden(D_108,k4_xboole_0(A_110,B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_779,plain,(
    ! [D_111,B_112] :
      ( ~ r2_hidden(D_111,k1_xboole_0)
      | ~ r2_hidden(D_111,B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_742])).

tff(c_791,plain,(
    ! [B_112] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),B_112)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_779])).

tff(c_815,plain,(
    ! [B_116] : ~ r2_hidden('#skF_1'(k1_xboole_0),B_116) ),
    inference(splitLeft,[status(thm)],[c_791])).

tff(c_833,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_374,c_815])).

tff(c_834,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_791])).

tff(c_520,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_4'(A_89,B_90),A_89)
      | r1_xboole_0(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_524,plain,(
    ! [A_89,B_90] :
      ( ~ v1_xboole_0(A_89)
      | r1_xboole_0(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_520,c_4])).

tff(c_1012,plain,(
    ! [A_132,B_133] :
      ( k4_xboole_0(k2_xboole_0(A_132,B_133),B_133) = A_132
      | ~ r1_xboole_0(A_132,B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1066,plain,(
    ! [A_134] :
      ( k4_xboole_0(A_134,A_134) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_1012])).

tff(c_1072,plain,(
    ! [B_90] :
      ( k4_xboole_0(B_90,B_90) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_524,c_1066])).

tff(c_1076,plain,(
    ! [B_90] : k4_xboole_0(B_90,B_90) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_1072])).

tff(c_36,plain,(
    ! [B_19] : r1_tarski(B_19,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_251,plain,(
    ! [A_62,B_63] :
      ( k3_xboole_0(A_62,B_63) = A_62
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_267,plain,(
    ! [B_19] : k3_xboole_0(B_19,B_19) = B_19 ),
    inference(resolution,[status(thm)],[c_36,c_251])).

tff(c_560,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k3_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_581,plain,(
    ! [B_19] : k5_xboole_0(B_19,B_19) = k4_xboole_0(B_19,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_560])).

tff(c_1079,plain,(
    ! [B_19] : k5_xboole_0(B_19,B_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1076,c_581])).

tff(c_389,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k1_tarski(A_75),B_76)
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3365,plain,(
    ! [A_212,B_213] :
      ( k3_xboole_0(k1_tarski(A_212),B_213) = k1_tarski(A_212)
      | ~ r2_hidden(A_212,B_213) ) ),
    inference(resolution,[status(thm)],[c_389,c_42])).

tff(c_38,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3371,plain,(
    ! [A_212,B_213] :
      ( k5_xboole_0(k1_tarski(A_212),k1_tarski(A_212)) = k4_xboole_0(k1_tarski(A_212),B_213)
      | ~ r2_hidden(A_212,B_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3365,c_38])).

tff(c_3420,plain,(
    ! [A_214,B_215] :
      ( k4_xboole_0(k1_tarski(A_214),B_215) = k1_xboole_0
      | ~ r2_hidden(A_214,B_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_3371])).

tff(c_44,plain,(
    ! [A_25,B_26] : k2_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3463,plain,(
    ! [B_215,A_214] :
      ( k2_xboole_0(B_215,k1_tarski(A_214)) = k2_xboole_0(B_215,k1_xboole_0)
      | ~ r2_hidden(A_214,B_215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3420,c_44])).

tff(c_3508,plain,(
    ! [B_216,A_217] :
      ( k2_xboole_0(B_216,k1_tarski(A_217)) = B_216
      | ~ r2_hidden(A_217,B_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3463])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_68,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_3632,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3508,c_68])).

tff(c_3700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.77  
% 4.13/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.77  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 4.13/1.77  
% 4.13/1.77  %Foreground sorts:
% 4.13/1.77  
% 4.13/1.77  
% 4.13/1.77  %Background operators:
% 4.13/1.77  
% 4.13/1.77  
% 4.13/1.77  %Foreground operators:
% 4.13/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.13/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.13/1.77  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.13/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.13/1.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.13/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.13/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.13/1.77  tff('#skF_5', type, '#skF_5': $i).
% 4.13/1.77  tff('#skF_6', type, '#skF_6': $i).
% 4.13/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.13/1.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.13/1.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.13/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.13/1.77  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.13/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.13/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.13/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.13/1.77  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.13/1.77  
% 4.29/1.79  tff(f_102, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.29/1.79  tff(f_71, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.29/1.79  tff(f_85, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.29/1.79  tff(f_97, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.29/1.79  tff(f_79, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.29/1.79  tff(f_95, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.29/1.79  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.29/1.79  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.29/1.79  tff(f_77, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.29/1.79  tff(f_43, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.29/1.79  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.29/1.79  tff(f_83, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 4.29/1.79  tff(f_67, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.29/1.79  tff(f_75, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.29/1.79  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.29/1.79  tff(c_66, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.29/1.79  tff(c_40, plain, (![A_22]: (k2_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.29/1.79  tff(c_50, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.29/1.79  tff(c_200, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.29/1.79  tff(c_209, plain, (![A_31]: (k3_tarski(k1_tarski(A_31))=k2_xboole_0(A_31, A_31))), inference(superposition, [status(thm), theory('equality')], [c_50, c_200])).
% 4.29/1.79  tff(c_46, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.29/1.79  tff(c_340, plain, (![A_69, B_70]: (r2_hidden(A_69, B_70) | ~r1_tarski(k1_tarski(A_69), B_70))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.29/1.79  tff(c_367, plain, (![A_73, B_74]: (r2_hidden(A_73, k2_xboole_0(k1_tarski(A_73), B_74)))), inference(resolution, [status(thm)], [c_46, c_340])).
% 4.29/1.79  tff(c_374, plain, (![A_73]: (r2_hidden(A_73, k3_tarski(k1_tarski(k1_tarski(A_73)))))), inference(superposition, [status(thm), theory('equality')], [c_209, c_367])).
% 4.29/1.79  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.29/1.79  tff(c_98, plain, (![B_52, A_53]: (k2_xboole_0(B_52, A_53)=k2_xboole_0(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.29/1.79  tff(c_120, plain, (![A_53]: (k2_xboole_0(k1_xboole_0, A_53)=A_53)), inference(superposition, [status(thm), theory('equality')], [c_98, c_40])).
% 4.29/1.79  tff(c_635, plain, (![A_104, B_105]: (k2_xboole_0(A_104, k4_xboole_0(B_105, A_104))=k2_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.29/1.79  tff(c_659, plain, (![B_105]: (k4_xboole_0(B_105, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_105))), inference(superposition, [status(thm), theory('equality')], [c_635, c_120])).
% 4.29/1.79  tff(c_682, plain, (![B_105]: (k4_xboole_0(B_105, k1_xboole_0)=B_105)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_659])).
% 4.29/1.79  tff(c_742, plain, (![D_108, B_109, A_110]: (~r2_hidden(D_108, B_109) | ~r2_hidden(D_108, k4_xboole_0(A_110, B_109)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.29/1.79  tff(c_779, plain, (![D_111, B_112]: (~r2_hidden(D_111, k1_xboole_0) | ~r2_hidden(D_111, B_112))), inference(superposition, [status(thm), theory('equality')], [c_682, c_742])).
% 4.29/1.79  tff(c_791, plain, (![B_112]: (~r2_hidden('#skF_1'(k1_xboole_0), B_112) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_779])).
% 4.29/1.79  tff(c_815, plain, (![B_116]: (~r2_hidden('#skF_1'(k1_xboole_0), B_116))), inference(splitLeft, [status(thm)], [c_791])).
% 4.29/1.79  tff(c_833, plain, $false, inference(resolution, [status(thm)], [c_374, c_815])).
% 4.29/1.79  tff(c_834, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_791])).
% 4.29/1.79  tff(c_520, plain, (![A_89, B_90]: (r2_hidden('#skF_4'(A_89, B_90), A_89) | r1_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.29/1.79  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.29/1.79  tff(c_524, plain, (![A_89, B_90]: (~v1_xboole_0(A_89) | r1_xboole_0(A_89, B_90))), inference(resolution, [status(thm)], [c_520, c_4])).
% 4.29/1.79  tff(c_1012, plain, (![A_132, B_133]: (k4_xboole_0(k2_xboole_0(A_132, B_133), B_133)=A_132 | ~r1_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.29/1.79  tff(c_1066, plain, (![A_134]: (k4_xboole_0(A_134, A_134)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_134))), inference(superposition, [status(thm), theory('equality')], [c_120, c_1012])).
% 4.29/1.79  tff(c_1072, plain, (![B_90]: (k4_xboole_0(B_90, B_90)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_524, c_1066])).
% 4.29/1.79  tff(c_1076, plain, (![B_90]: (k4_xboole_0(B_90, B_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_834, c_1072])).
% 4.29/1.79  tff(c_36, plain, (![B_19]: (r1_tarski(B_19, B_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.29/1.79  tff(c_251, plain, (![A_62, B_63]: (k3_xboole_0(A_62, B_63)=A_62 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.29/1.79  tff(c_267, plain, (![B_19]: (k3_xboole_0(B_19, B_19)=B_19)), inference(resolution, [status(thm)], [c_36, c_251])).
% 4.29/1.79  tff(c_560, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k3_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.29/1.79  tff(c_581, plain, (![B_19]: (k5_xboole_0(B_19, B_19)=k4_xboole_0(B_19, B_19))), inference(superposition, [status(thm), theory('equality')], [c_267, c_560])).
% 4.29/1.79  tff(c_1079, plain, (![B_19]: (k5_xboole_0(B_19, B_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1076, c_581])).
% 4.29/1.79  tff(c_389, plain, (![A_75, B_76]: (r1_tarski(k1_tarski(A_75), B_76) | ~r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.29/1.79  tff(c_42, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.29/1.79  tff(c_3365, plain, (![A_212, B_213]: (k3_xboole_0(k1_tarski(A_212), B_213)=k1_tarski(A_212) | ~r2_hidden(A_212, B_213))), inference(resolution, [status(thm)], [c_389, c_42])).
% 4.29/1.79  tff(c_38, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.29/1.79  tff(c_3371, plain, (![A_212, B_213]: (k5_xboole_0(k1_tarski(A_212), k1_tarski(A_212))=k4_xboole_0(k1_tarski(A_212), B_213) | ~r2_hidden(A_212, B_213))), inference(superposition, [status(thm), theory('equality')], [c_3365, c_38])).
% 4.29/1.79  tff(c_3420, plain, (![A_214, B_215]: (k4_xboole_0(k1_tarski(A_214), B_215)=k1_xboole_0 | ~r2_hidden(A_214, B_215))), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_3371])).
% 4.29/1.79  tff(c_44, plain, (![A_25, B_26]: (k2_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.29/1.79  tff(c_3463, plain, (![B_215, A_214]: (k2_xboole_0(B_215, k1_tarski(A_214))=k2_xboole_0(B_215, k1_xboole_0) | ~r2_hidden(A_214, B_215))), inference(superposition, [status(thm), theory('equality')], [c_3420, c_44])).
% 4.29/1.79  tff(c_3508, plain, (![B_216, A_217]: (k2_xboole_0(B_216, k1_tarski(A_217))=B_216 | ~r2_hidden(A_217, B_216))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3463])).
% 4.29/1.79  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.29/1.79  tff(c_64, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.29/1.79  tff(c_68, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_64])).
% 4.29/1.79  tff(c_3632, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3508, c_68])).
% 4.29/1.79  tff(c_3700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_3632])).
% 4.29/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.79  
% 4.29/1.79  Inference rules
% 4.29/1.79  ----------------------
% 4.29/1.79  #Ref     : 0
% 4.29/1.79  #Sup     : 876
% 4.29/1.79  #Fact    : 0
% 4.29/1.79  #Define  : 0
% 4.29/1.79  #Split   : 1
% 4.29/1.79  #Chain   : 0
% 4.29/1.79  #Close   : 0
% 4.29/1.79  
% 4.29/1.79  Ordering : KBO
% 4.29/1.79  
% 4.29/1.79  Simplification rules
% 4.29/1.79  ----------------------
% 4.29/1.79  #Subsume      : 145
% 4.29/1.79  #Demod        : 650
% 4.29/1.79  #Tautology    : 517
% 4.29/1.79  #SimpNegUnit  : 0
% 4.29/1.79  #BackRed      : 8
% 4.29/1.79  
% 4.29/1.79  #Partial instantiations: 0
% 4.29/1.79  #Strategies tried      : 1
% 4.29/1.79  
% 4.29/1.79  Timing (in seconds)
% 4.29/1.79  ----------------------
% 4.29/1.79  Preprocessing        : 0.34
% 4.29/1.79  Parsing              : 0.17
% 4.29/1.79  CNF conversion       : 0.02
% 4.29/1.79  Main loop            : 0.67
% 4.29/1.79  Inferencing          : 0.22
% 4.29/1.79  Reduction            : 0.28
% 4.29/1.79  Demodulation         : 0.23
% 4.29/1.79  BG Simplification    : 0.03
% 4.29/1.79  Subsumption          : 0.11
% 4.29/1.79  Abstraction          : 0.04
% 4.29/1.79  MUC search           : 0.00
% 4.29/1.79  Cooper               : 0.00
% 4.29/1.79  Total                : 1.04
% 4.29/1.79  Index Insertion      : 0.00
% 4.29/1.79  Index Deletion       : 0.00
% 4.29/1.79  Index Matching       : 0.00
% 4.29/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
