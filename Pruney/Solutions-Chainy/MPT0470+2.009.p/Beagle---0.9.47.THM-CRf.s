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
% DateTime   : Thu Dec  3 09:59:02 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 120 expanded)
%              Number of leaves         :   36 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  136 ( 200 expanded)
%              Number of equality atoms :   35 (  55 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_103,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_54,plain,
    ( k5_relat_1('#skF_8',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_85,plain,(
    k5_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_56,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_46] :
      ( v1_relat_1(A_46)
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_71,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_67])).

tff(c_40,plain,(
    ! [A_33,B_34] :
      ( v1_relat_1(k5_relat_1(A_33,B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_127,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_1'(A_58,B_59),A_58)
      | r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [A_50,B_51] : ~ r2_hidden(A_50,k2_zfmisc_1(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_107,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_101])).

tff(c_132,plain,(
    ! [B_59] : r1_tarski(k1_xboole_0,B_59) ),
    inference(resolution,[status(thm)],[c_127,c_107])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_169,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_72,B_73)),k1_relat_1(A_72))
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_174,plain,(
    ! [B_73] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_73)),k1_xboole_0)
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_169])).

tff(c_178,plain,(
    ! [B_74] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_74)),k1_xboole_0)
      | ~ v1_relat_1(B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_174])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_183,plain,(
    ! [B_74] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_74)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(k5_relat_1(k1_xboole_0,B_74)))
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_178,c_12])).

tff(c_188,plain,(
    ! [B_75] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_75)) = k1_xboole_0
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_183])).

tff(c_42,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(k1_relat_1(A_35))
      | ~ v1_relat_1(A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_203,plain,(
    ! [B_75] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_75))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_75))
      | ~ v1_relat_1(B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_42])).

tff(c_254,plain,(
    ! [B_80] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_80))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_203])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_263,plain,(
    ! [B_81] :
      ( k5_relat_1(k1_xboole_0,B_81) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(resolution,[status(thm)],[c_254,c_10])).

tff(c_267,plain,(
    ! [B_34] :
      ( k5_relat_1(k1_xboole_0,B_34) = k1_xboole_0
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_263])).

tff(c_287,plain,(
    ! [B_83] :
      ( k5_relat_1(k1_xboole_0,B_83) = k1_xboole_0
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_267])).

tff(c_296,plain,(
    k5_relat_1(k1_xboole_0,'#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_287])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_296])).

tff(c_303,plain,(
    k5_relat_1('#skF_8',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_324,plain,(
    ! [A_85,B_86] : ~ r2_hidden(A_85,k2_zfmisc_1(A_85,B_86)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_330,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_324])).

tff(c_363,plain,(
    ! [A_97,B_98] :
      ( r2_hidden('#skF_1'(A_97,B_98),A_97)
      | r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_374,plain,(
    ! [B_98] : r1_tarski(k1_xboole_0,B_98) ),
    inference(resolution,[status(thm)],[c_363,c_330])).

tff(c_50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_484,plain,(
    ! [A_113,B_114] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_113,B_114)),k2_relat_1(B_114))
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_492,plain,(
    ! [A_113] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_113,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_484])).

tff(c_498,plain,(
    ! [A_115] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_115,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_492])).

tff(c_503,plain,(
    ! [A_115] :
      ( k2_relat_1(k5_relat_1(A_115,k1_xboole_0)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(A_115,k1_xboole_0)))
      | ~ v1_relat_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_498,c_12])).

tff(c_508,plain,(
    ! [A_116] :
      ( k2_relat_1(k5_relat_1(A_116,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_503])).

tff(c_397,plain,(
    ! [A_107] :
      ( k1_xboole_0 = A_107
      | r2_hidden(k4_tarski('#skF_6'(A_107),'#skF_7'(A_107)),A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    ! [C_29,A_14,D_32] :
      ( r2_hidden(C_29,k2_relat_1(A_14))
      | ~ r2_hidden(k4_tarski(D_32,C_29),A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_407,plain,(
    ! [A_107] :
      ( r2_hidden('#skF_7'(A_107),k2_relat_1(A_107))
      | k1_xboole_0 = A_107
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_397,c_30])).

tff(c_523,plain,(
    ! [A_116] :
      ( r2_hidden('#skF_7'(k5_relat_1(A_116,k1_xboole_0)),k1_xboole_0)
      | k5_relat_1(A_116,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_116,k1_xboole_0))
      | ~ v1_relat_1(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_407])).

tff(c_547,plain,(
    ! [A_118] :
      ( k5_relat_1(A_118,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_118,k1_xboole_0))
      | ~ v1_relat_1(A_118) ) ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_523])).

tff(c_551,plain,(
    ! [A_33] :
      ( k5_relat_1(A_33,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_33) ) ),
    inference(resolution,[status(thm)],[c_40,c_547])).

tff(c_577,plain,(
    ! [A_121] :
      ( k5_relat_1(A_121,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_551])).

tff(c_586,plain,(
    k5_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_577])).

tff(c_592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:34:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.68  
% 3.04/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.68  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4
% 3.04/1.68  
% 3.04/1.68  %Foreground sorts:
% 3.04/1.68  
% 3.04/1.68  
% 3.04/1.68  %Background operators:
% 3.04/1.68  
% 3.04/1.68  
% 3.04/1.68  %Foreground operators:
% 3.04/1.68  tff('#skF_7', type, '#skF_7': $i > $i).
% 3.04/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.04/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.04/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.04/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.04/1.68  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.04/1.68  tff('#skF_8', type, '#skF_8': $i).
% 3.04/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.04/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.04/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.04/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.04/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.04/1.68  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.04/1.68  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.04/1.68  
% 3.29/1.71  tff(f_110, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.29/1.71  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.29/1.71  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.29/1.71  tff(f_70, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.29/1.71  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.29/1.71  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.29/1.71  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.29/1.71  tff(f_103, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.29/1.71  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.29/1.71  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.29/1.71  tff(f_78, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.29/1.71  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.29/1.71  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.29/1.71  tff(f_100, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 3.29/1.71  tff(f_64, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 3.29/1.71  tff(c_54, plain, (k5_relat_1('#skF_8', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.29/1.71  tff(c_85, plain, (k5_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 3.29/1.71  tff(c_56, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.29/1.71  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.29/1.71  tff(c_67, plain, (![A_46]: (v1_relat_1(A_46) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.71  tff(c_71, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_67])).
% 3.29/1.71  tff(c_40, plain, (![A_33, B_34]: (v1_relat_1(k5_relat_1(A_33, B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.29/1.71  tff(c_127, plain, (![A_58, B_59]: (r2_hidden('#skF_1'(A_58, B_59), A_58) | r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.71  tff(c_20, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.29/1.71  tff(c_101, plain, (![A_50, B_51]: (~r2_hidden(A_50, k2_zfmisc_1(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.29/1.71  tff(c_107, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_101])).
% 3.29/1.71  tff(c_132, plain, (![B_59]: (r1_tarski(k1_xboole_0, B_59))), inference(resolution, [status(thm)], [c_127, c_107])).
% 3.29/1.71  tff(c_52, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.29/1.71  tff(c_169, plain, (![A_72, B_73]: (r1_tarski(k1_relat_1(k5_relat_1(A_72, B_73)), k1_relat_1(A_72)) | ~v1_relat_1(B_73) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.29/1.71  tff(c_174, plain, (![B_73]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_73)), k1_xboole_0) | ~v1_relat_1(B_73) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_169])).
% 3.29/1.71  tff(c_178, plain, (![B_74]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_74)), k1_xboole_0) | ~v1_relat_1(B_74))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_174])).
% 3.29/1.71  tff(c_12, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.71  tff(c_183, plain, (![B_74]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_74))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_relat_1(k5_relat_1(k1_xboole_0, B_74))) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_178, c_12])).
% 3.29/1.71  tff(c_188, plain, (![B_75]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_75))=k1_xboole_0 | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_183])).
% 3.29/1.71  tff(c_42, plain, (![A_35]: (~v1_xboole_0(k1_relat_1(A_35)) | ~v1_relat_1(A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.29/1.71  tff(c_203, plain, (![B_75]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_75)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_75)) | ~v1_relat_1(B_75))), inference(superposition, [status(thm), theory('equality')], [c_188, c_42])).
% 3.29/1.71  tff(c_254, plain, (![B_80]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_80)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_80)) | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_203])).
% 3.29/1.71  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.71  tff(c_263, plain, (![B_81]: (k5_relat_1(k1_xboole_0, B_81)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_81)) | ~v1_relat_1(B_81))), inference(resolution, [status(thm)], [c_254, c_10])).
% 3.29/1.71  tff(c_267, plain, (![B_34]: (k5_relat_1(k1_xboole_0, B_34)=k1_xboole_0 | ~v1_relat_1(B_34) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_263])).
% 3.29/1.71  tff(c_287, plain, (![B_83]: (k5_relat_1(k1_xboole_0, B_83)=k1_xboole_0 | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_267])).
% 3.29/1.71  tff(c_296, plain, (k5_relat_1(k1_xboole_0, '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_287])).
% 3.29/1.71  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_296])).
% 3.29/1.71  tff(c_303, plain, (k5_relat_1('#skF_8', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.29/1.71  tff(c_324, plain, (![A_85, B_86]: (~r2_hidden(A_85, k2_zfmisc_1(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.29/1.71  tff(c_330, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_324])).
% 3.29/1.71  tff(c_363, plain, (![A_97, B_98]: (r2_hidden('#skF_1'(A_97, B_98), A_97) | r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.71  tff(c_374, plain, (![B_98]: (r1_tarski(k1_xboole_0, B_98))), inference(resolution, [status(thm)], [c_363, c_330])).
% 3.29/1.71  tff(c_50, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.29/1.71  tff(c_484, plain, (![A_113, B_114]: (r1_tarski(k2_relat_1(k5_relat_1(A_113, B_114)), k2_relat_1(B_114)) | ~v1_relat_1(B_114) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.29/1.71  tff(c_492, plain, (![A_113]: (r1_tarski(k2_relat_1(k5_relat_1(A_113, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_113))), inference(superposition, [status(thm), theory('equality')], [c_50, c_484])).
% 3.29/1.71  tff(c_498, plain, (![A_115]: (r1_tarski(k2_relat_1(k5_relat_1(A_115, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_492])).
% 3.29/1.71  tff(c_503, plain, (![A_115]: (k2_relat_1(k5_relat_1(A_115, k1_xboole_0))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_relat_1(k5_relat_1(A_115, k1_xboole_0))) | ~v1_relat_1(A_115))), inference(resolution, [status(thm)], [c_498, c_12])).
% 3.29/1.71  tff(c_508, plain, (![A_116]: (k2_relat_1(k5_relat_1(A_116, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_503])).
% 3.29/1.71  tff(c_397, plain, (![A_107]: (k1_xboole_0=A_107 | r2_hidden(k4_tarski('#skF_6'(A_107), '#skF_7'(A_107)), A_107) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.29/1.71  tff(c_30, plain, (![C_29, A_14, D_32]: (r2_hidden(C_29, k2_relat_1(A_14)) | ~r2_hidden(k4_tarski(D_32, C_29), A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.29/1.71  tff(c_407, plain, (![A_107]: (r2_hidden('#skF_7'(A_107), k2_relat_1(A_107)) | k1_xboole_0=A_107 | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_397, c_30])).
% 3.29/1.71  tff(c_523, plain, (![A_116]: (r2_hidden('#skF_7'(k5_relat_1(A_116, k1_xboole_0)), k1_xboole_0) | k5_relat_1(A_116, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_116, k1_xboole_0)) | ~v1_relat_1(A_116))), inference(superposition, [status(thm), theory('equality')], [c_508, c_407])).
% 3.29/1.71  tff(c_547, plain, (![A_118]: (k5_relat_1(A_118, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_118, k1_xboole_0)) | ~v1_relat_1(A_118))), inference(negUnitSimplification, [status(thm)], [c_330, c_523])).
% 3.29/1.71  tff(c_551, plain, (![A_33]: (k5_relat_1(A_33, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_33))), inference(resolution, [status(thm)], [c_40, c_547])).
% 3.29/1.71  tff(c_577, plain, (![A_121]: (k5_relat_1(A_121, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_121))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_551])).
% 3.29/1.71  tff(c_586, plain, (k5_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_577])).
% 3.29/1.71  tff(c_592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_303, c_586])).
% 3.29/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.71  
% 3.29/1.71  Inference rules
% 3.29/1.71  ----------------------
% 3.29/1.71  #Ref     : 0
% 3.29/1.71  #Sup     : 112
% 3.29/1.71  #Fact    : 0
% 3.29/1.71  #Define  : 0
% 3.29/1.71  #Split   : 1
% 3.29/1.71  #Chain   : 0
% 3.29/1.71  #Close   : 0
% 3.29/1.71  
% 3.29/1.71  Ordering : KBO
% 3.29/1.71  
% 3.29/1.71  Simplification rules
% 3.29/1.71  ----------------------
% 3.29/1.71  #Subsume      : 10
% 3.29/1.71  #Demod        : 65
% 3.29/1.71  #Tautology    : 60
% 3.29/1.71  #SimpNegUnit  : 5
% 3.29/1.71  #BackRed      : 0
% 3.29/1.71  
% 3.29/1.71  #Partial instantiations: 0
% 3.29/1.71  #Strategies tried      : 1
% 3.29/1.71  
% 3.29/1.71  Timing (in seconds)
% 3.29/1.71  ----------------------
% 3.29/1.71  Preprocessing        : 0.45
% 3.29/1.71  Parsing              : 0.24
% 3.29/1.71  CNF conversion       : 0.04
% 3.29/1.71  Main loop            : 0.45
% 3.29/1.71  Inferencing          : 0.17
% 3.29/1.71  Reduction            : 0.12
% 3.29/1.71  Demodulation         : 0.09
% 3.29/1.71  BG Simplification    : 0.03
% 3.29/1.71  Subsumption          : 0.09
% 3.29/1.71  Abstraction          : 0.02
% 3.29/1.71  MUC search           : 0.00
% 3.29/1.71  Cooper               : 0.00
% 3.29/1.71  Total                : 0.97
% 3.29/1.71  Index Insertion      : 0.00
% 3.29/1.72  Index Deletion       : 0.00
% 3.29/1.72  Index Matching       : 0.00
% 3.29/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
