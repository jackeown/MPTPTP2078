%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:13 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   63 (  97 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 150 expanded)
%              Number of equality atoms :   37 (  60 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_28,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_38,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_69,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    ! [A_32] :
      ( v1_relat_1(A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_50])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( v1_relat_1(k5_relat_1(A_22,B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_20,plain,(
    ! [B_18] : k2_zfmisc_1(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_161,plain,(
    ! [A_57,B_58] :
      ( k1_relat_1(k5_relat_1(A_57,B_58)) = k1_relat_1(A_57)
      | ~ r1_tarski(k2_relat_1(A_57),k1_relat_1(B_58))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_167,plain,(
    ! [B_58] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_58)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_58))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_161])).

tff(c_172,plain,(
    ! [B_59] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_59)) = k1_xboole_0
      | ~ v1_relat_1(B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6,c_36,c_167])).

tff(c_28,plain,(
    ! [A_24] :
      ( k3_xboole_0(A_24,k2_zfmisc_1(k1_relat_1(A_24),k2_relat_1(A_24))) = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_181,plain,(
    ! [B_59] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_59),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_59)))) = k5_relat_1(k1_xboole_0,B_59)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_28])).

tff(c_188,plain,(
    ! [B_60] :
      ( k5_relat_1(k1_xboole_0,B_60) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_60))
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_20,c_181])).

tff(c_192,plain,(
    ! [B_23] :
      ( k5_relat_1(k1_xboole_0,B_23) = k1_xboole_0
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_188])).

tff(c_196,plain,(
    ! [B_61] :
      ( k5_relat_1(k1_xboole_0,B_61) = k1_xboole_0
      | ~ v1_relat_1(B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_192])).

tff(c_205,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_196])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_205])).

tff(c_212,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_18,plain,(
    ! [A_17] : k2_zfmisc_1(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_373,plain,(
    ! [B_89,A_90] :
      ( k2_relat_1(k5_relat_1(B_89,A_90)) = k2_relat_1(A_90)
      | ~ r1_tarski(k1_relat_1(A_90),k2_relat_1(B_89))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_379,plain,(
    ! [B_89] :
      ( k2_relat_1(k5_relat_1(B_89,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_89))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_373])).

tff(c_403,plain,(
    ! [B_91] :
      ( k2_relat_1(k5_relat_1(B_91,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6,c_34,c_379])).

tff(c_415,plain,(
    ! [B_91] :
      ( k3_xboole_0(k5_relat_1(B_91,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_91,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_91,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_91,k1_xboole_0))
      | ~ v1_relat_1(B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_28])).

tff(c_429,plain,(
    ! [B_92] :
      ( k5_relat_1(B_92,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_92,k1_xboole_0))
      | ~ v1_relat_1(B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_18,c_415])).

tff(c_436,plain,(
    ! [A_22] :
      ( k5_relat_1(A_22,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_22) ) ),
    inference(resolution,[status(thm)],[c_26,c_429])).

tff(c_442,plain,(
    ! [A_93] :
      ( k5_relat_1(A_93,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_436])).

tff(c_451,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_442])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:23:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.32  
% 2.11/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.32  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.11/1.32  
% 2.11/1.32  %Foreground sorts:
% 2.11/1.32  
% 2.11/1.32  
% 2.11/1.32  %Background operators:
% 2.11/1.32  
% 2.11/1.32  
% 2.11/1.32  %Foreground operators:
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.11/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.11/1.32  
% 2.41/1.33  tff(f_88, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.41/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.41/1.33  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.41/1.33  tff(f_56, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.41/1.33  tff(f_28, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.41/1.33  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.41/1.33  tff(f_30, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.41/1.33  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.41/1.33  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.41/1.33  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 2.41/1.33  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.41/1.33  tff(c_38, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.41/1.33  tff(c_69, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 2.41/1.33  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.41/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.41/1.33  tff(c_50, plain, (![A_32]: (v1_relat_1(A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.33  tff(c_54, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_50])).
% 2.41/1.33  tff(c_26, plain, (![A_22, B_23]: (v1_relat_1(k5_relat_1(A_22, B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.41/1.33  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.41/1.33  tff(c_20, plain, (![B_18]: (k2_zfmisc_1(k1_xboole_0, B_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.41/1.33  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.41/1.33  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.41/1.33  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.41/1.33  tff(c_161, plain, (![A_57, B_58]: (k1_relat_1(k5_relat_1(A_57, B_58))=k1_relat_1(A_57) | ~r1_tarski(k2_relat_1(A_57), k1_relat_1(B_58)) | ~v1_relat_1(B_58) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.41/1.33  tff(c_167, plain, (![B_58]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_58))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_58)) | ~v1_relat_1(B_58) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_161])).
% 2.41/1.33  tff(c_172, plain, (![B_59]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_59))=k1_xboole_0 | ~v1_relat_1(B_59))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6, c_36, c_167])).
% 2.41/1.33  tff(c_28, plain, (![A_24]: (k3_xboole_0(A_24, k2_zfmisc_1(k1_relat_1(A_24), k2_relat_1(A_24)))=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.41/1.33  tff(c_181, plain, (![B_59]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_59), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_59))))=k5_relat_1(k1_xboole_0, B_59) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_59)) | ~v1_relat_1(B_59))), inference(superposition, [status(thm), theory('equality')], [c_172, c_28])).
% 2.41/1.33  tff(c_188, plain, (![B_60]: (k5_relat_1(k1_xboole_0, B_60)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_60)) | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_20, c_181])).
% 2.41/1.33  tff(c_192, plain, (![B_23]: (k5_relat_1(k1_xboole_0, B_23)=k1_xboole_0 | ~v1_relat_1(B_23) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_188])).
% 2.41/1.33  tff(c_196, plain, (![B_61]: (k5_relat_1(k1_xboole_0, B_61)=k1_xboole_0 | ~v1_relat_1(B_61))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_192])).
% 2.41/1.33  tff(c_205, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_196])).
% 2.41/1.33  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_205])).
% 2.41/1.33  tff(c_212, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.41/1.33  tff(c_18, plain, (![A_17]: (k2_zfmisc_1(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.41/1.33  tff(c_373, plain, (![B_89, A_90]: (k2_relat_1(k5_relat_1(B_89, A_90))=k2_relat_1(A_90) | ~r1_tarski(k1_relat_1(A_90), k2_relat_1(B_89)) | ~v1_relat_1(B_89) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.41/1.33  tff(c_379, plain, (![B_89]: (k2_relat_1(k5_relat_1(B_89, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_89)) | ~v1_relat_1(B_89) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_373])).
% 2.41/1.33  tff(c_403, plain, (![B_91]: (k2_relat_1(k5_relat_1(B_91, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6, c_34, c_379])).
% 2.41/1.33  tff(c_415, plain, (![B_91]: (k3_xboole_0(k5_relat_1(B_91, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_91, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_91, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_91, k1_xboole_0)) | ~v1_relat_1(B_91))), inference(superposition, [status(thm), theory('equality')], [c_403, c_28])).
% 2.41/1.33  tff(c_429, plain, (![B_92]: (k5_relat_1(B_92, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_92, k1_xboole_0)) | ~v1_relat_1(B_92))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18, c_415])).
% 2.41/1.33  tff(c_436, plain, (![A_22]: (k5_relat_1(A_22, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_22))), inference(resolution, [status(thm)], [c_26, c_429])).
% 2.41/1.33  tff(c_442, plain, (![A_93]: (k5_relat_1(A_93, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_436])).
% 2.41/1.33  tff(c_451, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_442])).
% 2.41/1.33  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_451])).
% 2.41/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.33  
% 2.41/1.33  Inference rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Ref     : 0
% 2.41/1.33  #Sup     : 92
% 2.41/1.33  #Fact    : 0
% 2.41/1.33  #Define  : 0
% 2.41/1.33  #Split   : 1
% 2.41/1.33  #Chain   : 0
% 2.41/1.33  #Close   : 0
% 2.41/1.33  
% 2.41/1.33  Ordering : KBO
% 2.41/1.33  
% 2.41/1.33  Simplification rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Subsume      : 3
% 2.41/1.33  #Demod        : 58
% 2.41/1.33  #Tautology    : 67
% 2.41/1.33  #SimpNegUnit  : 2
% 2.41/1.33  #BackRed      : 0
% 2.41/1.33  
% 2.41/1.33  #Partial instantiations: 0
% 2.41/1.33  #Strategies tried      : 1
% 2.41/1.33  
% 2.41/1.33  Timing (in seconds)
% 2.41/1.33  ----------------------
% 2.41/1.34  Preprocessing        : 0.33
% 2.41/1.34  Parsing              : 0.18
% 2.41/1.34  CNF conversion       : 0.02
% 2.41/1.34  Main loop            : 0.22
% 2.41/1.34  Inferencing          : 0.09
% 2.41/1.34  Reduction            : 0.07
% 2.41/1.34  Demodulation         : 0.05
% 2.41/1.34  BG Simplification    : 0.01
% 2.41/1.34  Subsumption          : 0.03
% 2.41/1.34  Abstraction          : 0.01
% 2.41/1.34  MUC search           : 0.00
% 2.41/1.34  Cooper               : 0.00
% 2.41/1.34  Total                : 0.59
% 2.41/1.34  Index Insertion      : 0.00
% 2.41/1.34  Index Deletion       : 0.00
% 2.41/1.34  Index Matching       : 0.00
% 2.41/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
