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
% DateTime   : Thu Dec  3 09:59:06 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 101 expanded)
%              Number of leaves         :   33 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 154 expanded)
%              Number of equality atoms :   37 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_34,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_89,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_48,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_91,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_92,plain,(
    ! [A_51] :
      ( v1_relat_1(A_51)
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_96,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_92])).

tff(c_36,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(k5_relat_1(A_37,B_38))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    ! [B_33] : k2_zfmisc_1(k1_xboole_0,B_33) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_178,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_67,B_68)),k1_relat_1(A_67))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_183,plain,(
    ! [B_68] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_68)),k1_xboole_0)
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_178])).

tff(c_187,plain,(
    ! [B_69] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_69)),k1_xboole_0)
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_183])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_127,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_127])).

tff(c_197,plain,(
    ! [B_70] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_70)) = k1_xboole_0
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_187,c_136])).

tff(c_38,plain,(
    ! [A_39] :
      ( k3_xboole_0(A_39,k2_zfmisc_1(k1_relat_1(A_39),k2_relat_1(A_39))) = A_39
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_212,plain,(
    ! [B_70] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_70),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_70)))) = k5_relat_1(k1_xboole_0,B_70)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_38])).

tff(c_231,plain,(
    ! [B_75] :
      ( k5_relat_1(k1_xboole_0,B_75) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_75))
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_30,c_212])).

tff(c_235,plain,(
    ! [B_38] :
      ( k5_relat_1(k1_xboole_0,B_38) = k1_xboole_0
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_231])).

tff(c_239,plain,(
    ! [B_76] :
      ( k5_relat_1(k1_xboole_0,B_76) = k1_xboole_0
      | ~ v1_relat_1(B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_235])).

tff(c_248,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_239])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_248])).

tff(c_255,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_257,plain,(
    ! [A_77] :
      ( v1_relat_1(A_77)
      | ~ v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_261,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_257])).

tff(c_28,plain,(
    ! [A_32] : k2_zfmisc_1(A_32,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_480,plain,(
    ! [B_108,A_109] :
      ( k2_relat_1(k5_relat_1(B_108,A_109)) = k2_relat_1(A_109)
      | ~ r1_tarski(k1_relat_1(A_109),k2_relat_1(B_108))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_486,plain,(
    ! [B_108] :
      ( k2_relat_1(k5_relat_1(B_108,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_108))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_480])).

tff(c_496,plain,(
    ! [B_110] :
      ( k2_relat_1(k5_relat_1(B_110,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_12,c_44,c_486])).

tff(c_505,plain,(
    ! [B_110] :
      ( k3_xboole_0(k5_relat_1(B_110,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_110,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_110,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_110,k1_xboole_0))
      | ~ v1_relat_1(B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_38])).

tff(c_517,plain,(
    ! [B_111] :
      ( k5_relat_1(B_111,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_111,k1_xboole_0))
      | ~ v1_relat_1(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_28,c_505])).

tff(c_524,plain,(
    ! [A_37] :
      ( k5_relat_1(A_37,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_36,c_517])).

tff(c_530,plain,(
    ! [A_112] :
      ( k5_relat_1(A_112,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_524])).

tff(c_539,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_530])).

tff(c_546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.38  
% 2.30/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.39  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.30/1.39  
% 2.30/1.39  %Foreground sorts:
% 2.30/1.39  
% 2.30/1.39  
% 2.30/1.39  %Background operators:
% 2.30/1.39  
% 2.30/1.39  
% 2.30/1.39  %Foreground operators:
% 2.30/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.39  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.30/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.30/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.30/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.30/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.30/1.39  
% 2.62/1.40  tff(f_96, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.62/1.40  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.62/1.40  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.62/1.40  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.62/1.40  tff(f_34, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.62/1.40  tff(f_54, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.62/1.40  tff(f_89, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.62/1.40  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.62/1.40  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.62/1.40  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.62/1.40  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 2.62/1.40  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.62/1.40  tff(c_48, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.62/1.40  tff(c_91, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.62/1.40  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.62/1.40  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.62/1.40  tff(c_92, plain, (![A_51]: (v1_relat_1(A_51) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.62/1.40  tff(c_96, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_92])).
% 2.62/1.40  tff(c_36, plain, (![A_37, B_38]: (v1_relat_1(k5_relat_1(A_37, B_38)) | ~v1_relat_1(B_38) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.62/1.40  tff(c_10, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.62/1.40  tff(c_30, plain, (![B_33]: (k2_zfmisc_1(k1_xboole_0, B_33)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.62/1.40  tff(c_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.62/1.40  tff(c_178, plain, (![A_67, B_68]: (r1_tarski(k1_relat_1(k5_relat_1(A_67, B_68)), k1_relat_1(A_67)) | ~v1_relat_1(B_68) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.62/1.40  tff(c_183, plain, (![B_68]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_68)), k1_xboole_0) | ~v1_relat_1(B_68) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_178])).
% 2.62/1.40  tff(c_187, plain, (![B_69]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_69)), k1_xboole_0) | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_183])).
% 2.62/1.40  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.62/1.40  tff(c_127, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.62/1.40  tff(c_136, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_127])).
% 2.62/1.40  tff(c_197, plain, (![B_70]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_70))=k1_xboole_0 | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_187, c_136])).
% 2.62/1.40  tff(c_38, plain, (![A_39]: (k3_xboole_0(A_39, k2_zfmisc_1(k1_relat_1(A_39), k2_relat_1(A_39)))=A_39 | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.62/1.40  tff(c_212, plain, (![B_70]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_70), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_70))))=k5_relat_1(k1_xboole_0, B_70) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_70)) | ~v1_relat_1(B_70))), inference(superposition, [status(thm), theory('equality')], [c_197, c_38])).
% 2.62/1.40  tff(c_231, plain, (![B_75]: (k5_relat_1(k1_xboole_0, B_75)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_75)) | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_30, c_212])).
% 2.62/1.40  tff(c_235, plain, (![B_38]: (k5_relat_1(k1_xboole_0, B_38)=k1_xboole_0 | ~v1_relat_1(B_38) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_231])).
% 2.62/1.40  tff(c_239, plain, (![B_76]: (k5_relat_1(k1_xboole_0, B_76)=k1_xboole_0 | ~v1_relat_1(B_76))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_235])).
% 2.62/1.40  tff(c_248, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_239])).
% 2.62/1.40  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_248])).
% 2.62/1.40  tff(c_255, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.62/1.40  tff(c_257, plain, (![A_77]: (v1_relat_1(A_77) | ~v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.62/1.40  tff(c_261, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_257])).
% 2.62/1.40  tff(c_28, plain, (![A_32]: (k2_zfmisc_1(A_32, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.62/1.40  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.62/1.40  tff(c_480, plain, (![B_108, A_109]: (k2_relat_1(k5_relat_1(B_108, A_109))=k2_relat_1(A_109) | ~r1_tarski(k1_relat_1(A_109), k2_relat_1(B_108)) | ~v1_relat_1(B_108) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.62/1.40  tff(c_486, plain, (![B_108]: (k2_relat_1(k5_relat_1(B_108, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_108)) | ~v1_relat_1(B_108) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_480])).
% 2.62/1.40  tff(c_496, plain, (![B_110]: (k2_relat_1(k5_relat_1(B_110, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_110))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_12, c_44, c_486])).
% 2.62/1.40  tff(c_505, plain, (![B_110]: (k3_xboole_0(k5_relat_1(B_110, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_110, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_110, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_110, k1_xboole_0)) | ~v1_relat_1(B_110))), inference(superposition, [status(thm), theory('equality')], [c_496, c_38])).
% 2.62/1.40  tff(c_517, plain, (![B_111]: (k5_relat_1(B_111, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_111, k1_xboole_0)) | ~v1_relat_1(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_28, c_505])).
% 2.62/1.40  tff(c_524, plain, (![A_37]: (k5_relat_1(A_37, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_36, c_517])).
% 2.62/1.40  tff(c_530, plain, (![A_112]: (k5_relat_1(A_112, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_524])).
% 2.62/1.40  tff(c_539, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_530])).
% 2.62/1.40  tff(c_546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_539])).
% 2.62/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.40  
% 2.62/1.40  Inference rules
% 2.62/1.40  ----------------------
% 2.62/1.40  #Ref     : 0
% 2.62/1.40  #Sup     : 106
% 2.62/1.40  #Fact    : 0
% 2.62/1.40  #Define  : 0
% 2.62/1.40  #Split   : 1
% 2.62/1.40  #Chain   : 0
% 2.62/1.40  #Close   : 0
% 2.62/1.40  
% 2.62/1.40  Ordering : KBO
% 2.62/1.40  
% 2.62/1.40  Simplification rules
% 2.62/1.40  ----------------------
% 2.62/1.40  #Subsume      : 5
% 2.62/1.40  #Demod        : 78
% 2.62/1.40  #Tautology    : 76
% 2.62/1.40  #SimpNegUnit  : 2
% 2.62/1.40  #BackRed      : 0
% 2.62/1.40  
% 2.62/1.40  #Partial instantiations: 0
% 2.62/1.40  #Strategies tried      : 1
% 2.62/1.40  
% 2.62/1.40  Timing (in seconds)
% 2.62/1.40  ----------------------
% 2.62/1.40  Preprocessing        : 0.35
% 2.62/1.40  Parsing              : 0.19
% 2.62/1.40  CNF conversion       : 0.02
% 2.62/1.40  Main loop            : 0.23
% 2.62/1.40  Inferencing          : 0.09
% 2.62/1.40  Reduction            : 0.07
% 2.62/1.40  Demodulation         : 0.05
% 2.62/1.40  BG Simplification    : 0.02
% 2.62/1.40  Subsumption          : 0.04
% 2.62/1.40  Abstraction          : 0.01
% 2.62/1.40  MUC search           : 0.00
% 2.62/1.40  Cooper               : 0.00
% 2.62/1.40  Total                : 0.61
% 2.62/1.40  Index Insertion      : 0.00
% 2.62/1.41  Index Deletion       : 0.00
% 2.62/1.41  Index Matching       : 0.00
% 2.62/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
