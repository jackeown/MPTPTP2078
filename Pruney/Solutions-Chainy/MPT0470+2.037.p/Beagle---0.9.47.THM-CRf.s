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

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   66 (  99 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 175 expanded)
%              Number of equality atoms :   31 (  45 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_83,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_36,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_77,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_72,plain,(
    ! [A_22] :
      ( v1_relat_1(A_22)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k5_relat_1(A_8,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_139,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_33,B_34)),k1_relat_1(A_33))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_144,plain,(
    ! [B_34] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_34)),k1_xboole_0)
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_139])).

tff(c_148,plain,(
    ! [B_35] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_35)),k1_xboole_0)
      | ~ v1_relat_1(B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_144])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_102,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_111,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_102])).

tff(c_158,plain,(
    ! [B_36] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_36)) = k1_xboole_0
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_148,c_111])).

tff(c_26,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,k2_zfmisc_1(k1_relat_1(A_11),k2_relat_1(A_11)))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_173,plain,(
    ! [B_36] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,B_36),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_36))))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_26])).

tff(c_472,plain,(
    ! [B_50] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,B_50),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_173])).

tff(c_487,plain,(
    ! [B_51] :
      ( k5_relat_1(k1_xboole_0,B_51) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_51))
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_472,c_111])).

tff(c_494,plain,(
    ! [B_9] :
      ( k5_relat_1(k1_xboole_0,B_9) = k1_xboole_0
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_487])).

tff(c_500,plain,(
    ! [B_52] :
      ( k5_relat_1(k1_xboole_0,B_52) = k1_xboole_0
      | ~ v1_relat_1(B_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_494])).

tff(c_509,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_500])).

tff(c_516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_509])).

tff(c_517,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_589,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_63,B_64)),k2_relat_1(B_64))
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_597,plain,(
    ! [A_63] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_63,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_589])).

tff(c_603,plain,(
    ! [A_65] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_65,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_597])).

tff(c_552,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_561,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_552])).

tff(c_613,plain,(
    ! [A_66] :
      ( k2_relat_1(k5_relat_1(A_66,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_603,c_561])).

tff(c_24,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k2_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_631,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_66,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_66,k1_xboole_0))
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_24])).

tff(c_643,plain,(
    ! [A_67] :
      ( ~ v1_relat_1(k5_relat_1(A_67,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_67,k1_xboole_0))
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_631])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_652,plain,(
    ! [A_68] :
      ( k5_relat_1(A_68,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_68,k1_xboole_0))
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_643,c_4])).

tff(c_656,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_22,c_652])).

tff(c_674,plain,(
    ! [A_71] :
      ( k5_relat_1(A_71,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_656])).

tff(c_683,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_674])).

tff(c_689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_517,c_683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:13:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.38  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.66/1.38  
% 2.66/1.38  %Foreground sorts:
% 2.66/1.38  
% 2.66/1.38  
% 2.66/1.38  %Background operators:
% 2.66/1.38  
% 2.66/1.38  
% 2.66/1.38  %Foreground operators:
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.66/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.66/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.38  
% 2.66/1.39  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.66/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.66/1.39  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.66/1.39  tff(f_54, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.66/1.39  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.66/1.39  tff(f_83, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.66/1.39  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.66/1.39  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.66/1.39  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.66/1.39  tff(f_66, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.66/1.39  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.66/1.39  tff(f_62, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.66/1.39  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.66/1.39  tff(c_36, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.66/1.39  tff(c_77, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.66/1.39  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.66/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.66/1.39  tff(c_72, plain, (![A_22]: (v1_relat_1(A_22) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.66/1.39  tff(c_76, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_72])).
% 2.66/1.39  tff(c_22, plain, (![A_8, B_9]: (v1_relat_1(k5_relat_1(A_8, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.66/1.39  tff(c_18, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.66/1.39  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.66/1.39  tff(c_139, plain, (![A_33, B_34]: (r1_tarski(k1_relat_1(k5_relat_1(A_33, B_34)), k1_relat_1(A_33)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.66/1.39  tff(c_144, plain, (![B_34]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_34)), k1_xboole_0) | ~v1_relat_1(B_34) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_139])).
% 2.66/1.39  tff(c_148, plain, (![B_35]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_35)), k1_xboole_0) | ~v1_relat_1(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_144])).
% 2.66/1.39  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.66/1.39  tff(c_102, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.66/1.39  tff(c_111, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_102])).
% 2.66/1.39  tff(c_158, plain, (![B_36]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_36))=k1_xboole_0 | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_148, c_111])).
% 2.66/1.39  tff(c_26, plain, (![A_11]: (r1_tarski(A_11, k2_zfmisc_1(k1_relat_1(A_11), k2_relat_1(A_11))) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.66/1.39  tff(c_173, plain, (![B_36]: (r1_tarski(k5_relat_1(k1_xboole_0, B_36), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_36)))) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_36)) | ~v1_relat_1(B_36))), inference(superposition, [status(thm), theory('equality')], [c_158, c_26])).
% 2.66/1.39  tff(c_472, plain, (![B_50]: (r1_tarski(k5_relat_1(k1_xboole_0, B_50), k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_50)) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_173])).
% 2.66/1.39  tff(c_487, plain, (![B_51]: (k5_relat_1(k1_xboole_0, B_51)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_51)) | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_472, c_111])).
% 2.66/1.39  tff(c_494, plain, (![B_9]: (k5_relat_1(k1_xboole_0, B_9)=k1_xboole_0 | ~v1_relat_1(B_9) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_487])).
% 2.66/1.39  tff(c_500, plain, (![B_52]: (k5_relat_1(k1_xboole_0, B_52)=k1_xboole_0 | ~v1_relat_1(B_52))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_494])).
% 2.66/1.39  tff(c_509, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_500])).
% 2.66/1.39  tff(c_516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_509])).
% 2.66/1.39  tff(c_517, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.66/1.39  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.66/1.39  tff(c_589, plain, (![A_63, B_64]: (r1_tarski(k2_relat_1(k5_relat_1(A_63, B_64)), k2_relat_1(B_64)) | ~v1_relat_1(B_64) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.66/1.39  tff(c_597, plain, (![A_63]: (r1_tarski(k2_relat_1(k5_relat_1(A_63, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_63))), inference(superposition, [status(thm), theory('equality')], [c_32, c_589])).
% 2.66/1.39  tff(c_603, plain, (![A_65]: (r1_tarski(k2_relat_1(k5_relat_1(A_65, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_597])).
% 2.66/1.39  tff(c_552, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.66/1.39  tff(c_561, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_552])).
% 2.66/1.39  tff(c_613, plain, (![A_66]: (k2_relat_1(k5_relat_1(A_66, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_603, c_561])).
% 2.66/1.39  tff(c_24, plain, (![A_10]: (~v1_xboole_0(k2_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.39  tff(c_631, plain, (![A_66]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_66, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_66, k1_xboole_0)) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_613, c_24])).
% 2.66/1.39  tff(c_643, plain, (![A_67]: (~v1_relat_1(k5_relat_1(A_67, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_67, k1_xboole_0)) | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_631])).
% 2.66/1.39  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.66/1.39  tff(c_652, plain, (![A_68]: (k5_relat_1(A_68, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_68, k1_xboole_0)) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_643, c_4])).
% 2.66/1.39  tff(c_656, plain, (![A_8]: (k5_relat_1(A_8, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_22, c_652])).
% 2.66/1.39  tff(c_674, plain, (![A_71]: (k5_relat_1(A_71, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_656])).
% 2.66/1.39  tff(c_683, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_674])).
% 2.66/1.39  tff(c_689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_517, c_683])).
% 2.66/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.39  
% 2.66/1.39  Inference rules
% 2.66/1.39  ----------------------
% 2.66/1.39  #Ref     : 0
% 2.66/1.39  #Sup     : 137
% 2.66/1.39  #Fact    : 0
% 2.66/1.39  #Define  : 0
% 2.66/1.39  #Split   : 1
% 2.66/1.39  #Chain   : 0
% 2.66/1.39  #Close   : 0
% 2.66/1.39  
% 2.66/1.39  Ordering : KBO
% 2.66/1.39  
% 2.66/1.39  Simplification rules
% 2.66/1.39  ----------------------
% 2.66/1.39  #Subsume      : 11
% 2.66/1.39  #Demod        : 194
% 2.66/1.39  #Tautology    : 88
% 2.66/1.39  #SimpNegUnit  : 2
% 2.66/1.39  #BackRed      : 0
% 2.66/1.39  
% 2.66/1.39  #Partial instantiations: 0
% 2.66/1.39  #Strategies tried      : 1
% 2.66/1.39  
% 2.66/1.39  Timing (in seconds)
% 2.66/1.39  ----------------------
% 2.95/1.40  Preprocessing        : 0.30
% 2.95/1.40  Parsing              : 0.16
% 2.95/1.40  CNF conversion       : 0.02
% 2.95/1.40  Main loop            : 0.33
% 2.95/1.40  Inferencing          : 0.13
% 2.95/1.40  Reduction            : 0.10
% 2.95/1.40  Demodulation         : 0.07
% 2.95/1.40  BG Simplification    : 0.02
% 2.95/1.40  Subsumption          : 0.06
% 2.95/1.40  Abstraction          : 0.01
% 2.95/1.40  MUC search           : 0.00
% 2.95/1.40  Cooper               : 0.00
% 2.95/1.40  Total                : 0.67
% 2.95/1.40  Index Insertion      : 0.00
% 2.95/1.40  Index Deletion       : 0.00
% 2.95/1.40  Index Matching       : 0.00
% 2.95/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
