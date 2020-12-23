%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:20 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   59 (  92 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 162 expanded)
%              Number of equality atoms :   32 (  62 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_83,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_30,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_75,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_70])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k5_relat_1(A_5,B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_129,plain,(
    ! [A_32,B_33] :
      ( k1_relat_1(k5_relat_1(A_32,B_33)) = k1_relat_1(A_32)
      | ~ r1_tarski(k2_relat_1(A_32),k1_relat_1(B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_138,plain,(
    ! [B_33] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_33)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_129])).

tff(c_145,plain,(
    ! [B_34] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_34)) = k1_xboole_0
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6,c_28,c_138])).

tff(c_18,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k1_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_157,plain,(
    ! [B_34] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_34))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_18])).

tff(c_172,plain,(
    ! [B_36] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_36))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_157])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_290,plain,(
    ! [B_42] :
      ( k5_relat_1(k1_xboole_0,B_42) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_172,c_4])).

tff(c_297,plain,(
    ! [B_6] :
      ( k5_relat_1(k1_xboole_0,B_6) = k1_xboole_0
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_290])).

tff(c_303,plain,(
    ! [B_43] :
      ( k5_relat_1(k1_xboole_0,B_43) = k1_xboole_0
      | ~ v1_relat_1(B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_297])).

tff(c_315,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_303])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_315])).

tff(c_324,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_434,plain,(
    ! [B_56,A_57] :
      ( k2_relat_1(k5_relat_1(B_56,A_57)) = k2_relat_1(A_57)
      | ~ r1_tarski(k1_relat_1(A_57),k2_relat_1(B_56))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_440,plain,(
    ! [B_56] :
      ( k2_relat_1(k5_relat_1(B_56,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_56))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_434])).

tff(c_497,plain,(
    ! [B_60] :
      ( k2_relat_1(k5_relat_1(B_60,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6,c_26,c_440])).

tff(c_20,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k2_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_509,plain,(
    ! [B_60] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_60,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_60,k1_xboole_0))
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_20])).

tff(c_571,plain,(
    ! [B_63] :
      ( ~ v1_relat_1(k5_relat_1(B_63,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_63,k1_xboole_0))
      | ~ v1_relat_1(B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_509])).

tff(c_581,plain,(
    ! [B_64] :
      ( k5_relat_1(B_64,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_64,k1_xboole_0))
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_571,c_4])).

tff(c_588,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_14,c_581])).

tff(c_594,plain,(
    ! [A_65] :
      ( k5_relat_1(A_65,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_588])).

tff(c_606,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_594])).

tff(c_614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_324,c_606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.30  
% 2.38/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.30  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.38/1.30  
% 2.38/1.30  %Foreground sorts:
% 2.38/1.30  
% 2.38/1.30  
% 2.38/1.30  %Background operators:
% 2.38/1.30  
% 2.38/1.30  
% 2.38/1.30  %Foreground operators:
% 2.38/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.38/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.38/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.38/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.30  
% 2.38/1.31  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.38/1.31  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.38/1.31  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.38/1.31  tff(f_44, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.38/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.38/1.31  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.38/1.31  tff(f_83, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.38/1.31  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.38/1.31  tff(f_54, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.38/1.31  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.38/1.31  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.38/1.31  tff(f_62, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.38/1.31  tff(c_30, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.38/1.31  tff(c_75, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 2.38/1.31  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.38/1.31  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.38/1.31  tff(c_70, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.31  tff(c_72, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_70])).
% 2.38/1.31  tff(c_14, plain, (![A_5, B_6]: (v1_relat_1(k5_relat_1(A_5, B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.38/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.38/1.31  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.38/1.31  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.38/1.31  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.38/1.31  tff(c_129, plain, (![A_32, B_33]: (k1_relat_1(k5_relat_1(A_32, B_33))=k1_relat_1(A_32) | ~r1_tarski(k2_relat_1(A_32), k1_relat_1(B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.38/1.31  tff(c_138, plain, (![B_33]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_33))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_129])).
% 2.38/1.31  tff(c_145, plain, (![B_34]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_34))=k1_xboole_0 | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6, c_28, c_138])).
% 2.38/1.31  tff(c_18, plain, (![A_9]: (~v1_xboole_0(k1_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.38/1.31  tff(c_157, plain, (![B_34]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_34)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_34)) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_145, c_18])).
% 2.38/1.31  tff(c_172, plain, (![B_36]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_36)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_36)) | ~v1_relat_1(B_36))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_157])).
% 2.38/1.31  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.38/1.31  tff(c_290, plain, (![B_42]: (k5_relat_1(k1_xboole_0, B_42)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_42)) | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_172, c_4])).
% 2.38/1.31  tff(c_297, plain, (![B_6]: (k5_relat_1(k1_xboole_0, B_6)=k1_xboole_0 | ~v1_relat_1(B_6) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_290])).
% 2.38/1.31  tff(c_303, plain, (![B_43]: (k5_relat_1(k1_xboole_0, B_43)=k1_xboole_0 | ~v1_relat_1(B_43))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_297])).
% 2.38/1.31  tff(c_315, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_303])).
% 2.38/1.31  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_315])).
% 2.38/1.31  tff(c_324, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.38/1.31  tff(c_434, plain, (![B_56, A_57]: (k2_relat_1(k5_relat_1(B_56, A_57))=k2_relat_1(A_57) | ~r1_tarski(k1_relat_1(A_57), k2_relat_1(B_56)) | ~v1_relat_1(B_56) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.38/1.31  tff(c_440, plain, (![B_56]: (k2_relat_1(k5_relat_1(B_56, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_56)) | ~v1_relat_1(B_56) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_434])).
% 2.38/1.31  tff(c_497, plain, (![B_60]: (k2_relat_1(k5_relat_1(B_60, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6, c_26, c_440])).
% 2.38/1.31  tff(c_20, plain, (![A_10]: (~v1_xboole_0(k2_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.38/1.31  tff(c_509, plain, (![B_60]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_60, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_60, k1_xboole_0)) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_497, c_20])).
% 2.38/1.31  tff(c_571, plain, (![B_63]: (~v1_relat_1(k5_relat_1(B_63, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_63, k1_xboole_0)) | ~v1_relat_1(B_63))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_509])).
% 2.38/1.31  tff(c_581, plain, (![B_64]: (k5_relat_1(B_64, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_64, k1_xboole_0)) | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_571, c_4])).
% 2.38/1.31  tff(c_588, plain, (![A_5]: (k5_relat_1(A_5, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_14, c_581])).
% 2.38/1.31  tff(c_594, plain, (![A_65]: (k5_relat_1(A_65, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_588])).
% 2.38/1.31  tff(c_606, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_594])).
% 2.38/1.31  tff(c_614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_324, c_606])).
% 2.38/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.31  
% 2.38/1.31  Inference rules
% 2.38/1.31  ----------------------
% 2.38/1.31  #Ref     : 0
% 2.38/1.31  #Sup     : 126
% 2.38/1.31  #Fact    : 0
% 2.38/1.31  #Define  : 0
% 2.38/1.31  #Split   : 1
% 2.38/1.31  #Chain   : 0
% 2.38/1.31  #Close   : 0
% 2.38/1.31  
% 2.38/1.31  Ordering : KBO
% 2.38/1.31  
% 2.38/1.31  Simplification rules
% 2.38/1.31  ----------------------
% 2.38/1.31  #Subsume      : 4
% 2.38/1.31  #Demod        : 147
% 2.38/1.31  #Tautology    : 84
% 2.38/1.31  #SimpNegUnit  : 2
% 2.38/1.31  #BackRed      : 0
% 2.38/1.31  
% 2.38/1.31  #Partial instantiations: 0
% 2.38/1.32  #Strategies tried      : 1
% 2.38/1.32  
% 2.38/1.32  Timing (in seconds)
% 2.38/1.32  ----------------------
% 2.74/1.32  Preprocessing        : 0.29
% 2.74/1.32  Parsing              : 0.17
% 2.74/1.32  CNF conversion       : 0.02
% 2.74/1.32  Main loop            : 0.26
% 2.74/1.32  Inferencing          : 0.10
% 2.74/1.32  Reduction            : 0.08
% 2.74/1.32  Demodulation         : 0.06
% 2.74/1.32  BG Simplification    : 0.01
% 2.74/1.32  Subsumption          : 0.05
% 2.74/1.32  Abstraction          : 0.01
% 2.74/1.32  MUC search           : 0.00
% 2.74/1.32  Cooper               : 0.00
% 2.74/1.32  Total                : 0.59
% 2.74/1.32  Index Insertion      : 0.00
% 2.74/1.32  Index Deletion       : 0.00
% 2.74/1.32  Index Matching       : 0.00
% 2.74/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
