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
% DateTime   : Thu Dec  3 09:59:05 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   63 (  95 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 170 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
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

tff(f_56,axiom,(
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

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_30,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_55,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    ! [A_19] :
      ( v1_relat_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_50])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_92,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_27,B_28)),k1_relat_1(A_27))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_97,plain,(
    ! [B_28] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_28)),k1_xboole_0)
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_92])).

tff(c_101,plain,(
    ! [B_29] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_29)),k1_xboole_0)
      | ~ v1_relat_1(B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_97])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [B_22,A_23] :
      ( B_22 = A_23
      | ~ r1_tarski(B_22,A_23)
      | ~ r1_tarski(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_77,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_68])).

tff(c_111,plain,(
    ! [B_30] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_30)) = k1_xboole_0
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_101,c_77])).

tff(c_18,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k1_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_126,plain,(
    ! [B_30] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_30))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_18])).

tff(c_182,plain,(
    ! [B_35] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_35))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_126])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_216,plain,(
    ! [B_39] :
      ( k5_relat_1(k1_xboole_0,B_39) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_182,c_4])).

tff(c_220,plain,(
    ! [B_7] :
      ( k5_relat_1(k1_xboole_0,B_7) = k1_xboole_0
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_216])).

tff(c_224,plain,(
    ! [B_40] :
      ( k5_relat_1(k1_xboole_0,B_40) = k1_xboole_0
      | ~ v1_relat_1(B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_220])).

tff(c_233,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_224])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_233])).

tff(c_240,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_287,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_48,B_49)),k2_relat_1(B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_295,plain,(
    ! [A_48] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_48,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_287])).

tff(c_301,plain,(
    ! [A_50] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_50,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_295])).

tff(c_258,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(B_43,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_267,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_258])).

tff(c_311,plain,(
    ! [A_51] :
      ( k2_relat_1(k5_relat_1(A_51,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_301,c_267])).

tff(c_20,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_326,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_51,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_51,k1_xboole_0))
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_20])).

tff(c_397,plain,(
    ! [A_56] :
      ( ~ v1_relat_1(k5_relat_1(A_56,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_56,k1_xboole_0))
      | ~ v1_relat_1(A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_326])).

tff(c_441,plain,(
    ! [A_60] :
      ( k5_relat_1(A_60,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_60,k1_xboole_0))
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_397,c_4])).

tff(c_445,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_441])).

tff(c_449,plain,(
    ! [A_61] :
      ( k5_relat_1(A_61,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_445])).

tff(c_458,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_449])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:21:06 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  
% 2.04/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.04/1.30  
% 2.04/1.30  %Foreground sorts:
% 2.04/1.30  
% 2.04/1.30  
% 2.04/1.30  %Background operators:
% 2.04/1.30  
% 2.04/1.30  
% 2.04/1.30  %Foreground operators:
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.04/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.04/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.30  
% 2.04/1.32  tff(f_88, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.04/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.04/1.32  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.04/1.32  tff(f_48, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.04/1.32  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.04/1.32  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.04/1.32  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.04/1.32  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.04/1.32  tff(f_56, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.04/1.32  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.04/1.32  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.04/1.32  tff(f_64, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.04/1.32  tff(c_30, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.04/1.32  tff(c_55, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 2.04/1.32  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.04/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.04/1.32  tff(c_50, plain, (![A_19]: (v1_relat_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.04/1.32  tff(c_54, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_50])).
% 2.04/1.32  tff(c_16, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.04/1.32  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.04/1.32  tff(c_92, plain, (![A_27, B_28]: (r1_tarski(k1_relat_1(k5_relat_1(A_27, B_28)), k1_relat_1(A_27)) | ~v1_relat_1(B_28) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.04/1.32  tff(c_97, plain, (![B_28]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_28)), k1_xboole_0) | ~v1_relat_1(B_28) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_92])).
% 2.04/1.32  tff(c_101, plain, (![B_29]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_29)), k1_xboole_0) | ~v1_relat_1(B_29))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_97])).
% 2.04/1.32  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.04/1.32  tff(c_68, plain, (![B_22, A_23]: (B_22=A_23 | ~r1_tarski(B_22, A_23) | ~r1_tarski(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.04/1.32  tff(c_77, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_68])).
% 2.04/1.32  tff(c_111, plain, (![B_30]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_30))=k1_xboole_0 | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_101, c_77])).
% 2.04/1.32  tff(c_18, plain, (![A_8]: (~v1_xboole_0(k1_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.04/1.32  tff(c_126, plain, (![B_30]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_30)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_30)) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_111, c_18])).
% 2.04/1.32  tff(c_182, plain, (![B_35]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_35)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_35)) | ~v1_relat_1(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_126])).
% 2.04/1.32  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.04/1.32  tff(c_216, plain, (![B_39]: (k5_relat_1(k1_xboole_0, B_39)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_39)) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_182, c_4])).
% 2.04/1.32  tff(c_220, plain, (![B_7]: (k5_relat_1(k1_xboole_0, B_7)=k1_xboole_0 | ~v1_relat_1(B_7) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_216])).
% 2.04/1.32  tff(c_224, plain, (![B_40]: (k5_relat_1(k1_xboole_0, B_40)=k1_xboole_0 | ~v1_relat_1(B_40))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_220])).
% 2.04/1.32  tff(c_233, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_224])).
% 2.04/1.32  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_233])).
% 2.04/1.32  tff(c_240, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.04/1.32  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.04/1.32  tff(c_287, plain, (![A_48, B_49]: (r1_tarski(k2_relat_1(k5_relat_1(A_48, B_49)), k2_relat_1(B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.04/1.32  tff(c_295, plain, (![A_48]: (r1_tarski(k2_relat_1(k5_relat_1(A_48, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_26, c_287])).
% 2.04/1.32  tff(c_301, plain, (![A_50]: (r1_tarski(k2_relat_1(k5_relat_1(A_50, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_295])).
% 2.04/1.32  tff(c_258, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(B_43, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.04/1.32  tff(c_267, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_258])).
% 2.04/1.32  tff(c_311, plain, (![A_51]: (k2_relat_1(k5_relat_1(A_51, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_301, c_267])).
% 2.04/1.32  tff(c_20, plain, (![A_9]: (~v1_xboole_0(k2_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.04/1.32  tff(c_326, plain, (![A_51]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_51, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_51, k1_xboole_0)) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_311, c_20])).
% 2.04/1.32  tff(c_397, plain, (![A_56]: (~v1_relat_1(k5_relat_1(A_56, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_56, k1_xboole_0)) | ~v1_relat_1(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_326])).
% 2.04/1.32  tff(c_441, plain, (![A_60]: (k5_relat_1(A_60, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_60, k1_xboole_0)) | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_397, c_4])).
% 2.04/1.32  tff(c_445, plain, (![A_6]: (k5_relat_1(A_6, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_441])).
% 2.04/1.32  tff(c_449, plain, (![A_61]: (k5_relat_1(A_61, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_445])).
% 2.04/1.32  tff(c_458, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_449])).
% 2.04/1.32  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_458])).
% 2.04/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.32  
% 2.04/1.32  Inference rules
% 2.04/1.32  ----------------------
% 2.04/1.32  #Ref     : 0
% 2.04/1.32  #Sup     : 89
% 2.04/1.32  #Fact    : 0
% 2.04/1.32  #Define  : 0
% 2.04/1.32  #Split   : 1
% 2.04/1.32  #Chain   : 0
% 2.04/1.32  #Close   : 0
% 2.04/1.32  
% 2.04/1.32  Ordering : KBO
% 2.04/1.32  
% 2.04/1.32  Simplification rules
% 2.04/1.32  ----------------------
% 2.04/1.32  #Subsume      : 11
% 2.04/1.32  #Demod        : 85
% 2.04/1.32  #Tautology    : 44
% 2.04/1.32  #SimpNegUnit  : 2
% 2.04/1.32  #BackRed      : 0
% 2.04/1.32  
% 2.04/1.32  #Partial instantiations: 0
% 2.04/1.32  #Strategies tried      : 1
% 2.04/1.32  
% 2.04/1.32  Timing (in seconds)
% 2.04/1.32  ----------------------
% 2.04/1.32  Preprocessing        : 0.28
% 2.04/1.32  Parsing              : 0.16
% 2.04/1.32  CNF conversion       : 0.02
% 2.04/1.32  Main loop            : 0.24
% 2.04/1.32  Inferencing          : 0.10
% 2.04/1.32  Reduction            : 0.07
% 2.04/1.32  Demodulation         : 0.05
% 2.04/1.32  BG Simplification    : 0.01
% 2.04/1.32  Subsumption          : 0.05
% 2.04/1.32  Abstraction          : 0.01
% 2.04/1.32  MUC search           : 0.00
% 2.04/1.32  Cooper               : 0.00
% 2.04/1.32  Total                : 0.55
% 2.04/1.32  Index Insertion      : 0.00
% 2.04/1.32  Index Deletion       : 0.00
% 2.04/1.32  Index Matching       : 0.00
% 2.04/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
