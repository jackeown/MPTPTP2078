%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:05 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   61 (  99 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 178 expanded)
%              Number of equality atoms :   29 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_87,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_30,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_53,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    ! [A_19] :
      ( v1_relat_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_96,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_30,B_31)),k1_relat_1(A_30))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_101,plain,(
    ! [B_31] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_31)),k1_xboole_0)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_96])).

tff(c_105,plain,(
    ! [B_32] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_32)),k1_xboole_0)
      | ~ v1_relat_1(B_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_101])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    ! [B_27,A_28] :
      ( B_27 = A_28
      | ~ r1_tarski(B_27,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_73])).

tff(c_143,plain,(
    ! [B_36] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_36)) = k1_xboole_0
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_105,c_82])).

tff(c_18,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k1_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_161,plain,(
    ! [B_36] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_36))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_18])).

tff(c_186,plain,(
    ! [B_38] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_38))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_161])).

tff(c_49,plain,(
    ! [B_20,A_21] :
      ( ~ v1_xboole_0(B_20)
      | B_20 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_395,plain,(
    ! [B_46] :
      ( k5_relat_1(k1_xboole_0,B_46) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_186,c_52])).

tff(c_402,plain,(
    ! [B_8] :
      ( k5_relat_1(k1_xboole_0,B_8) = k1_xboole_0
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_395])).

tff(c_408,plain,(
    ! [B_47] :
      ( k5_relat_1(k1_xboole_0,B_47) = k1_xboole_0
      | ~ v1_relat_1(B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_402])).

tff(c_417,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_408])).

tff(c_424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_417])).

tff(c_425,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_555,plain,(
    ! [B_61,A_62] :
      ( k2_relat_1(k5_relat_1(B_61,A_62)) = k2_relat_1(A_62)
      | ~ r1_tarski(k1_relat_1(A_62),k2_relat_1(B_61))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_561,plain,(
    ! [B_61] :
      ( k2_relat_1(k5_relat_1(B_61,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_61))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_555])).

tff(c_571,plain,(
    ! [B_63] :
      ( k2_relat_1(k5_relat_1(B_63,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10,c_26,c_561])).

tff(c_20,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k2_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_580,plain,(
    ! [B_63] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_63,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_63,k1_xboole_0))
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_20])).

tff(c_588,plain,(
    ! [B_64] :
      ( ~ v1_relat_1(k5_relat_1(B_64,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_64,k1_xboole_0))
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_580])).

tff(c_600,plain,(
    ! [B_65] :
      ( k5_relat_1(B_65,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_65,k1_xboole_0))
      | ~ v1_relat_1(B_65) ) ),
    inference(resolution,[status(thm)],[c_588,c_52])).

tff(c_604,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_16,c_600])).

tff(c_618,plain,(
    ! [A_68] :
      ( k5_relat_1(A_68,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_604])).

tff(c_627,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_618])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_425,c_627])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:00:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.30  
% 2.24/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.30  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.24/1.30  
% 2.24/1.30  %Foreground sorts:
% 2.24/1.30  
% 2.24/1.30  
% 2.24/1.30  %Background operators:
% 2.24/1.30  
% 2.24/1.30  
% 2.24/1.30  %Foreground operators:
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.24/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.24/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.30  
% 2.24/1.32  tff(f_94, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.24/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.24/1.32  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.24/1.32  tff(f_52, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.24/1.32  tff(f_87, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.24/1.32  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.24/1.32  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.24/1.32  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.24/1.32  tff(f_60, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.24/1.32  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.24/1.32  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.24/1.32  tff(f_68, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.24/1.32  tff(c_30, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.24/1.32  tff(c_53, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 2.24/1.32  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.24/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.24/1.32  tff(c_44, plain, (![A_19]: (v1_relat_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.24/1.32  tff(c_48, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_44])).
% 2.24/1.32  tff(c_16, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.24/1.32  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.24/1.32  tff(c_96, plain, (![A_30, B_31]: (r1_tarski(k1_relat_1(k5_relat_1(A_30, B_31)), k1_relat_1(A_30)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.24/1.32  tff(c_101, plain, (![B_31]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_31)), k1_xboole_0) | ~v1_relat_1(B_31) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_96])).
% 2.24/1.32  tff(c_105, plain, (![B_32]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_32)), k1_xboole_0) | ~v1_relat_1(B_32))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_101])).
% 2.24/1.32  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.24/1.32  tff(c_73, plain, (![B_27, A_28]: (B_27=A_28 | ~r1_tarski(B_27, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.32  tff(c_82, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_73])).
% 2.24/1.32  tff(c_143, plain, (![B_36]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_36))=k1_xboole_0 | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_105, c_82])).
% 2.24/1.32  tff(c_18, plain, (![A_9]: (~v1_xboole_0(k1_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.24/1.32  tff(c_161, plain, (![B_36]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_36)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_36)) | ~v1_relat_1(B_36))), inference(superposition, [status(thm), theory('equality')], [c_143, c_18])).
% 2.24/1.32  tff(c_186, plain, (![B_38]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_38)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_38)) | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_161])).
% 2.24/1.32  tff(c_49, plain, (![B_20, A_21]: (~v1_xboole_0(B_20) | B_20=A_21 | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.32  tff(c_52, plain, (![A_21]: (k1_xboole_0=A_21 | ~v1_xboole_0(A_21))), inference(resolution, [status(thm)], [c_2, c_49])).
% 2.24/1.32  tff(c_395, plain, (![B_46]: (k5_relat_1(k1_xboole_0, B_46)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_46)) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_186, c_52])).
% 2.24/1.32  tff(c_402, plain, (![B_8]: (k5_relat_1(k1_xboole_0, B_8)=k1_xboole_0 | ~v1_relat_1(B_8) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_395])).
% 2.24/1.32  tff(c_408, plain, (![B_47]: (k5_relat_1(k1_xboole_0, B_47)=k1_xboole_0 | ~v1_relat_1(B_47))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_402])).
% 2.24/1.32  tff(c_417, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_408])).
% 2.24/1.32  tff(c_424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_417])).
% 2.24/1.32  tff(c_425, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.24/1.32  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.24/1.32  tff(c_555, plain, (![B_61, A_62]: (k2_relat_1(k5_relat_1(B_61, A_62))=k2_relat_1(A_62) | ~r1_tarski(k1_relat_1(A_62), k2_relat_1(B_61)) | ~v1_relat_1(B_61) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.32  tff(c_561, plain, (![B_61]: (k2_relat_1(k5_relat_1(B_61, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_61)) | ~v1_relat_1(B_61) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_555])).
% 2.24/1.32  tff(c_571, plain, (![B_63]: (k2_relat_1(k5_relat_1(B_63, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_63))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10, c_26, c_561])).
% 2.24/1.32  tff(c_20, plain, (![A_10]: (~v1_xboole_0(k2_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.24/1.32  tff(c_580, plain, (![B_63]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_63, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_63, k1_xboole_0)) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_571, c_20])).
% 2.24/1.32  tff(c_588, plain, (![B_64]: (~v1_relat_1(k5_relat_1(B_64, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_64, k1_xboole_0)) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_580])).
% 2.24/1.32  tff(c_600, plain, (![B_65]: (k5_relat_1(B_65, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_65, k1_xboole_0)) | ~v1_relat_1(B_65))), inference(resolution, [status(thm)], [c_588, c_52])).
% 2.24/1.32  tff(c_604, plain, (![A_7]: (k5_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_16, c_600])).
% 2.24/1.32  tff(c_618, plain, (![A_68]: (k5_relat_1(A_68, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_604])).
% 2.24/1.32  tff(c_627, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_618])).
% 2.24/1.32  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_425, c_627])).
% 2.24/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.32  
% 2.24/1.32  Inference rules
% 2.24/1.32  ----------------------
% 2.24/1.32  #Ref     : 0
% 2.24/1.32  #Sup     : 127
% 2.24/1.32  #Fact    : 0
% 2.24/1.32  #Define  : 0
% 2.24/1.32  #Split   : 2
% 2.24/1.32  #Chain   : 0
% 2.24/1.32  #Close   : 0
% 2.24/1.32  
% 2.24/1.32  Ordering : KBO
% 2.24/1.32  
% 2.24/1.32  Simplification rules
% 2.24/1.32  ----------------------
% 2.24/1.32  #Subsume      : 11
% 2.24/1.32  #Demod        : 142
% 2.24/1.32  #Tautology    : 68
% 2.24/1.32  #SimpNegUnit  : 2
% 2.24/1.32  #BackRed      : 3
% 2.24/1.32  
% 2.24/1.32  #Partial instantiations: 0
% 2.24/1.32  #Strategies tried      : 1
% 2.24/1.32  
% 2.24/1.32  Timing (in seconds)
% 2.24/1.32  ----------------------
% 2.24/1.32  Preprocessing        : 0.27
% 2.24/1.32  Parsing              : 0.15
% 2.24/1.32  CNF conversion       : 0.02
% 2.24/1.32  Main loop            : 0.28
% 2.24/1.32  Inferencing          : 0.11
% 2.24/1.32  Reduction            : 0.08
% 2.24/1.32  Demodulation         : 0.05
% 2.24/1.32  BG Simplification    : 0.02
% 2.24/1.32  Subsumption          : 0.06
% 2.24/1.32  Abstraction          : 0.01
% 2.24/1.32  MUC search           : 0.00
% 2.51/1.32  Cooper               : 0.00
% 2.51/1.32  Total                : 0.58
% 2.51/1.32  Index Insertion      : 0.00
% 2.51/1.32  Index Deletion       : 0.00
% 2.51/1.32  Index Matching       : 0.00
% 2.51/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
