%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:12 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 160 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_87,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_28,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_47,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_47])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_102,plain,(
    ! [A_32,B_33] :
      ( k1_relat_1(k5_relat_1(A_32,B_33)) = k1_relat_1(A_32)
      | ~ r1_tarski(k2_relat_1(A_32),k1_relat_1(B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_108,plain,(
    ! [B_33] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_33)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_102])).

tff(c_113,plain,(
    ! [B_34] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_34)) = k1_xboole_0
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_6,c_26,c_108])).

tff(c_16,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k1_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_122,plain,(
    ! [B_34] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_34))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_16])).

tff(c_170,plain,(
    ! [B_37] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_37))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_122])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_237,plain,(
    ! [B_40] :
      ( k5_relat_1(k1_xboole_0,B_40) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(resolution,[status(thm)],[c_170,c_4])).

tff(c_241,plain,(
    ! [B_8] :
      ( k5_relat_1(k1_xboole_0,B_8) = k1_xboole_0
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_237])).

tff(c_341,plain,(
    ! [B_42] :
      ( k5_relat_1(k1_xboole_0,B_42) = k1_xboole_0
      | ~ v1_relat_1(B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_241])).

tff(c_353,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_341])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_353])).

tff(c_362,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_398,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_50,B_51)),k2_relat_1(B_51))
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_404,plain,(
    ! [A_50] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_50,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_398])).

tff(c_442,plain,(
    ! [A_55] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_55,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_404])).

tff(c_8,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_380,plain,(
    ! [B_45,A_46] :
      ( ~ r1_xboole_0(B_45,A_46)
      | ~ r1_tarski(B_45,A_46)
      | v1_xboole_0(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_384,plain,(
    ! [A_3] :
      ( ~ r1_tarski(A_3,k1_xboole_0)
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_380])).

tff(c_447,plain,(
    ! [A_56] :
      ( v1_xboole_0(k2_relat_1(k5_relat_1(A_56,k1_xboole_0)))
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_442,c_384])).

tff(c_18,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k2_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_514,plain,(
    ! [A_60] :
      ( ~ v1_relat_1(k5_relat_1(A_60,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_60,k1_xboole_0))
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_447,c_18])).

tff(c_655,plain,(
    ! [A_65] :
      ( k5_relat_1(A_65,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_65,k1_xboole_0))
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_514,c_4])).

tff(c_662,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_655])).

tff(c_668,plain,(
    ! [A_66] :
      ( k5_relat_1(A_66,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_662])).

tff(c_680,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_668])).

tff(c_688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_362,c_680])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:16:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.39  
% 2.53/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.40  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.53/1.40  
% 2.53/1.40  %Foreground sorts:
% 2.53/1.40  
% 2.53/1.40  
% 2.53/1.40  %Background operators:
% 2.53/1.40  
% 2.53/1.40  
% 2.53/1.40  %Foreground operators:
% 2.53/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.53/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.53/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.53/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.40  
% 2.53/1.41  tff(f_94, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.53/1.41  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.53/1.41  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.53/1.41  tff(f_52, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.53/1.41  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.53/1.41  tff(f_87, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.53/1.41  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.53/1.41  tff(f_60, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.53/1.41  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.53/1.41  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.53/1.41  tff(f_34, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.53/1.41  tff(f_42, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.53/1.41  tff(f_68, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.53/1.41  tff(c_28, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.53/1.41  tff(c_52, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_28])).
% 2.53/1.41  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.53/1.41  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.53/1.41  tff(c_47, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.53/1.41  tff(c_51, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_47])).
% 2.53/1.41  tff(c_14, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.53/1.41  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.41  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.41  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.41  tff(c_102, plain, (![A_32, B_33]: (k1_relat_1(k5_relat_1(A_32, B_33))=k1_relat_1(A_32) | ~r1_tarski(k2_relat_1(A_32), k1_relat_1(B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.53/1.41  tff(c_108, plain, (![B_33]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_33))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_102])).
% 2.53/1.41  tff(c_113, plain, (![B_34]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_34))=k1_xboole_0 | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_6, c_26, c_108])).
% 2.53/1.41  tff(c_16, plain, (![A_9]: (~v1_xboole_0(k1_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.53/1.41  tff(c_122, plain, (![B_34]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_34)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_34)) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_113, c_16])).
% 2.53/1.41  tff(c_170, plain, (![B_37]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_37)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_37)) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_122])).
% 2.53/1.41  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.53/1.41  tff(c_237, plain, (![B_40]: (k5_relat_1(k1_xboole_0, B_40)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_40)) | ~v1_relat_1(B_40))), inference(resolution, [status(thm)], [c_170, c_4])).
% 2.53/1.41  tff(c_241, plain, (![B_8]: (k5_relat_1(k1_xboole_0, B_8)=k1_xboole_0 | ~v1_relat_1(B_8) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_237])).
% 2.53/1.41  tff(c_341, plain, (![B_42]: (k5_relat_1(k1_xboole_0, B_42)=k1_xboole_0 | ~v1_relat_1(B_42))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_241])).
% 2.53/1.41  tff(c_353, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_341])).
% 2.53/1.41  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_353])).
% 2.53/1.41  tff(c_362, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.53/1.41  tff(c_398, plain, (![A_50, B_51]: (r1_tarski(k2_relat_1(k5_relat_1(A_50, B_51)), k2_relat_1(B_51)) | ~v1_relat_1(B_51) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.41  tff(c_404, plain, (![A_50]: (r1_tarski(k2_relat_1(k5_relat_1(A_50, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_24, c_398])).
% 2.53/1.41  tff(c_442, plain, (![A_55]: (r1_tarski(k2_relat_1(k5_relat_1(A_55, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_404])).
% 2.53/1.41  tff(c_8, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.53/1.41  tff(c_380, plain, (![B_45, A_46]: (~r1_xboole_0(B_45, A_46) | ~r1_tarski(B_45, A_46) | v1_xboole_0(B_45))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.53/1.41  tff(c_384, plain, (![A_3]: (~r1_tarski(A_3, k1_xboole_0) | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_8, c_380])).
% 2.53/1.41  tff(c_447, plain, (![A_56]: (v1_xboole_0(k2_relat_1(k5_relat_1(A_56, k1_xboole_0))) | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_442, c_384])).
% 2.53/1.41  tff(c_18, plain, (![A_10]: (~v1_xboole_0(k2_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.53/1.41  tff(c_514, plain, (![A_60]: (~v1_relat_1(k5_relat_1(A_60, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_60, k1_xboole_0)) | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_447, c_18])).
% 2.53/1.41  tff(c_655, plain, (![A_65]: (k5_relat_1(A_65, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_65, k1_xboole_0)) | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_514, c_4])).
% 2.53/1.41  tff(c_662, plain, (![A_7]: (k5_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_14, c_655])).
% 2.53/1.41  tff(c_668, plain, (![A_66]: (k5_relat_1(A_66, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_662])).
% 2.53/1.41  tff(c_680, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_668])).
% 2.53/1.41  tff(c_688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_362, c_680])).
% 2.53/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.41  
% 2.53/1.41  Inference rules
% 2.53/1.41  ----------------------
% 2.53/1.41  #Ref     : 0
% 2.53/1.41  #Sup     : 137
% 2.53/1.41  #Fact    : 0
% 2.53/1.41  #Define  : 0
% 2.53/1.41  #Split   : 2
% 2.53/1.41  #Chain   : 0
% 2.53/1.41  #Close   : 0
% 2.53/1.41  
% 2.53/1.41  Ordering : KBO
% 2.53/1.41  
% 2.53/1.41  Simplification rules
% 2.53/1.41  ----------------------
% 2.53/1.41  #Subsume      : 4
% 2.53/1.41  #Demod        : 166
% 2.53/1.41  #Tautology    : 86
% 2.53/1.41  #SimpNegUnit  : 2
% 2.53/1.41  #BackRed      : 3
% 2.53/1.41  
% 2.53/1.41  #Partial instantiations: 0
% 2.53/1.41  #Strategies tried      : 1
% 2.53/1.41  
% 2.53/1.41  Timing (in seconds)
% 2.53/1.41  ----------------------
% 2.53/1.41  Preprocessing        : 0.28
% 2.53/1.41  Parsing              : 0.16
% 2.53/1.41  CNF conversion       : 0.02
% 2.53/1.41  Main loop            : 0.29
% 2.53/1.41  Inferencing          : 0.11
% 2.53/1.41  Reduction            : 0.08
% 2.53/1.41  Demodulation         : 0.06
% 2.53/1.41  BG Simplification    : 0.01
% 2.53/1.41  Subsumption          : 0.05
% 2.53/1.41  Abstraction          : 0.01
% 2.53/1.41  MUC search           : 0.00
% 2.53/1.41  Cooper               : 0.00
% 2.53/1.41  Total                : 0.60
% 2.53/1.41  Index Insertion      : 0.00
% 2.53/1.41  Index Deletion       : 0.00
% 2.53/1.41  Index Matching       : 0.00
% 2.53/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
