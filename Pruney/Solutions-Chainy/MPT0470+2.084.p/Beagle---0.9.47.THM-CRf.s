%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:12 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 100 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  116 ( 176 expanded)
%              Number of equality atoms :   31 (  47 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_87,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_28,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_56,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_40,plain,(
    ! [A_19] :
      ( v1_relat_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_40])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k5_relat_1(A_8,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_96,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_31,B_32)),k1_relat_1(A_31))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_102,plain,(
    ! [B_32] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_32)),k1_xboole_0)
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_96])).

tff(c_106,plain,(
    ! [B_33] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_33)),k1_xboole_0)
      | ~ v1_relat_1(B_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_102])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_109,plain,(
    ! [B_33] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_33)),k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,B_33))
      | ~ v1_relat_1(B_33) ) ),
    inference(resolution,[status(thm)],[c_106,c_4])).

tff(c_140,plain,(
    ! [B_37] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_37)) = k1_xboole_0
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_109])).

tff(c_16,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k1_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_158,plain,(
    ! [B_37] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_37))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_16])).

tff(c_183,plain,(
    ! [B_39] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_39))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_158])).

tff(c_52,plain,(
    ! [B_21,A_22] :
      ( ~ v1_xboole_0(B_21)
      | B_21 = A_22
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_55,plain,(
    ! [A_22] :
      ( k1_xboole_0 = A_22
      | ~ v1_xboole_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_322,plain,(
    ! [B_43] :
      ( k5_relat_1(k1_xboole_0,B_43) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_43))
      | ~ v1_relat_1(B_43) ) ),
    inference(resolution,[status(thm)],[c_183,c_55])).

tff(c_329,plain,(
    ! [B_9] :
      ( k5_relat_1(k1_xboole_0,B_9) = k1_xboole_0
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_322])).

tff(c_335,plain,(
    ! [B_44] :
      ( k5_relat_1(k1_xboole_0,B_44) = k1_xboole_0
      | ~ v1_relat_1(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_329])).

tff(c_344,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_335])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_344])).

tff(c_352,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_8,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_476,plain,(
    ! [B_58,A_59] :
      ( k2_relat_1(k5_relat_1(B_58,A_59)) = k2_relat_1(A_59)
      | ~ r1_tarski(k1_relat_1(A_59),k2_relat_1(B_58))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_482,plain,(
    ! [B_58] :
      ( k2_relat_1(k5_relat_1(B_58,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_58))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_476])).

tff(c_492,plain,(
    ! [B_60] :
      ( k2_relat_1(k5_relat_1(B_60,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8,c_24,c_482])).

tff(c_18,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(k2_relat_1(A_11))
      | ~ v1_relat_1(A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_501,plain,(
    ! [B_60] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_60,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_60,k1_xboole_0))
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_18])).

tff(c_509,plain,(
    ! [B_61] :
      ( ~ v1_relat_1(k5_relat_1(B_61,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_61,k1_xboole_0))
      | ~ v1_relat_1(B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_501])).

tff(c_521,plain,(
    ! [B_62] :
      ( k5_relat_1(B_62,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_62,k1_xboole_0))
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_509,c_55])).

tff(c_525,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_521])).

tff(c_539,plain,(
    ! [A_65] :
      ( k5_relat_1(A_65,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_525])).

tff(c_548,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_539])).

tff(c_554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.71  
% 2.77/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.71  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.77/1.71  
% 2.77/1.71  %Foreground sorts:
% 2.77/1.71  
% 2.77/1.71  
% 2.77/1.71  %Background operators:
% 2.77/1.71  
% 2.77/1.71  
% 2.77/1.71  %Foreground operators:
% 2.77/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.71  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.77/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.71  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.71  
% 2.77/1.73  tff(f_94, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.77/1.73  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.77/1.73  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.77/1.73  tff(f_52, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.77/1.73  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.77/1.73  tff(f_87, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.77/1.73  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.77/1.73  tff(f_30, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.77/1.73  tff(f_60, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.77/1.73  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.77/1.73  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.77/1.73  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.77/1.73  tff(f_68, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.77/1.73  tff(c_28, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.77/1.73  tff(c_56, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_28])).
% 2.77/1.73  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.77/1.73  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.77/1.73  tff(c_40, plain, (![A_19]: (v1_relat_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.77/1.73  tff(c_44, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_40])).
% 2.77/1.73  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k5_relat_1(A_8, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.77/1.73  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.73  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.77/1.73  tff(c_96, plain, (![A_31, B_32]: (r1_tarski(k1_relat_1(k5_relat_1(A_31, B_32)), k1_relat_1(A_31)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.77/1.73  tff(c_102, plain, (![B_32]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_32)), k1_xboole_0) | ~v1_relat_1(B_32) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_96])).
% 2.77/1.73  tff(c_106, plain, (![B_33]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_33)), k1_xboole_0) | ~v1_relat_1(B_33))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_102])).
% 2.77/1.73  tff(c_4, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.77/1.73  tff(c_109, plain, (![B_33]: (k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_33)), k1_xboole_0)=k1_relat_1(k5_relat_1(k1_xboole_0, B_33)) | ~v1_relat_1(B_33))), inference(resolution, [status(thm)], [c_106, c_4])).
% 2.77/1.73  tff(c_140, plain, (![B_37]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_37))=k1_xboole_0 | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_109])).
% 2.77/1.73  tff(c_16, plain, (![A_10]: (~v1_xboole_0(k1_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.77/1.73  tff(c_158, plain, (![B_37]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_37)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_37)) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_140, c_16])).
% 2.77/1.73  tff(c_183, plain, (![B_39]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_39)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_39)) | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_158])).
% 2.77/1.73  tff(c_52, plain, (![B_21, A_22]: (~v1_xboole_0(B_21) | B_21=A_22 | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.77/1.73  tff(c_55, plain, (![A_22]: (k1_xboole_0=A_22 | ~v1_xboole_0(A_22))), inference(resolution, [status(thm)], [c_2, c_52])).
% 2.77/1.73  tff(c_322, plain, (![B_43]: (k5_relat_1(k1_xboole_0, B_43)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_43)) | ~v1_relat_1(B_43))), inference(resolution, [status(thm)], [c_183, c_55])).
% 2.77/1.73  tff(c_329, plain, (![B_9]: (k5_relat_1(k1_xboole_0, B_9)=k1_xboole_0 | ~v1_relat_1(B_9) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_322])).
% 2.77/1.73  tff(c_335, plain, (![B_44]: (k5_relat_1(k1_xboole_0, B_44)=k1_xboole_0 | ~v1_relat_1(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_329])).
% 2.77/1.73  tff(c_344, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_335])).
% 2.77/1.73  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_344])).
% 2.77/1.73  tff(c_352, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.77/1.73  tff(c_8, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.77/1.73  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.77/1.73  tff(c_476, plain, (![B_58, A_59]: (k2_relat_1(k5_relat_1(B_58, A_59))=k2_relat_1(A_59) | ~r1_tarski(k1_relat_1(A_59), k2_relat_1(B_58)) | ~v1_relat_1(B_58) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.77/1.73  tff(c_482, plain, (![B_58]: (k2_relat_1(k5_relat_1(B_58, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_58)) | ~v1_relat_1(B_58) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_476])).
% 2.77/1.73  tff(c_492, plain, (![B_60]: (k2_relat_1(k5_relat_1(B_60, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8, c_24, c_482])).
% 2.77/1.73  tff(c_18, plain, (![A_11]: (~v1_xboole_0(k2_relat_1(A_11)) | ~v1_relat_1(A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.77/1.73  tff(c_501, plain, (![B_60]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_60, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_60, k1_xboole_0)) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_492, c_18])).
% 2.77/1.73  tff(c_509, plain, (![B_61]: (~v1_relat_1(k5_relat_1(B_61, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_61, k1_xboole_0)) | ~v1_relat_1(B_61))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_501])).
% 2.77/1.73  tff(c_521, plain, (![B_62]: (k5_relat_1(B_62, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_62, k1_xboole_0)) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_509, c_55])).
% 2.77/1.73  tff(c_525, plain, (![A_8]: (k5_relat_1(A_8, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_14, c_521])).
% 2.77/1.73  tff(c_539, plain, (![A_65]: (k5_relat_1(A_65, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_525])).
% 2.77/1.73  tff(c_548, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_539])).
% 2.77/1.73  tff(c_554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_352, c_548])).
% 2.77/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.73  
% 2.77/1.73  Inference rules
% 2.77/1.73  ----------------------
% 2.77/1.73  #Ref     : 0
% 2.77/1.73  #Sup     : 115
% 2.77/1.73  #Fact    : 0
% 2.77/1.73  #Define  : 0
% 2.77/1.73  #Split   : 1
% 2.77/1.73  #Chain   : 0
% 2.77/1.73  #Close   : 0
% 2.77/1.73  
% 2.77/1.73  Ordering : KBO
% 2.77/1.73  
% 2.77/1.73  Simplification rules
% 2.77/1.73  ----------------------
% 2.77/1.73  #Subsume      : 4
% 2.77/1.73  #Demod        : 109
% 2.77/1.73  #Tautology    : 66
% 2.77/1.73  #SimpNegUnit  : 2
% 2.77/1.73  #BackRed      : 1
% 2.77/1.73  
% 2.77/1.73  #Partial instantiations: 0
% 2.77/1.73  #Strategies tried      : 1
% 2.77/1.73  
% 2.77/1.73  Timing (in seconds)
% 2.77/1.73  ----------------------
% 2.77/1.74  Preprocessing        : 0.41
% 2.77/1.74  Parsing              : 0.23
% 2.77/1.74  CNF conversion       : 0.03
% 2.77/1.74  Main loop            : 0.40
% 2.77/1.74  Inferencing          : 0.16
% 2.77/1.74  Reduction            : 0.11
% 2.77/1.74  Demodulation         : 0.08
% 2.77/1.74  BG Simplification    : 0.02
% 2.77/1.74  Subsumption          : 0.08
% 2.77/1.74  Abstraction          : 0.02
% 2.77/1.74  MUC search           : 0.00
% 2.77/1.74  Cooper               : 0.00
% 2.77/1.74  Total                : 0.86
% 2.77/1.74  Index Insertion      : 0.00
% 2.77/1.74  Index Deletion       : 0.00
% 2.77/1.74  Index Matching       : 0.00
% 2.77/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
