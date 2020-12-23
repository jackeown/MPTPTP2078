%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:42 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 128 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 207 expanded)
%              Number of equality atoms :   32 (  89 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_40,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_73,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | k3_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( r1_xboole_0(B_5,A_4)
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_106,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(B_33,A_34)
      | k3_xboole_0(A_34,B_33) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_80,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_474,plain,(
    ! [B_50,A_51] :
      ( k3_xboole_0(B_50,A_51) = k1_xboole_0
      | k3_xboole_0(A_51,B_50) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_490,plain,(
    ! [A_6] : k3_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_474])).

tff(c_197,plain,(
    ! [B_39,A_40] :
      ( k3_xboole_0(k1_relat_1(B_39),A_40) = k1_relat_1(k7_relat_1(B_39,A_40))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_130,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_40])).

tff(c_140,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130,c_2])).

tff(c_203,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_140])).

tff(c_223,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_203])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( k3_xboole_0(k1_relat_1(B_16),A_15) = k1_relat_1(k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_279,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_15)) = k3_xboole_0(k1_xboole_0,A_15)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_30])).

tff(c_520,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_15)) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_279])).

tff(c_521,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_520])).

tff(c_524,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_521])).

tff(c_528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_524])).

tff(c_530,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_24,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(k1_relat_1(A_14))
      | ~ v1_relat_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_282,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | v1_xboole_0(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_24])).

tff(c_286,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | v1_xboole_0(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_282])).

tff(c_697,plain,(
    v1_xboole_0(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_286])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_700,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_697,c_8])).

tff(c_704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_700])).

tff(c_706,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_899,plain,(
    ! [B_78,A_79] :
      ( k3_xboole_0(k1_relat_1(B_78),A_79) = k1_relat_1(k7_relat_1(B_78,A_79))
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_740,plain,(
    ! [A_66,B_67] :
      ( r1_xboole_0(A_66,B_67)
      | k3_xboole_0(A_66,B_67) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_705,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_754,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_740,c_705])).

tff(c_909,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_899,c_754])).

tff(c_931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_706,c_909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:10:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.43  
% 2.48/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.43  %$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.48/1.43  
% 2.48/1.43  %Foreground sorts:
% 2.48/1.43  
% 2.48/1.43  
% 2.48/1.43  %Background operators:
% 2.48/1.43  
% 2.48/1.43  
% 2.48/1.43  %Foreground operators:
% 2.48/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.48/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.48/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.48/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.48/1.43  
% 2.48/1.45  tff(f_74, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.48/1.45  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.48/1.45  tff(f_52, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.48/1.45  tff(f_40, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.48/1.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.48/1.45  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.48/1.45  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.48/1.45  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.48/1.45  tff(f_60, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.48/1.45  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.48/1.45  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.48/1.45  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.48/1.45  tff(c_34, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.48/1.45  tff(c_73, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 2.48/1.45  tff(c_22, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.48/1.45  tff(c_12, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.48/1.45  tff(c_80, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | k3_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.48/1.45  tff(c_10, plain, (![B_5, A_4]: (r1_xboole_0(B_5, A_4) | ~r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.45  tff(c_106, plain, (![B_33, A_34]: (r1_xboole_0(B_33, A_34) | k3_xboole_0(A_34, B_33)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_10])).
% 2.48/1.45  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.48/1.45  tff(c_474, plain, (![B_50, A_51]: (k3_xboole_0(B_50, A_51)=k1_xboole_0 | k3_xboole_0(A_51, B_50)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_106, c_2])).
% 2.48/1.45  tff(c_490, plain, (![A_6]: (k3_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_474])).
% 2.48/1.45  tff(c_197, plain, (![B_39, A_40]: (k3_xboole_0(k1_relat_1(B_39), A_40)=k1_relat_1(k7_relat_1(B_39, A_40)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.45  tff(c_40, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.48/1.45  tff(c_130, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_73, c_40])).
% 2.48/1.45  tff(c_140, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_130, c_2])).
% 2.48/1.45  tff(c_203, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_197, c_140])).
% 2.48/1.45  tff(c_223, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_203])).
% 2.48/1.45  tff(c_30, plain, (![B_16, A_15]: (k3_xboole_0(k1_relat_1(B_16), A_15)=k1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.45  tff(c_279, plain, (![A_15]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_15))=k3_xboole_0(k1_xboole_0, A_15) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_223, c_30])).
% 2.48/1.45  tff(c_520, plain, (![A_15]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_15))=k1_xboole_0 | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_279])).
% 2.48/1.45  tff(c_521, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_520])).
% 2.48/1.45  tff(c_524, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_521])).
% 2.48/1.45  tff(c_528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_524])).
% 2.48/1.45  tff(c_530, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_520])).
% 2.48/1.45  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.48/1.45  tff(c_24, plain, (![A_14]: (~v1_xboole_0(k1_relat_1(A_14)) | ~v1_relat_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.48/1.45  tff(c_282, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | v1_xboole_0(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_223, c_24])).
% 2.48/1.45  tff(c_286, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | v1_xboole_0(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_282])).
% 2.48/1.45  tff(c_697, plain, (v1_xboole_0(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_530, c_286])).
% 2.48/1.45  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.48/1.45  tff(c_700, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_697, c_8])).
% 2.48/1.45  tff(c_704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_700])).
% 2.48/1.45  tff(c_706, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 2.48/1.45  tff(c_899, plain, (![B_78, A_79]: (k3_xboole_0(k1_relat_1(B_78), A_79)=k1_relat_1(k7_relat_1(B_78, A_79)) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.45  tff(c_740, plain, (![A_66, B_67]: (r1_xboole_0(A_66, B_67) | k3_xboole_0(A_66, B_67)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.48/1.45  tff(c_705, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.48/1.45  tff(c_754, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_740, c_705])).
% 2.48/1.45  tff(c_909, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_899, c_754])).
% 2.48/1.45  tff(c_931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_706, c_909])).
% 2.48/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.45  
% 2.48/1.45  Inference rules
% 2.48/1.45  ----------------------
% 2.48/1.45  #Ref     : 0
% 2.48/1.45  #Sup     : 207
% 2.48/1.45  #Fact    : 0
% 2.48/1.45  #Define  : 0
% 2.48/1.45  #Split   : 3
% 2.48/1.45  #Chain   : 0
% 2.48/1.45  #Close   : 0
% 2.48/1.45  
% 2.48/1.45  Ordering : KBO
% 2.48/1.45  
% 2.48/1.45  Simplification rules
% 2.48/1.45  ----------------------
% 2.48/1.45  #Subsume      : 11
% 2.48/1.45  #Demod        : 79
% 2.48/1.45  #Tautology    : 132
% 2.48/1.45  #SimpNegUnit  : 3
% 2.48/1.45  #BackRed      : 0
% 2.48/1.45  
% 2.48/1.45  #Partial instantiations: 0
% 2.48/1.45  #Strategies tried      : 1
% 2.48/1.45  
% 2.48/1.45  Timing (in seconds)
% 2.48/1.45  ----------------------
% 2.84/1.45  Preprocessing        : 0.31
% 2.84/1.45  Parsing              : 0.17
% 2.84/1.45  CNF conversion       : 0.02
% 2.84/1.45  Main loop            : 0.32
% 2.84/1.45  Inferencing          : 0.13
% 2.84/1.45  Reduction            : 0.09
% 2.84/1.45  Demodulation         : 0.07
% 2.84/1.45  BG Simplification    : 0.02
% 2.84/1.45  Subsumption          : 0.05
% 2.84/1.45  Abstraction          : 0.02
% 2.84/1.45  MUC search           : 0.00
% 2.84/1.45  Cooper               : 0.00
% 2.84/1.45  Total                : 0.66
% 2.84/1.45  Index Insertion      : 0.00
% 2.84/1.45  Index Deletion       : 0.00
% 2.84/1.45  Index Matching       : 0.00
% 2.84/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
