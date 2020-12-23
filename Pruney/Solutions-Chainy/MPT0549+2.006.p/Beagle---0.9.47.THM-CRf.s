%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:48 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 112 expanded)
%              Number of leaves         :   35 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 173 expanded)
%              Number of equality atoms :   28 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_93,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_672,plain,(
    ! [B_140,A_141] :
      ( r1_xboole_0(k1_relat_1(B_140),A_141)
      | k7_relat_1(B_140,A_141) != k1_xboole_0
      | ~ v1_relat_1(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_62,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_88,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k9_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_128,plain,(
    k9_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_56])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_376,plain,(
    ! [B_101,A_102] :
      ( k7_relat_1(B_101,A_102) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_101),A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_382,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_376])).

tff(c_393,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_382])).

tff(c_42,plain,(
    ! [B_46,A_45] :
      ( k2_relat_1(k7_relat_1(B_46,A_45)) = k9_relat_1(B_46,A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_400,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_42])).

tff(c_407,plain,(
    k9_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_400])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_407])).

tff(c_411,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_684,plain,
    ( k7_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_672,c_411])).

tff(c_697,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_684])).

tff(c_40,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k7_relat_1(A_43,B_44))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_547,plain,(
    ! [C_130,D_131,A_132,B_133] :
      ( ~ r1_xboole_0(C_130,D_131)
      | r1_xboole_0(k2_zfmisc_1(A_132,C_130),k2_zfmisc_1(B_133,D_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_565,plain,(
    ! [B_134,D_135] :
      ( k2_zfmisc_1(B_134,D_135) = k1_xboole_0
      | ~ r1_xboole_0(D_135,D_135) ) ),
    inference(resolution,[status(thm)],[c_547,c_14])).

tff(c_581,plain,(
    ! [B_134] : k2_zfmisc_1(B_134,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_565])).

tff(c_410,plain,(
    k9_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_472,plain,(
    ! [A_116] :
      ( r1_tarski(A_116,k2_zfmisc_1(k1_relat_1(A_116),k2_relat_1(A_116)))
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1448,plain,(
    ! [B_282,A_283] :
      ( r1_tarski(k7_relat_1(B_282,A_283),k2_zfmisc_1(k1_relat_1(k7_relat_1(B_282,A_283)),k9_relat_1(B_282,A_283)))
      | ~ v1_relat_1(k7_relat_1(B_282,A_283))
      | ~ v1_relat_1(B_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_472])).

tff(c_1480,plain,
    ( r1_tarski(k7_relat_1('#skF_3','#skF_2'),k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_3','#skF_2')),k1_xboole_0))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_1448])).

tff(c_1498,plain,
    ( r1_tarski(k7_relat_1('#skF_3','#skF_2'),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_581,c_1480])).

tff(c_1499,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1498])).

tff(c_1502,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1499])).

tff(c_1506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1502])).

tff(c_1507,plain,(
    r1_tarski(k7_relat_1('#skF_3','#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1498])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_434,plain,(
    ! [B_109,A_110] :
      ( B_109 = A_110
      | ~ r1_tarski(B_109,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_439,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_434])).

tff(c_1515,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1507,c_439])).

tff(c_1521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_697,c_1515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:17:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.51  
% 3.44/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.44/1.51  
% 3.44/1.51  %Foreground sorts:
% 3.44/1.51  
% 3.44/1.51  
% 3.44/1.51  %Background operators:
% 3.44/1.51  
% 3.44/1.51  
% 3.44/1.51  %Foreground operators:
% 3.44/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.44/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.44/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.44/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.44/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.44/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.44/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.51  
% 3.44/1.52  tff(f_106, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 3.44/1.52  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.44/1.52  tff(f_93, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.44/1.52  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.44/1.52  tff(f_82, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.44/1.52  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.44/1.52  tff(f_65, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 3.44/1.52  tff(f_47, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.44/1.52  tff(f_90, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.44/1.52  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.44/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.44/1.52  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.44/1.52  tff(c_672, plain, (![B_140, A_141]: (r1_xboole_0(k1_relat_1(B_140), A_141) | k7_relat_1(B_140, A_141)!=k1_xboole_0 | ~v1_relat_1(B_140))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.44/1.52  tff(c_62, plain, (k9_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.44/1.52  tff(c_88, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 3.44/1.52  tff(c_56, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k9_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.44/1.52  tff(c_128, plain, (k9_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_88, c_56])).
% 3.44/1.52  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.44/1.52  tff(c_376, plain, (![B_101, A_102]: (k7_relat_1(B_101, A_102)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_101), A_102) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.44/1.52  tff(c_382, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_376])).
% 3.44/1.52  tff(c_393, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_382])).
% 3.44/1.52  tff(c_42, plain, (![B_46, A_45]: (k2_relat_1(k7_relat_1(B_46, A_45))=k9_relat_1(B_46, A_45) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.44/1.52  tff(c_400, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_393, c_42])).
% 3.44/1.52  tff(c_407, plain, (k9_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_400])).
% 3.44/1.52  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_407])).
% 3.44/1.52  tff(c_411, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 3.44/1.52  tff(c_684, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_672, c_411])).
% 3.44/1.52  tff(c_697, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_684])).
% 3.44/1.52  tff(c_40, plain, (![A_43, B_44]: (v1_relat_1(k7_relat_1(A_43, B_44)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.44/1.52  tff(c_10, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.44/1.52  tff(c_547, plain, (![C_130, D_131, A_132, B_133]: (~r1_xboole_0(C_130, D_131) | r1_xboole_0(k2_zfmisc_1(A_132, C_130), k2_zfmisc_1(B_133, D_131)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.44/1.52  tff(c_14, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.44/1.52  tff(c_565, plain, (![B_134, D_135]: (k2_zfmisc_1(B_134, D_135)=k1_xboole_0 | ~r1_xboole_0(D_135, D_135))), inference(resolution, [status(thm)], [c_547, c_14])).
% 3.44/1.52  tff(c_581, plain, (![B_134]: (k2_zfmisc_1(B_134, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_565])).
% 3.44/1.52  tff(c_410, plain, (k9_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 3.44/1.52  tff(c_472, plain, (![A_116]: (r1_tarski(A_116, k2_zfmisc_1(k1_relat_1(A_116), k2_relat_1(A_116))) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.44/1.52  tff(c_1448, plain, (![B_282, A_283]: (r1_tarski(k7_relat_1(B_282, A_283), k2_zfmisc_1(k1_relat_1(k7_relat_1(B_282, A_283)), k9_relat_1(B_282, A_283))) | ~v1_relat_1(k7_relat_1(B_282, A_283)) | ~v1_relat_1(B_282))), inference(superposition, [status(thm), theory('equality')], [c_42, c_472])).
% 3.44/1.52  tff(c_1480, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')), k1_xboole_0)) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_410, c_1448])).
% 3.44/1.52  tff(c_1498, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_581, c_1480])).
% 3.44/1.52  tff(c_1499, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1498])).
% 3.44/1.52  tff(c_1502, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1499])).
% 3.44/1.52  tff(c_1506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1502])).
% 3.44/1.52  tff(c_1507, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1498])).
% 3.44/1.52  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.44/1.52  tff(c_434, plain, (![B_109, A_110]: (B_109=A_110 | ~r1_tarski(B_109, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.52  tff(c_439, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_434])).
% 3.44/1.52  tff(c_1515, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1507, c_439])).
% 3.44/1.52  tff(c_1521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_697, c_1515])).
% 3.44/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.52  
% 3.44/1.52  Inference rules
% 3.44/1.52  ----------------------
% 3.44/1.52  #Ref     : 0
% 3.44/1.52  #Sup     : 318
% 3.44/1.52  #Fact    : 0
% 3.44/1.52  #Define  : 0
% 3.44/1.52  #Split   : 2
% 3.44/1.52  #Chain   : 0
% 3.44/1.52  #Close   : 0
% 3.44/1.52  
% 3.44/1.52  Ordering : KBO
% 3.44/1.52  
% 3.44/1.52  Simplification rules
% 3.44/1.52  ----------------------
% 3.44/1.52  #Subsume      : 2
% 3.44/1.52  #Demod        : 335
% 3.44/1.52  #Tautology    : 183
% 3.44/1.52  #SimpNegUnit  : 2
% 3.44/1.52  #BackRed      : 0
% 3.44/1.52  
% 3.44/1.52  #Partial instantiations: 0
% 3.44/1.52  #Strategies tried      : 1
% 3.44/1.52  
% 3.44/1.52  Timing (in seconds)
% 3.44/1.52  ----------------------
% 3.44/1.52  Preprocessing        : 0.31
% 3.44/1.52  Parsing              : 0.16
% 3.44/1.52  CNF conversion       : 0.02
% 3.44/1.52  Main loop            : 0.45
% 3.44/1.52  Inferencing          : 0.16
% 3.44/1.53  Reduction            : 0.14
% 3.44/1.53  Demodulation         : 0.10
% 3.44/1.53  BG Simplification    : 0.02
% 3.44/1.53  Subsumption          : 0.10
% 3.44/1.53  Abstraction          : 0.02
% 3.44/1.53  MUC search           : 0.00
% 3.44/1.53  Cooper               : 0.00
% 3.44/1.53  Total                : 0.80
% 3.44/1.53  Index Insertion      : 0.00
% 3.44/1.53  Index Deletion       : 0.00
% 3.44/1.53  Index Matching       : 0.00
% 3.44/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
