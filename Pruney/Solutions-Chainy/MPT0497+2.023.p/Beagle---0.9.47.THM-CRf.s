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
% DateTime   : Thu Dec  3 09:59:42 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 107 expanded)
%              Number of leaves         :   35 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 149 expanded)
%              Number of equality atoms :   29 (  56 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_104,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_75,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_60,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_110,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_205,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_54])).

tff(c_42,plain,(
    ! [A_45,B_46] :
      ( v1_relat_1(k7_relat_1(A_45,B_46))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    ! [B_42] : k2_zfmisc_1(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1145,plain,(
    ! [B_146,A_147] :
      ( k3_xboole_0(k1_relat_1(B_146),A_147) = k1_relat_1(k7_relat_1(B_146,A_147))
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_141,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = k1_xboole_0
      | ~ r1_xboole_0(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_159,plain,(
    k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_141])).

tff(c_1185,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1145,c_159])).

tff(c_1222,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1185])).

tff(c_44,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,k2_zfmisc_1(k1_relat_1(A_47),k2_relat_1(A_47)))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1235,plain,
    ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1('#skF_4','#skF_3'))))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1222,c_44])).

tff(c_1239,plain,
    ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1235])).

tff(c_1500,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1239])).

tff(c_1516,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1500])).

tff(c_1520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1516])).

tff(c_1521,plain,(
    r1_tarski(k7_relat_1('#skF_4','#skF_3'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1239])).

tff(c_22,plain,(
    ! [A_20] : r1_xboole_0(A_20,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_101,plain,(
    ! [B_54,A_55] :
      ( r1_xboole_0(B_54,A_55)
      | ~ r1_xboole_0(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [A_20] : r1_xboole_0(k1_xboole_0,A_20) ),
    inference(resolution,[status(thm)],[c_22,c_101])).

tff(c_325,plain,(
    ! [A_87,C_88,B_89] :
      ( r1_xboole_0(A_87,C_88)
      | ~ r1_xboole_0(B_89,C_88)
      | ~ r1_tarski(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_361,plain,(
    ! [A_92,A_93] :
      ( r1_xboole_0(A_92,A_93)
      | ~ r1_tarski(A_92,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_104,c_325])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_374,plain,(
    ! [A_92,A_93] :
      ( k3_xboole_0(A_92,A_93) = k1_xboole_0
      | ~ r1_tarski(A_92,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_361,c_2])).

tff(c_1653,plain,(
    ! [A_176] : k3_xboole_0(k7_relat_1('#skF_4','#skF_3'),A_176) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1521,c_374])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1695,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1653,c_6])).

tff(c_1735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_1695])).

tff(c_1736,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2458,plain,(
    ! [B_251,A_252] :
      ( k3_xboole_0(k1_relat_1(B_251),A_252) = k1_relat_1(k7_relat_1(B_251,A_252))
      | ~ v1_relat_1(B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1748,plain,(
    ! [A_179,B_180] :
      ( r1_xboole_0(A_179,B_180)
      | k3_xboole_0(A_179,B_180) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1737,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1754,plain,(
    k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1748,c_1737])).

tff(c_2494,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2458,c_1754])).

tff(c_2524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1736,c_2494])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:40:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.62  
% 3.47/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.62  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.47/1.62  
% 3.47/1.62  %Foreground sorts:
% 3.47/1.62  
% 3.47/1.62  
% 3.47/1.62  %Background operators:
% 3.47/1.62  
% 3.47/1.62  
% 3.47/1.62  %Foreground operators:
% 3.47/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.47/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.47/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.47/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.47/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.47/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.47/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.47/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.47/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.47/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.47/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.47/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.47/1.62  
% 3.89/1.63  tff(f_115, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.89/1.63  tff(f_104, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.89/1.63  tff(f_97, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.89/1.63  tff(f_91, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.89/1.63  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.89/1.63  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.89/1.63  tff(f_101, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.89/1.63  tff(f_75, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.89/1.63  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.89/1.63  tff(f_73, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.89/1.63  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.89/1.63  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.89/1.63  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.89/1.63  tff(c_60, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.89/1.63  tff(c_110, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_60])).
% 3.89/1.63  tff(c_54, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.89/1.63  tff(c_205, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_110, c_54])).
% 3.89/1.63  tff(c_42, plain, (![A_45, B_46]: (v1_relat_1(k7_relat_1(A_45, B_46)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.89/1.63  tff(c_38, plain, (![B_42]: (k2_zfmisc_1(k1_xboole_0, B_42)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.89/1.63  tff(c_1145, plain, (![B_146, A_147]: (k3_xboole_0(k1_relat_1(B_146), A_147)=k1_relat_1(k7_relat_1(B_146, A_147)) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.89/1.63  tff(c_141, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=k1_xboole_0 | ~r1_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.89/1.63  tff(c_159, plain, (k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_110, c_141])).
% 3.89/1.63  tff(c_1185, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1145, c_159])).
% 3.89/1.63  tff(c_1222, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1185])).
% 3.89/1.63  tff(c_44, plain, (![A_47]: (r1_tarski(A_47, k2_zfmisc_1(k1_relat_1(A_47), k2_relat_1(A_47))) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.89/1.63  tff(c_1235, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k7_relat_1('#skF_4', '#skF_3')))) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1222, c_44])).
% 3.89/1.63  tff(c_1239, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1235])).
% 3.89/1.63  tff(c_1500, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1239])).
% 3.89/1.63  tff(c_1516, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_1500])).
% 3.89/1.63  tff(c_1520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1516])).
% 3.89/1.63  tff(c_1521, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1239])).
% 3.89/1.63  tff(c_22, plain, (![A_20]: (r1_xboole_0(A_20, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.89/1.63  tff(c_101, plain, (![B_54, A_55]: (r1_xboole_0(B_54, A_55) | ~r1_xboole_0(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.89/1.63  tff(c_104, plain, (![A_20]: (r1_xboole_0(k1_xboole_0, A_20))), inference(resolution, [status(thm)], [c_22, c_101])).
% 3.89/1.63  tff(c_325, plain, (![A_87, C_88, B_89]: (r1_xboole_0(A_87, C_88) | ~r1_xboole_0(B_89, C_88) | ~r1_tarski(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.89/1.63  tff(c_361, plain, (![A_92, A_93]: (r1_xboole_0(A_92, A_93) | ~r1_tarski(A_92, k1_xboole_0))), inference(resolution, [status(thm)], [c_104, c_325])).
% 3.89/1.63  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.89/1.63  tff(c_374, plain, (![A_92, A_93]: (k3_xboole_0(A_92, A_93)=k1_xboole_0 | ~r1_tarski(A_92, k1_xboole_0))), inference(resolution, [status(thm)], [c_361, c_2])).
% 3.89/1.63  tff(c_1653, plain, (![A_176]: (k3_xboole_0(k7_relat_1('#skF_4', '#skF_3'), A_176)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1521, c_374])).
% 3.89/1.63  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.89/1.63  tff(c_1695, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1653, c_6])).
% 3.89/1.63  tff(c_1735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_1695])).
% 3.89/1.63  tff(c_1736, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.89/1.63  tff(c_2458, plain, (![B_251, A_252]: (k3_xboole_0(k1_relat_1(B_251), A_252)=k1_relat_1(k7_relat_1(B_251, A_252)) | ~v1_relat_1(B_251))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.89/1.63  tff(c_1748, plain, (![A_179, B_180]: (r1_xboole_0(A_179, B_180) | k3_xboole_0(A_179, B_180)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.89/1.63  tff(c_1737, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_60])).
% 3.89/1.63  tff(c_1754, plain, (k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1748, c_1737])).
% 3.89/1.63  tff(c_2494, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2458, c_1754])).
% 3.89/1.63  tff(c_2524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1736, c_2494])).
% 3.89/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.63  
% 3.89/1.63  Inference rules
% 3.89/1.63  ----------------------
% 3.89/1.63  #Ref     : 0
% 3.89/1.63  #Sup     : 597
% 3.89/1.63  #Fact    : 0
% 3.89/1.63  #Define  : 0
% 3.89/1.63  #Split   : 5
% 3.89/1.63  #Chain   : 0
% 3.89/1.63  #Close   : 0
% 3.89/1.63  
% 3.89/1.63  Ordering : KBO
% 3.89/1.63  
% 3.89/1.63  Simplification rules
% 3.89/1.63  ----------------------
% 3.89/1.63  #Subsume      : 186
% 3.89/1.63  #Demod        : 163
% 3.89/1.63  #Tautology    : 255
% 3.89/1.63  #SimpNegUnit  : 14
% 3.89/1.63  #BackRed      : 0
% 3.89/1.63  
% 3.89/1.63  #Partial instantiations: 0
% 3.89/1.63  #Strategies tried      : 1
% 3.89/1.63  
% 3.89/1.63  Timing (in seconds)
% 3.89/1.63  ----------------------
% 3.89/1.64  Preprocessing        : 0.34
% 3.89/1.64  Parsing              : 0.18
% 3.89/1.64  CNF conversion       : 0.02
% 3.89/1.64  Main loop            : 0.55
% 3.89/1.64  Inferencing          : 0.20
% 3.89/1.64  Reduction            : 0.16
% 3.89/1.64  Demodulation         : 0.11
% 3.89/1.64  BG Simplification    : 0.02
% 3.89/1.64  Subsumption          : 0.12
% 3.89/1.64  Abstraction          : 0.03
% 3.89/1.64  MUC search           : 0.00
% 3.89/1.64  Cooper               : 0.00
% 3.89/1.64  Total                : 0.92
% 3.89/1.64  Index Insertion      : 0.00
% 3.89/1.64  Index Deletion       : 0.00
% 3.89/1.64  Index Matching       : 0.00
% 3.89/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
