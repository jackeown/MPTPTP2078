%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:29 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 208 expanded)
%              Number of leaves         :   46 (  88 expanded)
%              Depth                    :   12
%              Number of atoms          :   78 ( 299 expanded)
%              Number of equality atoms :   48 ( 172 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_89,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_98,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_101,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

tff(f_83,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_81,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_75,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(c_14,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [A_9] :
      ( r2_xboole_0(k1_xboole_0,A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_157,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(A_65,B_66)
      | ~ r2_xboole_0(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_161,plain,(
    ! [A_9] :
      ( r1_tarski(k1_xboole_0,A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(resolution,[status(thm)],[c_18,c_157])).

tff(c_40,plain,(
    ! [C_44,A_40] :
      ( r2_hidden(C_44,k1_zfmisc_1(A_40))
      | ~ r1_tarski(C_44,A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_64,plain,(
    ! [A_52] : k9_setfam_1(A_52) = k1_zfmisc_1(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_68,plain,(
    ! [A_54] : k2_yellow_1(k9_setfam_1(A_54)) = k3_yellow_1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_71,plain,(
    ! [A_54] : k2_yellow_1(k1_zfmisc_1(A_54)) = k3_yellow_1(A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68])).

tff(c_311,plain,(
    ! [A_96] :
      ( k3_yellow_0(k2_yellow_1(A_96)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_96)
      | v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_335,plain,(
    ! [A_101] :
      ( k3_yellow_0(k3_yellow_1(A_101)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_101))
      | v1_xboole_0(k1_zfmisc_1(A_101)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_311])).

tff(c_345,plain,(
    ! [A_102] :
      ( k3_yellow_0(k3_yellow_1(A_102)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_102))
      | ~ r1_tarski(k1_xboole_0,A_102) ) ),
    inference(resolution,[status(thm)],[c_40,c_335])).

tff(c_20,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_370,plain,(
    ! [A_105] :
      ( k1_zfmisc_1(A_105) = k1_xboole_0
      | k3_yellow_0(k3_yellow_1(A_105)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_105) ) ),
    inference(resolution,[status(thm)],[c_345,c_20])).

tff(c_70,plain,(
    k3_yellow_0(k3_yellow_1('#skF_3')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_391,plain,
    ( k1_zfmisc_1('#skF_3') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_70])).

tff(c_397,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_402,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_161,c_397])).

tff(c_403,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_397])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_403])).

tff(c_427,plain,(
    k1_zfmisc_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_58,plain,(
    ! [A_47] : k3_tarski(k1_zfmisc_1(A_47)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_447,plain,(
    k3_tarski(k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_58])).

tff(c_56,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_526,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_56])).

tff(c_22,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_258,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_267,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_258])).

tff(c_270,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_267])).

tff(c_52,plain,(
    ! [B_46] : k4_xboole_0(k1_tarski(B_46),k1_tarski(B_46)) != k1_tarski(B_46) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_271,plain,(
    ! [B_46] : k1_tarski(B_46) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_52])).

tff(c_541,plain,(
    ! [B_46] : k1_tarski(B_46) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_271])).

tff(c_534,plain,(
    k1_zfmisc_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_427])).

tff(c_50,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_552,plain,(
    k1_zfmisc_1('#skF_3') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_526,c_50])).

tff(c_615,plain,(
    k1_tarski('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_552])).

tff(c_616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_541,c_615])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.40  
% 2.76/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.40  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.76/1.40  
% 2.76/1.40  %Foreground sorts:
% 2.76/1.40  
% 2.76/1.40  
% 2.76/1.40  %Background operators:
% 2.76/1.40  
% 2.76/1.40  
% 2.76/1.40  %Foreground operators:
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.40  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.76/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.40  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.76/1.40  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 2.76/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.76/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.76/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.40  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.76/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.40  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.76/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.40  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.76/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.76/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.76/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.76/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.76/1.40  
% 2.76/1.42  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.76/1.42  tff(f_47, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_xboole_1)).
% 2.76/1.42  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.76/1.42  tff(f_74, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.76/1.42  tff(f_89, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.76/1.42  tff(f_98, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.76/1.42  tff(f_96, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 2.76/1.42  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 2.76/1.42  tff(f_101, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_1)).
% 2.76/1.42  tff(f_83, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.76/1.42  tff(f_81, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.76/1.42  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.76/1.42  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.76/1.42  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.76/1.42  tff(f_80, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.76/1.42  tff(f_75, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.76/1.42  tff(c_14, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.42  tff(c_18, plain, (![A_9]: (r2_xboole_0(k1_xboole_0, A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.76/1.42  tff(c_157, plain, (![A_65, B_66]: (r1_tarski(A_65, B_66) | ~r2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.42  tff(c_161, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9) | k1_xboole_0=A_9)), inference(resolution, [status(thm)], [c_18, c_157])).
% 2.76/1.42  tff(c_40, plain, (![C_44, A_40]: (r2_hidden(C_44, k1_zfmisc_1(A_40)) | ~r1_tarski(C_44, A_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.76/1.42  tff(c_64, plain, (![A_52]: (k9_setfam_1(A_52)=k1_zfmisc_1(A_52))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.76/1.42  tff(c_68, plain, (![A_54]: (k2_yellow_1(k9_setfam_1(A_54))=k3_yellow_1(A_54))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.76/1.42  tff(c_71, plain, (![A_54]: (k2_yellow_1(k1_zfmisc_1(A_54))=k3_yellow_1(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68])).
% 2.76/1.42  tff(c_311, plain, (![A_96]: (k3_yellow_0(k2_yellow_1(A_96))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_96) | v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.76/1.42  tff(c_335, plain, (![A_101]: (k3_yellow_0(k3_yellow_1(A_101))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_101)) | v1_xboole_0(k1_zfmisc_1(A_101)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_311])).
% 2.76/1.42  tff(c_345, plain, (![A_102]: (k3_yellow_0(k3_yellow_1(A_102))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_102)) | ~r1_tarski(k1_xboole_0, A_102))), inference(resolution, [status(thm)], [c_40, c_335])).
% 2.76/1.42  tff(c_20, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.42  tff(c_370, plain, (![A_105]: (k1_zfmisc_1(A_105)=k1_xboole_0 | k3_yellow_0(k3_yellow_1(A_105))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_105))), inference(resolution, [status(thm)], [c_345, c_20])).
% 2.76/1.42  tff(c_70, plain, (k3_yellow_0(k3_yellow_1('#skF_3'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.76/1.42  tff(c_391, plain, (k1_zfmisc_1('#skF_3')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_370, c_70])).
% 2.76/1.42  tff(c_397, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_391])).
% 2.76/1.42  tff(c_402, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_161, c_397])).
% 2.76/1.42  tff(c_403, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_402, c_397])).
% 2.76/1.42  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_403])).
% 2.76/1.42  tff(c_427, plain, (k1_zfmisc_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_391])).
% 2.76/1.42  tff(c_58, plain, (![A_47]: (k3_tarski(k1_zfmisc_1(A_47))=A_47)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.76/1.42  tff(c_447, plain, (k3_tarski(k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_427, c_58])).
% 2.76/1.42  tff(c_56, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.76/1.42  tff(c_526, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_447, c_56])).
% 2.76/1.42  tff(c_22, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.76/1.42  tff(c_8, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.76/1.42  tff(c_258, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.76/1.42  tff(c_267, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_8, c_258])).
% 2.76/1.42  tff(c_270, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_267])).
% 2.76/1.42  tff(c_52, plain, (![B_46]: (k4_xboole_0(k1_tarski(B_46), k1_tarski(B_46))!=k1_tarski(B_46))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.76/1.42  tff(c_271, plain, (![B_46]: (k1_tarski(B_46)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_270, c_52])).
% 2.76/1.42  tff(c_541, plain, (![B_46]: (k1_tarski(B_46)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_526, c_271])).
% 2.76/1.42  tff(c_534, plain, (k1_zfmisc_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_526, c_427])).
% 2.76/1.42  tff(c_50, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.42  tff(c_552, plain, (k1_zfmisc_1('#skF_3')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_526, c_526, c_50])).
% 2.76/1.42  tff(c_615, plain, (k1_tarski('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_534, c_552])).
% 2.76/1.42  tff(c_616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_541, c_615])).
% 2.76/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.42  
% 2.76/1.42  Inference rules
% 2.76/1.42  ----------------------
% 2.76/1.42  #Ref     : 0
% 2.76/1.42  #Sup     : 116
% 2.76/1.42  #Fact    : 0
% 2.76/1.42  #Define  : 0
% 2.76/1.42  #Split   : 4
% 2.76/1.42  #Chain   : 0
% 2.76/1.42  #Close   : 0
% 2.76/1.42  
% 2.76/1.42  Ordering : KBO
% 2.76/1.42  
% 2.76/1.42  Simplification rules
% 2.76/1.42  ----------------------
% 2.76/1.42  #Subsume      : 2
% 2.76/1.42  #Demod        : 137
% 2.76/1.42  #Tautology    : 88
% 2.76/1.42  #SimpNegUnit  : 8
% 2.76/1.42  #BackRed      : 69
% 2.76/1.42  
% 2.76/1.42  #Partial instantiations: 0
% 2.76/1.42  #Strategies tried      : 1
% 2.76/1.42  
% 2.76/1.42  Timing (in seconds)
% 2.76/1.42  ----------------------
% 2.76/1.42  Preprocessing        : 0.34
% 2.76/1.42  Parsing              : 0.18
% 2.76/1.42  CNF conversion       : 0.02
% 2.76/1.42  Main loop            : 0.30
% 2.76/1.42  Inferencing          : 0.10
% 2.76/1.42  Reduction            : 0.10
% 2.76/1.42  Demodulation         : 0.07
% 2.76/1.42  BG Simplification    : 0.02
% 2.76/1.42  Subsumption          : 0.05
% 2.76/1.42  Abstraction          : 0.02
% 2.76/1.42  MUC search           : 0.00
% 2.76/1.42  Cooper               : 0.00
% 2.76/1.42  Total                : 0.69
% 2.76/1.42  Index Insertion      : 0.00
% 2.76/1.42  Index Deletion       : 0.00
% 2.76/1.42  Index Matching       : 0.00
% 2.76/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
