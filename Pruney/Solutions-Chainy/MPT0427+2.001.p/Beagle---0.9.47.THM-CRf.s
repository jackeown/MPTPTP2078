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
% DateTime   : Thu Dec  3 09:57:56 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 220 expanded)
%              Number of leaves         :   35 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 421 expanded)
%              Number of equality atoms :   46 ( 129 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k6_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_197,plain,(
    ! [A_66,B_67] :
      ( k6_setfam_1(A_66,B_67) = k1_setfam_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_210,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_197])).

tff(c_258,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k6_setfam_1(A_73,B_74),k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_274,plain,
    ( m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_258])).

tff(c_282,plain,(
    m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_274])).

tff(c_36,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_334,plain,(
    r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_282,c_36])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_59,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_66,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_59])).

tff(c_209,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_197])).

tff(c_285,plain,(
    ! [A_75,B_76] :
      ( k8_setfam_1(A_75,B_76) = k6_setfam_1(A_75,B_76)
      | k1_xboole_0 = B_76
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(A_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_296,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_285])).

tff(c_303,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_296])).

tff(c_347,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_38,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,k1_zfmisc_1(B_30))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_191,plain,(
    ! [A_64] :
      ( k8_setfam_1(A_64,k1_xboole_0) = A_64
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_195,plain,(
    ! [A_64] :
      ( k8_setfam_1(A_64,k1_xboole_0) = A_64
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_64)) ) ),
    inference(resolution,[status(thm)],[c_38,c_191])).

tff(c_391,plain,(
    ! [A_83] :
      ( k8_setfam_1(A_83,'#skF_3') = A_83
      | ~ r1_tarski('#skF_3',k1_zfmisc_1(A_83)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_347,c_195])).

tff(c_395,plain,(
    k8_setfam_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_391])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    ! [A_53,B_54] :
      ( k2_xboole_0(k1_tarski(A_53),B_54) = B_54
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),B_17) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_121,plain,(
    ! [B_55,A_56] :
      ( k1_xboole_0 != B_55
      | ~ r2_hidden(A_56,B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_22])).

tff(c_125,plain,(
    ! [A_1] :
      ( k1_xboole_0 != A_1
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_121])).

tff(c_44,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_150,plain,(
    ! [B_60,A_61] :
      ( v1_xboole_0(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_168,plain,(
    ! [A_62,B_63] :
      ( v1_xboole_0(A_62)
      | ~ v1_xboole_0(B_63)
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_38,c_150])).

tff(c_184,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_168])).

tff(c_185,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_189,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_125,c_185])).

tff(c_299,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_285])).

tff(c_305,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_299])).

tff(c_306,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_305])).

tff(c_42,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_307,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_42])).

tff(c_396,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_307])).

tff(c_399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_396])).

tff(c_401,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_40,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k1_setfam_1(B_32),k1_setfam_1(A_31))
      | k1_xboole_0 = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_400,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_402,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_307])).

tff(c_409,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_402])).

tff(c_412,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_409])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_412])).

tff(c_416,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_424,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_416,c_6])).

tff(c_415,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_420,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_415,c_6])).

tff(c_434,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_420])).

tff(c_126,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_141,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_126])).

tff(c_148,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_441,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_148])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_441])).

tff(c_450,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_466,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_42])).

tff(c_472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.32  
% 2.23/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.23/1.32  
% 2.23/1.32  %Foreground sorts:
% 2.23/1.32  
% 2.23/1.32  
% 2.23/1.32  %Background operators:
% 2.23/1.32  
% 2.23/1.32  
% 2.23/1.32  %Foreground operators:
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.32  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.23/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.32  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.32  
% 2.64/1.34  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.64/1.34  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.64/1.34  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.64/1.34  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k6_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_setfam_1)).
% 2.64/1.34  tff(f_86, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.64/1.34  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.64/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.64/1.34  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.64/1.34  tff(f_54, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.64/1.34  tff(f_61, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.64/1.34  tff(f_92, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.64/1.34  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.64/1.34  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.64/1.34  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.64/1.34  tff(c_197, plain, (![A_66, B_67]: (k6_setfam_1(A_66, B_67)=k1_setfam_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.64/1.34  tff(c_210, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_197])).
% 2.64/1.34  tff(c_258, plain, (![A_73, B_74]: (m1_subset_1(k6_setfam_1(A_73, B_74), k1_zfmisc_1(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.64/1.34  tff(c_274, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_210, c_258])).
% 2.64/1.34  tff(c_282, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_274])).
% 2.64/1.34  tff(c_36, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.64/1.34  tff(c_334, plain, (r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_282, c_36])).
% 2.64/1.34  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.64/1.34  tff(c_59, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.64/1.34  tff(c_66, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_59])).
% 2.64/1.34  tff(c_209, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_197])).
% 2.64/1.34  tff(c_285, plain, (![A_75, B_76]: (k8_setfam_1(A_75, B_76)=k6_setfam_1(A_75, B_76) | k1_xboole_0=B_76 | ~m1_subset_1(B_76, k1_zfmisc_1(k1_zfmisc_1(A_75))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.64/1.34  tff(c_296, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_48, c_285])).
% 2.64/1.34  tff(c_303, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_209, c_296])).
% 2.64/1.34  tff(c_347, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_303])).
% 2.64/1.34  tff(c_38, plain, (![A_29, B_30]: (m1_subset_1(A_29, k1_zfmisc_1(B_30)) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.64/1.34  tff(c_191, plain, (![A_64]: (k8_setfam_1(A_64, k1_xboole_0)=A_64 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_64))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.64/1.34  tff(c_195, plain, (![A_64]: (k8_setfam_1(A_64, k1_xboole_0)=A_64 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_64)))), inference(resolution, [status(thm)], [c_38, c_191])).
% 2.64/1.34  tff(c_391, plain, (![A_83]: (k8_setfam_1(A_83, '#skF_3')=A_83 | ~r1_tarski('#skF_3', k1_zfmisc_1(A_83)))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_347, c_195])).
% 2.64/1.34  tff(c_395, plain, (k8_setfam_1('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_66, c_391])).
% 2.64/1.34  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.34  tff(c_109, plain, (![A_53, B_54]: (k2_xboole_0(k1_tarski(A_53), B_54)=B_54 | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.64/1.34  tff(c_22, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.64/1.34  tff(c_121, plain, (![B_55, A_56]: (k1_xboole_0!=B_55 | ~r2_hidden(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_109, c_22])).
% 2.64/1.34  tff(c_125, plain, (![A_1]: (k1_xboole_0!=A_1 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_121])).
% 2.64/1.34  tff(c_44, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.64/1.34  tff(c_150, plain, (![B_60, A_61]: (v1_xboole_0(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.64/1.34  tff(c_168, plain, (![A_62, B_63]: (v1_xboole_0(A_62) | ~v1_xboole_0(B_63) | ~r1_tarski(A_62, B_63))), inference(resolution, [status(thm)], [c_38, c_150])).
% 2.64/1.34  tff(c_184, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_168])).
% 2.64/1.34  tff(c_185, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_184])).
% 2.64/1.34  tff(c_189, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_125, c_185])).
% 2.64/1.34  tff(c_299, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_285])).
% 2.64/1.34  tff(c_305, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_210, c_299])).
% 2.64/1.34  tff(c_306, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_189, c_305])).
% 2.64/1.34  tff(c_42, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.64/1.34  tff(c_307, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_42])).
% 2.64/1.34  tff(c_396, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_395, c_307])).
% 2.64/1.34  tff(c_399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_334, c_396])).
% 2.64/1.34  tff(c_401, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_303])).
% 2.64/1.34  tff(c_40, plain, (![B_32, A_31]: (r1_tarski(k1_setfam_1(B_32), k1_setfam_1(A_31)) | k1_xboole_0=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.64/1.34  tff(c_400, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_303])).
% 2.64/1.34  tff(c_402, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_307])).
% 2.64/1.34  tff(c_409, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_402])).
% 2.64/1.34  tff(c_412, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_409])).
% 2.64/1.34  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_401, c_412])).
% 2.64/1.34  tff(c_416, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_184])).
% 2.64/1.34  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.64/1.34  tff(c_424, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_416, c_6])).
% 2.64/1.34  tff(c_415, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_184])).
% 2.64/1.34  tff(c_420, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_415, c_6])).
% 2.64/1.34  tff(c_434, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_424, c_420])).
% 2.64/1.34  tff(c_126, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.64/1.34  tff(c_141, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_126])).
% 2.64/1.34  tff(c_148, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_141])).
% 2.64/1.34  tff(c_441, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_434, c_148])).
% 2.64/1.34  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_441])).
% 2.64/1.34  tff(c_450, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_141])).
% 2.64/1.34  tff(c_466, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_450, c_42])).
% 2.64/1.34  tff(c_472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_466])).
% 2.64/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.34  
% 2.64/1.34  Inference rules
% 2.64/1.34  ----------------------
% 2.64/1.34  #Ref     : 0
% 2.64/1.34  #Sup     : 89
% 2.64/1.34  #Fact    : 0
% 2.64/1.34  #Define  : 0
% 2.64/1.34  #Split   : 7
% 2.64/1.34  #Chain   : 0
% 2.64/1.34  #Close   : 0
% 2.64/1.34  
% 2.64/1.34  Ordering : KBO
% 2.64/1.34  
% 2.64/1.34  Simplification rules
% 2.64/1.34  ----------------------
% 2.64/1.34  #Subsume      : 8
% 2.64/1.34  #Demod        : 47
% 2.64/1.34  #Tautology    : 37
% 2.64/1.34  #SimpNegUnit  : 2
% 2.64/1.34  #BackRed      : 31
% 2.64/1.34  
% 2.64/1.34  #Partial instantiations: 0
% 2.64/1.34  #Strategies tried      : 1
% 2.64/1.34  
% 2.64/1.34  Timing (in seconds)
% 2.64/1.34  ----------------------
% 2.64/1.34  Preprocessing        : 0.31
% 2.64/1.34  Parsing              : 0.17
% 2.64/1.34  CNF conversion       : 0.02
% 2.64/1.34  Main loop            : 0.26
% 2.64/1.34  Inferencing          : 0.09
% 2.64/1.34  Reduction            : 0.08
% 2.64/1.34  Demodulation         : 0.06
% 2.64/1.34  BG Simplification    : 0.02
% 2.64/1.34  Subsumption          : 0.05
% 2.64/1.34  Abstraction          : 0.02
% 2.64/1.34  MUC search           : 0.00
% 2.64/1.34  Cooper               : 0.00
% 2.64/1.34  Total                : 0.61
% 2.64/1.34  Index Insertion      : 0.00
% 2.64/1.34  Index Deletion       : 0.00
% 2.64/1.34  Index Matching       : 0.00
% 2.64/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
