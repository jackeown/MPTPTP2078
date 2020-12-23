%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:39 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   69 (  78 expanded)
%              Number of leaves         :   36 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 (  89 expanded)
%              Number of equality atoms :   39 (  47 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_subset_1 > k1_enumset1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k7_subset_1(A,k2_subset_1(A),k5_setfam_1(A,B)) = k6_setfam_1(A,k7_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_259,plain,(
    ! [A_69,B_70,C_71] :
      ( k7_subset_1(A_69,B_70,C_71) = k4_xboole_0(B_70,C_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_457,plain,(
    ! [B_86,A_87,C_88] :
      ( k7_subset_1(B_86,A_87,C_88) = k4_xboole_0(A_87,C_88)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(resolution,[status(thm)],[c_32,c_259])).

tff(c_477,plain,(
    ! [B_2,C_88] : k7_subset_1(B_2,B_2,C_88) = k4_xboole_0(B_2,C_88) ),
    inference(resolution,[status(thm)],[c_6,c_457])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_139,plain,(
    ! [A_46,B_47] : k5_xboole_0(A_46,k3_xboole_0(A_46,B_47)) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_148,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_139])).

tff(c_151,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_148])).

tff(c_16,plain,(
    ! [A_9] : k1_subset_1(A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_subset_1(A_15)) = k2_subset_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_43,plain,(
    ! [A_15] : k3_subset_1(A_15,k1_xboole_0) = k2_subset_1(A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22])).

tff(c_24,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_181,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k3_subset_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_193,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = k3_subset_1(A_16,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_181])).

tff(c_198,plain,(
    ! [A_16] : k2_subset_1(A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_43,c_193])).

tff(c_34,plain,(
    ! [A_23,B_24] :
      ( k7_subset_1(A_23,k2_subset_1(A_23),k5_setfam_1(A_23,B_24)) = k6_setfam_1(A_23,k7_setfam_1(A_23,B_24))
      | k1_xboole_0 = B_24
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_408,plain,(
    ! [A_83,B_84] :
      ( k7_subset_1(A_83,A_83,k5_setfam_1(A_83,B_84)) = k6_setfam_1(A_83,k7_setfam_1(A_83,B_84))
      | k1_xboole_0 = B_84
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(A_83))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_34])).

tff(c_416,plain,
    ( k7_subset_1('#skF_1','#skF_1',k5_setfam_1('#skF_1','#skF_2')) = k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_408])).

tff(c_424,plain,(
    k7_subset_1('#skF_1','#skF_1',k5_setfam_1('#skF_1','#skF_2')) = k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_416])).

tff(c_478,plain,(
    k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k5_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_424])).

tff(c_38,plain,(
    k6_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k5_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_500,plain,(
    k4_xboole_0('#skF_1',k5_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k5_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_38])).

tff(c_272,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1(k5_setfam_1(A_72,B_73),k1_zfmisc_1(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k1_zfmisc_1(A_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_305,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k5_setfam_1(A_77,B_78),A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(resolution,[status(thm)],[c_272,c_30])).

tff(c_319,plain,(
    r1_tarski(k5_setfam_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_305])).

tff(c_195,plain,(
    ! [B_22,A_21] :
      ( k4_xboole_0(B_22,A_21) = k3_subset_1(B_22,A_21)
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(resolution,[status(thm)],[c_32,c_181])).

tff(c_326,plain,(
    k4_xboole_0('#skF_1',k5_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k5_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_319,c_195])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_500,c_326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:03:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.39  
% 2.56/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.39  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_subset_1 > k1_enumset1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.56/1.39  
% 2.56/1.39  %Foreground sorts:
% 2.56/1.39  
% 2.56/1.39  
% 2.56/1.39  %Background operators:
% 2.56/1.39  
% 2.56/1.39  
% 2.56/1.39  %Foreground operators:
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.56/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.39  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.56/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.56/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.56/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.39  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.56/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.56/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.39  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.39  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.39  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.56/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.56/1.39  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.56/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.56/1.39  
% 2.56/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.56/1.40  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.56/1.40  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.56/1.40  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 2.56/1.40  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.56/1.40  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.56/1.40  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.56/1.40  tff(f_41, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.56/1.40  tff(f_51, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.56/1.40  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.56/1.40  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.56/1.40  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k7_subset_1(A, k2_subset_1(A), k5_setfam_1(A, B)) = k6_setfam_1(A, k7_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_setfam_1)).
% 2.56/1.40  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.56/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.40  tff(c_32, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.56/1.40  tff(c_259, plain, (![A_69, B_70, C_71]: (k7_subset_1(A_69, B_70, C_71)=k4_xboole_0(B_70, C_71) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.56/1.40  tff(c_457, plain, (![B_86, A_87, C_88]: (k7_subset_1(B_86, A_87, C_88)=k4_xboole_0(A_87, C_88) | ~r1_tarski(A_87, B_86))), inference(resolution, [status(thm)], [c_32, c_259])).
% 2.56/1.40  tff(c_477, plain, (![B_2, C_88]: (k7_subset_1(B_2, B_2, C_88)=k4_xboole_0(B_2, C_88))), inference(resolution, [status(thm)], [c_6, c_457])).
% 2.56/1.40  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.56/1.40  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.56/1.40  tff(c_12, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.56/1.40  tff(c_10, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.40  tff(c_139, plain, (![A_46, B_47]: (k5_xboole_0(A_46, k3_xboole_0(A_46, B_47))=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.40  tff(c_148, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_139])).
% 2.56/1.40  tff(c_151, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_148])).
% 2.56/1.40  tff(c_16, plain, (![A_9]: (k1_subset_1(A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.56/1.40  tff(c_22, plain, (![A_15]: (k3_subset_1(A_15, k1_subset_1(A_15))=k2_subset_1(A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.56/1.40  tff(c_43, plain, (![A_15]: (k3_subset_1(A_15, k1_xboole_0)=k2_subset_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22])).
% 2.56/1.40  tff(c_24, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.56/1.40  tff(c_181, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k3_subset_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.56/1.40  tff(c_193, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=k3_subset_1(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_181])).
% 2.56/1.40  tff(c_198, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_151, c_43, c_193])).
% 2.56/1.40  tff(c_34, plain, (![A_23, B_24]: (k7_subset_1(A_23, k2_subset_1(A_23), k5_setfam_1(A_23, B_24))=k6_setfam_1(A_23, k7_setfam_1(A_23, B_24)) | k1_xboole_0=B_24 | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_23))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.56/1.40  tff(c_408, plain, (![A_83, B_84]: (k7_subset_1(A_83, A_83, k5_setfam_1(A_83, B_84))=k6_setfam_1(A_83, k7_setfam_1(A_83, B_84)) | k1_xboole_0=B_84 | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(A_83))))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_34])).
% 2.56/1.40  tff(c_416, plain, (k7_subset_1('#skF_1', '#skF_1', k5_setfam_1('#skF_1', '#skF_2'))=k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_42, c_408])).
% 2.56/1.40  tff(c_424, plain, (k7_subset_1('#skF_1', '#skF_1', k5_setfam_1('#skF_1', '#skF_2'))=k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_416])).
% 2.56/1.40  tff(c_478, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_424])).
% 2.56/1.40  tff(c_38, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.56/1.40  tff(c_500, plain, (k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_38])).
% 2.56/1.40  tff(c_272, plain, (![A_72, B_73]: (m1_subset_1(k5_setfam_1(A_72, B_73), k1_zfmisc_1(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(k1_zfmisc_1(A_72))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.56/1.40  tff(c_30, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.56/1.40  tff(c_305, plain, (![A_77, B_78]: (r1_tarski(k5_setfam_1(A_77, B_78), A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(resolution, [status(thm)], [c_272, c_30])).
% 2.56/1.40  tff(c_319, plain, (r1_tarski(k5_setfam_1('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_42, c_305])).
% 2.56/1.40  tff(c_195, plain, (![B_22, A_21]: (k4_xboole_0(B_22, A_21)=k3_subset_1(B_22, A_21) | ~r1_tarski(A_21, B_22))), inference(resolution, [status(thm)], [c_32, c_181])).
% 2.56/1.40  tff(c_326, plain, (k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_319, c_195])).
% 2.56/1.40  tff(c_527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_500, c_326])).
% 2.56/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.40  
% 2.56/1.40  Inference rules
% 2.56/1.40  ----------------------
% 2.56/1.40  #Ref     : 0
% 2.56/1.40  #Sup     : 114
% 2.56/1.40  #Fact    : 0
% 2.56/1.40  #Define  : 0
% 2.56/1.40  #Split   : 2
% 2.56/1.40  #Chain   : 0
% 2.56/1.40  #Close   : 0
% 2.56/1.40  
% 2.56/1.40  Ordering : KBO
% 2.56/1.40  
% 2.56/1.40  Simplification rules
% 2.56/1.40  ----------------------
% 2.56/1.40  #Subsume      : 3
% 2.56/1.40  #Demod        : 37
% 2.56/1.40  #Tautology    : 67
% 2.56/1.40  #SimpNegUnit  : 2
% 2.56/1.40  #BackRed      : 4
% 2.56/1.40  
% 2.56/1.40  #Partial instantiations: 0
% 2.56/1.40  #Strategies tried      : 1
% 2.56/1.40  
% 2.56/1.40  Timing (in seconds)
% 2.56/1.40  ----------------------
% 2.56/1.41  Preprocessing        : 0.31
% 2.56/1.41  Parsing              : 0.16
% 2.56/1.41  CNF conversion       : 0.02
% 2.56/1.41  Main loop            : 0.27
% 2.56/1.41  Inferencing          : 0.10
% 2.56/1.41  Reduction            : 0.08
% 2.56/1.41  Demodulation         : 0.06
% 2.56/1.41  BG Simplification    : 0.02
% 2.56/1.41  Subsumption          : 0.05
% 2.56/1.41  Abstraction          : 0.01
% 2.56/1.41  MUC search           : 0.00
% 2.56/1.41  Cooper               : 0.00
% 2.56/1.41  Total                : 0.61
% 2.56/1.41  Index Insertion      : 0.00
% 2.56/1.41  Index Deletion       : 0.00
% 2.56/1.41  Index Matching       : 0.00
% 2.56/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
