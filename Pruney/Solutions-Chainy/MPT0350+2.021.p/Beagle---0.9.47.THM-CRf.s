%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:28 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 100 expanded)
%              Number of leaves         :   35 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 143 expanded)
%              Number of equality atoms :   38 (  50 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_74,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_48,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_357,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(k3_subset_1(A_71,B_72),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_173,plain,(
    ! [B_54,A_55] :
      ( r2_hidden(B_54,A_55)
      | ~ m1_subset_1(B_54,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_177,plain,(
    ! [B_54,A_13] :
      ( r1_tarski(B_54,A_13)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_173,c_16])).

tff(c_180,plain,(
    ! [B_54,A_13] :
      ( r1_tarski(B_54,A_13)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_13)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_177])).

tff(c_366,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k3_subset_1(A_73,B_74),A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(resolution,[status(thm)],[c_357,c_180])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_421,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(k3_subset_1(A_81,B_82),A_81) = k1_xboole_0
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(resolution,[status(thm)],[c_366,c_4])).

tff(c_434,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_421])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_124,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_150,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(B_53,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_124])).

tff(c_28,plain,(
    ! [A_18,B_19] : k3_tarski(k2_tarski(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_156,plain,(
    ! [B_53,A_52] : k2_xboole_0(B_53,A_52) = k2_xboole_0(A_52,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_28])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_313,plain,(
    ! [B_64,A_65] :
      ( r1_tarski(B_64,A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_177])).

tff(c_322,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_313])).

tff(c_326,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_322,c_4])).

tff(c_8,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_330,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_8])).

tff(c_333,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_6,c_330])).

tff(c_371,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_388,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_371])).

tff(c_392,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_8])).

tff(c_395,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_392])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [C_17,A_13] :
      ( r2_hidden(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_301,plain,(
    ! [B_62,A_63] :
      ( m1_subset_1(B_62,A_63)
      | ~ r2_hidden(B_62,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_307,plain,(
    ! [C_17,A_13] :
      ( m1_subset_1(C_17,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_301])).

tff(c_311,plain,(
    ! [C_17,A_13] :
      ( m1_subset_1(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_307])).

tff(c_810,plain,(
    ! [A_104,B_105,C_106] :
      ( k4_subset_1(A_104,B_105,C_106) = k2_xboole_0(B_105,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2400,plain,(
    ! [A_161,B_162,C_163] :
      ( k4_subset_1(A_161,B_162,C_163) = k2_xboole_0(B_162,C_163)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(A_161))
      | ~ r1_tarski(C_163,A_161) ) ),
    inference(resolution,[status(thm)],[c_311,c_810])).

tff(c_2543,plain,(
    ! [C_168] :
      ( k4_subset_1('#skF_3','#skF_4',C_168) = k2_xboole_0('#skF_4',C_168)
      | ~ r1_tarski(C_168,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_2400])).

tff(c_2584,plain,(
    ! [A_169] :
      ( k4_subset_1('#skF_3','#skF_4',A_169) = k2_xboole_0('#skF_4',A_169)
      | k4_xboole_0(A_169,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_2543])).

tff(c_38,plain,(
    ! [A_22] : k2_subset_1(A_22) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_51,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_2597,plain,
    ( k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3'
    | k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2584,c_51])).

tff(c_2615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_395,c_2597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:45:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.86  
% 4.16/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.86  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.16/1.86  
% 4.16/1.86  %Foreground sorts:
% 4.16/1.86  
% 4.16/1.86  
% 4.16/1.86  %Background operators:
% 4.16/1.86  
% 4.16/1.86  
% 4.16/1.86  %Foreground operators:
% 4.16/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.16/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.16/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.16/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.16/1.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.16/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.16/1.86  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.16/1.86  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.16/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.16/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.16/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.16/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.86  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.16/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.16/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.16/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.16/1.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.16/1.86  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.16/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.16/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/1.86  
% 4.16/1.88  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 4.16/1.88  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.16/1.88  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.16/1.88  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.16/1.88  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.16/1.88  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.16/1.88  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.16/1.88  tff(f_48, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.16/1.88  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.16/1.88  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.16/1.88  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.16/1.88  tff(f_80, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.16/1.88  tff(f_63, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.16/1.88  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.16/1.88  tff(c_357, plain, (![A_71, B_72]: (m1_subset_1(k3_subset_1(A_71, B_72), k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.16/1.88  tff(c_44, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.16/1.88  tff(c_173, plain, (![B_54, A_55]: (r2_hidden(B_54, A_55) | ~m1_subset_1(B_54, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.16/1.88  tff(c_16, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.16/1.88  tff(c_177, plain, (![B_54, A_13]: (r1_tarski(B_54, A_13) | ~m1_subset_1(B_54, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_173, c_16])).
% 4.16/1.88  tff(c_180, plain, (![B_54, A_13]: (r1_tarski(B_54, A_13) | ~m1_subset_1(B_54, k1_zfmisc_1(A_13)))), inference(negUnitSimplification, [status(thm)], [c_44, c_177])).
% 4.16/1.88  tff(c_366, plain, (![A_73, B_74]: (r1_tarski(k3_subset_1(A_73, B_74), A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(resolution, [status(thm)], [c_357, c_180])).
% 4.16/1.88  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.16/1.88  tff(c_421, plain, (![A_81, B_82]: (k4_xboole_0(k3_subset_1(A_81, B_82), A_81)=k1_xboole_0 | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(resolution, [status(thm)], [c_366, c_4])).
% 4.16/1.88  tff(c_434, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_421])).
% 4.16/1.88  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.16/1.88  tff(c_124, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.16/1.88  tff(c_150, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(B_53, A_52))), inference(superposition, [status(thm), theory('equality')], [c_10, c_124])).
% 4.16/1.88  tff(c_28, plain, (![A_18, B_19]: (k3_tarski(k2_tarski(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.16/1.88  tff(c_156, plain, (![B_53, A_52]: (k2_xboole_0(B_53, A_52)=k2_xboole_0(A_52, B_53))), inference(superposition, [status(thm), theory('equality')], [c_150, c_28])).
% 4.16/1.88  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.16/1.88  tff(c_313, plain, (![B_64, A_65]: (r1_tarski(B_64, A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)))), inference(negUnitSimplification, [status(thm)], [c_44, c_177])).
% 4.16/1.88  tff(c_322, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_313])).
% 4.16/1.88  tff(c_326, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_322, c_4])).
% 4.16/1.88  tff(c_8, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.16/1.88  tff(c_330, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_326, c_8])).
% 4.16/1.88  tff(c_333, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_6, c_330])).
% 4.16/1.88  tff(c_371, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.16/1.88  tff(c_388, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_371])).
% 4.16/1.88  tff(c_392, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_388, c_8])).
% 4.16/1.88  tff(c_395, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_333, c_392])).
% 4.16/1.88  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.16/1.88  tff(c_18, plain, (![C_17, A_13]: (r2_hidden(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.16/1.88  tff(c_301, plain, (![B_62, A_63]: (m1_subset_1(B_62, A_63) | ~r2_hidden(B_62, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.16/1.88  tff(c_307, plain, (![C_17, A_13]: (m1_subset_1(C_17, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(resolution, [status(thm)], [c_18, c_301])).
% 4.16/1.88  tff(c_311, plain, (![C_17, A_13]: (m1_subset_1(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(negUnitSimplification, [status(thm)], [c_44, c_307])).
% 4.16/1.88  tff(c_810, plain, (![A_104, B_105, C_106]: (k4_subset_1(A_104, B_105, C_106)=k2_xboole_0(B_105, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(A_104)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.16/1.88  tff(c_2400, plain, (![A_161, B_162, C_163]: (k4_subset_1(A_161, B_162, C_163)=k2_xboole_0(B_162, C_163) | ~m1_subset_1(B_162, k1_zfmisc_1(A_161)) | ~r1_tarski(C_163, A_161))), inference(resolution, [status(thm)], [c_311, c_810])).
% 4.16/1.88  tff(c_2543, plain, (![C_168]: (k4_subset_1('#skF_3', '#skF_4', C_168)=k2_xboole_0('#skF_4', C_168) | ~r1_tarski(C_168, '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_2400])).
% 4.16/1.88  tff(c_2584, plain, (![A_169]: (k4_subset_1('#skF_3', '#skF_4', A_169)=k2_xboole_0('#skF_4', A_169) | k4_xboole_0(A_169, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_2543])).
% 4.16/1.88  tff(c_38, plain, (![A_22]: (k2_subset_1(A_22)=A_22)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.16/1.88  tff(c_48, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.16/1.88  tff(c_51, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_48])).
% 4.16/1.88  tff(c_2597, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3' | k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2584, c_51])).
% 4.16/1.88  tff(c_2615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_434, c_395, c_2597])).
% 4.16/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.88  
% 4.16/1.88  Inference rules
% 4.16/1.88  ----------------------
% 4.16/1.88  #Ref     : 1
% 4.16/1.88  #Sup     : 541
% 4.16/1.88  #Fact    : 0
% 4.16/1.88  #Define  : 0
% 4.16/1.88  #Split   : 6
% 4.16/1.88  #Chain   : 0
% 4.16/1.88  #Close   : 0
% 4.16/1.88  
% 4.16/1.88  Ordering : KBO
% 4.16/1.88  
% 4.16/1.88  Simplification rules
% 4.16/1.88  ----------------------
% 4.16/1.88  #Subsume      : 73
% 4.16/1.88  #Demod        : 329
% 4.16/1.88  #Tautology    : 303
% 4.16/1.88  #SimpNegUnit  : 16
% 4.16/1.88  #BackRed      : 1
% 4.16/1.88  
% 4.16/1.88  #Partial instantiations: 0
% 4.16/1.88  #Strategies tried      : 1
% 4.16/1.88  
% 4.16/1.88  Timing (in seconds)
% 4.16/1.88  ----------------------
% 4.16/1.88  Preprocessing        : 0.35
% 4.16/1.88  Parsing              : 0.18
% 4.16/1.88  CNF conversion       : 0.02
% 4.16/1.88  Main loop            : 0.62
% 4.16/1.88  Inferencing          : 0.23
% 4.16/1.88  Reduction            : 0.21
% 4.16/1.88  Demodulation         : 0.15
% 4.16/1.88  BG Simplification    : 0.03
% 4.16/1.88  Subsumption          : 0.12
% 4.16/1.88  Abstraction          : 0.03
% 4.16/1.88  MUC search           : 0.00
% 4.16/1.88  Cooper               : 0.00
% 4.16/1.88  Total                : 1.00
% 4.16/1.88  Index Insertion      : 0.00
% 4.16/1.88  Index Deletion       : 0.00
% 4.16/1.88  Index Matching       : 0.00
% 4.16/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
