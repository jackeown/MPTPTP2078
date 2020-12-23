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
% DateTime   : Thu Dec  3 10:15:29 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   69 (  81 expanded)
%              Number of leaves         :   40 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 124 expanded)
%              Number of equality atoms :   51 (  63 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_68,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(c_60,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [A_42] : k1_setfam_1(k1_tarski(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    ! [A_52,B_53] : k1_setfam_1(k2_tarski(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_103,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = k1_setfam_1(k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_94])).

tff(c_106,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_103])).

tff(c_130,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_139,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k4_xboole_0(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_130])).

tff(c_142,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_139])).

tff(c_20,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_143,plain,(
    ! [B_33] : k1_tarski(B_33) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_20])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_343,plain,(
    ! [D_158,C_159,B_160,A_161] :
      ( r2_hidden(k1_funct_1(D_158,C_159),B_160)
      | k1_xboole_0 = B_160
      | ~ r2_hidden(C_159,A_161)
      | ~ m1_subset_1(D_158,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160)))
      | ~ v1_funct_2(D_158,A_161,B_160)
      | ~ v1_funct_1(D_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_380,plain,(
    ! [D_162,B_163] :
      ( r2_hidden(k1_funct_1(D_162,'#skF_5'),B_163)
      | k1_xboole_0 = B_163
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_163)))
      | ~ v1_funct_2(D_162,'#skF_3',B_163)
      | ~ v1_funct_1(D_162) ) ),
    inference(resolution,[status(thm)],[c_62,c_343])).

tff(c_383,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_380])).

tff(c_386,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_383])).

tff(c_387,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_386])).

tff(c_8,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k2_enumset1(A_7,A_7,B_8,C_9) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_237,plain,(
    ! [C_110,F_108,A_106,D_107,B_109] :
      ( F_108 = D_107
      | F_108 = C_110
      | F_108 = B_109
      | F_108 = A_106
      | ~ r2_hidden(F_108,k2_enumset1(A_106,B_109,C_110,D_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_261,plain,(
    ! [F_111,C_112,B_113,A_114] :
      ( F_111 = C_112
      | F_111 = B_113
      | F_111 = A_114
      | F_111 = A_114
      | ~ r2_hidden(F_111,k1_enumset1(A_114,B_113,C_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_237])).

tff(c_280,plain,(
    ! [F_115,B_116,A_117] :
      ( F_115 = B_116
      | F_115 = A_117
      | F_115 = A_117
      | F_115 = A_117
      | ~ r2_hidden(F_115,k2_tarski(A_117,B_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_261])).

tff(c_289,plain,(
    ! [F_115,A_4] :
      ( F_115 = A_4
      | F_115 = A_4
      | F_115 = A_4
      | F_115 = A_4
      | ~ r2_hidden(F_115,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_280])).

tff(c_392,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_387,c_289])).

tff(c_397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_60,c_60,c_392])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:17:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.40  
% 2.67/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.41  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.67/1.41  
% 2.67/1.41  %Foreground sorts:
% 2.67/1.41  
% 2.67/1.41  
% 2.67/1.41  %Background operators:
% 2.67/1.41  
% 2.67/1.41  
% 2.67/1.41  %Foreground operators:
% 2.67/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.67/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.67/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.67/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.67/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.67/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.67/1.41  
% 2.67/1.42  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.67/1.42  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.67/1.42  tff(f_68, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.67/1.42  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.67/1.42  tff(f_70, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.67/1.42  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.67/1.42  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.67/1.42  tff(f_82, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.67/1.42  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.67/1.42  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.67/1.42  tff(f_66, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 2.67/1.42  tff(c_60, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.42  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.67/1.42  tff(c_54, plain, (![A_42]: (k1_setfam_1(k1_tarski(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.67/1.42  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.42  tff(c_94, plain, (![A_52, B_53]: (k1_setfam_1(k2_tarski(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.67/1.42  tff(c_103, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=k1_setfam_1(k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_94])).
% 2.67/1.42  tff(c_106, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_103])).
% 2.67/1.42  tff(c_130, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.42  tff(c_139, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k4_xboole_0(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_106, c_130])).
% 2.67/1.42  tff(c_142, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_139])).
% 2.67/1.42  tff(c_20, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.42  tff(c_143, plain, (![B_33]: (k1_tarski(B_33)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_142, c_20])).
% 2.67/1.42  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.42  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.42  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.42  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.42  tff(c_343, plain, (![D_158, C_159, B_160, A_161]: (r2_hidden(k1_funct_1(D_158, C_159), B_160) | k1_xboole_0=B_160 | ~r2_hidden(C_159, A_161) | ~m1_subset_1(D_158, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))) | ~v1_funct_2(D_158, A_161, B_160) | ~v1_funct_1(D_158))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.42  tff(c_380, plain, (![D_162, B_163]: (r2_hidden(k1_funct_1(D_162, '#skF_5'), B_163) | k1_xboole_0=B_163 | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_163))) | ~v1_funct_2(D_162, '#skF_3', B_163) | ~v1_funct_1(D_162))), inference(resolution, [status(thm)], [c_62, c_343])).
% 2.67/1.42  tff(c_383, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_380])).
% 2.67/1.42  tff(c_386, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_383])).
% 2.67/1.42  tff(c_387, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_143, c_386])).
% 2.67/1.42  tff(c_8, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.42  tff(c_10, plain, (![A_7, B_8, C_9]: (k2_enumset1(A_7, A_7, B_8, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.42  tff(c_237, plain, (![C_110, F_108, A_106, D_107, B_109]: (F_108=D_107 | F_108=C_110 | F_108=B_109 | F_108=A_106 | ~r2_hidden(F_108, k2_enumset1(A_106, B_109, C_110, D_107)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.67/1.42  tff(c_261, plain, (![F_111, C_112, B_113, A_114]: (F_111=C_112 | F_111=B_113 | F_111=A_114 | F_111=A_114 | ~r2_hidden(F_111, k1_enumset1(A_114, B_113, C_112)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_237])).
% 2.67/1.42  tff(c_280, plain, (![F_115, B_116, A_117]: (F_115=B_116 | F_115=A_117 | F_115=A_117 | F_115=A_117 | ~r2_hidden(F_115, k2_tarski(A_117, B_116)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_261])).
% 2.67/1.42  tff(c_289, plain, (![F_115, A_4]: (F_115=A_4 | F_115=A_4 | F_115=A_4 | F_115=A_4 | ~r2_hidden(F_115, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_280])).
% 2.67/1.42  tff(c_392, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_387, c_289])).
% 2.67/1.42  tff(c_397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_60, c_60, c_392])).
% 2.67/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.42  
% 2.67/1.42  Inference rules
% 2.67/1.42  ----------------------
% 2.67/1.42  #Ref     : 0
% 2.67/1.42  #Sup     : 73
% 2.67/1.42  #Fact    : 0
% 2.67/1.42  #Define  : 0
% 2.67/1.42  #Split   : 0
% 2.67/1.42  #Chain   : 0
% 2.67/1.42  #Close   : 0
% 2.67/1.42  
% 2.67/1.42  Ordering : KBO
% 2.67/1.42  
% 2.67/1.42  Simplification rules
% 2.67/1.42  ----------------------
% 2.67/1.42  #Subsume      : 0
% 2.67/1.42  #Demod        : 8
% 2.67/1.42  #Tautology    : 43
% 2.67/1.42  #SimpNegUnit  : 4
% 2.67/1.42  #BackRed      : 1
% 2.67/1.42  
% 2.67/1.42  #Partial instantiations: 0
% 2.67/1.42  #Strategies tried      : 1
% 2.67/1.42  
% 2.67/1.42  Timing (in seconds)
% 2.67/1.42  ----------------------
% 2.67/1.42  Preprocessing        : 0.33
% 2.67/1.42  Parsing              : 0.16
% 2.67/1.42  CNF conversion       : 0.02
% 2.67/1.42  Main loop            : 0.27
% 2.67/1.42  Inferencing          : 0.10
% 2.67/1.42  Reduction            : 0.08
% 2.67/1.42  Demodulation         : 0.06
% 2.67/1.42  BG Simplification    : 0.02
% 2.67/1.42  Subsumption          : 0.05
% 2.67/1.42  Abstraction          : 0.02
% 2.67/1.42  MUC search           : 0.00
% 2.67/1.42  Cooper               : 0.00
% 2.67/1.43  Total                : 0.63
% 2.67/1.43  Index Insertion      : 0.00
% 2.67/1.43  Index Deletion       : 0.00
% 2.67/1.43  Index Matching       : 0.00
% 2.67/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
