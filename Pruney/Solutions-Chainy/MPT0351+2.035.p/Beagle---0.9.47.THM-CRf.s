%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:41 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   70 (  79 expanded)
%              Number of leaves         :   38 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 (  77 expanded)
%              Number of equality atoms :   32 (  39 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_60,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_34,plain,(
    ! [A_45] : k2_subset_1(A_45) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_42])).

tff(c_18,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_106,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_131,plain,(
    ! [B_66,A_67] : k3_tarski(k2_tarski(B_66,A_67)) = k2_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_106])).

tff(c_32,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_137,plain,(
    ! [B_66,A_67] : k2_xboole_0(B_66,A_67) = k2_xboole_0(A_67,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_32])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_372,plain,(
    ! [C_90,A_91,B_92] :
      ( r2_hidden(C_90,A_91)
      | ~ r2_hidden(C_90,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_397,plain,(
    ! [A_100,B_101,A_102] :
      ( r2_hidden('#skF_1'(A_100,B_101),A_102)
      | ~ m1_subset_1(A_100,k1_zfmisc_1(A_102))
      | r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_6,c_372])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_409,plain,(
    ! [A_103,A_104] :
      ( ~ m1_subset_1(A_103,k1_zfmisc_1(A_104))
      | r1_tarski(A_103,A_104) ) ),
    inference(resolution,[status(thm)],[c_397,c_4])).

tff(c_418,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_409])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_431,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_418,c_12])).

tff(c_8,plain,(
    ! [A_6,B_7] : k5_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_435,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_8])).

tff(c_438,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_435])).

tff(c_14,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_443,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_14])).

tff(c_446,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_10,c_443])).

tff(c_36,plain,(
    ! [A_46] : m1_subset_1(k2_subset_1(A_46),k1_zfmisc_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_45,plain,(
    ! [A_46] : m1_subset_1(A_46,k1_zfmisc_1(A_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_527,plain,(
    ! [A_132,B_133,C_134] :
      ( k4_subset_1(A_132,B_133,C_134) = k2_xboole_0(B_133,C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(A_132))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_534,plain,(
    ! [A_135,B_136] :
      ( k4_subset_1(A_135,B_136,A_135) = k2_xboole_0(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(A_135)) ) ),
    inference(resolution,[status(thm)],[c_45,c_527])).

tff(c_538,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_534])).

tff(c_542,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_538])).

tff(c_544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_542])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:55:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.40  
% 2.66/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.41  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.66/1.41  
% 2.66/1.41  %Foreground sorts:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Background operators:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Foreground operators:
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.66/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.66/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.41  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.66/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.66/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.41  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.66/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.41  
% 2.66/1.42  tff(f_62, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.66/1.42  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.66/1.42  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.66/1.42  tff(f_60, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.66/1.42  tff(f_36, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.66/1.42  tff(f_44, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.66/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.66/1.42  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.66/1.42  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.66/1.42  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.66/1.42  tff(f_42, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.66/1.42  tff(f_64, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.66/1.42  tff(f_77, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.66/1.42  tff(c_34, plain, (![A_45]: (k2_subset_1(A_45)=A_45)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.42  tff(c_42, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.66/1.42  tff(c_46, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_42])).
% 2.66/1.42  tff(c_18, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.42  tff(c_106, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.42  tff(c_131, plain, (![B_66, A_67]: (k3_tarski(k2_tarski(B_66, A_67))=k2_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_18, c_106])).
% 2.66/1.42  tff(c_32, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.42  tff(c_137, plain, (![B_66, A_67]: (k2_xboole_0(B_66, A_67)=k2_xboole_0(A_67, B_66))), inference(superposition, [status(thm), theory('equality')], [c_131, c_32])).
% 2.66/1.42  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.66/1.42  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.66/1.42  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.66/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.42  tff(c_372, plain, (![C_90, A_91, B_92]: (r2_hidden(C_90, A_91) | ~r2_hidden(C_90, B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.66/1.42  tff(c_397, plain, (![A_100, B_101, A_102]: (r2_hidden('#skF_1'(A_100, B_101), A_102) | ~m1_subset_1(A_100, k1_zfmisc_1(A_102)) | r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_6, c_372])).
% 2.66/1.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.42  tff(c_409, plain, (![A_103, A_104]: (~m1_subset_1(A_103, k1_zfmisc_1(A_104)) | r1_tarski(A_103, A_104))), inference(resolution, [status(thm)], [c_397, c_4])).
% 2.66/1.42  tff(c_418, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_409])).
% 2.66/1.42  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.66/1.42  tff(c_431, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_418, c_12])).
% 2.66/1.42  tff(c_8, plain, (![A_6, B_7]: (k5_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.66/1.42  tff(c_435, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_431, c_8])).
% 2.66/1.42  tff(c_438, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_435])).
% 2.66/1.42  tff(c_14, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.66/1.42  tff(c_443, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_438, c_14])).
% 2.66/1.42  tff(c_446, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_10, c_443])).
% 2.66/1.42  tff(c_36, plain, (![A_46]: (m1_subset_1(k2_subset_1(A_46), k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.66/1.42  tff(c_45, plain, (![A_46]: (m1_subset_1(A_46, k1_zfmisc_1(A_46)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 2.66/1.42  tff(c_527, plain, (![A_132, B_133, C_134]: (k4_subset_1(A_132, B_133, C_134)=k2_xboole_0(B_133, C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(A_132)) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.66/1.42  tff(c_534, plain, (![A_135, B_136]: (k4_subset_1(A_135, B_136, A_135)=k2_xboole_0(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(A_135)))), inference(resolution, [status(thm)], [c_45, c_527])).
% 2.66/1.42  tff(c_538, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_534])).
% 2.66/1.42  tff(c_542, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_446, c_538])).
% 2.66/1.42  tff(c_544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_542])).
% 2.66/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.42  
% 2.66/1.42  Inference rules
% 2.66/1.42  ----------------------
% 2.66/1.42  #Ref     : 0
% 2.66/1.42  #Sup     : 118
% 2.66/1.42  #Fact    : 0
% 2.66/1.42  #Define  : 0
% 2.66/1.42  #Split   : 1
% 2.66/1.42  #Chain   : 0
% 2.66/1.42  #Close   : 0
% 2.66/1.42  
% 2.66/1.42  Ordering : KBO
% 2.66/1.42  
% 2.66/1.42  Simplification rules
% 2.66/1.42  ----------------------
% 2.66/1.42  #Subsume      : 6
% 2.66/1.42  #Demod        : 27
% 2.66/1.42  #Tautology    : 79
% 2.66/1.42  #SimpNegUnit  : 1
% 2.66/1.42  #BackRed      : 0
% 2.66/1.42  
% 2.66/1.42  #Partial instantiations: 0
% 2.66/1.42  #Strategies tried      : 1
% 2.66/1.42  
% 2.66/1.42  Timing (in seconds)
% 2.66/1.42  ----------------------
% 2.66/1.42  Preprocessing        : 0.32
% 2.66/1.42  Parsing              : 0.17
% 2.66/1.42  CNF conversion       : 0.02
% 2.66/1.42  Main loop            : 0.27
% 2.66/1.42  Inferencing          : 0.10
% 2.66/1.42  Reduction            : 0.08
% 2.66/1.42  Demodulation         : 0.06
% 2.66/1.42  BG Simplification    : 0.02
% 2.66/1.42  Subsumption          : 0.05
% 2.66/1.42  Abstraction          : 0.02
% 2.66/1.42  MUC search           : 0.00
% 2.66/1.42  Cooper               : 0.00
% 2.66/1.42  Total                : 0.63
% 2.66/1.42  Index Insertion      : 0.00
% 2.66/1.42  Index Deletion       : 0.00
% 2.66/1.42  Index Matching       : 0.00
% 2.66/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
