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
% DateTime   : Thu Dec  3 10:07:04 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 111 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 174 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_26,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_79,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_82,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_79])).

tff(c_85,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_82])).

tff(c_147,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_151,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_147])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v5_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_161,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(A_67,k2_xboole_0(B_68,C_69))
      | ~ r1_tarski(k4_xboole_0(A_67,B_68),C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_174,plain,(
    ! [A_70,B_71] : r1_tarski(A_70,k2_xboole_0(B_71,A_70)) ),
    inference(resolution,[status(thm)],[c_6,c_161])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_199,plain,(
    ! [A_3,B_71,A_70] :
      ( r1_tarski(A_3,k2_xboole_0(B_71,A_70))
      | ~ r1_tarski(A_3,A_70) ) ),
    inference(resolution,[status(thm)],[c_174,c_4])).

tff(c_93,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_97,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_93])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_535,plain,(
    ! [A_109,B_110,A_111] :
      ( r1_tarski(A_109,k2_xboole_0(B_110,A_111))
      | ~ r1_tarski(A_109,A_111) ) ),
    inference(resolution,[status(thm)],[c_174,c_4])).

tff(c_558,plain,(
    ! [A_109,B_2,A_1] :
      ( r1_tarski(A_109,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_109,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_535])).

tff(c_24,plain,(
    ! [A_23] :
      ( k2_xboole_0(k1_relat_1(A_23),k2_relat_1(A_23)) = k3_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_233,plain,(
    ! [A_74,C_75,B_76] :
      ( r1_tarski(k2_xboole_0(A_74,C_75),B_76)
      | ~ r1_tarski(C_75,B_76)
      | ~ r1_tarski(A_74,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_753,plain,(
    ! [A_131,B_132] :
      ( r1_tarski(k3_relat_1(A_131),B_132)
      | ~ r1_tarski(k2_relat_1(A_131),B_132)
      | ~ r1_tarski(k1_relat_1(A_131),B_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_233])).

tff(c_32,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_777,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_753,c_32])).

tff(c_791,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_777])).

tff(c_799,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_791])).

tff(c_809,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_558,c_799])).

tff(c_816,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_809])).

tff(c_820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_97,c_816])).

tff(c_821,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_791])).

tff(c_833,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_199,c_821])).

tff(c_839,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_833])).

tff(c_843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_151,c_839])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:33:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.49  
% 3.06/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.49  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.06/1.49  
% 3.06/1.49  %Foreground sorts:
% 3.06/1.49  
% 3.06/1.49  
% 3.06/1.49  %Background operators:
% 3.06/1.49  
% 3.06/1.49  
% 3.06/1.49  %Foreground operators:
% 3.06/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.06/1.49  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.06/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.06/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.06/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.06/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.06/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.06/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.49  
% 3.06/1.51  tff(f_72, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.06/1.51  tff(f_83, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 3.06/1.51  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.06/1.51  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.06/1.51  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.06/1.51  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.06/1.51  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.06/1.51  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.06/1.51  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.06/1.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.06/1.51  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.06/1.51  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.06/1.51  tff(c_26, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.06/1.51  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.06/1.51  tff(c_79, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.06/1.51  tff(c_82, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_79])).
% 3.06/1.51  tff(c_85, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_82])).
% 3.06/1.51  tff(c_147, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.06/1.51  tff(c_151, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_147])).
% 3.06/1.51  tff(c_22, plain, (![B_22, A_21]: (r1_tarski(k2_relat_1(B_22), A_21) | ~v5_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.06/1.51  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.51  tff(c_161, plain, (![A_67, B_68, C_69]: (r1_tarski(A_67, k2_xboole_0(B_68, C_69)) | ~r1_tarski(k4_xboole_0(A_67, B_68), C_69))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.06/1.51  tff(c_174, plain, (![A_70, B_71]: (r1_tarski(A_70, k2_xboole_0(B_71, A_70)))), inference(resolution, [status(thm)], [c_6, c_161])).
% 3.06/1.51  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.51  tff(c_199, plain, (![A_3, B_71, A_70]: (r1_tarski(A_3, k2_xboole_0(B_71, A_70)) | ~r1_tarski(A_3, A_70))), inference(resolution, [status(thm)], [c_174, c_4])).
% 3.06/1.51  tff(c_93, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.06/1.51  tff(c_97, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_93])).
% 3.06/1.51  tff(c_18, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.06/1.51  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.06/1.51  tff(c_535, plain, (![A_109, B_110, A_111]: (r1_tarski(A_109, k2_xboole_0(B_110, A_111)) | ~r1_tarski(A_109, A_111))), inference(resolution, [status(thm)], [c_174, c_4])).
% 3.06/1.51  tff(c_558, plain, (![A_109, B_2, A_1]: (r1_tarski(A_109, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_109, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_535])).
% 3.06/1.51  tff(c_24, plain, (![A_23]: (k2_xboole_0(k1_relat_1(A_23), k2_relat_1(A_23))=k3_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.06/1.51  tff(c_233, plain, (![A_74, C_75, B_76]: (r1_tarski(k2_xboole_0(A_74, C_75), B_76) | ~r1_tarski(C_75, B_76) | ~r1_tarski(A_74, B_76))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.06/1.51  tff(c_753, plain, (![A_131, B_132]: (r1_tarski(k3_relat_1(A_131), B_132) | ~r1_tarski(k2_relat_1(A_131), B_132) | ~r1_tarski(k1_relat_1(A_131), B_132) | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_24, c_233])).
% 3.06/1.51  tff(c_32, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.06/1.51  tff(c_777, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_753, c_32])).
% 3.06/1.51  tff(c_791, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_777])).
% 3.06/1.51  tff(c_799, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_791])).
% 3.06/1.51  tff(c_809, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_558, c_799])).
% 3.06/1.51  tff(c_816, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_809])).
% 3.06/1.51  tff(c_820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_97, c_816])).
% 3.06/1.51  tff(c_821, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_791])).
% 3.06/1.51  tff(c_833, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_199, c_821])).
% 3.06/1.51  tff(c_839, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_833])).
% 3.06/1.51  tff(c_843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_151, c_839])).
% 3.06/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.51  
% 3.06/1.51  Inference rules
% 3.06/1.51  ----------------------
% 3.06/1.51  #Ref     : 0
% 3.06/1.51  #Sup     : 189
% 3.06/1.51  #Fact    : 0
% 3.06/1.51  #Define  : 0
% 3.06/1.51  #Split   : 2
% 3.06/1.51  #Chain   : 0
% 3.06/1.51  #Close   : 0
% 3.06/1.51  
% 3.06/1.51  Ordering : KBO
% 3.06/1.51  
% 3.06/1.51  Simplification rules
% 3.06/1.51  ----------------------
% 3.06/1.51  #Subsume      : 21
% 3.06/1.51  #Demod        : 35
% 3.06/1.51  #Tautology    : 40
% 3.06/1.51  #SimpNegUnit  : 0
% 3.06/1.51  #BackRed      : 0
% 3.06/1.51  
% 3.06/1.51  #Partial instantiations: 0
% 3.06/1.51  #Strategies tried      : 1
% 3.06/1.51  
% 3.06/1.51  Timing (in seconds)
% 3.06/1.51  ----------------------
% 3.06/1.51  Preprocessing        : 0.30
% 3.06/1.51  Parsing              : 0.17
% 3.06/1.51  CNF conversion       : 0.02
% 3.06/1.51  Main loop            : 0.43
% 3.06/1.51  Inferencing          : 0.15
% 3.06/1.51  Reduction            : 0.15
% 3.06/1.51  Demodulation         : 0.12
% 3.06/1.51  BG Simplification    : 0.02
% 3.06/1.51  Subsumption          : 0.08
% 3.06/1.51  Abstraction          : 0.02
% 3.06/1.51  MUC search           : 0.00
% 3.06/1.51  Cooper               : 0.00
% 3.06/1.51  Total                : 0.77
% 3.06/1.51  Index Insertion      : 0.00
% 3.06/1.51  Index Deletion       : 0.00
% 3.06/1.51  Index Matching       : 0.00
% 3.06/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
