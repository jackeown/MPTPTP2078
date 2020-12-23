%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:48 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   66 (  79 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   78 ( 104 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_564,plain,(
    ! [A_75,B_76,D_77] :
      ( r2_relset_1(A_75,B_76,D_77,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_571,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_564])).

tff(c_16,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_152,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_158,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_152])).

tff(c_162,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_158])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_96,plain,(
    ! [A_45,B_46] :
      ( k2_xboole_0(A_45,B_46) = B_46
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_96])).

tff(c_132,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_112])).

tff(c_668,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_677,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_668])).

tff(c_721,plain,(
    ! [A_91,B_92,C_93] :
      ( m1_subset_1(k2_relset_1(A_91,B_92,C_93),k1_zfmisc_1(B_92))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_737,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_721])).

tff(c_743,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_737])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_751,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_743,c_10])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_765,plain,(
    k2_xboole_0(k2_relat_1('#skF_4'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_751,c_6])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_220,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(A_53,C_54)
      | ~ r1_tarski(k2_xboole_0(A_53,B_55),C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_297,plain,(
    ! [A_59,B_60,B_61] : r1_tarski(A_59,k2_xboole_0(k2_xboole_0(A_59,B_60),B_61)) ),
    inference(resolution,[status(thm)],[c_8,c_220])).

tff(c_326,plain,(
    ! [A_59,B_2,B_60] : r1_tarski(A_59,k2_xboole_0(B_2,k2_xboole_0(A_59,B_60))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_297])).

tff(c_926,plain,(
    ! [B_99] : r1_tarski(k2_relat_1('#skF_4'),k2_xboole_0(B_99,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_326])).

tff(c_941,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_926])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k8_relat_1(A_17,B_18) = B_18
      | ~ r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_959,plain,
    ( k8_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_941,c_18])).

tff(c_968,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_959])).

tff(c_868,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k6_relset_1(A_94,B_95,C_96,D_97) = k8_relat_1(C_96,D_97)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_879,plain,(
    ! [C_96] : k6_relset_1('#skF_1','#skF_2',C_96,'#skF_4') = k8_relat_1(C_96,'#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_868])).

tff(c_30,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_914,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_30])).

tff(c_1079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_968,c_914])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:54:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.50  
% 2.97/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.51  %$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.97/1.51  
% 2.97/1.51  %Foreground sorts:
% 2.97/1.51  
% 2.97/1.51  
% 2.97/1.51  %Background operators:
% 2.97/1.51  
% 2.97/1.51  
% 2.97/1.51  %Foreground operators:
% 2.97/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.97/1.51  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.97/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.51  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.97/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.97/1.51  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.97/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.97/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.97/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.97/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.51  
% 2.97/1.52  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_relset_1)).
% 2.97/1.52  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.97/1.52  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.97/1.52  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.97/1.52  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.97/1.52  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.97/1.52  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.97/1.52  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.97/1.52  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.97/1.52  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.97/1.52  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.97/1.52  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.97/1.52  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.97/1.52  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.97/1.52  tff(c_564, plain, (![A_75, B_76, D_77]: (r2_relset_1(A_75, B_76, D_77, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.97/1.52  tff(c_571, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_564])).
% 2.97/1.52  tff(c_16, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.97/1.52  tff(c_152, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.97/1.52  tff(c_158, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_152])).
% 2.97/1.52  tff(c_162, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_158])).
% 2.97/1.52  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.97/1.52  tff(c_32, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.97/1.52  tff(c_96, plain, (![A_45, B_46]: (k2_xboole_0(A_45, B_46)=B_46 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.52  tff(c_112, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_32, c_96])).
% 2.97/1.52  tff(c_132, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_112])).
% 2.97/1.52  tff(c_668, plain, (![A_85, B_86, C_87]: (k2_relset_1(A_85, B_86, C_87)=k2_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.97/1.52  tff(c_677, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_668])).
% 2.97/1.52  tff(c_721, plain, (![A_91, B_92, C_93]: (m1_subset_1(k2_relset_1(A_91, B_92, C_93), k1_zfmisc_1(B_92)) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.97/1.52  tff(c_737, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_677, c_721])).
% 2.97/1.52  tff(c_743, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_737])).
% 2.97/1.52  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.97/1.52  tff(c_751, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_743, c_10])).
% 2.97/1.52  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.52  tff(c_765, plain, (k2_xboole_0(k2_relat_1('#skF_4'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_751, c_6])).
% 2.97/1.52  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.52  tff(c_220, plain, (![A_53, C_54, B_55]: (r1_tarski(A_53, C_54) | ~r1_tarski(k2_xboole_0(A_53, B_55), C_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.52  tff(c_297, plain, (![A_59, B_60, B_61]: (r1_tarski(A_59, k2_xboole_0(k2_xboole_0(A_59, B_60), B_61)))), inference(resolution, [status(thm)], [c_8, c_220])).
% 2.97/1.52  tff(c_326, plain, (![A_59, B_2, B_60]: (r1_tarski(A_59, k2_xboole_0(B_2, k2_xboole_0(A_59, B_60))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_297])).
% 2.97/1.52  tff(c_926, plain, (![B_99]: (r1_tarski(k2_relat_1('#skF_4'), k2_xboole_0(B_99, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_765, c_326])).
% 2.97/1.52  tff(c_941, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_132, c_926])).
% 2.97/1.52  tff(c_18, plain, (![A_17, B_18]: (k8_relat_1(A_17, B_18)=B_18 | ~r1_tarski(k2_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.97/1.52  tff(c_959, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_941, c_18])).
% 2.97/1.52  tff(c_968, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_959])).
% 2.97/1.52  tff(c_868, plain, (![A_94, B_95, C_96, D_97]: (k6_relset_1(A_94, B_95, C_96, D_97)=k8_relat_1(C_96, D_97) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.97/1.52  tff(c_879, plain, (![C_96]: (k6_relset_1('#skF_1', '#skF_2', C_96, '#skF_4')=k8_relat_1(C_96, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_868])).
% 2.97/1.52  tff(c_30, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.97/1.52  tff(c_914, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_879, c_30])).
% 2.97/1.52  tff(c_1079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_571, c_968, c_914])).
% 2.97/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.52  
% 2.97/1.52  Inference rules
% 2.97/1.52  ----------------------
% 2.97/1.52  #Ref     : 0
% 2.97/1.52  #Sup     : 273
% 2.97/1.52  #Fact    : 0
% 2.97/1.52  #Define  : 0
% 2.97/1.52  #Split   : 4
% 2.97/1.52  #Chain   : 0
% 2.97/1.52  #Close   : 0
% 2.97/1.52  
% 2.97/1.52  Ordering : KBO
% 2.97/1.52  
% 2.97/1.52  Simplification rules
% 2.97/1.52  ----------------------
% 2.97/1.52  #Subsume      : 63
% 2.97/1.52  #Demod        : 80
% 2.97/1.52  #Tautology    : 109
% 2.97/1.52  #SimpNegUnit  : 11
% 2.97/1.52  #BackRed      : 1
% 2.97/1.52  
% 2.97/1.52  #Partial instantiations: 0
% 2.97/1.52  #Strategies tried      : 1
% 2.97/1.52  
% 2.97/1.52  Timing (in seconds)
% 2.97/1.52  ----------------------
% 2.97/1.52  Preprocessing        : 0.35
% 2.97/1.52  Parsing              : 0.18
% 2.97/1.52  CNF conversion       : 0.02
% 2.97/1.52  Main loop            : 0.37
% 2.97/1.52  Inferencing          : 0.12
% 2.97/1.52  Reduction            : 0.13
% 2.97/1.52  Demodulation         : 0.10
% 2.97/1.52  BG Simplification    : 0.02
% 2.97/1.52  Subsumption          : 0.06
% 2.97/1.52  Abstraction          : 0.02
% 2.97/1.52  MUC search           : 0.00
% 2.97/1.52  Cooper               : 0.00
% 2.97/1.52  Total                : 0.75
% 2.97/1.52  Index Insertion      : 0.00
% 2.97/1.52  Index Deletion       : 0.00
% 2.97/1.52  Index Matching       : 0.00
% 2.97/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
