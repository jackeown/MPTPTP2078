%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:27 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 103 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 163 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_47,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_47])).

tff(c_79,plain,(
    ! [C_49,A_50,B_51] :
      ( v4_relat_1(C_49,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_88,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_79])).

tff(c_16,plain,(
    ! [C_10,A_8,B_9] :
      ( v1_relat_1(k7_relat_1(C_10,A_8))
      | ~ v4_relat_1(C_10,B_9)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_90,plain,(
    ! [A_8] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_8))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_88,c_16])).

tff(c_93,plain,(
    ! [A_8] : v1_relat_1(k7_relat_1('#skF_4',A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_90])).

tff(c_176,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(k7_relat_1(C_77,A_78),A_78)
      | ~ v4_relat_1(C_77,B_79)
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_182,plain,(
    ! [A_78] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_78),A_78)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_88,c_176])).

tff(c_187,plain,(
    ! [A_78] : v4_relat_1(k7_relat_1('#skF_4',A_78),A_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_182])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_12,A_11)),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_250,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_259,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_250])).

tff(c_341,plain,(
    ! [A_117,B_118,C_119] :
      ( m1_subset_1(k2_relset_1(A_117,B_118,C_119),k1_zfmisc_1(B_118))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_363,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_341])).

tff(c_370,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_363])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_374,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_370,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_381,plain,(
    ! [A_120] :
      ( r1_tarski(A_120,'#skF_3')
      | ~ r1_tarski(A_120,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_374,c_2])).

tff(c_385,plain,(
    ! [A_11] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_11)),'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_381])).

tff(c_392,plain,(
    ! [A_11] : r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_11)),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_385])).

tff(c_542,plain,(
    ! [C_148,A_149,B_150] :
      ( m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ r1_tarski(k2_relat_1(C_148),B_150)
      | ~ r1_tarski(k1_relat_1(C_148),A_149)
      | ~ v1_relat_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_441,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( k5_relset_1(A_128,B_129,C_130,D_131) = k7_relat_1(C_130,D_131)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_452,plain,(
    ! [D_131] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_131) = k7_relat_1('#skF_4',D_131) ),
    inference(resolution,[status(thm)],[c_36,c_441])).

tff(c_34,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_454,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_34])).

tff(c_545,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_542,c_454])).

tff(c_565,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_392,c_545])).

tff(c_574,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_565])).

tff(c_578,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_187,c_574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:06:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.60  
% 2.84/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.61  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.84/1.61  
% 2.84/1.61  %Foreground sorts:
% 2.84/1.61  
% 2.84/1.61  
% 2.84/1.61  %Background operators:
% 2.84/1.61  
% 2.84/1.61  
% 2.84/1.61  %Foreground operators:
% 2.84/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.84/1.61  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.84/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.84/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.84/1.61  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.61  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.61  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.84/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.84/1.61  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.84/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.84/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.61  
% 2.84/1.62  tff(f_90, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.84/1.62  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.84/1.62  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.84/1.62  tff(f_51, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 2.84/1.62  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.84/1.62  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 2.84/1.62  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.84/1.62  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.84/1.62  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.84/1.62  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.84/1.62  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.84/1.62  tff(f_77, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.84/1.62  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.84/1.62  tff(c_47, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.84/1.62  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_47])).
% 2.84/1.62  tff(c_79, plain, (![C_49, A_50, B_51]: (v4_relat_1(C_49, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.84/1.62  tff(c_88, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_79])).
% 2.84/1.62  tff(c_16, plain, (![C_10, A_8, B_9]: (v1_relat_1(k7_relat_1(C_10, A_8)) | ~v4_relat_1(C_10, B_9) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.84/1.62  tff(c_90, plain, (![A_8]: (v1_relat_1(k7_relat_1('#skF_4', A_8)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_88, c_16])).
% 2.84/1.62  tff(c_93, plain, (![A_8]: (v1_relat_1(k7_relat_1('#skF_4', A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_90])).
% 2.84/1.62  tff(c_176, plain, (![C_77, A_78, B_79]: (v4_relat_1(k7_relat_1(C_77, A_78), A_78) | ~v4_relat_1(C_77, B_79) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.84/1.62  tff(c_182, plain, (![A_78]: (v4_relat_1(k7_relat_1('#skF_4', A_78), A_78) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_88, c_176])).
% 2.84/1.62  tff(c_187, plain, (![A_78]: (v4_relat_1(k7_relat_1('#skF_4', A_78), A_78))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_182])).
% 2.84/1.62  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.84/1.62  tff(c_18, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(k7_relat_1(B_12, A_11)), k2_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.84/1.62  tff(c_250, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.62  tff(c_259, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_250])).
% 2.84/1.62  tff(c_341, plain, (![A_117, B_118, C_119]: (m1_subset_1(k2_relset_1(A_117, B_118, C_119), k1_zfmisc_1(B_118)) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.84/1.62  tff(c_363, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_259, c_341])).
% 2.84/1.62  tff(c_370, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_363])).
% 2.84/1.62  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.62  tff(c_374, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_370, c_4])).
% 2.84/1.62  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.62  tff(c_381, plain, (![A_120]: (r1_tarski(A_120, '#skF_3') | ~r1_tarski(A_120, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_374, c_2])).
% 2.84/1.62  tff(c_385, plain, (![A_11]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_11)), '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_381])).
% 2.84/1.62  tff(c_392, plain, (![A_11]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_11)), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_385])).
% 2.84/1.62  tff(c_542, plain, (![C_148, A_149, B_150]: (m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~r1_tarski(k2_relat_1(C_148), B_150) | ~r1_tarski(k1_relat_1(C_148), A_149) | ~v1_relat_1(C_148))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.84/1.62  tff(c_441, plain, (![A_128, B_129, C_130, D_131]: (k5_relset_1(A_128, B_129, C_130, D_131)=k7_relat_1(C_130, D_131) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.84/1.62  tff(c_452, plain, (![D_131]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_131)=k7_relat_1('#skF_4', D_131))), inference(resolution, [status(thm)], [c_36, c_441])).
% 2.84/1.62  tff(c_34, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.84/1.62  tff(c_454, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_34])).
% 2.84/1.62  tff(c_545, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_542, c_454])).
% 2.84/1.62  tff(c_565, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_392, c_545])).
% 2.84/1.62  tff(c_574, plain, (~v4_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_565])).
% 2.84/1.62  tff(c_578, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_187, c_574])).
% 2.84/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.62  
% 2.84/1.62  Inference rules
% 2.84/1.62  ----------------------
% 2.84/1.62  #Ref     : 0
% 2.84/1.62  #Sup     : 109
% 2.84/1.62  #Fact    : 0
% 2.84/1.62  #Define  : 0
% 2.84/1.62  #Split   : 1
% 2.84/1.62  #Chain   : 0
% 2.84/1.62  #Close   : 0
% 2.84/1.62  
% 2.84/1.62  Ordering : KBO
% 2.84/1.62  
% 2.84/1.62  Simplification rules
% 2.84/1.62  ----------------------
% 2.84/1.62  #Subsume      : 7
% 2.84/1.62  #Demod        : 40
% 2.84/1.62  #Tautology    : 12
% 2.84/1.62  #SimpNegUnit  : 0
% 2.84/1.62  #BackRed      : 2
% 2.84/1.62  
% 2.84/1.62  #Partial instantiations: 0
% 2.84/1.62  #Strategies tried      : 1
% 2.84/1.62  
% 2.84/1.62  Timing (in seconds)
% 2.84/1.62  ----------------------
% 2.84/1.62  Preprocessing        : 0.42
% 2.84/1.62  Parsing              : 0.27
% 2.84/1.62  CNF conversion       : 0.02
% 2.84/1.62  Main loop            : 0.31
% 2.84/1.62  Inferencing          : 0.12
% 2.84/1.62  Reduction            : 0.09
% 2.84/1.62  Demodulation         : 0.06
% 2.84/1.62  BG Simplification    : 0.02
% 2.84/1.62  Subsumption          : 0.06
% 2.84/1.62  Abstraction          : 0.02
% 2.84/1.62  MUC search           : 0.00
% 2.84/1.62  Cooper               : 0.00
% 2.84/1.62  Total                : 0.76
% 2.84/1.62  Index Insertion      : 0.00
% 2.84/1.62  Index Deletion       : 0.00
% 2.84/1.62  Index Matching       : 0.00
% 2.84/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
