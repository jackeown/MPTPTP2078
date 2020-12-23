%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:01 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   60 (  90 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 136 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_65,axiom,(
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

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_59,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_63,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_232,plain,(
    ! [C_69,B_70,A_71] :
      ( v5_relat_1(C_69,B_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_236,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_232])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_190,plain,(
    ! [C_63,A_64,B_65] :
      ( v4_relat_1(C_63,A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_194,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_190])).

tff(c_181,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(k1_relat_1(B_61),A_62)
      | ~ v4_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_520,plain,(
    ! [B_98,A_99] :
      ( k2_xboole_0(k1_relat_1(B_98),A_99) = A_99
      | ~ v4_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_181,c_6])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(k2_xboole_0(A_40,B_42),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_40,B_42,B_10] : r1_tarski(A_40,k2_xboole_0(k2_xboole_0(A_40,B_42),B_10)) ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_559,plain,(
    ! [B_98,A_99,B_10] :
      ( r1_tarski(k1_relat_1(B_98),k2_xboole_0(A_99,B_10))
      | ~ v4_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_69])).

tff(c_24,plain,(
    ! [A_22] :
      ( k2_xboole_0(k1_relat_1(A_22),k2_relat_1(A_22)) = k3_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_255,plain,(
    ! [A_76,C_77,B_78] :
      ( r1_tarski(k2_xboole_0(A_76,C_77),B_78)
      | ~ r1_tarski(C_77,B_78)
      | ~ r1_tarski(A_76,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1178,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(k3_relat_1(A_144),B_145)
      | ~ r1_tarski(k2_relat_1(A_144),B_145)
      | ~ r1_tarski(k1_relat_1(A_144),B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_255])).

tff(c_32,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1190,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1178,c_32])).

tff(c_1198,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1190])).

tff(c_1206,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1198])).

tff(c_1209,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_559,c_1206])).

tff(c_1219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_194,c_1209])).

tff(c_1220,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1198])).

tff(c_1237,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_1220])).

tff(c_1240,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_1237])).

tff(c_1244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_236,c_1240])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.52  
% 3.12/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.52  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.12/1.52  
% 3.12/1.52  %Foreground sorts:
% 3.12/1.52  
% 3.12/1.52  
% 3.12/1.52  %Background operators:
% 3.12/1.52  
% 3.12/1.52  
% 3.12/1.52  %Foreground operators:
% 3.12/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.52  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.12/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.12/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.12/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.12/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.12/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.12/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.12/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.52  
% 3.31/1.53  tff(f_80, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 3.31/1.53  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.31/1.53  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.31/1.53  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.31/1.53  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.31/1.53  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.31/1.53  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.31/1.53  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.31/1.53  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.31/1.53  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.31/1.53  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.31/1.53  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.31/1.53  tff(c_59, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.31/1.53  tff(c_63, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_59])).
% 3.31/1.53  tff(c_232, plain, (![C_69, B_70, A_71]: (v5_relat_1(C_69, B_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.31/1.53  tff(c_236, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_232])).
% 3.31/1.53  tff(c_22, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(B_21), A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.31/1.53  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.31/1.53  tff(c_190, plain, (![C_63, A_64, B_65]: (v4_relat_1(C_63, A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.31/1.53  tff(c_194, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_190])).
% 3.31/1.53  tff(c_181, plain, (![B_61, A_62]: (r1_tarski(k1_relat_1(B_61), A_62) | ~v4_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.31/1.53  tff(c_6, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.53  tff(c_520, plain, (![B_98, A_99]: (k2_xboole_0(k1_relat_1(B_98), A_99)=A_99 | ~v4_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_181, c_6])).
% 3.31/1.53  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.31/1.53  tff(c_64, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(k2_xboole_0(A_40, B_42), C_41))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.31/1.53  tff(c_69, plain, (![A_40, B_42, B_10]: (r1_tarski(A_40, k2_xboole_0(k2_xboole_0(A_40, B_42), B_10)))), inference(resolution, [status(thm)], [c_8, c_64])).
% 3.31/1.53  tff(c_559, plain, (![B_98, A_99, B_10]: (r1_tarski(k1_relat_1(B_98), k2_xboole_0(A_99, B_10)) | ~v4_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(superposition, [status(thm), theory('equality')], [c_520, c_69])).
% 3.31/1.53  tff(c_24, plain, (![A_22]: (k2_xboole_0(k1_relat_1(A_22), k2_relat_1(A_22))=k3_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.53  tff(c_255, plain, (![A_76, C_77, B_78]: (r1_tarski(k2_xboole_0(A_76, C_77), B_78) | ~r1_tarski(C_77, B_78) | ~r1_tarski(A_76, B_78))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.31/1.53  tff(c_1178, plain, (![A_144, B_145]: (r1_tarski(k3_relat_1(A_144), B_145) | ~r1_tarski(k2_relat_1(A_144), B_145) | ~r1_tarski(k1_relat_1(A_144), B_145) | ~v1_relat_1(A_144))), inference(superposition, [status(thm), theory('equality')], [c_24, c_255])).
% 3.31/1.53  tff(c_32, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.31/1.53  tff(c_1190, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1178, c_32])).
% 3.31/1.53  tff(c_1198, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1190])).
% 3.31/1.53  tff(c_1206, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1198])).
% 3.31/1.53  tff(c_1209, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_559, c_1206])).
% 3.31/1.53  tff(c_1219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_194, c_1209])).
% 3.31/1.53  tff(c_1220, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1198])).
% 3.31/1.53  tff(c_1237, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2, c_1220])).
% 3.31/1.53  tff(c_1240, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_1237])).
% 3.31/1.53  tff(c_1244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_236, c_1240])).
% 3.31/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.53  
% 3.31/1.53  Inference rules
% 3.31/1.53  ----------------------
% 3.31/1.53  #Ref     : 0
% 3.31/1.53  #Sup     : 311
% 3.31/1.53  #Fact    : 0
% 3.31/1.53  #Define  : 0
% 3.31/1.53  #Split   : 2
% 3.31/1.53  #Chain   : 0
% 3.31/1.53  #Close   : 0
% 3.31/1.53  
% 3.31/1.53  Ordering : KBO
% 3.31/1.53  
% 3.31/1.53  Simplification rules
% 3.31/1.53  ----------------------
% 3.31/1.53  #Subsume      : 61
% 3.31/1.53  #Demod        : 29
% 3.31/1.53  #Tautology    : 73
% 3.31/1.53  #SimpNegUnit  : 0
% 3.31/1.53  #BackRed      : 0
% 3.31/1.53  
% 3.31/1.53  #Partial instantiations: 0
% 3.31/1.53  #Strategies tried      : 1
% 3.31/1.53  
% 3.31/1.53  Timing (in seconds)
% 3.31/1.53  ----------------------
% 3.31/1.54  Preprocessing        : 0.30
% 3.31/1.54  Parsing              : 0.17
% 3.31/1.54  CNF conversion       : 0.02
% 3.31/1.54  Main loop            : 0.44
% 3.31/1.54  Inferencing          : 0.17
% 3.31/1.54  Reduction            : 0.12
% 3.31/1.54  Demodulation         : 0.09
% 3.31/1.54  BG Simplification    : 0.02
% 3.31/1.54  Subsumption          : 0.09
% 3.31/1.54  Abstraction          : 0.02
% 3.34/1.54  MUC search           : 0.00
% 3.34/1.54  Cooper               : 0.00
% 3.34/1.54  Total                : 0.77
% 3.34/1.54  Index Insertion      : 0.00
% 3.34/1.54  Index Deletion       : 0.00
% 3.34/1.54  Index Matching       : 0.00
% 3.34/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
