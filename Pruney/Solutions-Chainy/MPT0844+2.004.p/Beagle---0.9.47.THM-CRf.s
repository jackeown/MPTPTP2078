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
% DateTime   : Thu Dec  3 10:08:40 EST 2020

% Result     : Theorem 4.48s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   60 (  70 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 106 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_338,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( k5_relset_1(A_92,B_93,C_94,D_95) = k7_relat_1(C_94,D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_341,plain,(
    ! [D_95] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_95) = k7_relat_1('#skF_4',D_95) ),
    inference(resolution,[status(thm)],[c_36,c_338])).

tff(c_32,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_415,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_32])).

tff(c_65,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_69,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_65])).

tff(c_147,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_151,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_147])).

tff(c_34,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_39,plain,(
    ! [B_26,A_27] :
      ( r1_xboole_0(B_26,A_27)
      | ~ r1_xboole_0(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_39])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_223,plain,(
    ! [A_87,B_88,C_89] :
      ( r1_tarski(A_87,k4_xboole_0(B_88,C_89))
      | ~ r1_xboole_0(A_87,C_89)
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_47,plain,(
    ! [A_28,B_29,C_30] :
      ( r1_tarski(A_28,B_29)
      | ~ r1_tarski(A_28,k4_xboole_0(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    ! [B_29,C_30] : r1_tarski(k4_xboole_0(B_29,C_30),B_29) ),
    inference(resolution,[status(thm)],[c_8,c_47])).

tff(c_70,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [B_29,C_30] :
      ( k4_xboole_0(B_29,C_30) = B_29
      | ~ r1_tarski(B_29,k4_xboole_0(B_29,C_30)) ) ),
    inference(resolution,[status(thm)],[c_52,c_70])).

tff(c_227,plain,(
    ! [B_88,C_89] :
      ( k4_xboole_0(B_88,C_89) = B_88
      | ~ r1_xboole_0(B_88,C_89)
      | ~ r1_tarski(B_88,B_88) ) ),
    inference(resolution,[status(thm)],[c_223,c_78])).

tff(c_247,plain,(
    ! [B_90,C_91] :
      ( k4_xboole_0(B_90,C_91) = B_90
      | ~ r1_xboole_0(B_90,C_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_227])).

tff(c_286,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_247])).

tff(c_108,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(k1_relat_1(B_48),A_49)
      | ~ v4_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,C_7)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_856,plain,(
    ! [B_116,C_117,B_118] :
      ( r1_xboole_0(k1_relat_1(B_116),C_117)
      | ~ v4_relat_1(B_116,k4_xboole_0(B_118,C_117))
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_108,c_10])).

tff(c_2525,plain,(
    ! [B_163] :
      ( r1_xboole_0(k1_relat_1(B_163),'#skF_2')
      | ~ v4_relat_1(B_163,'#skF_3')
      | ~ v1_relat_1(B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_856])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3506,plain,(
    ! [B_212] :
      ( k7_relat_1(B_212,'#skF_2') = k1_xboole_0
      | ~ v4_relat_1(B_212,'#skF_3')
      | ~ v1_relat_1(B_212) ) ),
    inference(resolution,[status(thm)],[c_2525,c_20])).

tff(c_3509,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_151,c_3506])).

tff(c_3512,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_3509])).

tff(c_3514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_3512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.48/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.83  
% 4.48/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.83  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.48/1.83  
% 4.48/1.83  %Foreground sorts:
% 4.48/1.83  
% 4.48/1.83  
% 4.48/1.83  %Background operators:
% 4.48/1.83  
% 4.48/1.83  
% 4.48/1.83  %Foreground operators:
% 4.48/1.83  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 4.48/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.48/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.48/1.83  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.48/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.48/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.48/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.48/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.48/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.48/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.48/1.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.48/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.48/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.48/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.48/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.48/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.48/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.48/1.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.48/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.48/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.48/1.83  
% 4.48/1.84  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 4.48/1.84  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 4.48/1.84  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.48/1.84  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.48/1.84  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.48/1.84  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.48/1.84  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 4.48/1.84  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.48/1.84  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.48/1.84  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 4.48/1.84  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.48/1.84  tff(c_338, plain, (![A_92, B_93, C_94, D_95]: (k5_relset_1(A_92, B_93, C_94, D_95)=k7_relat_1(C_94, D_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.48/1.84  tff(c_341, plain, (![D_95]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_95)=k7_relat_1('#skF_4', D_95))), inference(resolution, [status(thm)], [c_36, c_338])).
% 4.48/1.84  tff(c_32, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.48/1.84  tff(c_415, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_341, c_32])).
% 4.48/1.84  tff(c_65, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.48/1.84  tff(c_69, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_65])).
% 4.48/1.84  tff(c_147, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.48/1.84  tff(c_151, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_147])).
% 4.48/1.84  tff(c_34, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.48/1.84  tff(c_39, plain, (![B_26, A_27]: (r1_xboole_0(B_26, A_27) | ~r1_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.48/1.84  tff(c_42, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_39])).
% 4.48/1.84  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.48/1.84  tff(c_223, plain, (![A_87, B_88, C_89]: (r1_tarski(A_87, k4_xboole_0(B_88, C_89)) | ~r1_xboole_0(A_87, C_89) | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.48/1.84  tff(c_47, plain, (![A_28, B_29, C_30]: (r1_tarski(A_28, B_29) | ~r1_tarski(A_28, k4_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.48/1.84  tff(c_52, plain, (![B_29, C_30]: (r1_tarski(k4_xboole_0(B_29, C_30), B_29))), inference(resolution, [status(thm)], [c_8, c_47])).
% 4.48/1.84  tff(c_70, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.48/1.84  tff(c_78, plain, (![B_29, C_30]: (k4_xboole_0(B_29, C_30)=B_29 | ~r1_tarski(B_29, k4_xboole_0(B_29, C_30)))), inference(resolution, [status(thm)], [c_52, c_70])).
% 4.48/1.84  tff(c_227, plain, (![B_88, C_89]: (k4_xboole_0(B_88, C_89)=B_88 | ~r1_xboole_0(B_88, C_89) | ~r1_tarski(B_88, B_88))), inference(resolution, [status(thm)], [c_223, c_78])).
% 4.48/1.84  tff(c_247, plain, (![B_90, C_91]: (k4_xboole_0(B_90, C_91)=B_90 | ~r1_xboole_0(B_90, C_91))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_227])).
% 4.48/1.84  tff(c_286, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_42, c_247])).
% 4.48/1.84  tff(c_108, plain, (![B_48, A_49]: (r1_tarski(k1_relat_1(B_48), A_49) | ~v4_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.48/1.84  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, C_7) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.48/1.84  tff(c_856, plain, (![B_116, C_117, B_118]: (r1_xboole_0(k1_relat_1(B_116), C_117) | ~v4_relat_1(B_116, k4_xboole_0(B_118, C_117)) | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_108, c_10])).
% 4.48/1.84  tff(c_2525, plain, (![B_163]: (r1_xboole_0(k1_relat_1(B_163), '#skF_2') | ~v4_relat_1(B_163, '#skF_3') | ~v1_relat_1(B_163))), inference(superposition, [status(thm), theory('equality')], [c_286, c_856])).
% 4.48/1.84  tff(c_20, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.48/1.84  tff(c_3506, plain, (![B_212]: (k7_relat_1(B_212, '#skF_2')=k1_xboole_0 | ~v4_relat_1(B_212, '#skF_3') | ~v1_relat_1(B_212))), inference(resolution, [status(thm)], [c_2525, c_20])).
% 4.48/1.84  tff(c_3509, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_151, c_3506])).
% 4.48/1.84  tff(c_3512, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_69, c_3509])).
% 4.48/1.84  tff(c_3514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_415, c_3512])).
% 4.48/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.84  
% 4.48/1.84  Inference rules
% 4.48/1.84  ----------------------
% 4.48/1.84  #Ref     : 0
% 4.48/1.84  #Sup     : 875
% 4.48/1.84  #Fact    : 0
% 4.48/1.84  #Define  : 0
% 4.48/1.84  #Split   : 0
% 4.48/1.84  #Chain   : 0
% 4.48/1.84  #Close   : 0
% 4.48/1.84  
% 4.48/1.84  Ordering : KBO
% 4.48/1.84  
% 4.48/1.84  Simplification rules
% 4.48/1.84  ----------------------
% 4.48/1.84  #Subsume      : 123
% 4.48/1.84  #Demod        : 506
% 4.48/1.84  #Tautology    : 499
% 4.48/1.84  #SimpNegUnit  : 1
% 4.48/1.84  #BackRed      : 1
% 4.48/1.84  
% 4.48/1.84  #Partial instantiations: 0
% 4.48/1.84  #Strategies tried      : 1
% 4.48/1.84  
% 4.48/1.84  Timing (in seconds)
% 4.48/1.84  ----------------------
% 4.48/1.85  Preprocessing        : 0.30
% 4.48/1.85  Parsing              : 0.17
% 4.48/1.85  CNF conversion       : 0.02
% 4.48/1.85  Main loop            : 0.71
% 4.48/1.85  Inferencing          : 0.24
% 4.48/1.85  Reduction            : 0.26
% 4.48/1.85  Demodulation         : 0.20
% 4.48/1.85  BG Simplification    : 0.03
% 4.48/1.85  Subsumption          : 0.14
% 4.48/1.85  Abstraction          : 0.04
% 4.48/1.85  MUC search           : 0.00
% 4.48/1.85  Cooper               : 0.00
% 4.48/1.85  Total                : 1.05
% 4.48/1.85  Index Insertion      : 0.00
% 4.48/1.85  Index Deletion       : 0.00
% 4.48/1.85  Index Matching       : 0.00
% 4.48/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
