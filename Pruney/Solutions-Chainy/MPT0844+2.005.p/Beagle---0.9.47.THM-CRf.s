%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:40 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   65 (  85 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 129 expanded)
%              Number of equality atoms :   20 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

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

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_446,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k5_relset_1(A_98,B_99,C_100,D_101) = k7_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_449,plain,(
    ! [D_101] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_101) = k7_relat_1('#skF_4',D_101) ),
    inference(resolution,[status(thm)],[c_36,c_446])).

tff(c_32,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_613,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_32])).

tff(c_65,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_65])).

tff(c_137,plain,(
    ! [C_63,A_64,B_65] :
      ( v4_relat_1(C_63,A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_141,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_137])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_144,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_16])).

tff(c_147,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_144])).

tff(c_34,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_39,plain,(
    ! [B_28,A_29] :
      ( r1_xboole_0(B_28,A_29)
      | ~ r1_xboole_0(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_39])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_232,plain,(
    ! [A_89,B_90,C_91] :
      ( r1_tarski(A_89,k4_xboole_0(B_90,C_91))
      | ~ r1_xboole_0(A_89,C_91)
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_47,plain,(
    ! [A_30,B_31,C_32] :
      ( r1_tarski(A_30,B_31)
      | ~ r1_tarski(A_30,k4_xboole_0(B_31,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    ! [B_31,C_32] : r1_tarski(k4_xboole_0(B_31,C_32),B_31) ),
    inference(resolution,[status(thm)],[c_8,c_47])).

tff(c_76,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(B_43,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [B_31,C_32] :
      ( k4_xboole_0(B_31,C_32) = B_31
      | ~ r1_tarski(B_31,k4_xboole_0(B_31,C_32)) ) ),
    inference(resolution,[status(thm)],[c_52,c_76])).

tff(c_236,plain,(
    ! [B_90,C_91] :
      ( k4_xboole_0(B_90,C_91) = B_90
      | ~ r1_xboole_0(B_90,C_91)
      | ~ r1_tarski(B_90,B_90) ) ),
    inference(resolution,[status(thm)],[c_232,c_87])).

tff(c_251,plain,(
    ! [B_92,C_93] :
      ( k4_xboole_0(B_92,C_93) = B_92
      | ~ r1_xboole_0(B_92,C_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_236])).

tff(c_290,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_251])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_xboole_0(A_45,C_46)
      | ~ r1_tarski(A_45,k4_xboole_0(B_47,C_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [B_14,B_47,C_46] :
      ( r1_xboole_0(k1_relat_1(k7_relat_1(B_14,k4_xboole_0(B_47,C_46))),C_46)
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_92])).

tff(c_1133,plain,(
    ! [B_133] :
      ( r1_xboole_0(k1_relat_1(k7_relat_1(B_133,'#skF_3')),'#skF_2')
      | ~ v1_relat_1(B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_109])).

tff(c_1144,plain,
    ( r1_xboole_0(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_1133])).

tff(c_1149,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1144])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( k7_relat_1(B_16,A_15) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1155,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1149,c_20])).

tff(c_1161,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1155])).

tff(c_1163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_613,c_1161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.49  
% 3.05/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.49  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.22/1.49  
% 3.22/1.49  %Foreground sorts:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Background operators:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Foreground operators:
% 3.22/1.49  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.22/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.22/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.22/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.22/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.22/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.49  
% 3.22/1.51  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 3.22/1.51  tff(f_77, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.22/1.51  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.22/1.51  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.22/1.51  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.22/1.51  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.22/1.51  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.22/1.51  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.22/1.51  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.22/1.51  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.22/1.51  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.22/1.51  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.51  tff(c_446, plain, (![A_98, B_99, C_100, D_101]: (k5_relset_1(A_98, B_99, C_100, D_101)=k7_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.22/1.51  tff(c_449, plain, (![D_101]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_101)=k7_relat_1('#skF_4', D_101))), inference(resolution, [status(thm)], [c_36, c_446])).
% 3.22/1.51  tff(c_32, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.51  tff(c_613, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_449, c_32])).
% 3.22/1.51  tff(c_65, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.51  tff(c_69, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_65])).
% 3.22/1.51  tff(c_137, plain, (![C_63, A_64, B_65]: (v4_relat_1(C_63, A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.22/1.51  tff(c_141, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_137])).
% 3.22/1.51  tff(c_16, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.22/1.51  tff(c_144, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_141, c_16])).
% 3.22/1.51  tff(c_147, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_144])).
% 3.22/1.51  tff(c_34, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.51  tff(c_39, plain, (![B_28, A_29]: (r1_xboole_0(B_28, A_29) | ~r1_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.51  tff(c_42, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_39])).
% 3.22/1.51  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.51  tff(c_232, plain, (![A_89, B_90, C_91]: (r1_tarski(A_89, k4_xboole_0(B_90, C_91)) | ~r1_xboole_0(A_89, C_91) | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.51  tff(c_47, plain, (![A_30, B_31, C_32]: (r1_tarski(A_30, B_31) | ~r1_tarski(A_30, k4_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.51  tff(c_52, plain, (![B_31, C_32]: (r1_tarski(k4_xboole_0(B_31, C_32), B_31))), inference(resolution, [status(thm)], [c_8, c_47])).
% 3.22/1.51  tff(c_76, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(B_43, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.51  tff(c_87, plain, (![B_31, C_32]: (k4_xboole_0(B_31, C_32)=B_31 | ~r1_tarski(B_31, k4_xboole_0(B_31, C_32)))), inference(resolution, [status(thm)], [c_52, c_76])).
% 3.22/1.51  tff(c_236, plain, (![B_90, C_91]: (k4_xboole_0(B_90, C_91)=B_90 | ~r1_xboole_0(B_90, C_91) | ~r1_tarski(B_90, B_90))), inference(resolution, [status(thm)], [c_232, c_87])).
% 3.22/1.51  tff(c_251, plain, (![B_92, C_93]: (k4_xboole_0(B_92, C_93)=B_92 | ~r1_xboole_0(B_92, C_93))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_236])).
% 3.22/1.51  tff(c_290, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_42, c_251])).
% 3.22/1.51  tff(c_18, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.22/1.51  tff(c_92, plain, (![A_45, C_46, B_47]: (r1_xboole_0(A_45, C_46) | ~r1_tarski(A_45, k4_xboole_0(B_47, C_46)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.51  tff(c_109, plain, (![B_14, B_47, C_46]: (r1_xboole_0(k1_relat_1(k7_relat_1(B_14, k4_xboole_0(B_47, C_46))), C_46) | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_18, c_92])).
% 3.22/1.51  tff(c_1133, plain, (![B_133]: (r1_xboole_0(k1_relat_1(k7_relat_1(B_133, '#skF_3')), '#skF_2') | ~v1_relat_1(B_133))), inference(superposition, [status(thm), theory('equality')], [c_290, c_109])).
% 3.22/1.51  tff(c_1144, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_147, c_1133])).
% 3.22/1.51  tff(c_1149, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1144])).
% 3.22/1.51  tff(c_20, plain, (![B_16, A_15]: (k7_relat_1(B_16, A_15)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.22/1.51  tff(c_1155, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1149, c_20])).
% 3.22/1.51  tff(c_1161, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1155])).
% 3.22/1.51  tff(c_1163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_613, c_1161])).
% 3.22/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.51  
% 3.22/1.51  Inference rules
% 3.22/1.51  ----------------------
% 3.22/1.51  #Ref     : 0
% 3.22/1.51  #Sup     : 277
% 3.22/1.51  #Fact    : 0
% 3.22/1.51  #Define  : 0
% 3.22/1.51  #Split   : 1
% 3.22/1.51  #Chain   : 0
% 3.22/1.51  #Close   : 0
% 3.22/1.51  
% 3.22/1.51  Ordering : KBO
% 3.22/1.51  
% 3.22/1.51  Simplification rules
% 3.22/1.51  ----------------------
% 3.22/1.51  #Subsume      : 8
% 3.22/1.51  #Demod        : 123
% 3.22/1.51  #Tautology    : 145
% 3.22/1.51  #SimpNegUnit  : 1
% 3.22/1.51  #BackRed      : 1
% 3.22/1.51  
% 3.22/1.51  #Partial instantiations: 0
% 3.22/1.51  #Strategies tried      : 1
% 3.22/1.51  
% 3.22/1.51  Timing (in seconds)
% 3.22/1.51  ----------------------
% 3.22/1.51  Preprocessing        : 0.32
% 3.22/1.51  Parsing              : 0.17
% 3.22/1.51  CNF conversion       : 0.02
% 3.22/1.51  Main loop            : 0.42
% 3.22/1.51  Inferencing          : 0.15
% 3.22/1.51  Reduction            : 0.13
% 3.22/1.51  Demodulation         : 0.09
% 3.22/1.51  BG Simplification    : 0.02
% 3.22/1.51  Subsumption          : 0.08
% 3.22/1.51  Abstraction          : 0.02
% 3.22/1.51  MUC search           : 0.00
% 3.22/1.51  Cooper               : 0.00
% 3.22/1.51  Total                : 0.77
% 3.22/1.51  Index Insertion      : 0.00
% 3.22/1.51  Index Deletion       : 0.00
% 3.22/1.51  Index Matching       : 0.00
% 3.22/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
