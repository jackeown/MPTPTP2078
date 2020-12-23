%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:40 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   50 (  57 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 (  78 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_138,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k5_relset_1(A_54,B_55,C_56,D_57) = k7_relat_1(C_56,D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_141,plain,(
    ! [D_57] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_57) = k7_relat_1('#skF_4',D_57) ),
    inference(resolution,[status(thm)],[c_24,c_138])).

tff(c_20,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_142,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_20])).

tff(c_33,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_37,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_33])).

tff(c_84,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_84])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_25,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(B_21,A_22)
      | ~ r1_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_25])).

tff(c_38,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_xboole_0(A_26,C_27)
      | ~ r1_xboole_0(B_28,C_27)
      | ~ r1_tarski(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    ! [A_30] :
      ( r1_xboole_0(A_30,'#skF_2')
      | ~ r1_tarski(A_30,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_30] :
      ( r1_xboole_0('#skF_2',A_30)
      | ~ r1_tarski(A_30,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_111,plain,(
    ! [A_51,B_52] :
      ( k7_relat_1(A_51,B_52) = k1_xboole_0
      | ~ r1_xboole_0(B_52,k1_relat_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_160,plain,(
    ! [A_62] :
      ( k7_relat_1(A_62,'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(A_62)
      | ~ r1_tarski(k1_relat_1(A_62),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_111])).

tff(c_166,plain,(
    ! [B_63] :
      ( k7_relat_1(B_63,'#skF_2') = k1_xboole_0
      | ~ v4_relat_1(B_63,'#skF_3')
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_8,c_160])).

tff(c_169,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_166])).

tff(c_172,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_169])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:00:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  
% 2.17/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.24  
% 2.17/1.24  %Foreground sorts:
% 2.17/1.24  
% 2.17/1.24  
% 2.17/1.24  %Background operators:
% 2.17/1.24  
% 2.17/1.24  
% 2.17/1.24  %Foreground operators:
% 2.17/1.24  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.17/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.17/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.17/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.24  
% 2.17/1.26  tff(f_69, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 2.17/1.26  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.17/1.26  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.17/1.26  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.17/1.26  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.17/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.17/1.26  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.17/1.26  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.17/1.26  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.17/1.26  tff(c_138, plain, (![A_54, B_55, C_56, D_57]: (k5_relset_1(A_54, B_55, C_56, D_57)=k7_relat_1(C_56, D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.26  tff(c_141, plain, (![D_57]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_57)=k7_relat_1('#skF_4', D_57))), inference(resolution, [status(thm)], [c_24, c_138])).
% 2.17/1.26  tff(c_20, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.17/1.26  tff(c_142, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_141, c_20])).
% 2.17/1.26  tff(c_33, plain, (![C_23, A_24, B_25]: (v1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.17/1.26  tff(c_37, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_33])).
% 2.17/1.26  tff(c_84, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.26  tff(c_88, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_84])).
% 2.17/1.26  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.17/1.26  tff(c_22, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.17/1.26  tff(c_25, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | ~r1_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.26  tff(c_28, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_25])).
% 2.17/1.26  tff(c_38, plain, (![A_26, C_27, B_28]: (r1_xboole_0(A_26, C_27) | ~r1_xboole_0(B_28, C_27) | ~r1_tarski(A_26, B_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.26  tff(c_52, plain, (![A_30]: (r1_xboole_0(A_30, '#skF_2') | ~r1_tarski(A_30, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_38])).
% 2.17/1.26  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.26  tff(c_58, plain, (![A_30]: (r1_xboole_0('#skF_2', A_30) | ~r1_tarski(A_30, '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_2])).
% 2.17/1.26  tff(c_111, plain, (![A_51, B_52]: (k7_relat_1(A_51, B_52)=k1_xboole_0 | ~r1_xboole_0(B_52, k1_relat_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.17/1.26  tff(c_160, plain, (![A_62]: (k7_relat_1(A_62, '#skF_2')=k1_xboole_0 | ~v1_relat_1(A_62) | ~r1_tarski(k1_relat_1(A_62), '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_111])).
% 2.17/1.26  tff(c_166, plain, (![B_63]: (k7_relat_1(B_63, '#skF_2')=k1_xboole_0 | ~v4_relat_1(B_63, '#skF_3') | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_8, c_160])).
% 2.17/1.26  tff(c_169, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_166])).
% 2.17/1.26  tff(c_172, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_37, c_169])).
% 2.17/1.26  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_172])).
% 2.17/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  Inference rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Ref     : 0
% 2.17/1.26  #Sup     : 33
% 2.17/1.26  #Fact    : 0
% 2.17/1.26  #Define  : 0
% 2.17/1.26  #Split   : 1
% 2.17/1.26  #Chain   : 0
% 2.17/1.26  #Close   : 0
% 2.17/1.26  
% 2.17/1.26  Ordering : KBO
% 2.17/1.26  
% 2.17/1.26  Simplification rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Subsume      : 4
% 2.17/1.26  #Demod        : 4
% 2.17/1.26  #Tautology    : 4
% 2.17/1.26  #SimpNegUnit  : 1
% 2.17/1.26  #BackRed      : 1
% 2.17/1.26  
% 2.17/1.26  #Partial instantiations: 0
% 2.17/1.26  #Strategies tried      : 1
% 2.17/1.26  
% 2.17/1.26  Timing (in seconds)
% 2.17/1.26  ----------------------
% 2.17/1.26  Preprocessing        : 0.30
% 2.17/1.26  Parsing              : 0.16
% 2.17/1.26  CNF conversion       : 0.02
% 2.17/1.26  Main loop            : 0.19
% 2.17/1.26  Inferencing          : 0.07
% 2.17/1.26  Reduction            : 0.05
% 2.17/1.26  Demodulation         : 0.03
% 2.17/1.26  BG Simplification    : 0.01
% 2.17/1.26  Subsumption          : 0.05
% 2.17/1.26  Abstraction          : 0.01
% 2.17/1.26  MUC search           : 0.00
% 2.17/1.26  Cooper               : 0.00
% 2.17/1.26  Total                : 0.53
% 2.17/1.26  Index Insertion      : 0.00
% 2.17/1.26  Index Deletion       : 0.00
% 2.17/1.26  Index Matching       : 0.00
% 2.17/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
