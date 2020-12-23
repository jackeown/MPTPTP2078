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
% DateTime   : Thu Dec  3 10:08:42 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   53 (  60 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 (  84 expanded)
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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
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

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_137,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( k5_relset_1(A_56,B_57,C_58,D_59) = k7_relat_1(C_58,D_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_140,plain,(
    ! [D_59] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_59) = k7_relat_1('#skF_4',D_59) ),
    inference(resolution,[status(thm)],[c_26,c_137])).

tff(c_22,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_141,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_22])).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    ! [B_27,A_28] :
      ( v1_relat_1(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_35,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_32])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_35])).

tff(c_79,plain,(
    ! [C_38,A_39,B_40] :
      ( v4_relat_1(C_38,A_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_83,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_79])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(B_25,A_26)
      | ~ r1_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_28])).

tff(c_43,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_xboole_0(A_29,C_30)
      | ~ r1_xboole_0(B_31,C_30)
      | ~ r1_tarski(A_29,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_33] :
      ( r1_xboole_0(A_33,'#skF_2')
      | ~ r1_tarski(A_33,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_31,c_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [A_33] :
      ( r1_xboole_0('#skF_2',A_33)
      | ~ r1_tarski(A_33,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_57,c_2])).

tff(c_116,plain,(
    ! [A_54,B_55] :
      ( k7_relat_1(A_54,B_55) = k1_xboole_0
      | ~ r1_xboole_0(B_55,k1_relat_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_165,plain,(
    ! [A_65] :
      ( k7_relat_1(A_65,'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(A_65)
      | ~ r1_tarski(k1_relat_1(A_65),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_63,c_116])).

tff(c_171,plain,(
    ! [B_66] :
      ( k7_relat_1(B_66,'#skF_2') = k1_xboole_0
      | ~ v4_relat_1(B_66,'#skF_3')
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_174,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_83,c_171])).

tff(c_177,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_174])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.26  
% 2.02/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.26  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.26  
% 2.02/1.26  %Foreground sorts:
% 2.02/1.26  
% 2.02/1.26  
% 2.02/1.26  %Background operators:
% 2.02/1.26  
% 2.02/1.26  
% 2.02/1.26  %Foreground operators:
% 2.02/1.26  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.02/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.02/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.02/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.26  
% 2.02/1.28  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 2.02/1.28  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.02/1.28  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.02/1.28  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.02/1.28  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.02/1.28  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.02/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.02/1.28  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.02/1.28  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.02/1.28  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.28  tff(c_137, plain, (![A_56, B_57, C_58, D_59]: (k5_relset_1(A_56, B_57, C_58, D_59)=k7_relat_1(C_58, D_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.28  tff(c_140, plain, (![D_59]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_59)=k7_relat_1('#skF_4', D_59))), inference(resolution, [status(thm)], [c_26, c_137])).
% 2.02/1.28  tff(c_22, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.28  tff(c_141, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140, c_22])).
% 2.02/1.28  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.02/1.28  tff(c_32, plain, (![B_27, A_28]: (v1_relat_1(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.02/1.28  tff(c_35, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_32])).
% 2.02/1.28  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_35])).
% 2.02/1.28  tff(c_79, plain, (![C_38, A_39, B_40]: (v4_relat_1(C_38, A_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.28  tff(c_83, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_79])).
% 2.02/1.28  tff(c_10, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.02/1.28  tff(c_24, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.28  tff(c_28, plain, (![B_25, A_26]: (r1_xboole_0(B_25, A_26) | ~r1_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.28  tff(c_31, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_28])).
% 2.02/1.28  tff(c_43, plain, (![A_29, C_30, B_31]: (r1_xboole_0(A_29, C_30) | ~r1_xboole_0(B_31, C_30) | ~r1_tarski(A_29, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.28  tff(c_57, plain, (![A_33]: (r1_xboole_0(A_33, '#skF_2') | ~r1_tarski(A_33, '#skF_3'))), inference(resolution, [status(thm)], [c_31, c_43])).
% 2.02/1.28  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.28  tff(c_63, plain, (![A_33]: (r1_xboole_0('#skF_2', A_33) | ~r1_tarski(A_33, '#skF_3'))), inference(resolution, [status(thm)], [c_57, c_2])).
% 2.02/1.28  tff(c_116, plain, (![A_54, B_55]: (k7_relat_1(A_54, B_55)=k1_xboole_0 | ~r1_xboole_0(B_55, k1_relat_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.02/1.28  tff(c_165, plain, (![A_65]: (k7_relat_1(A_65, '#skF_2')=k1_xboole_0 | ~v1_relat_1(A_65) | ~r1_tarski(k1_relat_1(A_65), '#skF_3'))), inference(resolution, [status(thm)], [c_63, c_116])).
% 2.02/1.28  tff(c_171, plain, (![B_66]: (k7_relat_1(B_66, '#skF_2')=k1_xboole_0 | ~v4_relat_1(B_66, '#skF_3') | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_10, c_165])).
% 2.02/1.28  tff(c_174, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_83, c_171])).
% 2.02/1.28  tff(c_177, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_174])).
% 2.02/1.28  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_177])).
% 2.02/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.28  
% 2.02/1.28  Inference rules
% 2.02/1.28  ----------------------
% 2.02/1.28  #Ref     : 0
% 2.02/1.28  #Sup     : 33
% 2.02/1.28  #Fact    : 0
% 2.02/1.28  #Define  : 0
% 2.02/1.28  #Split   : 1
% 2.02/1.28  #Chain   : 0
% 2.02/1.28  #Close   : 0
% 2.02/1.28  
% 2.02/1.28  Ordering : KBO
% 2.02/1.28  
% 2.02/1.28  Simplification rules
% 2.02/1.28  ----------------------
% 2.02/1.28  #Subsume      : 4
% 2.02/1.28  #Demod        : 5
% 2.02/1.28  #Tautology    : 4
% 2.02/1.28  #SimpNegUnit  : 1
% 2.02/1.28  #BackRed      : 1
% 2.02/1.28  
% 2.02/1.28  #Partial instantiations: 0
% 2.02/1.28  #Strategies tried      : 1
% 2.02/1.28  
% 2.02/1.28  Timing (in seconds)
% 2.02/1.28  ----------------------
% 2.02/1.28  Preprocessing        : 0.28
% 2.02/1.28  Parsing              : 0.15
% 2.02/1.28  CNF conversion       : 0.02
% 2.02/1.28  Main loop            : 0.18
% 2.02/1.28  Inferencing          : 0.07
% 2.02/1.28  Reduction            : 0.05
% 2.02/1.28  Demodulation         : 0.03
% 2.02/1.28  BG Simplification    : 0.01
% 2.02/1.28  Subsumption          : 0.04
% 2.02/1.28  Abstraction          : 0.01
% 2.02/1.28  MUC search           : 0.00
% 2.02/1.28  Cooper               : 0.00
% 2.02/1.28  Total                : 0.49
% 2.02/1.28  Index Insertion      : 0.00
% 2.02/1.28  Index Deletion       : 0.00
% 2.02/1.28  Index Matching       : 0.00
% 2.02/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
