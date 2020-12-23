%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:41 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   48 (  54 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  72 expanded)
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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_145,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k5_relset_1(A_54,B_55,C_56,D_57) = k7_relat_1(C_56,D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_148,plain,(
    ! [D_57] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_57) = k7_relat_1('#skF_4',D_57) ),
    inference(resolution,[status(thm)],[c_26,c_145])).

tff(c_22,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_149,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_22])).

tff(c_35,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_39,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_35])).

tff(c_40,plain,(
    ! [C_25,A_26,B_27] :
      ( v4_relat_1(C_25,A_26)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_40])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_27,plain,(
    ! [B_20,A_21] :
      ( r1_xboole_0(B_20,A_21)
      | ~ r1_xboole_0(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_27])).

tff(c_51,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_xboole_0(A_32,C_33)
      | ~ r1_xboole_0(B_34,C_33)
      | ~ r1_tarski(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_32] :
      ( r1_xboole_0(A_32,'#skF_2')
      | ~ r1_tarski(A_32,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_51])).

tff(c_113,plain,(
    ! [B_50,A_51] :
      ( k7_relat_1(B_50,A_51) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_50),A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_178,plain,(
    ! [B_63] :
      ( k7_relat_1(B_63,'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(B_63)
      | ~ r1_tarski(k1_relat_1(B_63),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_113])).

tff(c_184,plain,(
    ! [B_64] :
      ( k7_relat_1(B_64,'#skF_2') = k1_xboole_0
      | ~ v4_relat_1(B_64,'#skF_3')
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_8,c_178])).

tff(c_187,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_184])).

tff(c_190,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_187])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:44:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.26  
% 1.98/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.27  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.98/1.27  
% 1.98/1.27  %Foreground sorts:
% 1.98/1.27  
% 1.98/1.27  
% 1.98/1.27  %Background operators:
% 1.98/1.27  
% 1.98/1.27  
% 1.98/1.27  %Foreground operators:
% 1.98/1.27  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.98/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.98/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.27  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.98/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.27  
% 1.98/1.28  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 1.98/1.28  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.98/1.28  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.98/1.28  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.98/1.28  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 1.98/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.98/1.28  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.98/1.28  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.98/1.28  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.28  tff(c_145, plain, (![A_54, B_55, C_56, D_57]: (k5_relset_1(A_54, B_55, C_56, D_57)=k7_relat_1(C_56, D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.98/1.28  tff(c_148, plain, (![D_57]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_57)=k7_relat_1('#skF_4', D_57))), inference(resolution, [status(thm)], [c_26, c_145])).
% 1.98/1.28  tff(c_22, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.28  tff(c_149, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_148, c_22])).
% 1.98/1.28  tff(c_35, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.28  tff(c_39, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_35])).
% 1.98/1.28  tff(c_40, plain, (![C_25, A_26, B_27]: (v4_relat_1(C_25, A_26) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.98/1.28  tff(c_44, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_40])).
% 1.98/1.28  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.28  tff(c_24, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.28  tff(c_27, plain, (![B_20, A_21]: (r1_xboole_0(B_20, A_21) | ~r1_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.28  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_27])).
% 1.98/1.28  tff(c_51, plain, (![A_32, C_33, B_34]: (r1_xboole_0(A_32, C_33) | ~r1_xboole_0(B_34, C_33) | ~r1_tarski(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.98/1.28  tff(c_56, plain, (![A_32]: (r1_xboole_0(A_32, '#skF_2') | ~r1_tarski(A_32, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_51])).
% 1.98/1.28  tff(c_113, plain, (![B_50, A_51]: (k7_relat_1(B_50, A_51)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_50), A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.28  tff(c_178, plain, (![B_63]: (k7_relat_1(B_63, '#skF_2')=k1_xboole_0 | ~v1_relat_1(B_63) | ~r1_tarski(k1_relat_1(B_63), '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_113])).
% 1.98/1.28  tff(c_184, plain, (![B_64]: (k7_relat_1(B_64, '#skF_2')=k1_xboole_0 | ~v4_relat_1(B_64, '#skF_3') | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_8, c_178])).
% 1.98/1.28  tff(c_187, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_184])).
% 1.98/1.28  tff(c_190, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_39, c_187])).
% 1.98/1.28  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_190])).
% 1.98/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.28  
% 1.98/1.28  Inference rules
% 1.98/1.28  ----------------------
% 1.98/1.28  #Ref     : 0
% 1.98/1.28  #Sup     : 38
% 1.98/1.28  #Fact    : 0
% 1.98/1.28  #Define  : 0
% 1.98/1.28  #Split   : 0
% 1.98/1.28  #Chain   : 0
% 1.98/1.28  #Close   : 0
% 1.98/1.28  
% 1.98/1.28  Ordering : KBO
% 1.98/1.28  
% 1.98/1.28  Simplification rules
% 1.98/1.28  ----------------------
% 1.98/1.28  #Subsume      : 5
% 1.98/1.28  #Demod        : 3
% 1.98/1.28  #Tautology    : 5
% 1.98/1.28  #SimpNegUnit  : 1
% 1.98/1.28  #BackRed      : 1
% 1.98/1.28  
% 1.98/1.28  #Partial instantiations: 0
% 1.98/1.28  #Strategies tried      : 1
% 1.98/1.28  
% 1.98/1.28  Timing (in seconds)
% 1.98/1.28  ----------------------
% 1.98/1.28  Preprocessing        : 0.29
% 1.98/1.28  Parsing              : 0.16
% 1.98/1.28  CNF conversion       : 0.02
% 1.98/1.28  Main loop            : 0.19
% 1.98/1.28  Inferencing          : 0.08
% 1.98/1.28  Reduction            : 0.05
% 1.98/1.28  Demodulation         : 0.03
% 1.98/1.28  BG Simplification    : 0.01
% 1.98/1.28  Subsumption          : 0.04
% 1.98/1.28  Abstraction          : 0.01
% 1.98/1.28  MUC search           : 0.00
% 1.98/1.28  Cooper               : 0.00
% 1.98/1.28  Total                : 0.51
% 1.98/1.28  Index Insertion      : 0.00
% 1.98/1.28  Index Deletion       : 0.00
% 1.98/1.28  Index Matching       : 0.00
% 1.98/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
