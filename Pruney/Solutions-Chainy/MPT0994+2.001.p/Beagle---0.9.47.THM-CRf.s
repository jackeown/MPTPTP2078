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
% DateTime   : Thu Dec  3 10:13:48 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   52 (  64 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   78 ( 144 expanded)
%              Number of equality atoms :   29 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( ( v1_funct_1(E)
          & v1_funct_2(E,A,B)
          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( r2_hidden(C,A)
            & r2_hidden(k1_funct_1(E,C),D) )
         => ( B = k1_xboole_0
            | k1_funct_1(k6_relset_1(A,B,D,E),C) = k1_funct_1(E,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
       => k1_funct_1(k8_relat_1(B,C),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_58,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( k6_relset_1(A_32,B_33,C_34,D_35) = k8_relat_1(C_34,D_35)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_61,plain,(
    ! [C_34] : k6_relset_1('#skF_1','#skF_2',C_34,'#skF_5') = k8_relat_1(C_34,'#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_58])).

tff(c_28,plain,(
    k1_funct_1(k6_relset_1('#skF_1','#skF_2','#skF_4','#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_63,plain,(
    k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_28])).

tff(c_41,plain,(
    ! [C_20,A_21,B_22] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_45,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_41])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_46,plain,(
    ! [A_23,B_24,C_25] :
      ( k1_relset_1(A_23,B_24,C_25) = k1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_46])).

tff(c_82,plain,(
    ! [B_47,A_48,C_49] :
      ( k1_xboole_0 = B_47
      | k1_relset_1(A_48,B_47,C_49) = A_48
      | ~ v1_funct_2(C_49,A_48,B_47)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_48,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_85,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_82])).

tff(c_88,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50,c_85])).

tff(c_89,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_88])).

tff(c_32,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_100,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden(A_53,k1_relat_1(k8_relat_1(B_54,C_55)))
      | ~ r2_hidden(k1_funct_1(C_55,A_53),B_54)
      | ~ r2_hidden(A_53,k1_relat_1(C_55))
      | ~ v1_funct_1(C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [B_5,C_6,A_4] :
      ( k1_funct_1(k8_relat_1(B_5,C_6),A_4) = k1_funct_1(C_6,A_4)
      | ~ r2_hidden(A_4,k1_relat_1(k8_relat_1(B_5,C_6)))
      | ~ v1_funct_1(C_6)
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_113,plain,(
    ! [B_56,C_57,A_58] :
      ( k1_funct_1(k8_relat_1(B_56,C_57),A_58) = k1_funct_1(C_57,A_58)
      | ~ r2_hidden(k1_funct_1(C_57,A_58),B_56)
      | ~ r2_hidden(A_58,k1_relat_1(C_57))
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(resolution,[status(thm)],[c_100,c_8])).

tff(c_120,plain,
    ( k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_124,plain,(
    k1_funct_1(k8_relat_1('#skF_4','#skF_5'),'#skF_3') = k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_40,c_34,c_89,c_120])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:13:40 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.27  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.06/1.27  
% 2.06/1.27  %Foreground sorts:
% 2.06/1.27  
% 2.06/1.27  
% 2.06/1.27  %Background operators:
% 2.06/1.27  
% 2.06/1.27  
% 2.06/1.27  %Foreground operators:
% 2.06/1.27  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.06/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.27  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.06/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.06/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.06/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.27  
% 2.06/1.28  tff(f_88, negated_conjecture, ~(![A, B, C, D, E]: (((v1_funct_1(E) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((r2_hidden(C, A) & r2_hidden(k1_funct_1(E, C), D)) => ((B = k1_xboole_0) | (k1_funct_1(k6_relset_1(A, B, D, E), C) = k1_funct_1(E, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_funct_2)).
% 2.06/1.28  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.06/1.28  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.06/1.28  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.06/1.28  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.06/1.28  tff(f_35, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_funct_1)).
% 2.06/1.28  tff(f_43, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_1)).
% 2.06/1.28  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.06/1.28  tff(c_58, plain, (![A_32, B_33, C_34, D_35]: (k6_relset_1(A_32, B_33, C_34, D_35)=k8_relat_1(C_34, D_35) | ~m1_subset_1(D_35, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.28  tff(c_61, plain, (![C_34]: (k6_relset_1('#skF_1', '#skF_2', C_34, '#skF_5')=k8_relat_1(C_34, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_58])).
% 2.06/1.28  tff(c_28, plain, (k1_funct_1(k6_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.06/1.28  tff(c_63, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_28])).
% 2.06/1.28  tff(c_41, plain, (![C_20, A_21, B_22]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.06/1.28  tff(c_45, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_41])).
% 2.06/1.28  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.06/1.28  tff(c_34, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.06/1.28  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.06/1.28  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.06/1.28  tff(c_46, plain, (![A_23, B_24, C_25]: (k1_relset_1(A_23, B_24, C_25)=k1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.06/1.28  tff(c_50, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_46])).
% 2.06/1.28  tff(c_82, plain, (![B_47, A_48, C_49]: (k1_xboole_0=B_47 | k1_relset_1(A_48, B_47, C_49)=A_48 | ~v1_funct_2(C_49, A_48, B_47) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_48, B_47))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.06/1.28  tff(c_85, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_82])).
% 2.06/1.28  tff(c_88, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50, c_85])).
% 2.06/1.28  tff(c_89, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_30, c_88])).
% 2.06/1.28  tff(c_32, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.06/1.28  tff(c_100, plain, (![A_53, B_54, C_55]: (r2_hidden(A_53, k1_relat_1(k8_relat_1(B_54, C_55))) | ~r2_hidden(k1_funct_1(C_55, A_53), B_54) | ~r2_hidden(A_53, k1_relat_1(C_55)) | ~v1_funct_1(C_55) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.28  tff(c_8, plain, (![B_5, C_6, A_4]: (k1_funct_1(k8_relat_1(B_5, C_6), A_4)=k1_funct_1(C_6, A_4) | ~r2_hidden(A_4, k1_relat_1(k8_relat_1(B_5, C_6))) | ~v1_funct_1(C_6) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.06/1.28  tff(c_113, plain, (![B_56, C_57, A_58]: (k1_funct_1(k8_relat_1(B_56, C_57), A_58)=k1_funct_1(C_57, A_58) | ~r2_hidden(k1_funct_1(C_57, A_58), B_56) | ~r2_hidden(A_58, k1_relat_1(C_57)) | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(resolution, [status(thm)], [c_100, c_8])).
% 2.06/1.28  tff(c_120, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_113])).
% 2.06/1.28  tff(c_124, plain, (k1_funct_1(k8_relat_1('#skF_4', '#skF_5'), '#skF_3')=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_40, c_34, c_89, c_120])).
% 2.06/1.28  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_124])).
% 2.06/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.28  
% 2.06/1.28  Inference rules
% 2.06/1.28  ----------------------
% 2.06/1.28  #Ref     : 0
% 2.06/1.28  #Sup     : 18
% 2.06/1.28  #Fact    : 0
% 2.06/1.28  #Define  : 0
% 2.06/1.28  #Split   : 0
% 2.06/1.28  #Chain   : 0
% 2.06/1.28  #Close   : 0
% 2.06/1.28  
% 2.06/1.28  Ordering : KBO
% 2.06/1.28  
% 2.06/1.28  Simplification rules
% 2.06/1.28  ----------------------
% 2.06/1.28  #Subsume      : 0
% 2.06/1.28  #Demod        : 10
% 2.06/1.28  #Tautology    : 11
% 2.06/1.28  #SimpNegUnit  : 3
% 2.06/1.28  #BackRed      : 2
% 2.06/1.28  
% 2.06/1.28  #Partial instantiations: 0
% 2.06/1.28  #Strategies tried      : 1
% 2.06/1.28  
% 2.06/1.28  Timing (in seconds)
% 2.06/1.28  ----------------------
% 2.06/1.29  Preprocessing        : 0.33
% 2.06/1.29  Parsing              : 0.18
% 2.06/1.29  CNF conversion       : 0.02
% 2.06/1.29  Main loop            : 0.15
% 2.06/1.29  Inferencing          : 0.06
% 2.06/1.29  Reduction            : 0.05
% 2.06/1.29  Demodulation         : 0.03
% 2.06/1.29  BG Simplification    : 0.01
% 2.06/1.29  Subsumption          : 0.02
% 2.06/1.29  Abstraction          : 0.01
% 2.06/1.29  MUC search           : 0.00
% 2.06/1.29  Cooper               : 0.00
% 2.06/1.29  Total                : 0.50
% 2.06/1.29  Index Insertion      : 0.00
% 2.06/1.29  Index Deletion       : 0.00
% 2.06/1.29  Index Matching       : 0.00
% 2.06/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
