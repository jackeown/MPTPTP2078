%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:52 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   56 (  72 expanded)
%              Number of leaves         :   34 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 ( 103 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_52,plain,(
    ! [C_31,A_32,B_33] :
      ( v1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k9_relat_1(B_11,A_10),k2_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_126,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( k7_relset_1(A_56,B_57,C_58,D_59) = k9_relat_1(C_58,D_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_129,plain,(
    ! [D_59] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_59) = k9_relat_1('#skF_4',D_59) ),
    inference(resolution,[status(thm)],[c_28,c_126])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_76,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_83,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_12])).

tff(c_86,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_83])).

tff(c_92,plain,(
    ! [B_51,A_52] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_51,k1_tarski(A_52))),k1_tarski(k1_funct_1(B_51,A_52)))
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_97,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_funct_1('#skF_4','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_92])).

tff(c_100,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32,c_97])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,k1_tarski(k1_funct_1('#skF_4','#skF_1')))
      | ~ r1_tarski(A_53,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_24,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_111,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_104,c_24])).

tff(c_130,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_111])).

tff(c_143,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_130])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:12:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.46  
% 1.99/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.99/1.47  
% 1.99/1.47  %Foreground sorts:
% 1.99/1.47  
% 1.99/1.47  
% 1.99/1.47  %Background operators:
% 1.99/1.47  
% 1.99/1.47  
% 1.99/1.47  %Foreground operators:
% 1.99/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.99/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.99/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.47  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.99/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.99/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.47  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.99/1.47  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.47  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.99/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.99/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.47  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.99/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.47  
% 1.99/1.48  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 1.99/1.48  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.99/1.48  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 1.99/1.48  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.99/1.48  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.99/1.48  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.99/1.48  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 1.99/1.48  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.99/1.48  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.99/1.48  tff(c_52, plain, (![C_31, A_32, B_33]: (v1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.48  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_52])).
% 1.99/1.48  tff(c_10, plain, (![B_11, A_10]: (r1_tarski(k9_relat_1(B_11, A_10), k2_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.48  tff(c_126, plain, (![A_56, B_57, C_58, D_59]: (k7_relset_1(A_56, B_57, C_58, D_59)=k9_relat_1(C_58, D_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.99/1.48  tff(c_129, plain, (![D_59]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_59)=k9_relat_1('#skF_4', D_59))), inference(resolution, [status(thm)], [c_28, c_126])).
% 1.99/1.48  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.99/1.48  tff(c_76, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.99/1.48  tff(c_80, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_76])).
% 1.99/1.48  tff(c_12, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.48  tff(c_83, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_12])).
% 1.99/1.48  tff(c_86, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_83])).
% 1.99/1.48  tff(c_92, plain, (![B_51, A_52]: (r1_tarski(k2_relat_1(k7_relat_1(B_51, k1_tarski(A_52))), k1_tarski(k1_funct_1(B_51, A_52))) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.48  tff(c_97, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_funct_1('#skF_4', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_86, c_92])).
% 1.99/1.48  tff(c_100, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_32, c_97])).
% 1.99/1.48  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.48  tff(c_104, plain, (![A_53]: (r1_tarski(A_53, k1_tarski(k1_funct_1('#skF_4', '#skF_1'))) | ~r1_tarski(A_53, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_100, c_2])).
% 1.99/1.48  tff(c_24, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.99/1.48  tff(c_111, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_104, c_24])).
% 1.99/1.48  tff(c_130, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_111])).
% 1.99/1.48  tff(c_143, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_130])).
% 1.99/1.48  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_143])).
% 1.99/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.48  
% 1.99/1.48  Inference rules
% 1.99/1.48  ----------------------
% 1.99/1.48  #Ref     : 0
% 1.99/1.48  #Sup     : 26
% 1.99/1.48  #Fact    : 0
% 1.99/1.48  #Define  : 0
% 1.99/1.48  #Split   : 0
% 1.99/1.48  #Chain   : 0
% 1.99/1.48  #Close   : 0
% 1.99/1.48  
% 1.99/1.48  Ordering : KBO
% 1.99/1.48  
% 1.99/1.48  Simplification rules
% 1.99/1.48  ----------------------
% 1.99/1.48  #Subsume      : 1
% 1.99/1.48  #Demod        : 7
% 1.99/1.48  #Tautology    : 11
% 1.99/1.48  #SimpNegUnit  : 0
% 1.99/1.48  #BackRed      : 2
% 1.99/1.48  
% 1.99/1.48  #Partial instantiations: 0
% 1.99/1.48  #Strategies tried      : 1
% 1.99/1.48  
% 1.99/1.48  Timing (in seconds)
% 1.99/1.48  ----------------------
% 1.99/1.48  Preprocessing        : 0.38
% 1.99/1.48  Parsing              : 0.22
% 1.99/1.48  CNF conversion       : 0.02
% 1.99/1.48  Main loop            : 0.14
% 1.99/1.48  Inferencing          : 0.06
% 1.99/1.48  Reduction            : 0.04
% 1.99/1.48  Demodulation         : 0.03
% 1.99/1.48  BG Simplification    : 0.01
% 1.99/1.48  Subsumption          : 0.02
% 1.99/1.48  Abstraction          : 0.01
% 1.99/1.48  MUC search           : 0.00
% 1.99/1.48  Cooper               : 0.00
% 1.99/1.48  Total                : 0.55
% 1.99/1.48  Index Insertion      : 0.00
% 1.99/1.48  Index Deletion       : 0.00
% 1.99/1.48  Index Matching       : 0.00
% 1.99/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
