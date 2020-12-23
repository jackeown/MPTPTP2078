%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:56 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  88 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,k1_tarski(A),B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
     => ( B != k1_xboole_0
       => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_21,plain,(
    ! [C_16,A_17,B_18] :
      ( v1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_25,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_21])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k9_relat_1(B_2,A_1),k2_relat_1(B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_27,plain,(
    ! [A_21,B_22,C_23] :
      ( k2_relset_1(A_21,B_22,C_23) = k2_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_27])).

tff(c_50,plain,(
    ! [A_29,B_30,C_31] :
      ( k2_relset_1(k1_tarski(A_29),B_30,C_31) = k1_tarski(k1_funct_1(C_31,A_29))
      | k1_xboole_0 = B_30
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_29),B_30)))
      | ~ v1_funct_2(C_31,k1_tarski(A_29),B_30)
      | ~ v1_funct_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_53,plain,
    ( k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski(k1_funct_1('#skF_4','#skF_1'))
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_50])).

tff(c_56,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_31,c_53])).

tff(c_57,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_56])).

tff(c_36,plain,(
    ! [A_24,B_25,C_26,D_27] :
      ( k7_relset_1(A_24,B_25,C_26,D_27) = k9_relat_1(C_26,D_27)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39,plain,(
    ! [D_27] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_27) = k9_relat_1('#skF_4',D_27) ),
    inference(resolution,[status(thm)],[c_16,c_36])).

tff(c_12,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_40,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_12])).

tff(c_58,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_40])).

tff(c_69,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_58])).

tff(c_73,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:16:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.22  
% 1.79/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.22  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.79/1.22  
% 1.79/1.22  %Foreground sorts:
% 1.79/1.22  
% 1.79/1.22  
% 1.79/1.22  %Background operators:
% 1.79/1.22  
% 1.79/1.22  
% 1.79/1.22  %Foreground operators:
% 1.79/1.22  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.79/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.79/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.22  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.79/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.79/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.79/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.79/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.79/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.22  
% 1.94/1.23  tff(f_64, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 1.94/1.23  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.94/1.23  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 1.94/1.23  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.94/1.23  tff(f_52, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 1.94/1.23  tff(f_41, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.94/1.23  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.23  tff(c_21, plain, (![C_16, A_17, B_18]: (v1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.23  tff(c_25, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_21])).
% 1.94/1.23  tff(c_2, plain, (![B_2, A_1]: (r1_tarski(k9_relat_1(B_2, A_1), k2_relat_1(B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.23  tff(c_14, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.23  tff(c_20, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.23  tff(c_18, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.23  tff(c_27, plain, (![A_21, B_22, C_23]: (k2_relset_1(A_21, B_22, C_23)=k2_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.23  tff(c_31, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_27])).
% 1.94/1.23  tff(c_50, plain, (![A_29, B_30, C_31]: (k2_relset_1(k1_tarski(A_29), B_30, C_31)=k1_tarski(k1_funct_1(C_31, A_29)) | k1_xboole_0=B_30 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_29), B_30))) | ~v1_funct_2(C_31, k1_tarski(A_29), B_30) | ~v1_funct_1(C_31))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.23  tff(c_53, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski(k1_funct_1('#skF_4', '#skF_1')) | k1_xboole_0='#skF_2' | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_50])).
% 1.94/1.23  tff(c_56, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_31, c_53])).
% 1.94/1.23  tff(c_57, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_14, c_56])).
% 1.94/1.23  tff(c_36, plain, (![A_24, B_25, C_26, D_27]: (k7_relset_1(A_24, B_25, C_26, D_27)=k9_relat_1(C_26, D_27) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.94/1.23  tff(c_39, plain, (![D_27]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_27)=k9_relat_1('#skF_4', D_27))), inference(resolution, [status(thm)], [c_16, c_36])).
% 1.94/1.23  tff(c_12, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.23  tff(c_40, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_12])).
% 1.94/1.23  tff(c_58, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_40])).
% 1.94/1.23  tff(c_69, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2, c_58])).
% 1.94/1.23  tff(c_73, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25, c_69])).
% 1.94/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  Inference rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Ref     : 0
% 1.94/1.23  #Sup     : 12
% 1.94/1.23  #Fact    : 0
% 1.94/1.23  #Define  : 0
% 1.94/1.23  #Split   : 0
% 1.94/1.23  #Chain   : 0
% 1.94/1.23  #Close   : 0
% 1.94/1.23  
% 1.94/1.23  Ordering : KBO
% 1.94/1.23  
% 1.94/1.23  Simplification rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Subsume      : 0
% 1.94/1.23  #Demod        : 8
% 1.94/1.23  #Tautology    : 6
% 1.94/1.23  #SimpNegUnit  : 1
% 1.94/1.23  #BackRed      : 2
% 1.94/1.23  
% 1.94/1.23  #Partial instantiations: 0
% 1.94/1.23  #Strategies tried      : 1
% 1.94/1.23  
% 1.94/1.23  Timing (in seconds)
% 1.94/1.23  ----------------------
% 1.94/1.23  Preprocessing        : 0.31
% 1.94/1.23  Parsing              : 0.17
% 1.94/1.23  CNF conversion       : 0.02
% 1.94/1.23  Main loop            : 0.10
% 1.94/1.23  Inferencing          : 0.04
% 1.94/1.23  Reduction            : 0.03
% 1.94/1.23  Demodulation         : 0.02
% 1.94/1.23  BG Simplification    : 0.01
% 1.94/1.23  Subsumption          : 0.01
% 1.94/1.23  Abstraction          : 0.00
% 1.94/1.23  MUC search           : 0.00
% 1.94/1.23  Cooper               : 0.00
% 1.94/1.23  Total                : 0.43
% 1.94/1.23  Index Insertion      : 0.00
% 1.94/1.23  Index Deletion       : 0.00
% 1.94/1.23  Index Matching       : 0.00
% 1.94/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
