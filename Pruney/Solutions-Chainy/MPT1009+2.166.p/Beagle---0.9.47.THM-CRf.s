%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:05 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   50 (  60 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  94 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,k1_tarski(A),B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
     => ( B != k1_xboole_0
       => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_25,plain,(
    ! [B_22,A_23] :
      ( v1_relat_1(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_25])).

tff(c_31,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_28])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k9_relat_1(B_7,A_6),k2_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [A_24,B_25,C_26] :
      ( k2_relset_1(A_24,B_25,C_26) = k2_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_32])).

tff(c_55,plain,(
    ! [A_32,B_33,C_34] :
      ( k2_relset_1(k1_tarski(A_32),B_33,C_34) = k1_tarski(k1_funct_1(C_34,A_32))
      | k1_xboole_0 = B_33
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_32),B_33)))
      | ~ v1_funct_2(C_34,k1_tarski(A_32),B_33)
      | ~ v1_funct_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,
    ( k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski(k1_funct_1('#skF_4','#skF_1'))
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_55])).

tff(c_61,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_36,c_58])).

tff(c_62,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_61])).

tff(c_41,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( k7_relset_1(A_27,B_28,C_29,D_30) = k9_relat_1(C_29,D_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    ! [D_30] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_30) = k9_relat_1('#skF_4',D_30) ),
    inference(resolution,[status(thm)],[c_18,c_41])).

tff(c_14,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_45,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_14])).

tff(c_63,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_45])).

tff(c_74,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.14  
% 1.82/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.14  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.82/1.14  
% 1.82/1.14  %Foreground sorts:
% 1.82/1.14  
% 1.82/1.14  
% 1.82/1.14  %Background operators:
% 1.82/1.14  
% 1.82/1.14  
% 1.82/1.14  %Foreground operators:
% 1.82/1.14  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.82/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.82/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.82/1.14  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.82/1.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.82/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.82/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.82/1.14  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.82/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.82/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.82/1.14  
% 1.82/1.15  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.82/1.15  tff(f_69, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 1.82/1.15  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.82/1.15  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 1.82/1.15  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.82/1.15  tff(f_57, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 1.82/1.15  tff(f_46, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.82/1.15  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.82/1.15  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.82/1.15  tff(c_25, plain, (![B_22, A_23]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.15  tff(c_28, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_25])).
% 1.82/1.15  tff(c_31, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_28])).
% 1.82/1.15  tff(c_6, plain, (![B_7, A_6]: (r1_tarski(k9_relat_1(B_7, A_6), k2_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.82/1.15  tff(c_16, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.82/1.15  tff(c_22, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.82/1.15  tff(c_20, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.82/1.15  tff(c_32, plain, (![A_24, B_25, C_26]: (k2_relset_1(A_24, B_25, C_26)=k2_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.82/1.15  tff(c_36, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_32])).
% 1.82/1.15  tff(c_55, plain, (![A_32, B_33, C_34]: (k2_relset_1(k1_tarski(A_32), B_33, C_34)=k1_tarski(k1_funct_1(C_34, A_32)) | k1_xboole_0=B_33 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_32), B_33))) | ~v1_funct_2(C_34, k1_tarski(A_32), B_33) | ~v1_funct_1(C_34))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.15  tff(c_58, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski(k1_funct_1('#skF_4', '#skF_1')) | k1_xboole_0='#skF_2' | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_55])).
% 1.82/1.15  tff(c_61, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_36, c_58])).
% 1.82/1.15  tff(c_62, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_16, c_61])).
% 1.82/1.15  tff(c_41, plain, (![A_27, B_28, C_29, D_30]: (k7_relset_1(A_27, B_28, C_29, D_30)=k9_relat_1(C_29, D_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.15  tff(c_44, plain, (![D_30]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_30)=k9_relat_1('#skF_4', D_30))), inference(resolution, [status(thm)], [c_18, c_41])).
% 1.82/1.15  tff(c_14, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.82/1.15  tff(c_45, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_14])).
% 1.82/1.15  tff(c_63, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_45])).
% 1.82/1.15  tff(c_74, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_63])).
% 1.82/1.15  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31, c_74])).
% 1.82/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.15  
% 1.82/1.15  Inference rules
% 1.82/1.15  ----------------------
% 1.82/1.15  #Ref     : 0
% 1.82/1.15  #Sup     : 12
% 1.82/1.15  #Fact    : 0
% 1.82/1.15  #Define  : 0
% 1.82/1.15  #Split   : 0
% 1.82/1.15  #Chain   : 0
% 1.82/1.15  #Close   : 0
% 1.82/1.15  
% 1.82/1.15  Ordering : KBO
% 1.82/1.15  
% 1.82/1.15  Simplification rules
% 1.82/1.15  ----------------------
% 1.82/1.15  #Subsume      : 0
% 1.82/1.15  #Demod        : 9
% 1.82/1.15  #Tautology    : 6
% 1.82/1.15  #SimpNegUnit  : 1
% 1.82/1.15  #BackRed      : 2
% 1.82/1.15  
% 1.82/1.15  #Partial instantiations: 0
% 1.82/1.15  #Strategies tried      : 1
% 1.82/1.15  
% 1.82/1.15  Timing (in seconds)
% 1.82/1.15  ----------------------
% 1.82/1.15  Preprocessing        : 0.29
% 1.82/1.15  Parsing              : 0.16
% 1.82/1.15  CNF conversion       : 0.02
% 1.82/1.15  Main loop            : 0.10
% 1.82/1.15  Inferencing          : 0.04
% 1.82/1.15  Reduction            : 0.04
% 1.82/1.15  Demodulation         : 0.03
% 1.82/1.15  BG Simplification    : 0.01
% 1.82/1.15  Subsumption          : 0.01
% 1.82/1.15  Abstraction          : 0.00
% 1.82/1.15  MUC search           : 0.00
% 1.82/1.15  Cooper               : 0.00
% 1.82/1.15  Total                : 0.42
% 1.82/1.15  Index Insertion      : 0.00
% 1.82/1.15  Index Deletion       : 0.00
% 1.82/1.15  Index Matching       : 0.00
% 1.82/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
