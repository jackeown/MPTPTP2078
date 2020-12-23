%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:33 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  59 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 (  85 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_25,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_29,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_25])).

tff(c_63,plain,(
    ! [C_38,A_39,B_40] :
      ( v4_relat_1(C_38,A_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_67,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_63])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_tarski(A_29,C_30)
      | ~ r1_tarski(B_31,C_30)
      | ~ r1_tarski(A_29,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [A_32] :
      ( r1_tarski(A_32,'#skF_3')
      | ~ r1_tarski(A_32,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_36])).

tff(c_48,plain,(
    ! [B_5] :
      ( r1_tarski(k1_relat_1(B_5),'#skF_3')
      | ~ v4_relat_1(B_5,'#skF_2')
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_74,plain,(
    ! [B_41,A_42] :
      ( k7_relat_1(B_41,A_42) = B_41
      | ~ r1_tarski(k1_relat_1(B_41),A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_100,plain,(
    ! [B_45] :
      ( k7_relat_1(B_45,'#skF_3') = B_45
      | ~ v4_relat_1(B_45,'#skF_2')
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_48,c_74])).

tff(c_103,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_67,c_100])).

tff(c_106,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_103])).

tff(c_123,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k5_relset_1(A_51,B_52,C_53,D_54) = k7_relat_1(C_53,D_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_126,plain,(
    ! [D_54] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_54) = k7_relat_1('#skF_4',D_54) ),
    inference(resolution,[status(thm)],[c_24,c_123])).

tff(c_20,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_131,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_20])).

tff(c_132,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_131])).

tff(c_127,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( r2_relset_1(A_55,B_56,C_57,C_57)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_142,plain,(
    ! [C_60] :
      ( r2_relset_1('#skF_2','#skF_1',C_60,C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_24,c_127])).

tff(c_144,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_142])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 19:14:12 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.45  
% 2.03/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.46  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.03/1.46  
% 2.03/1.46  %Foreground sorts:
% 2.03/1.46  
% 2.03/1.46  
% 2.03/1.46  %Background operators:
% 2.03/1.46  
% 2.03/1.46  
% 2.03/1.46  %Foreground operators:
% 2.03/1.46  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.03/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.46  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.03/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.03/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.03/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.03/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.46  
% 2.22/1.47  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.22/1.47  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.22/1.47  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.22/1.47  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.22/1.47  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.22/1.47  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.22/1.47  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.22/1.47  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.22/1.47  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.22/1.47  tff(c_25, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.47  tff(c_29, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_25])).
% 2.22/1.47  tff(c_63, plain, (![C_38, A_39, B_40]: (v4_relat_1(C_38, A_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.22/1.47  tff(c_67, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_63])).
% 2.22/1.47  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.47  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.22/1.47  tff(c_36, plain, (![A_29, C_30, B_31]: (r1_tarski(A_29, C_30) | ~r1_tarski(B_31, C_30) | ~r1_tarski(A_29, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.47  tff(c_43, plain, (![A_32]: (r1_tarski(A_32, '#skF_3') | ~r1_tarski(A_32, '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_36])).
% 2.22/1.47  tff(c_48, plain, (![B_5]: (r1_tarski(k1_relat_1(B_5), '#skF_3') | ~v4_relat_1(B_5, '#skF_2') | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_43])).
% 2.22/1.47  tff(c_74, plain, (![B_41, A_42]: (k7_relat_1(B_41, A_42)=B_41 | ~r1_tarski(k1_relat_1(B_41), A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.47  tff(c_100, plain, (![B_45]: (k7_relat_1(B_45, '#skF_3')=B_45 | ~v4_relat_1(B_45, '#skF_2') | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_48, c_74])).
% 2.22/1.47  tff(c_103, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_67, c_100])).
% 2.22/1.47  tff(c_106, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_29, c_103])).
% 2.22/1.47  tff(c_123, plain, (![A_51, B_52, C_53, D_54]: (k5_relset_1(A_51, B_52, C_53, D_54)=k7_relat_1(C_53, D_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.22/1.47  tff(c_126, plain, (![D_54]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_54)=k7_relat_1('#skF_4', D_54))), inference(resolution, [status(thm)], [c_24, c_123])).
% 2.22/1.47  tff(c_20, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.22/1.47  tff(c_131, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_20])).
% 2.22/1.47  tff(c_132, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_131])).
% 2.22/1.47  tff(c_127, plain, (![A_55, B_56, C_57, D_58]: (r2_relset_1(A_55, B_56, C_57, C_57) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.47  tff(c_142, plain, (![C_60]: (r2_relset_1('#skF_2', '#skF_1', C_60, C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_24, c_127])).
% 2.22/1.47  tff(c_144, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_142])).
% 2.22/1.47  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_144])).
% 2.22/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.47  
% 2.22/1.47  Inference rules
% 2.22/1.47  ----------------------
% 2.22/1.47  #Ref     : 0
% 2.22/1.47  #Sup     : 26
% 2.22/1.47  #Fact    : 0
% 2.22/1.47  #Define  : 0
% 2.22/1.47  #Split   : 0
% 2.22/1.47  #Chain   : 0
% 2.22/1.47  #Close   : 0
% 2.22/1.47  
% 2.22/1.47  Ordering : KBO
% 2.22/1.47  
% 2.22/1.47  Simplification rules
% 2.22/1.47  ----------------------
% 2.22/1.47  #Subsume      : 0
% 2.22/1.47  #Demod        : 7
% 2.22/1.47  #Tautology    : 8
% 2.22/1.47  #SimpNegUnit  : 1
% 2.22/1.47  #BackRed      : 1
% 2.22/1.47  
% 2.22/1.47  #Partial instantiations: 0
% 2.22/1.47  #Strategies tried      : 1
% 2.22/1.47  
% 2.22/1.47  Timing (in seconds)
% 2.22/1.47  ----------------------
% 2.23/1.47  Preprocessing        : 0.39
% 2.23/1.47  Parsing              : 0.23
% 2.23/1.47  CNF conversion       : 0.02
% 2.23/1.47  Main loop            : 0.18
% 2.23/1.47  Inferencing          : 0.07
% 2.23/1.47  Reduction            : 0.05
% 2.23/1.47  Demodulation         : 0.04
% 2.23/1.47  BG Simplification    : 0.01
% 2.23/1.47  Subsumption          : 0.03
% 2.23/1.47  Abstraction          : 0.01
% 2.23/1.47  MUC search           : 0.00
% 2.23/1.47  Cooper               : 0.00
% 2.23/1.47  Total                : 0.60
% 2.23/1.47  Index Insertion      : 0.00
% 2.23/1.47  Index Deletion       : 0.00
% 2.23/1.47  Index Matching       : 0.00
% 2.23/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
