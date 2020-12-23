%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:17 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 109 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 191 expanded)
%              Number of equality atoms :   17 (  39 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_51,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_31,plain,(
    ! [C_21,A_22,B_23] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_35,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_31])).

tff(c_52,plain,(
    ! [C_28,A_29,B_30] :
      ( v4_relat_1(C_28,A_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_57,plain,(
    ! [B_31,A_32] :
      ( k7_relat_1(B_31,A_32) = B_31
      | ~ v4_relat_1(B_31,A_32)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_57])).

tff(c_63,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_60])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_6,A_5)),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_67,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_10])).

tff(c_71,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_67])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_81,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_82,plain,(
    ! [A_36,B_37,C_38] :
      ( k1_relset_1(A_36,B_37,C_38) = k1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_86,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_82])).

tff(c_26,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_99,plain,(
    ! [C_41,A_42,B_43,D_44] :
      ( r1_tarski(C_41,k1_relset_1(A_42,B_43,D_44))
      | ~ r1_tarski(k6_relat_1(C_41),D_44)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_115,plain,(
    ! [A_49,B_50] :
      ( r1_tarski('#skF_2',k1_relset_1(A_49,B_50,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(resolution,[status(thm)],[c_26,c_99])).

tff(c_118,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_115])).

tff(c_120,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_118])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_120])).

tff(c_123,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_132,plain,(
    ! [A_51,B_52,C_53] :
      ( k1_relset_1(A_51,B_52,C_53) = k1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_135,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_132])).

tff(c_137,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_135])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_137])).

tff(c_140,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_208,plain,(
    ! [C_70,A_71,B_72,D_73] :
      ( r1_tarski(C_70,k2_relset_1(A_71,B_72,D_73))
      | ~ r1_tarski(k6_relat_1(C_70),D_73)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_216,plain,(
    ! [A_74,B_75] :
      ( r1_tarski('#skF_2',k2_relset_1(A_74,B_75,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(resolution,[status(thm)],[c_26,c_208])).

tff(c_219,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_216])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 18:38:19 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.63  
% 2.48/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.64  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.48/1.64  
% 2.48/1.64  %Foreground sorts:
% 2.48/1.64  
% 2.48/1.64  
% 2.48/1.64  %Background operators:
% 2.48/1.64  
% 2.48/1.64  
% 2.48/1.64  %Foreground operators:
% 2.48/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.48/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.48/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.64  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.64  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.64  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.48/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.48/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.48/1.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.48/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.48/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.48/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.64  
% 2.48/1.66  tff(f_72, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relset_1)).
% 2.48/1.66  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.48/1.66  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.48/1.66  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.48/1.66  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.48/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.48/1.66  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.48/1.66  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 2.48/1.66  tff(c_24, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.48/1.66  tff(c_51, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.48/1.66  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.48/1.66  tff(c_31, plain, (![C_21, A_22, B_23]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.48/1.66  tff(c_35, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_31])).
% 2.48/1.66  tff(c_52, plain, (![C_28, A_29, B_30]: (v4_relat_1(C_28, A_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.48/1.66  tff(c_56, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_52])).
% 2.48/1.66  tff(c_57, plain, (![B_31, A_32]: (k7_relat_1(B_31, A_32)=B_31 | ~v4_relat_1(B_31, A_32) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.48/1.66  tff(c_60, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_57])).
% 2.48/1.66  tff(c_63, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_60])).
% 2.48/1.66  tff(c_10, plain, (![B_6, A_5]: (r1_tarski(k1_relat_1(k7_relat_1(B_6, A_5)), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.66  tff(c_67, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_63, c_10])).
% 2.48/1.66  tff(c_71, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_67])).
% 2.48/1.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.66  tff(c_80, plain, (k1_relat_1('#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_71, c_2])).
% 2.48/1.66  tff(c_81, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_80])).
% 2.48/1.66  tff(c_82, plain, (![A_36, B_37, C_38]: (k1_relset_1(A_36, B_37, C_38)=k1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.66  tff(c_86, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_82])).
% 2.48/1.66  tff(c_26, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.48/1.66  tff(c_99, plain, (![C_41, A_42, B_43, D_44]: (r1_tarski(C_41, k1_relset_1(A_42, B_43, D_44)) | ~r1_tarski(k6_relat_1(C_41), D_44) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.48/1.66  tff(c_115, plain, (![A_49, B_50]: (r1_tarski('#skF_2', k1_relset_1(A_49, B_50, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(resolution, [status(thm)], [c_26, c_99])).
% 2.48/1.66  tff(c_118, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_115])).
% 2.48/1.66  tff(c_120, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_118])).
% 2.48/1.66  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_120])).
% 2.48/1.66  tff(c_123, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_80])).
% 2.48/1.66  tff(c_132, plain, (![A_51, B_52, C_53]: (k1_relset_1(A_51, B_52, C_53)=k1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.48/1.66  tff(c_135, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_132])).
% 2.48/1.66  tff(c_137, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_135])).
% 2.48/1.66  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_137])).
% 2.48/1.66  tff(c_140, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_24])).
% 2.48/1.66  tff(c_208, plain, (![C_70, A_71, B_72, D_73]: (r1_tarski(C_70, k2_relset_1(A_71, B_72, D_73)) | ~r1_tarski(k6_relat_1(C_70), D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.48/1.66  tff(c_216, plain, (![A_74, B_75]: (r1_tarski('#skF_2', k2_relset_1(A_74, B_75, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(resolution, [status(thm)], [c_26, c_208])).
% 2.48/1.66  tff(c_219, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_216])).
% 2.48/1.66  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_219])).
% 2.48/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.66  
% 2.48/1.66  Inference rules
% 2.48/1.66  ----------------------
% 2.48/1.66  #Ref     : 0
% 2.48/1.66  #Sup     : 40
% 2.48/1.66  #Fact    : 0
% 2.48/1.66  #Define  : 0
% 2.48/1.66  #Split   : 4
% 2.48/1.66  #Chain   : 0
% 2.48/1.66  #Close   : 0
% 2.48/1.66  
% 2.48/1.66  Ordering : KBO
% 2.48/1.66  
% 2.48/1.66  Simplification rules
% 2.48/1.66  ----------------------
% 2.48/1.66  #Subsume      : 1
% 2.48/1.66  #Demod        : 30
% 2.48/1.66  #Tautology    : 20
% 2.48/1.66  #SimpNegUnit  : 4
% 2.48/1.66  #BackRed      : 5
% 2.48/1.66  
% 2.48/1.66  #Partial instantiations: 0
% 2.48/1.66  #Strategies tried      : 1
% 2.48/1.66  
% 2.48/1.66  Timing (in seconds)
% 2.48/1.66  ----------------------
% 2.48/1.67  Preprocessing        : 0.47
% 2.48/1.67  Parsing              : 0.24
% 2.48/1.67  CNF conversion       : 0.03
% 2.48/1.67  Main loop            : 0.30
% 2.48/1.67  Inferencing          : 0.10
% 2.48/1.67  Reduction            : 0.10
% 2.48/1.67  Demodulation         : 0.07
% 2.48/1.67  BG Simplification    : 0.02
% 2.48/1.67  Subsumption          : 0.05
% 2.48/1.67  Abstraction          : 0.02
% 2.48/1.67  MUC search           : 0.00
% 2.48/1.67  Cooper               : 0.00
% 2.48/1.67  Total                : 0.82
% 2.48/1.67  Index Insertion      : 0.00
% 2.48/1.67  Index Deletion       : 0.00
% 2.48/1.67  Index Matching       : 0.00
% 2.48/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
