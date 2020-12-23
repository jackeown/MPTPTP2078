%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:03 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   54 (  81 expanded)
%              Number of leaves         :   30 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 152 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_41,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_45,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_41])).

tff(c_58,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k7_relset_1(A_42,B_43,C_44,D_45) = k9_relat_1(C_44,D_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_61,plain,(
    ! [D_45] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_45) = k9_relat_1('#skF_5',D_45) ),
    inference(resolution,[status(thm)],[c_30,c_58])).

tff(c_120,plain,(
    ! [A_61,B_62,C_63] :
      ( k7_relset_1(A_61,B_62,C_63,A_61) = k2_relset_1(A_61,B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_122,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') = k2_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_120])).

tff(c_124,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k9_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_122])).

tff(c_28,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_126,plain,(
    r2_hidden('#skF_2',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_28])).

tff(c_47,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden('#skF_1'(A_33,B_34,C_35),B_34)
      | ~ r2_hidden(A_33,k9_relat_1(C_35,B_34))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [A_33,B_34,C_35] :
      ( m1_subset_1('#skF_1'(A_33,B_34,C_35),B_34)
      | ~ r2_hidden(A_33,k9_relat_1(C_35,B_34))
      | ~ v1_relat_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_47,c_2])).

tff(c_132,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_126,c_51])).

tff(c_138,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_132])).

tff(c_26,plain,(
    ! [E_23] :
      ( k1_funct_1('#skF_5',E_23) != '#skF_2'
      | ~ m1_subset_1(E_23,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_160,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_138,c_26])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_77,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden(k4_tarski('#skF_1'(A_53,B_54,C_55),A_53),C_55)
      | ~ r2_hidden(A_53,k9_relat_1(C_55,B_54))
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [C_11,A_9,B_10] :
      ( k1_funct_1(C_11,A_9) = B_10
      | ~ r2_hidden(k4_tarski(A_9,B_10),C_11)
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_208,plain,(
    ! [C_73,A_74,B_75] :
      ( k1_funct_1(C_73,'#skF_1'(A_74,B_75,C_73)) = A_74
      | ~ v1_funct_1(C_73)
      | ~ r2_hidden(A_74,k9_relat_1(C_73,B_75))
      | ~ v1_relat_1(C_73) ) ),
    inference(resolution,[status(thm)],[c_77,c_14])).

tff(c_210,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_126,c_208])).

tff(c_222,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_34,c_210])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.26  
% 2.19/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.26  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.19/1.26  
% 2.19/1.26  %Foreground sorts:
% 2.19/1.26  
% 2.19/1.26  
% 2.19/1.26  %Background operators:
% 2.19/1.26  
% 2.19/1.26  
% 2.19/1.26  %Foreground operators:
% 2.19/1.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.19/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.19/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.19/1.26  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.19/1.26  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.19/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.19/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.19/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.19/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.19/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.26  
% 2.19/1.27  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 2.19/1.27  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.19/1.27  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.19/1.27  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.19/1.27  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.19/1.27  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.19/1.27  tff(f_50, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.19/1.27  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.19/1.27  tff(c_41, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.19/1.27  tff(c_45, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_41])).
% 2.19/1.27  tff(c_58, plain, (![A_42, B_43, C_44, D_45]: (k7_relset_1(A_42, B_43, C_44, D_45)=k9_relat_1(C_44, D_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.19/1.27  tff(c_61, plain, (![D_45]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_45)=k9_relat_1('#skF_5', D_45))), inference(resolution, [status(thm)], [c_30, c_58])).
% 2.19/1.27  tff(c_120, plain, (![A_61, B_62, C_63]: (k7_relset_1(A_61, B_62, C_63, A_61)=k2_relset_1(A_61, B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.19/1.27  tff(c_122, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')=k2_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_120])).
% 2.19/1.27  tff(c_124, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k9_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_122])).
% 2.19/1.27  tff(c_28, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.19/1.27  tff(c_126, plain, (r2_hidden('#skF_2', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_28])).
% 2.19/1.27  tff(c_47, plain, (![A_33, B_34, C_35]: (r2_hidden('#skF_1'(A_33, B_34, C_35), B_34) | ~r2_hidden(A_33, k9_relat_1(C_35, B_34)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.27  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.27  tff(c_51, plain, (![A_33, B_34, C_35]: (m1_subset_1('#skF_1'(A_33, B_34, C_35), B_34) | ~r2_hidden(A_33, k9_relat_1(C_35, B_34)) | ~v1_relat_1(C_35))), inference(resolution, [status(thm)], [c_47, c_2])).
% 2.19/1.27  tff(c_132, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_126, c_51])).
% 2.19/1.27  tff(c_138, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_132])).
% 2.19/1.27  tff(c_26, plain, (![E_23]: (k1_funct_1('#skF_5', E_23)!='#skF_2' | ~m1_subset_1(E_23, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.19/1.27  tff(c_160, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))!='#skF_2'), inference(resolution, [status(thm)], [c_138, c_26])).
% 2.19/1.27  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.19/1.27  tff(c_77, plain, (![A_53, B_54, C_55]: (r2_hidden(k4_tarski('#skF_1'(A_53, B_54, C_55), A_53), C_55) | ~r2_hidden(A_53, k9_relat_1(C_55, B_54)) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.27  tff(c_14, plain, (![C_11, A_9, B_10]: (k1_funct_1(C_11, A_9)=B_10 | ~r2_hidden(k4_tarski(A_9, B_10), C_11) | ~v1_funct_1(C_11) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.19/1.27  tff(c_208, plain, (![C_73, A_74, B_75]: (k1_funct_1(C_73, '#skF_1'(A_74, B_75, C_73))=A_74 | ~v1_funct_1(C_73) | ~r2_hidden(A_74, k9_relat_1(C_73, B_75)) | ~v1_relat_1(C_73))), inference(resolution, [status(thm)], [c_77, c_14])).
% 2.19/1.27  tff(c_210, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_126, c_208])).
% 2.19/1.27  tff(c_222, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_34, c_210])).
% 2.19/1.27  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_222])).
% 2.19/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.27  
% 2.19/1.27  Inference rules
% 2.19/1.27  ----------------------
% 2.19/1.27  #Ref     : 0
% 2.19/1.27  #Sup     : 44
% 2.19/1.27  #Fact    : 0
% 2.19/1.27  #Define  : 0
% 2.19/1.27  #Split   : 1
% 2.19/1.27  #Chain   : 0
% 2.19/1.27  #Close   : 0
% 2.19/1.27  
% 2.19/1.27  Ordering : KBO
% 2.19/1.27  
% 2.19/1.27  Simplification rules
% 2.19/1.27  ----------------------
% 2.19/1.27  #Subsume      : 2
% 2.19/1.27  #Demod        : 7
% 2.19/1.27  #Tautology    : 9
% 2.19/1.27  #SimpNegUnit  : 1
% 2.19/1.27  #BackRed      : 2
% 2.19/1.27  
% 2.19/1.27  #Partial instantiations: 0
% 2.19/1.27  #Strategies tried      : 1
% 2.19/1.27  
% 2.19/1.27  Timing (in seconds)
% 2.19/1.27  ----------------------
% 2.19/1.27  Preprocessing        : 0.32
% 2.19/1.28  Parsing              : 0.17
% 2.19/1.28  CNF conversion       : 0.02
% 2.19/1.28  Main loop            : 0.20
% 2.19/1.28  Inferencing          : 0.08
% 2.19/1.28  Reduction            : 0.06
% 2.19/1.28  Demodulation         : 0.04
% 2.19/1.28  BG Simplification    : 0.01
% 2.19/1.28  Subsumption          : 0.03
% 2.19/1.28  Abstraction          : 0.02
% 2.19/1.28  MUC search           : 0.00
% 2.19/1.28  Cooper               : 0.00
% 2.19/1.28  Total                : 0.55
% 2.19/1.28  Index Insertion      : 0.00
% 2.19/1.28  Index Deletion       : 0.00
% 2.19/1.28  Index Matching       : 0.00
% 2.19/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
