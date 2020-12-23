%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:31 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   51 (  78 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 147 expanded)
%              Number of equality atoms :   18 (  35 expanded)
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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_34])).

tff(c_54,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( k7_relset_1(A_40,B_41,C_42,D_43) = k9_relat_1(C_42,D_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_57,plain,(
    ! [D_43] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_43) = k9_relat_1('#skF_5',D_43) ),
    inference(resolution,[status(thm)],[c_28,c_54])).

tff(c_87,plain,(
    ! [A_47,B_48,C_49] :
      ( k7_relset_1(A_47,B_48,C_49,A_47) = k2_relset_1(A_47,B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_89,plain,(
    k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_2') = k2_relset_1('#skF_2','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_91,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k9_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_89])).

tff(c_26,plain,(
    r2_hidden('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_92,plain,(
    r2_hidden('#skF_4',k9_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_26])).

tff(c_40,plain,(
    ! [A_29,B_30,C_31] :
      ( r2_hidden('#skF_1'(A_29,B_30,C_31),B_30)
      | ~ r2_hidden(A_29,k9_relat_1(C_31,B_30))
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [E_21] :
      ( k1_funct_1('#skF_5',E_21) != '#skF_4'
      | ~ r2_hidden(E_21,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_45,plain,(
    ! [A_29,C_31] :
      ( k1_funct_1('#skF_5','#skF_1'(A_29,'#skF_2',C_31)) != '#skF_4'
      | ~ r2_hidden(A_29,k9_relat_1(C_31,'#skF_2'))
      | ~ v1_relat_1(C_31) ) ),
    inference(resolution,[status(thm)],[c_40,c_24])).

tff(c_99,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_2','#skF_5')) != '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_45])).

tff(c_102,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_2','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_99])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_112,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden(k4_tarski('#skF_1'(A_53,B_54,C_55),A_53),C_55)
      | ~ r2_hidden(A_53,k9_relat_1(C_55,B_54))
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [C_9,A_7,B_8] :
      ( k1_funct_1(C_9,A_7) = B_8
      | ~ r2_hidden(k4_tarski(A_7,B_8),C_9)
      | ~ v1_funct_1(C_9)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_131,plain,(
    ! [C_56,A_57,B_58] :
      ( k1_funct_1(C_56,'#skF_1'(A_57,B_58,C_56)) = A_57
      | ~ v1_funct_1(C_56)
      | ~ r2_hidden(A_57,k9_relat_1(C_56,B_58))
      | ~ v1_relat_1(C_56) ) ),
    inference(resolution,[status(thm)],[c_112,c_12])).

tff(c_136,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_2','#skF_5')) = '#skF_4'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_131])).

tff(c_146,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_2','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_136])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:09:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.21  
% 1.92/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.21  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 1.92/1.21  
% 1.92/1.21  %Foreground sorts:
% 1.92/1.21  
% 1.92/1.21  
% 1.92/1.21  %Background operators:
% 1.92/1.21  
% 1.92/1.21  
% 1.92/1.21  %Foreground operators:
% 1.92/1.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.92/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.92/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.92/1.21  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.92/1.21  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.92/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.92/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.92/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.92/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.92/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.92/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.92/1.21  
% 1.92/1.22  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 1.92/1.22  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.92/1.22  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.92/1.22  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 1.92/1.22  tff(f_36, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 1.92/1.22  tff(f_46, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 1.92/1.22  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.92/1.22  tff(c_34, plain, (![C_23, A_24, B_25]: (v1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.22  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_34])).
% 1.92/1.22  tff(c_54, plain, (![A_40, B_41, C_42, D_43]: (k7_relset_1(A_40, B_41, C_42, D_43)=k9_relat_1(C_42, D_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.92/1.22  tff(c_57, plain, (![D_43]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_43)=k9_relat_1('#skF_5', D_43))), inference(resolution, [status(thm)], [c_28, c_54])).
% 1.92/1.22  tff(c_87, plain, (![A_47, B_48, C_49]: (k7_relset_1(A_47, B_48, C_49, A_47)=k2_relset_1(A_47, B_48, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.22  tff(c_89, plain, (k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_2')=k2_relset_1('#skF_2', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_87])).
% 1.92/1.22  tff(c_91, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k9_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_89])).
% 1.92/1.22  tff(c_26, plain, (r2_hidden('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.92/1.22  tff(c_92, plain, (r2_hidden('#skF_4', k9_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_26])).
% 1.92/1.22  tff(c_40, plain, (![A_29, B_30, C_31]: (r2_hidden('#skF_1'(A_29, B_30, C_31), B_30) | ~r2_hidden(A_29, k9_relat_1(C_31, B_30)) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.92/1.22  tff(c_24, plain, (![E_21]: (k1_funct_1('#skF_5', E_21)!='#skF_4' | ~r2_hidden(E_21, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.92/1.22  tff(c_45, plain, (![A_29, C_31]: (k1_funct_1('#skF_5', '#skF_1'(A_29, '#skF_2', C_31))!='#skF_4' | ~r2_hidden(A_29, k9_relat_1(C_31, '#skF_2')) | ~v1_relat_1(C_31))), inference(resolution, [status(thm)], [c_40, c_24])).
% 1.92/1.22  tff(c_99, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_2', '#skF_5'))!='#skF_4' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_45])).
% 1.92/1.22  tff(c_102, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_2', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_99])).
% 1.92/1.22  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.92/1.22  tff(c_112, plain, (![A_53, B_54, C_55]: (r2_hidden(k4_tarski('#skF_1'(A_53, B_54, C_55), A_53), C_55) | ~r2_hidden(A_53, k9_relat_1(C_55, B_54)) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.92/1.22  tff(c_12, plain, (![C_9, A_7, B_8]: (k1_funct_1(C_9, A_7)=B_8 | ~r2_hidden(k4_tarski(A_7, B_8), C_9) | ~v1_funct_1(C_9) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.92/1.22  tff(c_131, plain, (![C_56, A_57, B_58]: (k1_funct_1(C_56, '#skF_1'(A_57, B_58, C_56))=A_57 | ~v1_funct_1(C_56) | ~r2_hidden(A_57, k9_relat_1(C_56, B_58)) | ~v1_relat_1(C_56))), inference(resolution, [status(thm)], [c_112, c_12])).
% 1.92/1.22  tff(c_136, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_2', '#skF_5'))='#skF_4' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_131])).
% 1.92/1.22  tff(c_146, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_2', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_136])).
% 1.92/1.22  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_146])).
% 1.92/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  Inference rules
% 1.92/1.22  ----------------------
% 1.92/1.22  #Ref     : 0
% 1.92/1.22  #Sup     : 25
% 1.92/1.22  #Fact    : 0
% 1.92/1.22  #Define  : 0
% 1.92/1.22  #Split   : 1
% 1.92/1.22  #Chain   : 0
% 1.92/1.22  #Close   : 0
% 1.92/1.22  
% 1.92/1.22  Ordering : KBO
% 1.92/1.22  
% 1.92/1.22  Simplification rules
% 1.92/1.22  ----------------------
% 1.92/1.22  #Subsume      : 2
% 1.92/1.22  #Demod        : 5
% 1.92/1.22  #Tautology    : 8
% 1.92/1.22  #SimpNegUnit  : 1
% 1.92/1.22  #BackRed      : 1
% 1.92/1.22  
% 1.92/1.22  #Partial instantiations: 0
% 1.92/1.22  #Strategies tried      : 1
% 1.92/1.22  
% 1.92/1.22  Timing (in seconds)
% 1.92/1.22  ----------------------
% 1.92/1.22  Preprocessing        : 0.31
% 1.92/1.22  Parsing              : 0.16
% 1.92/1.22  CNF conversion       : 0.02
% 1.92/1.22  Main loop            : 0.15
% 1.92/1.22  Inferencing          : 0.06
% 1.92/1.22  Reduction            : 0.04
% 1.92/1.22  Demodulation         : 0.03
% 1.92/1.22  BG Simplification    : 0.01
% 1.92/1.22  Subsumption          : 0.03
% 1.92/1.22  Abstraction          : 0.01
% 1.92/1.22  MUC search           : 0.00
% 1.92/1.22  Cooper               : 0.00
% 1.92/1.22  Total                : 0.49
% 1.92/1.22  Index Insertion      : 0.00
% 1.92/1.22  Index Deletion       : 0.00
% 1.92/1.22  Index Matching       : 0.00
% 1.92/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
