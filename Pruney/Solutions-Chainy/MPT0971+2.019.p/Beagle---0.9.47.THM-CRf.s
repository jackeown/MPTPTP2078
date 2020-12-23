%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:32 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 118 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 273 expanded)
%              Number of equality atoms :   11 (  35 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_57,plain,(
    ! [B_66,A_67] :
      ( v1_relat_1(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_44,c_57])).

tff(c_63,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_60])).

tff(c_72,plain,(
    ! [C_72,A_73,B_74] :
      ( v4_relat_1(C_72,A_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_76,plain,(
    v4_relat_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18,plain,(
    ! [A_13,C_49] :
      ( k1_funct_1(A_13,'#skF_5'(A_13,k2_relat_1(A_13),C_49)) = C_49
      | ~ r2_hidden(C_49,k2_relat_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_167,plain,(
    ! [A_104,C_105] :
      ( r2_hidden('#skF_5'(A_104,k2_relat_1(A_104),C_105),k1_relat_1(A_104))
      | ~ r2_hidden(C_105,k2_relat_1(A_104))
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_259,plain,(
    ! [A_130,C_131,B_132] :
      ( r2_hidden('#skF_5'(A_130,k2_relat_1(A_130),C_131),B_132)
      | ~ r1_tarski(k1_relat_1(A_130),B_132)
      | ~ r2_hidden(C_131,k2_relat_1(A_130))
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(resolution,[status(thm)],[c_167,c_2])).

tff(c_40,plain,(
    ! [E_60] :
      ( k1_funct_1('#skF_9',E_60) != '#skF_8'
      | ~ r2_hidden(E_60,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_301,plain,(
    ! [A_135,C_136] :
      ( k1_funct_1('#skF_9','#skF_5'(A_135,k2_relat_1(A_135),C_136)) != '#skF_8'
      | ~ r1_tarski(k1_relat_1(A_135),'#skF_6')
      | ~ r2_hidden(C_136,k2_relat_1(A_135))
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(resolution,[status(thm)],[c_259,c_40])).

tff(c_305,plain,(
    ! [C_49] :
      ( C_49 != '#skF_8'
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_6')
      | ~ r2_hidden(C_49,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_49,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_301])).

tff(c_307,plain,(
    ! [C_49] :
      ( C_49 != '#skF_8'
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_6')
      | ~ r2_hidden(C_49,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_63,c_48,c_305])).

tff(c_308,plain,(
    ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_312,plain,
    ( ~ v4_relat_1('#skF_9','#skF_6')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_12,c_308])).

tff(c_316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_76,c_312])).

tff(c_331,plain,(
    ~ r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_122,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_126,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_122])).

tff(c_42,plain,(
    r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_128,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_42])).

tff(c_333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.44  
% 2.73/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.73/1.44  
% 2.73/1.44  %Foreground sorts:
% 2.73/1.44  
% 2.73/1.44  
% 2.73/1.44  %Background operators:
% 2.73/1.44  
% 2.73/1.44  
% 2.73/1.44  %Foreground operators:
% 2.73/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.73/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.73/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.73/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.44  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.73/1.44  tff('#skF_9', type, '#skF_9': $i).
% 2.73/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.73/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.44  tff('#skF_8', type, '#skF_8': $i).
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.73/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.73/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.44  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.73/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.44  
% 2.73/1.45  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.73/1.45  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 2.73/1.45  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.73/1.45  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.73/1.45  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.73/1.45  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.73/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.73/1.45  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.73/1.45  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.73/1.45  tff(c_44, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.73/1.45  tff(c_57, plain, (![B_66, A_67]: (v1_relat_1(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.73/1.45  tff(c_60, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_44, c_57])).
% 2.73/1.45  tff(c_63, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_60])).
% 2.73/1.45  tff(c_72, plain, (![C_72, A_73, B_74]: (v4_relat_1(C_72, A_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.73/1.45  tff(c_76, plain, (v4_relat_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_44, c_72])).
% 2.73/1.45  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.73/1.45  tff(c_48, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.73/1.45  tff(c_18, plain, (![A_13, C_49]: (k1_funct_1(A_13, '#skF_5'(A_13, k2_relat_1(A_13), C_49))=C_49 | ~r2_hidden(C_49, k2_relat_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.73/1.45  tff(c_167, plain, (![A_104, C_105]: (r2_hidden('#skF_5'(A_104, k2_relat_1(A_104), C_105), k1_relat_1(A_104)) | ~r2_hidden(C_105, k2_relat_1(A_104)) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.73/1.45  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.73/1.45  tff(c_259, plain, (![A_130, C_131, B_132]: (r2_hidden('#skF_5'(A_130, k2_relat_1(A_130), C_131), B_132) | ~r1_tarski(k1_relat_1(A_130), B_132) | ~r2_hidden(C_131, k2_relat_1(A_130)) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(resolution, [status(thm)], [c_167, c_2])).
% 2.73/1.45  tff(c_40, plain, (![E_60]: (k1_funct_1('#skF_9', E_60)!='#skF_8' | ~r2_hidden(E_60, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.73/1.45  tff(c_301, plain, (![A_135, C_136]: (k1_funct_1('#skF_9', '#skF_5'(A_135, k2_relat_1(A_135), C_136))!='#skF_8' | ~r1_tarski(k1_relat_1(A_135), '#skF_6') | ~r2_hidden(C_136, k2_relat_1(A_135)) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(resolution, [status(thm)], [c_259, c_40])).
% 2.73/1.45  tff(c_305, plain, (![C_49]: (C_49!='#skF_8' | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_6') | ~r2_hidden(C_49, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_49, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_301])).
% 2.73/1.45  tff(c_307, plain, (![C_49]: (C_49!='#skF_8' | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_6') | ~r2_hidden(C_49, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_63, c_48, c_305])).
% 2.73/1.45  tff(c_308, plain, (~r1_tarski(k1_relat_1('#skF_9'), '#skF_6')), inference(splitLeft, [status(thm)], [c_307])).
% 2.73/1.45  tff(c_312, plain, (~v4_relat_1('#skF_9', '#skF_6') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_12, c_308])).
% 2.73/1.45  tff(c_316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_76, c_312])).
% 2.73/1.45  tff(c_331, plain, (~r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_307])).
% 2.73/1.45  tff(c_122, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.73/1.45  tff(c_126, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_44, c_122])).
% 2.73/1.45  tff(c_42, plain, (r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.73/1.45  tff(c_128, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_42])).
% 2.73/1.45  tff(c_333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_331, c_128])).
% 2.73/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.45  
% 2.73/1.45  Inference rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Ref     : 0
% 2.73/1.45  #Sup     : 59
% 2.73/1.45  #Fact    : 0
% 2.73/1.45  #Define  : 0
% 2.73/1.45  #Split   : 1
% 2.73/1.45  #Chain   : 0
% 2.73/1.45  #Close   : 0
% 2.73/1.45  
% 2.73/1.45  Ordering : KBO
% 2.73/1.45  
% 2.73/1.45  Simplification rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Subsume      : 5
% 2.73/1.45  #Demod        : 13
% 2.73/1.45  #Tautology    : 12
% 2.73/1.45  #SimpNegUnit  : 1
% 2.73/1.45  #BackRed      : 3
% 2.73/1.45  
% 2.73/1.45  #Partial instantiations: 0
% 2.73/1.45  #Strategies tried      : 1
% 2.73/1.45  
% 2.73/1.45  Timing (in seconds)
% 2.73/1.45  ----------------------
% 2.73/1.46  Preprocessing        : 0.36
% 2.73/1.46  Parsing              : 0.19
% 2.73/1.46  CNF conversion       : 0.03
% 2.73/1.46  Main loop            : 0.29
% 2.73/1.46  Inferencing          : 0.11
% 2.73/1.46  Reduction            : 0.08
% 2.73/1.46  Demodulation         : 0.06
% 2.73/1.46  BG Simplification    : 0.02
% 2.73/1.46  Subsumption          : 0.06
% 2.73/1.46  Abstraction          : 0.02
% 2.73/1.46  MUC search           : 0.00
% 2.73/1.46  Cooper               : 0.00
% 2.73/1.46  Total                : 0.69
% 2.73/1.46  Index Insertion      : 0.00
% 2.73/1.46  Index Deletion       : 0.00
% 2.73/1.46  Index Matching       : 0.00
% 2.73/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
