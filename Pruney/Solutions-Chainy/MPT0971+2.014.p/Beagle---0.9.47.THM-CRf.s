%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:31 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   52 (  69 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   74 ( 138 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_47,axiom,(
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
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_40])).

tff(c_38,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_65,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_69,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_24,plain,(
    ! [A_48,B_49,C_50] :
      ( m1_subset_1(k1_relset_1(A_48,B_49,C_50),k1_zfmisc_1(A_48))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_89,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_24])).

tff(c_93,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_89])).

tff(c_6,plain,(
    ! [A_5,C_41] :
      ( k1_funct_1(A_5,'#skF_4'(A_5,k2_relat_1(A_5),C_41)) = C_41
      | ~ r2_hidden(C_41,k2_relat_1(A_5))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_99,plain,(
    ! [A_79,C_80] :
      ( r2_hidden('#skF_4'(A_79,k2_relat_1(A_79),C_80),k1_relat_1(A_79))
      | ~ r2_hidden(C_80,k2_relat_1(A_79))
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_161,plain,(
    ! [A_97,C_98,A_99] :
      ( r2_hidden('#skF_4'(A_97,k2_relat_1(A_97),C_98),A_99)
      | ~ m1_subset_1(k1_relat_1(A_97),k1_zfmisc_1(A_99))
      | ~ r2_hidden(C_98,k2_relat_1(A_97))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_30,plain,(
    ! [E_58] :
      ( k1_funct_1('#skF_8',E_58) != '#skF_7'
      | ~ r2_hidden(E_58,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_172,plain,(
    ! [A_104,C_105] :
      ( k1_funct_1('#skF_8','#skF_4'(A_104,k2_relat_1(A_104),C_105)) != '#skF_7'
      | ~ m1_subset_1(k1_relat_1(A_104),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(C_105,k2_relat_1(A_104))
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_161,c_30])).

tff(c_175,plain,(
    ! [C_41] :
      ( C_41 != '#skF_7'
      | ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(C_41,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_41,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_172])).

tff(c_178,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_44,c_38,c_93,c_175])).

tff(c_50,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_32,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_56,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.25  
% 2.28/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.25  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.28/1.25  
% 2.28/1.25  %Foreground sorts:
% 2.28/1.25  
% 2.28/1.25  
% 2.28/1.25  %Background operators:
% 2.28/1.25  
% 2.28/1.25  
% 2.28/1.25  %Foreground operators:
% 2.28/1.25  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.28/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.28/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.28/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.28/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.28/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.28/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.28/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.28/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.28/1.25  tff('#skF_8', type, '#skF_8': $i).
% 2.28/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.28/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.28/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.25  
% 2.28/1.26  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 2.28/1.26  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.28/1.26  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.28/1.26  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.28/1.26  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.28/1.26  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.28/1.26  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.28/1.26  tff(c_34, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.28/1.26  tff(c_40, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.28/1.26  tff(c_44, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_40])).
% 2.28/1.26  tff(c_38, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.28/1.26  tff(c_65, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.28/1.26  tff(c_69, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_65])).
% 2.28/1.26  tff(c_24, plain, (![A_48, B_49, C_50]: (m1_subset_1(k1_relset_1(A_48, B_49, C_50), k1_zfmisc_1(A_48)) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.28/1.26  tff(c_89, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_69, c_24])).
% 2.28/1.26  tff(c_93, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_89])).
% 2.28/1.26  tff(c_6, plain, (![A_5, C_41]: (k1_funct_1(A_5, '#skF_4'(A_5, k2_relat_1(A_5), C_41))=C_41 | ~r2_hidden(C_41, k2_relat_1(A_5)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.26  tff(c_99, plain, (![A_79, C_80]: (r2_hidden('#skF_4'(A_79, k2_relat_1(A_79), C_80), k1_relat_1(A_79)) | ~r2_hidden(C_80, k2_relat_1(A_79)) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.26  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.28/1.26  tff(c_161, plain, (![A_97, C_98, A_99]: (r2_hidden('#skF_4'(A_97, k2_relat_1(A_97), C_98), A_99) | ~m1_subset_1(k1_relat_1(A_97), k1_zfmisc_1(A_99)) | ~r2_hidden(C_98, k2_relat_1(A_97)) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_99, c_2])).
% 2.28/1.26  tff(c_30, plain, (![E_58]: (k1_funct_1('#skF_8', E_58)!='#skF_7' | ~r2_hidden(E_58, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.28/1.26  tff(c_172, plain, (![A_104, C_105]: (k1_funct_1('#skF_8', '#skF_4'(A_104, k2_relat_1(A_104), C_105))!='#skF_7' | ~m1_subset_1(k1_relat_1(A_104), k1_zfmisc_1('#skF_5')) | ~r2_hidden(C_105, k2_relat_1(A_104)) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_161, c_30])).
% 2.28/1.26  tff(c_175, plain, (![C_41]: (C_41!='#skF_7' | ~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~r2_hidden(C_41, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_41, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_172])).
% 2.28/1.26  tff(c_178, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_44, c_38, c_93, c_175])).
% 2.28/1.26  tff(c_50, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.26  tff(c_54, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_50])).
% 2.28/1.26  tff(c_32, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.28/1.26  tff(c_56, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_32])).
% 2.28/1.26  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_56])).
% 2.28/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.26  
% 2.28/1.26  Inference rules
% 2.28/1.26  ----------------------
% 2.28/1.26  #Ref     : 0
% 2.28/1.26  #Sup     : 31
% 2.28/1.26  #Fact    : 0
% 2.28/1.26  #Define  : 0
% 2.28/1.26  #Split   : 0
% 2.28/1.26  #Chain   : 0
% 2.28/1.26  #Close   : 0
% 2.28/1.26  
% 2.28/1.26  Ordering : KBO
% 2.28/1.26  
% 2.28/1.26  Simplification rules
% 2.28/1.26  ----------------------
% 2.28/1.26  #Subsume      : 1
% 2.28/1.26  #Demod        : 8
% 2.28/1.26  #Tautology    : 9
% 2.28/1.26  #SimpNegUnit  : 1
% 2.28/1.26  #BackRed      : 3
% 2.28/1.26  
% 2.28/1.26  #Partial instantiations: 0
% 2.28/1.26  #Strategies tried      : 1
% 2.28/1.26  
% 2.28/1.26  Timing (in seconds)
% 2.28/1.26  ----------------------
% 2.40/1.27  Preprocessing        : 0.31
% 2.40/1.27  Parsing              : 0.16
% 2.40/1.27  CNF conversion       : 0.02
% 2.40/1.27  Main loop            : 0.18
% 2.40/1.27  Inferencing          : 0.07
% 2.40/1.27  Reduction            : 0.05
% 2.40/1.27  Demodulation         : 0.04
% 2.40/1.27  BG Simplification    : 0.02
% 2.40/1.27  Subsumption          : 0.03
% 2.40/1.27  Abstraction          : 0.01
% 2.40/1.27  MUC search           : 0.00
% 2.40/1.27  Cooper               : 0.00
% 2.40/1.27  Total                : 0.52
% 2.40/1.27  Index Insertion      : 0.00
% 2.40/1.27  Index Deletion       : 0.00
% 2.40/1.27  Index Matching       : 0.00
% 2.40/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
