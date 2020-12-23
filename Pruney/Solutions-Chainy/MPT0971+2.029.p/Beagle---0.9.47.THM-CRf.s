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
% DateTime   : Thu Dec  3 10:11:33 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   51 (  69 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    5
%              Number of atoms          :   63 ( 127 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_47,plain,(
    ! [B_60,A_61] :
      ( v1_relat_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_47])).

tff(c_53,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_50])).

tff(c_44,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [A_6,B_29,D_44] :
      ( k1_funct_1(A_6,'#skF_4'(A_6,B_29,k9_relat_1(A_6,B_29),D_44)) = D_44
      | ~ r2_hidden(D_44,k9_relat_1(A_6,B_29))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    ! [A_73,B_74,D_75] :
      ( r2_hidden('#skF_4'(A_73,B_74,k9_relat_1(A_73,B_74),D_75),B_74)
      | ~ r2_hidden(D_75,k9_relat_1(A_73,B_74))
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [E_56] :
      ( k1_funct_1('#skF_8',E_56) != '#skF_7'
      | ~ r2_hidden(E_56,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_105,plain,(
    ! [A_85,D_86] :
      ( k1_funct_1('#skF_8','#skF_4'(A_85,'#skF_5',k9_relat_1(A_85,'#skF_5'),D_86)) != '#skF_7'
      | ~ r2_hidden(D_86,k9_relat_1(A_85,'#skF_5'))
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_85,c_36])).

tff(c_109,plain,(
    ! [D_44] :
      ( D_44 != '#skF_7'
      | ~ r2_hidden(D_44,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_44,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_105])).

tff(c_112,plain,(
    ~ r2_hidden('#skF_7',k9_relat_1('#skF_8','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_44,c_53,c_44,c_109])).

tff(c_54,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k7_relset_1(A_62,B_63,C_64,D_65) = k9_relat_1(C_64,D_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_57,plain,(
    ! [D_65] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_65) = k9_relat_1('#skF_8',D_65) ),
    inference(resolution,[status(thm)],[c_40,c_54])).

tff(c_67,plain,(
    ! [A_67,B_68,C_69] :
      ( k7_relset_1(A_67,B_68,C_69,A_67) = k2_relset_1(A_67,B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_69,plain,(
    k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_5') = k2_relset_1('#skF_5','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_71,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k9_relat_1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_69])).

tff(c_38,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_72,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_8','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_38])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:04:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.66  
% 2.55/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.66  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.55/1.66  
% 2.55/1.66  %Foreground sorts:
% 2.55/1.66  
% 2.55/1.66  
% 2.55/1.66  %Background operators:
% 2.55/1.66  
% 2.55/1.66  
% 2.55/1.66  %Foreground operators:
% 2.55/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.55/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.55/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.55/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.66  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.55/1.66  tff('#skF_7', type, '#skF_7': $i).
% 2.55/1.66  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.55/1.66  tff('#skF_5', type, '#skF_5': $i).
% 2.55/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.55/1.66  tff('#skF_6', type, '#skF_6': $i).
% 2.55/1.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.55/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.55/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.55/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.55/1.67  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.55/1.67  tff('#skF_8', type, '#skF_8': $i).
% 2.55/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.55/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.55/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.67  
% 2.60/1.68  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.60/1.68  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 2.60/1.68  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.60/1.68  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.60/1.68  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.60/1.68  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.60/1.68  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.60/1.68  tff(c_40, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.60/1.68  tff(c_47, plain, (![B_60, A_61]: (v1_relat_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.68  tff(c_50, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_47])).
% 2.60/1.68  tff(c_53, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_50])).
% 2.60/1.68  tff(c_44, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.60/1.68  tff(c_8, plain, (![A_6, B_29, D_44]: (k1_funct_1(A_6, '#skF_4'(A_6, B_29, k9_relat_1(A_6, B_29), D_44))=D_44 | ~r2_hidden(D_44, k9_relat_1(A_6, B_29)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.60/1.68  tff(c_85, plain, (![A_73, B_74, D_75]: (r2_hidden('#skF_4'(A_73, B_74, k9_relat_1(A_73, B_74), D_75), B_74) | ~r2_hidden(D_75, k9_relat_1(A_73, B_74)) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.60/1.68  tff(c_36, plain, (![E_56]: (k1_funct_1('#skF_8', E_56)!='#skF_7' | ~r2_hidden(E_56, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.60/1.68  tff(c_105, plain, (![A_85, D_86]: (k1_funct_1('#skF_8', '#skF_4'(A_85, '#skF_5', k9_relat_1(A_85, '#skF_5'), D_86))!='#skF_7' | ~r2_hidden(D_86, k9_relat_1(A_85, '#skF_5')) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(resolution, [status(thm)], [c_85, c_36])).
% 2.60/1.68  tff(c_109, plain, (![D_44]: (D_44!='#skF_7' | ~r2_hidden(D_44, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_44, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_105])).
% 2.60/1.68  tff(c_112, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_8', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_44, c_53, c_44, c_109])).
% 2.60/1.68  tff(c_54, plain, (![A_62, B_63, C_64, D_65]: (k7_relset_1(A_62, B_63, C_64, D_65)=k9_relat_1(C_64, D_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.60/1.68  tff(c_57, plain, (![D_65]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_65)=k9_relat_1('#skF_8', D_65))), inference(resolution, [status(thm)], [c_40, c_54])).
% 2.60/1.68  tff(c_67, plain, (![A_67, B_68, C_69]: (k7_relset_1(A_67, B_68, C_69, A_67)=k2_relset_1(A_67, B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.60/1.68  tff(c_69, plain, (k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_5')=k2_relset_1('#skF_5', '#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_40, c_67])).
% 2.60/1.68  tff(c_71, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k9_relat_1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_69])).
% 2.60/1.68  tff(c_38, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.60/1.68  tff(c_72, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_8', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_38])).
% 2.60/1.68  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_72])).
% 2.60/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.68  
% 2.60/1.68  Inference rules
% 2.60/1.68  ----------------------
% 2.60/1.68  #Ref     : 0
% 2.60/1.68  #Sup     : 15
% 2.60/1.68  #Fact    : 0
% 2.60/1.68  #Define  : 0
% 2.60/1.68  #Split   : 0
% 2.60/1.68  #Chain   : 0
% 2.60/1.68  #Close   : 0
% 2.60/1.68  
% 2.60/1.68  Ordering : KBO
% 2.60/1.68  
% 2.60/1.68  Simplification rules
% 2.60/1.68  ----------------------
% 2.60/1.68  #Subsume      : 0
% 2.60/1.68  #Demod        : 7
% 2.60/1.68  #Tautology    : 8
% 2.60/1.68  #SimpNegUnit  : 1
% 2.60/1.68  #BackRed      : 2
% 2.60/1.68  
% 2.60/1.68  #Partial instantiations: 0
% 2.60/1.68  #Strategies tried      : 1
% 2.60/1.68  
% 2.60/1.68  Timing (in seconds)
% 2.60/1.68  ----------------------
% 2.60/1.69  Preprocessing        : 0.51
% 2.60/1.69  Parsing              : 0.25
% 2.60/1.69  CNF conversion       : 0.05
% 2.60/1.69  Main loop            : 0.22
% 2.60/1.69  Inferencing          : 0.08
% 2.60/1.69  Reduction            : 0.07
% 2.60/1.69  Demodulation         : 0.05
% 2.60/1.69  BG Simplification    : 0.02
% 2.60/1.69  Subsumption          : 0.03
% 2.60/1.69  Abstraction          : 0.02
% 2.60/1.69  MUC search           : 0.00
% 2.60/1.69  Cooper               : 0.00
% 2.60/1.69  Total                : 0.78
% 2.60/1.69  Index Insertion      : 0.00
% 2.60/1.69  Index Deletion       : 0.00
% 2.60/1.69  Index Matching       : 0.00
% 2.60/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
