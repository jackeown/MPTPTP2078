%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:01 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   51 (  66 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   65 ( 123 expanded)
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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

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

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_51,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_51])).

tff(c_44,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_3,B_26,D_41] :
      ( k1_funct_1(A_3,'#skF_4'(A_3,B_26,k9_relat_1(A_3,B_26),D_41)) = D_41
      | ~ r2_hidden(D_41,k9_relat_1(A_3,B_26))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_98,plain,(
    ! [A_77,B_78,D_79] :
      ( r2_hidden('#skF_4'(A_77,B_78,k9_relat_1(A_77,B_78),D_79),B_78)
      | ~ r2_hidden(D_79,k9_relat_1(A_77,B_78))
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_119,plain,(
    ! [A_86,B_87,D_88] :
      ( m1_subset_1('#skF_4'(A_86,B_87,k9_relat_1(A_86,B_87),D_88),B_87)
      | ~ r2_hidden(D_88,k9_relat_1(A_86,B_87))
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_36,plain,(
    ! [E_56] :
      ( k1_funct_1('#skF_8',E_56) != '#skF_5'
      | ~ m1_subset_1(E_56,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_148,plain,(
    ! [A_95,D_96] :
      ( k1_funct_1('#skF_8','#skF_4'(A_95,'#skF_6',k9_relat_1(A_95,'#skF_6'),D_96)) != '#skF_5'
      | ~ r2_hidden(D_96,k9_relat_1(A_95,'#skF_6'))
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_119,c_36])).

tff(c_152,plain,(
    ! [D_41] :
      ( D_41 != '#skF_5'
      | ~ r2_hidden(D_41,k9_relat_1('#skF_8','#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_41,k9_relat_1('#skF_8','#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_148])).

tff(c_156,plain,(
    ~ r2_hidden('#skF_5',k9_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44,c_55,c_44,c_152])).

tff(c_56,plain,(
    ! [A_63,B_64,C_65,D_66] :
      ( k7_relset_1(A_63,B_64,C_65,D_66) = k9_relat_1(C_65,D_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_59,plain,(
    ! [D_66] : k7_relset_1('#skF_6','#skF_7','#skF_8',D_66) = k9_relat_1('#skF_8',D_66) ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_69,plain,(
    ! [A_68,B_69,C_70] :
      ( k7_relset_1(A_68,B_69,C_70,A_68) = k2_relset_1(A_68,B_69,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_71,plain,(
    k7_relset_1('#skF_6','#skF_7','#skF_8','#skF_6') = k2_relset_1('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_69])).

tff(c_73,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k9_relat_1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_71])).

tff(c_38,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_75,plain,(
    r2_hidden('#skF_5',k9_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_38])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.26  
% 2.33/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.26  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.33/1.26  
% 2.33/1.26  %Foreground sorts:
% 2.33/1.26  
% 2.33/1.26  
% 2.33/1.26  %Background operators:
% 2.33/1.26  
% 2.33/1.26  
% 2.33/1.26  %Foreground operators:
% 2.33/1.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.33/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.33/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.33/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.26  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.33/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.33/1.26  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.33/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.33/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.33/1.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.33/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.33/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.33/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.33/1.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.33/1.26  tff('#skF_8', type, '#skF_8': $i).
% 2.33/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.33/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.33/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.26  
% 2.41/1.27  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 2.41/1.27  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.41/1.27  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.41/1.27  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.41/1.27  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.41/1.27  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.41/1.27  tff(c_40, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.27  tff(c_51, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.27  tff(c_55, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_51])).
% 2.41/1.27  tff(c_44, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.27  tff(c_6, plain, (![A_3, B_26, D_41]: (k1_funct_1(A_3, '#skF_4'(A_3, B_26, k9_relat_1(A_3, B_26), D_41))=D_41 | ~r2_hidden(D_41, k9_relat_1(A_3, B_26)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.41/1.27  tff(c_98, plain, (![A_77, B_78, D_79]: (r2_hidden('#skF_4'(A_77, B_78, k9_relat_1(A_77, B_78), D_79), B_78) | ~r2_hidden(D_79, k9_relat_1(A_77, B_78)) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.41/1.27  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.41/1.27  tff(c_119, plain, (![A_86, B_87, D_88]: (m1_subset_1('#skF_4'(A_86, B_87, k9_relat_1(A_86, B_87), D_88), B_87) | ~r2_hidden(D_88, k9_relat_1(A_86, B_87)) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(resolution, [status(thm)], [c_98, c_2])).
% 2.41/1.27  tff(c_36, plain, (![E_56]: (k1_funct_1('#skF_8', E_56)!='#skF_5' | ~m1_subset_1(E_56, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.27  tff(c_148, plain, (![A_95, D_96]: (k1_funct_1('#skF_8', '#skF_4'(A_95, '#skF_6', k9_relat_1(A_95, '#skF_6'), D_96))!='#skF_5' | ~r2_hidden(D_96, k9_relat_1(A_95, '#skF_6')) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_119, c_36])).
% 2.41/1.27  tff(c_152, plain, (![D_41]: (D_41!='#skF_5' | ~r2_hidden(D_41, k9_relat_1('#skF_8', '#skF_6')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_41, k9_relat_1('#skF_8', '#skF_6')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_148])).
% 2.41/1.27  tff(c_156, plain, (~r2_hidden('#skF_5', k9_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44, c_55, c_44, c_152])).
% 2.41/1.27  tff(c_56, plain, (![A_63, B_64, C_65, D_66]: (k7_relset_1(A_63, B_64, C_65, D_66)=k9_relat_1(C_65, D_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.27  tff(c_59, plain, (![D_66]: (k7_relset_1('#skF_6', '#skF_7', '#skF_8', D_66)=k9_relat_1('#skF_8', D_66))), inference(resolution, [status(thm)], [c_40, c_56])).
% 2.41/1.27  tff(c_69, plain, (![A_68, B_69, C_70]: (k7_relset_1(A_68, B_69, C_70, A_68)=k2_relset_1(A_68, B_69, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.41/1.27  tff(c_71, plain, (k7_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_6')=k2_relset_1('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_40, c_69])).
% 2.41/1.27  tff(c_73, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k9_relat_1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_71])).
% 2.41/1.27  tff(c_38, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.27  tff(c_75, plain, (r2_hidden('#skF_5', k9_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_38])).
% 2.41/1.27  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_75])).
% 2.41/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.27  
% 2.41/1.27  Inference rules
% 2.41/1.27  ----------------------
% 2.41/1.27  #Ref     : 0
% 2.41/1.27  #Sup     : 25
% 2.41/1.27  #Fact    : 0
% 2.41/1.27  #Define  : 0
% 2.41/1.27  #Split   : 0
% 2.41/1.27  #Chain   : 0
% 2.41/1.27  #Close   : 0
% 2.41/1.27  
% 2.41/1.27  Ordering : KBO
% 2.41/1.27  
% 2.41/1.27  Simplification rules
% 2.41/1.27  ----------------------
% 2.41/1.27  #Subsume      : 0
% 2.41/1.27  #Demod        : 8
% 2.41/1.27  #Tautology    : 9
% 2.41/1.27  #SimpNegUnit  : 1
% 2.41/1.27  #BackRed      : 3
% 2.41/1.27  
% 2.41/1.27  #Partial instantiations: 0
% 2.41/1.27  #Strategies tried      : 1
% 2.41/1.27  
% 2.41/1.27  Timing (in seconds)
% 2.41/1.27  ----------------------
% 2.41/1.27  Preprocessing        : 0.34
% 2.41/1.27  Parsing              : 0.17
% 2.41/1.27  CNF conversion       : 0.03
% 2.41/1.27  Main loop            : 0.17
% 2.41/1.27  Inferencing          : 0.06
% 2.41/1.27  Reduction            : 0.05
% 2.41/1.27  Demodulation         : 0.04
% 2.41/1.27  BG Simplification    : 0.02
% 2.41/1.27  Subsumption          : 0.03
% 2.41/1.28  Abstraction          : 0.02
% 2.41/1.28  MUC search           : 0.00
% 2.41/1.28  Cooper               : 0.00
% 2.41/1.28  Total                : 0.54
% 2.41/1.28  Index Insertion      : 0.00
% 2.41/1.28  Index Deletion       : 0.00
% 2.41/1.28  Index Matching       : 0.00
% 2.41/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
