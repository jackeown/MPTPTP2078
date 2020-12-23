%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:34 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   55 (  75 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   80 ( 150 expanded)
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

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_84,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_56,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_6,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_43,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_36,c_43])).

tff(c_49,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_46])).

tff(c_40,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70,plain,(
    ! [A_74,B_75,C_76] :
      ( k1_relset_1(A_74,B_75,C_76) = k1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_74,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_70])).

tff(c_79,plain,(
    ! [A_77,B_78,C_79] :
      ( m1_subset_1(k1_relset_1(A_77,B_78,C_79),k1_zfmisc_1(A_77))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_93,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_79])).

tff(c_98,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_93])).

tff(c_10,plain,(
    ! [A_10,C_46] :
      ( k1_funct_1(A_10,'#skF_4'(A_10,k2_relat_1(A_10),C_46)) = C_46
      | ~ r2_hidden(C_46,k2_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_119,plain,(
    ! [A_85,C_86] :
      ( r2_hidden('#skF_4'(A_85,k2_relat_1(A_85),C_86),k1_relat_1(A_85))
      | ~ r2_hidden(C_86,k2_relat_1(A_85))
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_175,plain,(
    ! [A_99,C_100,A_101] :
      ( r2_hidden('#skF_4'(A_99,k2_relat_1(A_99),C_100),A_101)
      | ~ m1_subset_1(k1_relat_1(A_99),k1_zfmisc_1(A_101))
      | ~ r2_hidden(C_100,k2_relat_1(A_99))
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_32,plain,(
    ! [E_60] :
      ( k1_funct_1('#skF_8',E_60) != '#skF_7'
      | ~ r2_hidden(E_60,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_191,plain,(
    ! [A_110,C_111] :
      ( k1_funct_1('#skF_8','#skF_4'(A_110,k2_relat_1(A_110),C_111)) != '#skF_7'
      | ~ m1_subset_1(k1_relat_1(A_110),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(C_111,k2_relat_1(A_110))
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(resolution,[status(thm)],[c_175,c_32])).

tff(c_194,plain,(
    ! [C_46] :
      ( C_46 != '#skF_7'
      | ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(C_46,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_46,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_191])).

tff(c_198,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_40,c_49,c_40,c_98,c_194])).

tff(c_55,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_59,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_34,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_61,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_34])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.25  
% 2.16/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.25  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.16/1.25  
% 2.16/1.25  %Foreground sorts:
% 2.16/1.25  
% 2.16/1.25  
% 2.16/1.25  %Background operators:
% 2.16/1.25  
% 2.16/1.25  
% 2.16/1.25  %Foreground operators:
% 2.16/1.25  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.16/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.16/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.16/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.16/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.16/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.16/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.16/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.16/1.25  tff('#skF_8', type, '#skF_8': $i).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.25  
% 2.16/1.26  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.16/1.26  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 2.16/1.26  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.16/1.26  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.16/1.26  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.16/1.26  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.16/1.26  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.16/1.26  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.16/1.26  tff(c_6, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.26  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.16/1.26  tff(c_43, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.26  tff(c_46, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_43])).
% 2.16/1.26  tff(c_49, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_46])).
% 2.16/1.26  tff(c_40, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.16/1.26  tff(c_70, plain, (![A_74, B_75, C_76]: (k1_relset_1(A_74, B_75, C_76)=k1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.26  tff(c_74, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_70])).
% 2.16/1.26  tff(c_79, plain, (![A_77, B_78, C_79]: (m1_subset_1(k1_relset_1(A_77, B_78, C_79), k1_zfmisc_1(A_77)) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.26  tff(c_93, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_74, c_79])).
% 2.16/1.26  tff(c_98, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_93])).
% 2.16/1.26  tff(c_10, plain, (![A_10, C_46]: (k1_funct_1(A_10, '#skF_4'(A_10, k2_relat_1(A_10), C_46))=C_46 | ~r2_hidden(C_46, k2_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.26  tff(c_119, plain, (![A_85, C_86]: (r2_hidden('#skF_4'(A_85, k2_relat_1(A_85), C_86), k1_relat_1(A_85)) | ~r2_hidden(C_86, k2_relat_1(A_85)) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.26  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.26  tff(c_175, plain, (![A_99, C_100, A_101]: (r2_hidden('#skF_4'(A_99, k2_relat_1(A_99), C_100), A_101) | ~m1_subset_1(k1_relat_1(A_99), k1_zfmisc_1(A_101)) | ~r2_hidden(C_100, k2_relat_1(A_99)) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(resolution, [status(thm)], [c_119, c_2])).
% 2.16/1.26  tff(c_32, plain, (![E_60]: (k1_funct_1('#skF_8', E_60)!='#skF_7' | ~r2_hidden(E_60, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.16/1.26  tff(c_191, plain, (![A_110, C_111]: (k1_funct_1('#skF_8', '#skF_4'(A_110, k2_relat_1(A_110), C_111))!='#skF_7' | ~m1_subset_1(k1_relat_1(A_110), k1_zfmisc_1('#skF_5')) | ~r2_hidden(C_111, k2_relat_1(A_110)) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(resolution, [status(thm)], [c_175, c_32])).
% 2.16/1.26  tff(c_194, plain, (![C_46]: (C_46!='#skF_7' | ~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~r2_hidden(C_46, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_46, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_191])).
% 2.16/1.26  tff(c_198, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_40, c_49, c_40, c_98, c_194])).
% 2.16/1.26  tff(c_55, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.16/1.26  tff(c_59, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_55])).
% 2.16/1.26  tff(c_34, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.16/1.26  tff(c_61, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_34])).
% 2.16/1.26  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_61])).
% 2.16/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.26  
% 2.16/1.26  Inference rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Ref     : 0
% 2.16/1.26  #Sup     : 34
% 2.16/1.26  #Fact    : 0
% 2.16/1.26  #Define  : 0
% 2.16/1.26  #Split   : 1
% 2.16/1.26  #Chain   : 0
% 2.16/1.26  #Close   : 0
% 2.16/1.26  
% 2.16/1.26  Ordering : KBO
% 2.16/1.26  
% 2.16/1.26  Simplification rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Subsume      : 2
% 2.16/1.26  #Demod        : 10
% 2.16/1.26  #Tautology    : 9
% 2.16/1.26  #SimpNegUnit  : 1
% 2.16/1.26  #BackRed      : 3
% 2.16/1.26  
% 2.16/1.26  #Partial instantiations: 0
% 2.16/1.26  #Strategies tried      : 1
% 2.16/1.26  
% 2.16/1.26  Timing (in seconds)
% 2.16/1.26  ----------------------
% 2.16/1.26  Preprocessing        : 0.31
% 2.16/1.26  Parsing              : 0.16
% 2.16/1.26  CNF conversion       : 0.02
% 2.16/1.26  Main loop            : 0.20
% 2.16/1.26  Inferencing          : 0.08
% 2.16/1.26  Reduction            : 0.05
% 2.16/1.26  Demodulation         : 0.04
% 2.16/1.27  BG Simplification    : 0.01
% 2.16/1.27  Subsumption          : 0.04
% 2.16/1.27  Abstraction          : 0.01
% 2.16/1.27  MUC search           : 0.00
% 2.16/1.27  Cooper               : 0.00
% 2.16/1.27  Total                : 0.53
% 2.16/1.27  Index Insertion      : 0.00
% 2.16/1.27  Index Deletion       : 0.00
% 2.16/1.27  Index Matching       : 0.00
% 2.16/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
