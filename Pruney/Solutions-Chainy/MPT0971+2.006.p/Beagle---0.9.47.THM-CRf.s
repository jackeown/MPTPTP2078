%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:30 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   57 (  82 expanded)
%              Number of leaves         :   32 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   78 ( 159 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_46])).

tff(c_44,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [A_6,C_42] :
      ( k1_funct_1(A_6,'#skF_4'(A_6,k2_relat_1(A_6),C_42)) = C_42
      | ~ r2_hidden(C_42,k2_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_122,plain,(
    ! [A_86,C_87] :
      ( r2_hidden('#skF_4'(A_86,k2_relat_1(A_86),C_87),k1_relat_1(A_86))
      | ~ r2_hidden(C_87,k2_relat_1(A_86))
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_51,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_55,plain,(
    v4_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_51])).

tff(c_61,plain,(
    ! [B_67,A_68] :
      ( k7_relat_1(B_67,A_68) = B_67
      | ~ v4_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,
    ( k7_relat_1('#skF_8','#skF_5') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_55,c_61])).

tff(c_67,plain,(
    k7_relat_1('#skF_8','#skF_5') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64])).

tff(c_72,plain,(
    ! [A_69,B_70,C_71] :
      ( r2_hidden(A_69,B_70)
      | ~ r2_hidden(A_69,k1_relat_1(k7_relat_1(C_71,B_70)))
      | ~ v1_relat_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    ! [A_69] :
      ( r2_hidden(A_69,'#skF_5')
      | ~ r2_hidden(A_69,k1_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_72])).

tff(c_77,plain,(
    ! [A_69] :
      ( r2_hidden(A_69,'#skF_5')
      | ~ r2_hidden(A_69,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_75])).

tff(c_130,plain,(
    ! [C_87] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_87),'#skF_5')
      | ~ r2_hidden(C_87,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_122,c_77])).

tff(c_140,plain,(
    ! [C_88] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_88),'#skF_5')
      | ~ r2_hidden(C_88,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_130])).

tff(c_36,plain,(
    ! [E_56] :
      ( k1_funct_1('#skF_8',E_56) != '#skF_7'
      | ~ r2_hidden(E_56,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_145,plain,(
    ! [C_89] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_89)) != '#skF_7'
      | ~ r2_hidden(C_89,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_140,c_36])).

tff(c_149,plain,(
    ! [C_42] :
      ( C_42 != '#skF_7'
      | ~ r2_hidden(C_42,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_42,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_145])).

tff(c_173,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_149])).

tff(c_79,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_83,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_79])).

tff(c_38,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_84,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_38])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:04:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.23  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 1.89/1.23  
% 1.89/1.23  %Foreground sorts:
% 1.89/1.23  
% 1.89/1.23  
% 1.89/1.23  %Background operators:
% 1.89/1.23  
% 1.89/1.23  
% 1.89/1.23  %Foreground operators:
% 1.89/1.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.89/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.89/1.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.89/1.23  tff('#skF_7', type, '#skF_7': $i).
% 1.89/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.89/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.89/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.89/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.89/1.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.89/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.89/1.23  tff('#skF_8', type, '#skF_8': $i).
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.89/1.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.89/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.23  
% 2.09/1.24  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.09/1.24  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.09/1.24  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.09/1.24  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.09/1.24  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.09/1.24  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 2.09/1.24  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.09/1.24  tff(c_40, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.09/1.24  tff(c_46, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.24  tff(c_50, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_46])).
% 2.09/1.24  tff(c_44, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.09/1.24  tff(c_12, plain, (![A_6, C_42]: (k1_funct_1(A_6, '#skF_4'(A_6, k2_relat_1(A_6), C_42))=C_42 | ~r2_hidden(C_42, k2_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.24  tff(c_122, plain, (![A_86, C_87]: (r2_hidden('#skF_4'(A_86, k2_relat_1(A_86), C_87), k1_relat_1(A_86)) | ~r2_hidden(C_87, k2_relat_1(A_86)) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.24  tff(c_51, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.24  tff(c_55, plain, (v4_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_51])).
% 2.09/1.24  tff(c_61, plain, (![B_67, A_68]: (k7_relat_1(B_67, A_68)=B_67 | ~v4_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.24  tff(c_64, plain, (k7_relat_1('#skF_8', '#skF_5')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_55, c_61])).
% 2.09/1.24  tff(c_67, plain, (k7_relat_1('#skF_8', '#skF_5')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_64])).
% 2.09/1.24  tff(c_72, plain, (![A_69, B_70, C_71]: (r2_hidden(A_69, B_70) | ~r2_hidden(A_69, k1_relat_1(k7_relat_1(C_71, B_70))) | ~v1_relat_1(C_71))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.24  tff(c_75, plain, (![A_69]: (r2_hidden(A_69, '#skF_5') | ~r2_hidden(A_69, k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_72])).
% 2.09/1.24  tff(c_77, plain, (![A_69]: (r2_hidden(A_69, '#skF_5') | ~r2_hidden(A_69, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_75])).
% 2.09/1.24  tff(c_130, plain, (![C_87]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_87), '#skF_5') | ~r2_hidden(C_87, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_122, c_77])).
% 2.09/1.24  tff(c_140, plain, (![C_88]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_88), '#skF_5') | ~r2_hidden(C_88, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_130])).
% 2.09/1.24  tff(c_36, plain, (![E_56]: (k1_funct_1('#skF_8', E_56)!='#skF_7' | ~r2_hidden(E_56, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.09/1.24  tff(c_145, plain, (![C_89]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_89))!='#skF_7' | ~r2_hidden(C_89, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_140, c_36])).
% 2.09/1.24  tff(c_149, plain, (![C_42]: (C_42!='#skF_7' | ~r2_hidden(C_42, k2_relat_1('#skF_8')) | ~r2_hidden(C_42, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_145])).
% 2.09/1.24  tff(c_173, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_149])).
% 2.09/1.24  tff(c_79, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.09/1.24  tff(c_83, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_79])).
% 2.09/1.24  tff(c_38, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.09/1.24  tff(c_84, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_38])).
% 2.09/1.24  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_84])).
% 2.09/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.24  
% 2.09/1.24  Inference rules
% 2.09/1.24  ----------------------
% 2.09/1.24  #Ref     : 0
% 2.09/1.24  #Sup     : 26
% 2.09/1.24  #Fact    : 0
% 2.09/1.24  #Define  : 0
% 2.09/1.24  #Split   : 0
% 2.09/1.24  #Chain   : 0
% 2.09/1.24  #Close   : 0
% 2.09/1.24  
% 2.09/1.24  Ordering : KBO
% 2.09/1.24  
% 2.09/1.24  Simplification rules
% 2.09/1.24  ----------------------
% 2.09/1.24  #Subsume      : 0
% 2.09/1.24  #Demod        : 9
% 2.09/1.24  #Tautology    : 11
% 2.09/1.24  #SimpNegUnit  : 1
% 2.09/1.24  #BackRed      : 2
% 2.09/1.24  
% 2.09/1.24  #Partial instantiations: 0
% 2.09/1.24  #Strategies tried      : 1
% 2.09/1.24  
% 2.09/1.24  Timing (in seconds)
% 2.09/1.24  ----------------------
% 2.09/1.24  Preprocessing        : 0.31
% 2.09/1.24  Parsing              : 0.16
% 2.09/1.24  CNF conversion       : 0.02
% 2.09/1.24  Main loop            : 0.16
% 2.09/1.24  Inferencing          : 0.06
% 2.09/1.24  Reduction            : 0.05
% 2.09/1.24  Demodulation         : 0.03
% 2.09/1.24  BG Simplification    : 0.01
% 2.09/1.24  Subsumption          : 0.03
% 2.09/1.24  Abstraction          : 0.01
% 2.09/1.24  MUC search           : 0.00
% 2.09/1.24  Cooper               : 0.00
% 2.09/1.24  Total                : 0.50
% 2.09/1.25  Index Insertion      : 0.00
% 2.09/1.25  Index Deletion       : 0.00
% 2.09/1.25  Index Matching       : 0.00
% 2.09/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
