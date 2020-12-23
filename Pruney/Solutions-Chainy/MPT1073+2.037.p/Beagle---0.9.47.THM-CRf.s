%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:03 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   54 (  71 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 ( 135 expanded)
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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
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

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_40])).

tff(c_38,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_4,C_40] :
      ( k1_funct_1(A_4,'#skF_4'(A_4,k2_relat_1(A_4),C_40)) = C_40
      | ~ r2_hidden(C_40,k2_relat_1(A_4))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_121,plain,(
    ! [A_88,C_89] :
      ( r2_hidden('#skF_4'(A_88,k2_relat_1(A_88),C_89),k1_relat_1(A_88))
      | ~ r2_hidden(C_89,k2_relat_1(A_88))
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_60])).

tff(c_69,plain,(
    ! [A_72,B_73,C_74] :
      ( m1_subset_1(k1_relset_1(A_72,B_73,C_74),k1_zfmisc_1(A_72))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_86,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_69])).

tff(c_92,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_86])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_6')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_125,plain,(
    ! [C_89] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_89),'#skF_6')
      | ~ r2_hidden(C_89,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_121,c_96])).

tff(c_129,plain,(
    ! [C_90] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_90),'#skF_6')
      | ~ r2_hidden(C_90,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_125])).

tff(c_30,plain,(
    ! [E_57] :
      ( k1_funct_1('#skF_8',E_57) != '#skF_5'
      | ~ m1_subset_1(E_57,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_134,plain,(
    ! [C_91] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_91)) != '#skF_5'
      | ~ r2_hidden(C_91,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_129,c_30])).

tff(c_138,plain,(
    ! [C_40] :
      ( C_40 != '#skF_5'
      | ~ r2_hidden(C_40,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_40,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_134])).

tff(c_141,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_138])).

tff(c_50,plain,(
    ! [A_66,B_67,C_68] :
      ( k2_relset_1(A_66,B_67,C_68) = k2_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_32,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_55,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:22:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.24  
% 1.88/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.25  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 1.88/1.25  
% 1.88/1.25  %Foreground sorts:
% 1.88/1.25  
% 1.88/1.25  
% 1.88/1.25  %Background operators:
% 1.88/1.25  
% 1.88/1.25  
% 1.88/1.25  %Foreground operators:
% 1.88/1.25  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.88/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.88/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.88/1.25  tff('#skF_7', type, '#skF_7': $i).
% 1.88/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.88/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.88/1.25  tff('#skF_6', type, '#skF_6': $i).
% 1.88/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.88/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.88/1.25  tff('#skF_8', type, '#skF_8': $i).
% 1.88/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.88/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.88/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.25  
% 1.88/1.26  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 1.88/1.26  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.88/1.26  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 1.88/1.26  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.88/1.26  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 1.88/1.26  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 1.88/1.26  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.88/1.26  tff(c_34, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.88/1.26  tff(c_40, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.88/1.26  tff(c_44, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_40])).
% 1.88/1.26  tff(c_38, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.88/1.26  tff(c_6, plain, (![A_4, C_40]: (k1_funct_1(A_4, '#skF_4'(A_4, k2_relat_1(A_4), C_40))=C_40 | ~r2_hidden(C_40, k2_relat_1(A_4)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.88/1.26  tff(c_121, plain, (![A_88, C_89]: (r2_hidden('#skF_4'(A_88, k2_relat_1(A_88), C_89), k1_relat_1(A_88)) | ~r2_hidden(C_89, k2_relat_1(A_88)) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.88/1.26  tff(c_60, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.88/1.26  tff(c_64, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_60])).
% 1.88/1.26  tff(c_69, plain, (![A_72, B_73, C_74]: (m1_subset_1(k1_relset_1(A_72, B_73, C_74), k1_zfmisc_1(A_72)) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.88/1.26  tff(c_86, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_69])).
% 1.88/1.26  tff(c_92, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_86])).
% 1.88/1.26  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.26  tff(c_96, plain, (![A_1]: (m1_subset_1(A_1, '#skF_6') | ~r2_hidden(A_1, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_92, c_2])).
% 1.88/1.26  tff(c_125, plain, (![C_89]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_89), '#skF_6') | ~r2_hidden(C_89, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_121, c_96])).
% 1.88/1.26  tff(c_129, plain, (![C_90]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_90), '#skF_6') | ~r2_hidden(C_90, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_125])).
% 1.88/1.26  tff(c_30, plain, (![E_57]: (k1_funct_1('#skF_8', E_57)!='#skF_5' | ~m1_subset_1(E_57, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.88/1.26  tff(c_134, plain, (![C_91]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_91))!='#skF_5' | ~r2_hidden(C_91, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_129, c_30])).
% 1.88/1.26  tff(c_138, plain, (![C_40]: (C_40!='#skF_5' | ~r2_hidden(C_40, k2_relat_1('#skF_8')) | ~r2_hidden(C_40, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_134])).
% 1.88/1.26  tff(c_141, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_138])).
% 1.88/1.26  tff(c_50, plain, (![A_66, B_67, C_68]: (k2_relset_1(A_66, B_67, C_68)=k2_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.88/1.26  tff(c_54, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_50])).
% 1.88/1.26  tff(c_32, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.88/1.26  tff(c_55, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_32])).
% 1.88/1.26  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_55])).
% 1.88/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.26  
% 1.88/1.26  Inference rules
% 1.88/1.26  ----------------------
% 1.88/1.26  #Ref     : 0
% 1.88/1.26  #Sup     : 22
% 1.88/1.26  #Fact    : 0
% 1.88/1.26  #Define  : 0
% 1.88/1.26  #Split   : 0
% 1.88/1.26  #Chain   : 0
% 1.88/1.26  #Close   : 0
% 1.88/1.26  
% 1.88/1.26  Ordering : KBO
% 1.88/1.26  
% 1.88/1.26  Simplification rules
% 1.88/1.26  ----------------------
% 1.88/1.26  #Subsume      : 1
% 1.88/1.26  #Demod        : 7
% 1.88/1.26  #Tautology    : 7
% 1.88/1.26  #SimpNegUnit  : 1
% 1.88/1.26  #BackRed      : 2
% 1.88/1.26  
% 1.88/1.26  #Partial instantiations: 0
% 1.88/1.26  #Strategies tried      : 1
% 1.88/1.26  
% 1.88/1.26  Timing (in seconds)
% 1.88/1.26  ----------------------
% 2.10/1.26  Preprocessing        : 0.30
% 2.10/1.26  Parsing              : 0.15
% 2.10/1.26  CNF conversion       : 0.03
% 2.10/1.26  Main loop            : 0.14
% 2.10/1.26  Inferencing          : 0.05
% 2.10/1.26  Reduction            : 0.04
% 2.10/1.26  Demodulation         : 0.03
% 2.10/1.26  BG Simplification    : 0.01
% 2.10/1.26  Subsumption          : 0.02
% 2.10/1.26  Abstraction          : 0.01
% 2.10/1.26  MUC search           : 0.00
% 2.10/1.26  Cooper               : 0.00
% 2.10/1.26  Total                : 0.47
% 2.10/1.26  Index Insertion      : 0.00
% 2.10/1.26  Index Deletion       : 0.00
% 2.10/1.26  Index Matching       : 0.00
% 2.10/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
