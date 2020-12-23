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
% DateTime   : Thu Dec  3 10:16:34 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   58 (  83 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 188 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_45,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_49,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_45])).

tff(c_44,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_4,B_27,D_42] :
      ( k1_funct_1(A_4,'#skF_4'(A_4,B_27,k9_relat_1(A_4,B_27),D_42)) = D_42
      | ~ r2_hidden(D_42,k9_relat_1(A_4,B_27))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_146,plain,(
    ! [A_103,B_104,D_105] :
      ( r2_hidden('#skF_4'(A_103,B_104,k9_relat_1(A_103,B_104),D_105),k1_relat_1(A_103))
      | ~ r2_hidden(D_105,k9_relat_1(A_103,B_104))
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_56,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_60,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_65,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1(k1_relset_1(A_75,B_76,C_77),k1_zfmisc_1(A_75))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_78,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_65])).

tff(c_83,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_78])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_5')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_150,plain,(
    ! [B_104,D_105] :
      ( m1_subset_1('#skF_4'('#skF_8',B_104,k9_relat_1('#skF_8',B_104),D_105),'#skF_5')
      | ~ r2_hidden(D_105,k9_relat_1('#skF_8',B_104))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_146,c_86])).

tff(c_154,plain,(
    ! [B_106,D_107] :
      ( m1_subset_1('#skF_4'('#skF_8',B_106,k9_relat_1('#skF_8',B_106),D_107),'#skF_5')
      | ~ r2_hidden(D_107,k9_relat_1('#skF_8',B_106)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_44,c_150])).

tff(c_96,plain,(
    ! [A_83,B_84,D_85] :
      ( r2_hidden('#skF_4'(A_83,B_84,k9_relat_1(A_83,B_84),D_85),B_84)
      | ~ r2_hidden(D_85,k9_relat_1(A_83,B_84))
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ! [F_63] :
      ( k1_funct_1('#skF_8',F_63) != '#skF_9'
      | ~ r2_hidden(F_63,'#skF_7')
      | ~ m1_subset_1(F_63,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_106,plain,(
    ! [A_83,D_85] :
      ( k1_funct_1('#skF_8','#skF_4'(A_83,'#skF_7',k9_relat_1(A_83,'#skF_7'),D_85)) != '#skF_9'
      | ~ m1_subset_1('#skF_4'(A_83,'#skF_7',k9_relat_1(A_83,'#skF_7'),D_85),'#skF_5')
      | ~ r2_hidden(D_85,k9_relat_1(A_83,'#skF_7'))
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_96,c_36])).

tff(c_158,plain,(
    ! [D_107] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_107)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_107,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_154,c_106])).

tff(c_163,plain,(
    ! [D_111] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_111)) != '#skF_9'
      | ~ r2_hidden(D_111,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_44,c_158])).

tff(c_167,plain,(
    ! [D_42] :
      ( D_42 != '#skF_9'
      | ~ r2_hidden(D_42,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_42,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_163])).

tff(c_170,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_44,c_167])).

tff(c_88,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k7_relset_1(A_79,B_80,C_81,D_82) = k9_relat_1(C_81,D_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_95,plain,(
    ! [D_82] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_82) = k9_relat_1('#skF_8',D_82) ),
    inference(resolution,[status(thm)],[c_40,c_88])).

tff(c_38,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_107,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_38])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.20  
% 2.04/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.20  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.04/1.20  
% 2.04/1.20  %Foreground sorts:
% 2.04/1.20  
% 2.04/1.20  
% 2.04/1.20  %Background operators:
% 2.04/1.20  
% 2.04/1.20  
% 2.04/1.20  %Foreground operators:
% 2.04/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.04/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.04/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.20  tff('#skF_7', type, '#skF_7': $i).
% 2.04/1.20  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.04/1.20  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.04/1.20  tff('#skF_6', type, '#skF_6': $i).
% 2.04/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.04/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.04/1.20  tff('#skF_9', type, '#skF_9': $i).
% 2.04/1.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.04/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.04/1.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.04/1.20  tff('#skF_8', type, '#skF_8': $i).
% 2.04/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.04/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.20  
% 2.04/1.21  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 2.04/1.21  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.04/1.21  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.04/1.21  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.04/1.21  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.04/1.21  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.04/1.21  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.04/1.21  tff(c_40, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.04/1.21  tff(c_45, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.04/1.21  tff(c_49, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_45])).
% 2.04/1.21  tff(c_44, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.04/1.21  tff(c_6, plain, (![A_4, B_27, D_42]: (k1_funct_1(A_4, '#skF_4'(A_4, B_27, k9_relat_1(A_4, B_27), D_42))=D_42 | ~r2_hidden(D_42, k9_relat_1(A_4, B_27)) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.04/1.21  tff(c_146, plain, (![A_103, B_104, D_105]: (r2_hidden('#skF_4'(A_103, B_104, k9_relat_1(A_103, B_104), D_105), k1_relat_1(A_103)) | ~r2_hidden(D_105, k9_relat_1(A_103, B_104)) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.04/1.21  tff(c_56, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.04/1.21  tff(c_60, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_56])).
% 2.04/1.21  tff(c_65, plain, (![A_75, B_76, C_77]: (m1_subset_1(k1_relset_1(A_75, B_76, C_77), k1_zfmisc_1(A_75)) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.04/1.21  tff(c_78, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_65])).
% 2.04/1.21  tff(c_83, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_78])).
% 2.04/1.21  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.21  tff(c_86, plain, (![A_1]: (m1_subset_1(A_1, '#skF_5') | ~r2_hidden(A_1, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_83, c_2])).
% 2.04/1.21  tff(c_150, plain, (![B_104, D_105]: (m1_subset_1('#skF_4'('#skF_8', B_104, k9_relat_1('#skF_8', B_104), D_105), '#skF_5') | ~r2_hidden(D_105, k9_relat_1('#skF_8', B_104)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_146, c_86])).
% 2.04/1.21  tff(c_154, plain, (![B_106, D_107]: (m1_subset_1('#skF_4'('#skF_8', B_106, k9_relat_1('#skF_8', B_106), D_107), '#skF_5') | ~r2_hidden(D_107, k9_relat_1('#skF_8', B_106)))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_44, c_150])).
% 2.04/1.21  tff(c_96, plain, (![A_83, B_84, D_85]: (r2_hidden('#skF_4'(A_83, B_84, k9_relat_1(A_83, B_84), D_85), B_84) | ~r2_hidden(D_85, k9_relat_1(A_83, B_84)) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.04/1.21  tff(c_36, plain, (![F_63]: (k1_funct_1('#skF_8', F_63)!='#skF_9' | ~r2_hidden(F_63, '#skF_7') | ~m1_subset_1(F_63, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.04/1.21  tff(c_106, plain, (![A_83, D_85]: (k1_funct_1('#skF_8', '#skF_4'(A_83, '#skF_7', k9_relat_1(A_83, '#skF_7'), D_85))!='#skF_9' | ~m1_subset_1('#skF_4'(A_83, '#skF_7', k9_relat_1(A_83, '#skF_7'), D_85), '#skF_5') | ~r2_hidden(D_85, k9_relat_1(A_83, '#skF_7')) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_96, c_36])).
% 2.04/1.21  tff(c_158, plain, (![D_107]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_107))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_107, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_154, c_106])).
% 2.04/1.21  tff(c_163, plain, (![D_111]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_111))!='#skF_9' | ~r2_hidden(D_111, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_44, c_158])).
% 2.04/1.21  tff(c_167, plain, (![D_42]: (D_42!='#skF_9' | ~r2_hidden(D_42, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_42, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_163])).
% 2.04/1.21  tff(c_170, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_44, c_167])).
% 2.04/1.21  tff(c_88, plain, (![A_79, B_80, C_81, D_82]: (k7_relset_1(A_79, B_80, C_81, D_82)=k9_relat_1(C_81, D_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.04/1.21  tff(c_95, plain, (![D_82]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_82)=k9_relat_1('#skF_8', D_82))), inference(resolution, [status(thm)], [c_40, c_88])).
% 2.04/1.21  tff(c_38, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.04/1.21  tff(c_107, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_38])).
% 2.04/1.21  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_107])).
% 2.04/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.21  
% 2.04/1.21  Inference rules
% 2.04/1.21  ----------------------
% 2.04/1.21  #Ref     : 0
% 2.04/1.21  #Sup     : 25
% 2.04/1.21  #Fact    : 0
% 2.04/1.21  #Define  : 0
% 2.04/1.21  #Split   : 0
% 2.04/1.21  #Chain   : 0
% 2.04/1.21  #Close   : 0
% 2.04/1.21  
% 2.04/1.21  Ordering : KBO
% 2.04/1.21  
% 2.04/1.21  Simplification rules
% 2.04/1.21  ----------------------
% 2.04/1.22  #Subsume      : 1
% 2.04/1.22  #Demod        : 9
% 2.04/1.22  #Tautology    : 6
% 2.04/1.22  #SimpNegUnit  : 1
% 2.04/1.22  #BackRed      : 2
% 2.04/1.22  
% 2.04/1.22  #Partial instantiations: 0
% 2.04/1.22  #Strategies tried      : 1
% 2.04/1.22  
% 2.04/1.22  Timing (in seconds)
% 2.04/1.22  ----------------------
% 2.04/1.22  Preprocessing        : 0.31
% 2.04/1.22  Parsing              : 0.16
% 2.04/1.22  CNF conversion       : 0.03
% 2.04/1.22  Main loop            : 0.16
% 2.04/1.22  Inferencing          : 0.06
% 2.04/1.22  Reduction            : 0.04
% 2.04/1.22  Demodulation         : 0.03
% 2.04/1.22  BG Simplification    : 0.01
% 2.04/1.22  Subsumption          : 0.03
% 2.04/1.22  Abstraction          : 0.01
% 2.04/1.22  MUC search           : 0.00
% 2.04/1.22  Cooper               : 0.00
% 2.04/1.22  Total                : 0.49
% 2.04/1.22  Index Insertion      : 0.00
% 2.04/1.22  Index Deletion       : 0.00
% 2.04/1.22  Index Matching       : 0.00
% 2.04/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
