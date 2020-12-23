%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:37 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   61 (  92 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 206 expanded)
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_88,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_57,axiom,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_61,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_6,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_42,c_48])).

tff(c_54,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_51])).

tff(c_46,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10,plain,(
    ! [A_9,B_32,D_47] :
      ( k1_funct_1(A_9,'#skF_4'(A_9,B_32,k9_relat_1(A_9,B_32),D_47)) = D_47
      | ~ r2_hidden(D_47,k9_relat_1(A_9,B_32))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,(
    ! [A_100,B_101,D_102] :
      ( r2_hidden('#skF_4'(A_100,B_101,k9_relat_1(A_100,B_101),D_102),k1_relat_1(A_100))
      | ~ r2_hidden(D_102,k9_relat_1(A_100,B_101))
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_61,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_65,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_61])).

tff(c_70,plain,(
    ! [A_78,B_79,C_80] :
      ( m1_subset_1(k1_relset_1(A_78,B_79,C_80),k1_zfmisc_1(A_78))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_82,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_70])).

tff(c_87,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_82])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_5')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_151,plain,(
    ! [B_101,D_102] :
      ( m1_subset_1('#skF_4'('#skF_8',B_101,k9_relat_1('#skF_8',B_101),D_102),'#skF_5')
      | ~ r2_hidden(D_102,k9_relat_1('#skF_8',B_101))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_147,c_93])).

tff(c_154,plain,(
    ! [B_101,D_102] :
      ( m1_subset_1('#skF_4'('#skF_8',B_101,k9_relat_1('#skF_8',B_101),D_102),'#skF_5')
      | ~ r2_hidden(D_102,k9_relat_1('#skF_8',B_101)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_151])).

tff(c_132,plain,(
    ! [A_97,B_98,D_99] :
      ( r2_hidden('#skF_4'(A_97,B_98,k9_relat_1(A_97,B_98),D_99),B_98)
      | ~ r2_hidden(D_99,k9_relat_1(A_97,B_98))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ! [F_65] :
      ( k1_funct_1('#skF_8',F_65) != '#skF_9'
      | ~ r2_hidden(F_65,'#skF_7')
      | ~ m1_subset_1(F_65,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_305,plain,(
    ! [A_136,D_137] :
      ( k1_funct_1('#skF_8','#skF_4'(A_136,'#skF_7',k9_relat_1(A_136,'#skF_7'),D_137)) != '#skF_9'
      | ~ m1_subset_1('#skF_4'(A_136,'#skF_7',k9_relat_1(A_136,'#skF_7'),D_137),'#skF_5')
      | ~ r2_hidden(D_137,k9_relat_1(A_136,'#skF_7'))
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(resolution,[status(thm)],[c_132,c_38])).

tff(c_309,plain,(
    ! [D_102] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_102)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_102,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_154,c_305])).

tff(c_313,plain,(
    ! [D_138] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_138)) != '#skF_9'
      | ~ r2_hidden(D_138,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_309])).

tff(c_317,plain,(
    ! [D_47] :
      ( D_47 != '#skF_9'
      | ~ r2_hidden(D_47,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_47,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_313])).

tff(c_320,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_317])).

tff(c_96,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k7_relset_1(A_81,B_82,C_83,D_84) = k9_relat_1(C_83,D_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_103,plain,(
    ! [D_84] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_84) = k9_relat_1('#skF_8',D_84) ),
    inference(resolution,[status(thm)],[c_42,c_96])).

tff(c_40,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_105,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_40])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.17/1.31  
% 2.17/1.31  %Foreground sorts:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Background operators:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Foreground operators:
% 2.17/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.17/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.17/1.31  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.17/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.17/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.17/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.17/1.31  tff('#skF_9', type, '#skF_9': $i).
% 2.17/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.17/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.17/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.31  
% 2.17/1.33  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.17/1.33  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 2.17/1.33  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.17/1.33  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.17/1.33  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.17/1.33  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.17/1.33  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.17/1.33  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.17/1.33  tff(c_6, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.17/1.33  tff(c_42, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.17/1.33  tff(c_48, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.17/1.33  tff(c_51, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_48])).
% 2.17/1.33  tff(c_54, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_51])).
% 2.17/1.33  tff(c_46, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.17/1.33  tff(c_10, plain, (![A_9, B_32, D_47]: (k1_funct_1(A_9, '#skF_4'(A_9, B_32, k9_relat_1(A_9, B_32), D_47))=D_47 | ~r2_hidden(D_47, k9_relat_1(A_9, B_32)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.33  tff(c_147, plain, (![A_100, B_101, D_102]: (r2_hidden('#skF_4'(A_100, B_101, k9_relat_1(A_100, B_101), D_102), k1_relat_1(A_100)) | ~r2_hidden(D_102, k9_relat_1(A_100, B_101)) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.33  tff(c_61, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.17/1.33  tff(c_65, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_61])).
% 2.17/1.33  tff(c_70, plain, (![A_78, B_79, C_80]: (m1_subset_1(k1_relset_1(A_78, B_79, C_80), k1_zfmisc_1(A_78)) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.33  tff(c_82, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_65, c_70])).
% 2.17/1.33  tff(c_87, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_82])).
% 2.17/1.33  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.33  tff(c_93, plain, (![A_1]: (m1_subset_1(A_1, '#skF_5') | ~r2_hidden(A_1, k1_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_87, c_2])).
% 2.17/1.33  tff(c_151, plain, (![B_101, D_102]: (m1_subset_1('#skF_4'('#skF_8', B_101, k9_relat_1('#skF_8', B_101), D_102), '#skF_5') | ~r2_hidden(D_102, k9_relat_1('#skF_8', B_101)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_147, c_93])).
% 2.17/1.33  tff(c_154, plain, (![B_101, D_102]: (m1_subset_1('#skF_4'('#skF_8', B_101, k9_relat_1('#skF_8', B_101), D_102), '#skF_5') | ~r2_hidden(D_102, k9_relat_1('#skF_8', B_101)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_151])).
% 2.17/1.33  tff(c_132, plain, (![A_97, B_98, D_99]: (r2_hidden('#skF_4'(A_97, B_98, k9_relat_1(A_97, B_98), D_99), B_98) | ~r2_hidden(D_99, k9_relat_1(A_97, B_98)) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.33  tff(c_38, plain, (![F_65]: (k1_funct_1('#skF_8', F_65)!='#skF_9' | ~r2_hidden(F_65, '#skF_7') | ~m1_subset_1(F_65, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.17/1.33  tff(c_305, plain, (![A_136, D_137]: (k1_funct_1('#skF_8', '#skF_4'(A_136, '#skF_7', k9_relat_1(A_136, '#skF_7'), D_137))!='#skF_9' | ~m1_subset_1('#skF_4'(A_136, '#skF_7', k9_relat_1(A_136, '#skF_7'), D_137), '#skF_5') | ~r2_hidden(D_137, k9_relat_1(A_136, '#skF_7')) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(resolution, [status(thm)], [c_132, c_38])).
% 2.17/1.33  tff(c_309, plain, (![D_102]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_102))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_102, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_154, c_305])).
% 2.17/1.33  tff(c_313, plain, (![D_138]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_138))!='#skF_9' | ~r2_hidden(D_138, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_309])).
% 2.17/1.33  tff(c_317, plain, (![D_47]: (D_47!='#skF_9' | ~r2_hidden(D_47, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_47, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_313])).
% 2.17/1.33  tff(c_320, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_317])).
% 2.17/1.33  tff(c_96, plain, (![A_81, B_82, C_83, D_84]: (k7_relset_1(A_81, B_82, C_83, D_84)=k9_relat_1(C_83, D_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.17/1.33  tff(c_103, plain, (![D_84]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_84)=k9_relat_1('#skF_8', D_84))), inference(resolution, [status(thm)], [c_42, c_96])).
% 2.17/1.33  tff(c_40, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.17/1.33  tff(c_105, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_40])).
% 2.17/1.33  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_105])).
% 2.17/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.33  
% 2.17/1.33  Inference rules
% 2.17/1.33  ----------------------
% 2.17/1.33  #Ref     : 0
% 2.17/1.33  #Sup     : 53
% 2.17/1.33  #Fact    : 0
% 2.17/1.33  #Define  : 0
% 2.17/1.33  #Split   : 1
% 2.17/1.33  #Chain   : 0
% 2.17/1.33  #Close   : 0
% 2.17/1.33  
% 2.17/1.33  Ordering : KBO
% 2.17/1.33  
% 2.17/1.33  Simplification rules
% 2.17/1.33  ----------------------
% 2.17/1.33  #Subsume      : 2
% 2.17/1.33  #Demod        : 13
% 2.17/1.33  #Tautology    : 8
% 2.17/1.33  #SimpNegUnit  : 1
% 2.17/1.33  #BackRed      : 2
% 2.17/1.33  
% 2.17/1.33  #Partial instantiations: 0
% 2.17/1.33  #Strategies tried      : 1
% 2.17/1.33  
% 2.17/1.33  Timing (in seconds)
% 2.17/1.33  ----------------------
% 2.59/1.33  Preprocessing        : 0.33
% 2.59/1.33  Parsing              : 0.17
% 2.59/1.33  CNF conversion       : 0.03
% 2.59/1.33  Main loop            : 0.24
% 2.59/1.33  Inferencing          : 0.10
% 2.59/1.33  Reduction            : 0.07
% 2.59/1.33  Demodulation         : 0.05
% 2.59/1.33  BG Simplification    : 0.02
% 2.59/1.33  Subsumption          : 0.05
% 2.59/1.33  Abstraction          : 0.02
% 2.59/1.33  MUC search           : 0.00
% 2.59/1.33  Cooper               : 0.00
% 2.59/1.33  Total                : 0.60
% 2.59/1.33  Index Insertion      : 0.00
% 2.59/1.33  Index Deletion       : 0.00
% 2.59/1.33  Index Matching       : 0.00
% 2.59/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
