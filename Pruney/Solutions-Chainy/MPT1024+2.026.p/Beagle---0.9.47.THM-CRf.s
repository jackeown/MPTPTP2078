%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:25 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   58 (  88 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 217 expanded)
%              Number of equality atoms :   13 (  28 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_53,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_57,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_53])).

tff(c_52,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12,plain,(
    ! [A_9,B_32,D_47] :
      ( k1_funct_1(A_9,'#skF_4'(A_9,B_32,k9_relat_1(A_9,B_32),D_47)) = D_47
      | ~ r2_hidden(D_47,k9_relat_1(A_9,B_32))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_9,B_32,D_47] :
      ( r2_hidden('#skF_4'(A_9,B_32,k9_relat_1(A_9,B_32),D_47),k1_relat_1(A_9))
      | ~ r2_hidden(D_47,k9_relat_1(A_9,B_32))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_92,plain,(
    ! [A_96,C_97] :
      ( r2_hidden(k4_tarski(A_96,k1_funct_1(C_97,A_96)),C_97)
      | ~ r2_hidden(A_96,k1_relat_1(C_97))
      | ~ v1_funct_1(C_97)
      | ~ v1_relat_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_185,plain,(
    ! [A_120,C_121,A_122] :
      ( r2_hidden(k4_tarski(A_120,k1_funct_1(C_121,A_120)),A_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(A_122))
      | ~ r2_hidden(A_120,k1_relat_1(C_121))
      | ~ v1_funct_1(C_121)
      | ~ v1_relat_1(C_121) ) ),
    inference(resolution,[status(thm)],[c_92,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_234,plain,(
    ! [A_125,C_126,C_127,D_128] :
      ( r2_hidden(A_125,C_126)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(C_126,D_128)))
      | ~ r2_hidden(A_125,k1_relat_1(C_127))
      | ~ v1_funct_1(C_127)
      | ~ v1_relat_1(C_127) ) ),
    inference(resolution,[status(thm)],[c_185,c_6])).

tff(c_236,plain,(
    ! [A_125] :
      ( r2_hidden(A_125,'#skF_5')
      | ~ r2_hidden(A_125,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_48,c_234])).

tff(c_240,plain,(
    ! [A_129] :
      ( r2_hidden(A_129,'#skF_5')
      | ~ r2_hidden(A_129,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_52,c_236])).

tff(c_248,plain,(
    ! [B_32,D_47] :
      ( r2_hidden('#skF_4'('#skF_8',B_32,k9_relat_1('#skF_8',B_32),D_47),'#skF_5')
      | ~ r2_hidden(D_47,k9_relat_1('#skF_8',B_32))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_16,c_240])).

tff(c_260,plain,(
    ! [B_32,D_47] :
      ( r2_hidden('#skF_4'('#skF_8',B_32,k9_relat_1('#skF_8',B_32),D_47),'#skF_5')
      | ~ r2_hidden(D_47,k9_relat_1('#skF_8',B_32)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_52,c_248])).

tff(c_143,plain,(
    ! [A_108,B_109,D_110] :
      ( r2_hidden('#skF_4'(A_108,B_109,k9_relat_1(A_108,B_109),D_110),B_109)
      | ~ r2_hidden(D_110,k9_relat_1(A_108,B_109))
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    ! [F_65] :
      ( k1_funct_1('#skF_8',F_65) != '#skF_9'
      | ~ r2_hidden(F_65,'#skF_7')
      | ~ r2_hidden(F_65,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_688,plain,(
    ! [A_181,D_182] :
      ( k1_funct_1('#skF_8','#skF_4'(A_181,'#skF_7',k9_relat_1(A_181,'#skF_7'),D_182)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_181,'#skF_7',k9_relat_1(A_181,'#skF_7'),D_182),'#skF_5')
      | ~ r2_hidden(D_182,k9_relat_1(A_181,'#skF_7'))
      | ~ v1_funct_1(A_181)
      | ~ v1_relat_1(A_181) ) ),
    inference(resolution,[status(thm)],[c_143,c_44])).

tff(c_696,plain,(
    ! [D_47] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_47)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_47,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_260,c_688])).

tff(c_703,plain,(
    ! [D_183] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_183)) != '#skF_9'
      | ~ r2_hidden(D_183,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_52,c_696])).

tff(c_707,plain,(
    ! [D_47] :
      ( D_47 != '#skF_9'
      | ~ r2_hidden(D_47,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_47,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_703])).

tff(c_710,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_52,c_707])).

tff(c_88,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( k7_relset_1(A_92,B_93,C_94,D_95) = k9_relat_1(C_94,D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_91,plain,(
    ! [D_95] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_95) = k9_relat_1('#skF_8',D_95) ),
    inference(resolution,[status(thm)],[c_48,c_88])).

tff(c_46,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_121,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_46])).

tff(c_712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_710,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.59  
% 3.12/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.59  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.12/1.59  
% 3.12/1.59  %Foreground sorts:
% 3.12/1.59  
% 3.12/1.59  
% 3.12/1.59  %Background operators:
% 3.12/1.59  
% 3.12/1.59  
% 3.12/1.59  %Foreground operators:
% 3.12/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.12/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.12/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.12/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.12/1.59  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.12/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.12/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.12/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.12/1.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.12/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.12/1.59  tff('#skF_9', type, '#skF_9': $i).
% 3.12/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.12/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.12/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.12/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.12/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.12/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.59  
% 3.12/1.61  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 3.12/1.61  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.12/1.61  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 3.12/1.61  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.12/1.61  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.12/1.61  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.12/1.61  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.12/1.61  tff(c_48, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.12/1.61  tff(c_53, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.12/1.61  tff(c_57, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_53])).
% 3.12/1.61  tff(c_52, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.12/1.61  tff(c_12, plain, (![A_9, B_32, D_47]: (k1_funct_1(A_9, '#skF_4'(A_9, B_32, k9_relat_1(A_9, B_32), D_47))=D_47 | ~r2_hidden(D_47, k9_relat_1(A_9, B_32)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.12/1.61  tff(c_16, plain, (![A_9, B_32, D_47]: (r2_hidden('#skF_4'(A_9, B_32, k9_relat_1(A_9, B_32), D_47), k1_relat_1(A_9)) | ~r2_hidden(D_47, k9_relat_1(A_9, B_32)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.12/1.61  tff(c_92, plain, (![A_96, C_97]: (r2_hidden(k4_tarski(A_96, k1_funct_1(C_97, A_96)), C_97) | ~r2_hidden(A_96, k1_relat_1(C_97)) | ~v1_funct_1(C_97) | ~v1_relat_1(C_97))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.12/1.61  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.12/1.61  tff(c_185, plain, (![A_120, C_121, A_122]: (r2_hidden(k4_tarski(A_120, k1_funct_1(C_121, A_120)), A_122) | ~m1_subset_1(C_121, k1_zfmisc_1(A_122)) | ~r2_hidden(A_120, k1_relat_1(C_121)) | ~v1_funct_1(C_121) | ~v1_relat_1(C_121))), inference(resolution, [status(thm)], [c_92, c_8])).
% 3.12/1.61  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.61  tff(c_234, plain, (![A_125, C_126, C_127, D_128]: (r2_hidden(A_125, C_126) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(C_126, D_128))) | ~r2_hidden(A_125, k1_relat_1(C_127)) | ~v1_funct_1(C_127) | ~v1_relat_1(C_127))), inference(resolution, [status(thm)], [c_185, c_6])).
% 3.12/1.61  tff(c_236, plain, (![A_125]: (r2_hidden(A_125, '#skF_5') | ~r2_hidden(A_125, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_48, c_234])).
% 3.12/1.61  tff(c_240, plain, (![A_129]: (r2_hidden(A_129, '#skF_5') | ~r2_hidden(A_129, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_52, c_236])).
% 3.12/1.61  tff(c_248, plain, (![B_32, D_47]: (r2_hidden('#skF_4'('#skF_8', B_32, k9_relat_1('#skF_8', B_32), D_47), '#skF_5') | ~r2_hidden(D_47, k9_relat_1('#skF_8', B_32)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_16, c_240])).
% 3.12/1.61  tff(c_260, plain, (![B_32, D_47]: (r2_hidden('#skF_4'('#skF_8', B_32, k9_relat_1('#skF_8', B_32), D_47), '#skF_5') | ~r2_hidden(D_47, k9_relat_1('#skF_8', B_32)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_52, c_248])).
% 3.12/1.61  tff(c_143, plain, (![A_108, B_109, D_110]: (r2_hidden('#skF_4'(A_108, B_109, k9_relat_1(A_108, B_109), D_110), B_109) | ~r2_hidden(D_110, k9_relat_1(A_108, B_109)) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.12/1.61  tff(c_44, plain, (![F_65]: (k1_funct_1('#skF_8', F_65)!='#skF_9' | ~r2_hidden(F_65, '#skF_7') | ~r2_hidden(F_65, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.12/1.61  tff(c_688, plain, (![A_181, D_182]: (k1_funct_1('#skF_8', '#skF_4'(A_181, '#skF_7', k9_relat_1(A_181, '#skF_7'), D_182))!='#skF_9' | ~r2_hidden('#skF_4'(A_181, '#skF_7', k9_relat_1(A_181, '#skF_7'), D_182), '#skF_5') | ~r2_hidden(D_182, k9_relat_1(A_181, '#skF_7')) | ~v1_funct_1(A_181) | ~v1_relat_1(A_181))), inference(resolution, [status(thm)], [c_143, c_44])).
% 3.12/1.61  tff(c_696, plain, (![D_47]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_47))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_47, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_260, c_688])).
% 3.12/1.61  tff(c_703, plain, (![D_183]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_183))!='#skF_9' | ~r2_hidden(D_183, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_52, c_696])).
% 3.12/1.61  tff(c_707, plain, (![D_47]: (D_47!='#skF_9' | ~r2_hidden(D_47, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_47, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_703])).
% 3.12/1.61  tff(c_710, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_52, c_707])).
% 3.12/1.61  tff(c_88, plain, (![A_92, B_93, C_94, D_95]: (k7_relset_1(A_92, B_93, C_94, D_95)=k9_relat_1(C_94, D_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.12/1.61  tff(c_91, plain, (![D_95]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_95)=k9_relat_1('#skF_8', D_95))), inference(resolution, [status(thm)], [c_48, c_88])).
% 3.12/1.61  tff(c_46, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.12/1.61  tff(c_121, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_46])).
% 3.12/1.61  tff(c_712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_710, c_121])).
% 3.12/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.61  
% 3.12/1.61  Inference rules
% 3.12/1.61  ----------------------
% 3.12/1.61  #Ref     : 0
% 3.12/1.61  #Sup     : 139
% 3.12/1.61  #Fact    : 0
% 3.12/1.61  #Define  : 0
% 3.12/1.61  #Split   : 8
% 3.12/1.61  #Chain   : 0
% 3.12/1.61  #Close   : 0
% 3.12/1.61  
% 3.12/1.61  Ordering : KBO
% 3.12/1.61  
% 3.12/1.61  Simplification rules
% 3.12/1.61  ----------------------
% 3.12/1.61  #Subsume      : 8
% 3.12/1.61  #Demod        : 32
% 3.12/1.61  #Tautology    : 11
% 3.12/1.61  #SimpNegUnit  : 1
% 3.12/1.61  #BackRed      : 3
% 3.12/1.61  
% 3.12/1.61  #Partial instantiations: 0
% 3.12/1.61  #Strategies tried      : 1
% 3.12/1.61  
% 3.12/1.61  Timing (in seconds)
% 3.12/1.61  ----------------------
% 3.12/1.61  Preprocessing        : 0.31
% 3.12/1.61  Parsing              : 0.16
% 3.12/1.61  CNF conversion       : 0.03
% 3.12/1.61  Main loop            : 0.46
% 3.12/1.61  Inferencing          : 0.18
% 3.12/1.61  Reduction            : 0.11
% 3.12/1.61  Demodulation         : 0.08
% 3.12/1.61  BG Simplification    : 0.03
% 3.12/1.61  Subsumption          : 0.10
% 3.12/1.61  Abstraction          : 0.03
% 3.12/1.61  MUC search           : 0.00
% 3.12/1.61  Cooper               : 0.00
% 3.12/1.61  Total                : 0.81
% 3.12/1.61  Index Insertion      : 0.00
% 3.12/1.61  Index Deletion       : 0.00
% 3.12/1.61  Index Matching       : 0.00
% 3.12/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
