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
% DateTime   : Thu Dec  3 10:16:25 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   61 (  92 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 224 expanded)
%              Number of equality atoms :   13 (  27 expanded)
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

tff(f_88,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_61,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_47,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_51,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_47])).

tff(c_46,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_187,plain,(
    ! [A_120,B_121,D_122] :
      ( r2_hidden(k4_tarski('#skF_4'(A_120,B_121,k9_relat_1(A_120,B_121),D_122),D_122),A_120)
      | ~ r2_hidden(D_122,k9_relat_1(A_120,B_121))
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [C_53,A_51,B_52] :
      ( k1_funct_1(C_53,A_51) = B_52
      | ~ r2_hidden(k4_tarski(A_51,B_52),C_53)
      | ~ v1_funct_1(C_53)
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_217,plain,(
    ! [A_120,B_121,D_122] :
      ( k1_funct_1(A_120,'#skF_4'(A_120,B_121,k9_relat_1(A_120,B_121),D_122)) = D_122
      | ~ v1_funct_1(A_120)
      | ~ r2_hidden(D_122,k9_relat_1(A_120,B_121))
      | ~ v1_relat_1(A_120) ) ),
    inference(resolution,[status(thm)],[c_187,c_30])).

tff(c_32,plain,(
    ! [A_51,C_53,B_52] :
      ( r2_hidden(A_51,k1_relat_1(C_53))
      | ~ r2_hidden(k4_tarski(A_51,B_52),C_53)
      | ~ v1_funct_1(C_53)
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_382,plain,(
    ! [A_150,B_151,D_152] :
      ( r2_hidden('#skF_4'(A_150,B_151,k9_relat_1(A_150,B_151),D_152),k1_relat_1(A_150))
      | ~ v1_funct_1(A_150)
      | ~ r2_hidden(D_152,k9_relat_1(A_150,B_151))
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_187,c_32])).

tff(c_86,plain,(
    ! [A_96,C_97] :
      ( r2_hidden(k4_tarski(A_96,k1_funct_1(C_97,A_96)),C_97)
      | ~ r2_hidden(A_96,k1_relat_1(C_97))
      | ~ v1_funct_1(C_97)
      | ~ v1_relat_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_297,plain,(
    ! [A_138,C_139,A_140] :
      ( r2_hidden(k4_tarski(A_138,k1_funct_1(C_139,A_138)),A_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(A_140))
      | ~ r2_hidden(A_138,k1_relat_1(C_139))
      | ~ v1_funct_1(C_139)
      | ~ v1_relat_1(C_139) ) ),
    inference(resolution,[status(thm)],[c_86,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_345,plain,(
    ! [A_145,C_146,C_147,D_148] :
      ( r2_hidden(A_145,C_146)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(C_146,D_148)))
      | ~ r2_hidden(A_145,k1_relat_1(C_147))
      | ~ v1_funct_1(C_147)
      | ~ v1_relat_1(C_147) ) ),
    inference(resolution,[status(thm)],[c_297,c_6])).

tff(c_347,plain,(
    ! [A_145] :
      ( r2_hidden(A_145,'#skF_5')
      | ~ r2_hidden(A_145,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_345])).

tff(c_350,plain,(
    ! [A_145] :
      ( r2_hidden(A_145,'#skF_5')
      | ~ r2_hidden(A_145,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_46,c_347])).

tff(c_386,plain,(
    ! [B_151,D_152] :
      ( r2_hidden('#skF_4'('#skF_8',B_151,k9_relat_1('#skF_8',B_151),D_152),'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ r2_hidden(D_152,k9_relat_1('#skF_8',B_151))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_382,c_350])).

tff(c_402,plain,(
    ! [B_155,D_156] :
      ( r2_hidden('#skF_4'('#skF_8',B_155,k9_relat_1('#skF_8',B_155),D_156),'#skF_5')
      | ~ r2_hidden(D_156,k9_relat_1('#skF_8',B_155)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_46,c_386])).

tff(c_157,plain,(
    ! [A_106,B_107,D_108] :
      ( r2_hidden('#skF_4'(A_106,B_107,k9_relat_1(A_106,B_107),D_108),B_107)
      | ~ r2_hidden(D_108,k9_relat_1(A_106,B_107))
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [F_65] :
      ( k1_funct_1('#skF_8',F_65) != '#skF_9'
      | ~ r2_hidden(F_65,'#skF_7')
      | ~ r2_hidden(F_65,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_167,plain,(
    ! [A_106,D_108] :
      ( k1_funct_1('#skF_8','#skF_4'(A_106,'#skF_7',k9_relat_1(A_106,'#skF_7'),D_108)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_106,'#skF_7',k9_relat_1(A_106,'#skF_7'),D_108),'#skF_5')
      | ~ r2_hidden(D_108,k9_relat_1(A_106,'#skF_7'))
      | ~ v1_relat_1(A_106) ) ),
    inference(resolution,[status(thm)],[c_157,c_38])).

tff(c_406,plain,(
    ! [D_156] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_156)) != '#skF_9'
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_156,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_402,c_167])).

tff(c_416,plain,(
    ! [D_157] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_157)) != '#skF_9'
      | ~ r2_hidden(D_157,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_406])).

tff(c_420,plain,(
    ! [D_122] :
      ( D_122 != '#skF_9'
      | ~ r2_hidden(D_122,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ r2_hidden(D_122,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_416])).

tff(c_423,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_46,c_420])).

tff(c_82,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( k7_relset_1(A_92,B_93,C_94,D_95) = k9_relat_1(C_94,D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_85,plain,(
    ! [D_95] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_95) = k9_relat_1('#skF_8',D_95) ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_40,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_115,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40])).

tff(c_425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_423,c_115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n024.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 18:29:51 EST 2020
% 0.18/0.32  % CPUTime    : 
% 0.18/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.32  
% 2.49/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.32  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.49/1.32  
% 2.49/1.32  %Foreground sorts:
% 2.49/1.32  
% 2.49/1.32  
% 2.49/1.32  %Background operators:
% 2.49/1.32  
% 2.49/1.32  
% 2.49/1.32  %Foreground operators:
% 2.49/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.49/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.49/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.49/1.32  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.49/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.49/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.49/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.49/1.32  tff('#skF_9', type, '#skF_9': $i).
% 2.49/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.49/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.49/1.32  tff('#skF_8', type, '#skF_8': $i).
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.32  
% 2.49/1.34  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 2.49/1.34  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.49/1.34  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 2.49/1.34  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.49/1.34  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.49/1.34  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.49/1.34  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.49/1.34  tff(c_42, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.49/1.34  tff(c_47, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.49/1.34  tff(c_51, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_42, c_47])).
% 2.49/1.34  tff(c_46, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.49/1.34  tff(c_187, plain, (![A_120, B_121, D_122]: (r2_hidden(k4_tarski('#skF_4'(A_120, B_121, k9_relat_1(A_120, B_121), D_122), D_122), A_120) | ~r2_hidden(D_122, k9_relat_1(A_120, B_121)) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.49/1.34  tff(c_30, plain, (![C_53, A_51, B_52]: (k1_funct_1(C_53, A_51)=B_52 | ~r2_hidden(k4_tarski(A_51, B_52), C_53) | ~v1_funct_1(C_53) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.49/1.34  tff(c_217, plain, (![A_120, B_121, D_122]: (k1_funct_1(A_120, '#skF_4'(A_120, B_121, k9_relat_1(A_120, B_121), D_122))=D_122 | ~v1_funct_1(A_120) | ~r2_hidden(D_122, k9_relat_1(A_120, B_121)) | ~v1_relat_1(A_120))), inference(resolution, [status(thm)], [c_187, c_30])).
% 2.49/1.34  tff(c_32, plain, (![A_51, C_53, B_52]: (r2_hidden(A_51, k1_relat_1(C_53)) | ~r2_hidden(k4_tarski(A_51, B_52), C_53) | ~v1_funct_1(C_53) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.49/1.34  tff(c_382, plain, (![A_150, B_151, D_152]: (r2_hidden('#skF_4'(A_150, B_151, k9_relat_1(A_150, B_151), D_152), k1_relat_1(A_150)) | ~v1_funct_1(A_150) | ~r2_hidden(D_152, k9_relat_1(A_150, B_151)) | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_187, c_32])).
% 2.49/1.34  tff(c_86, plain, (![A_96, C_97]: (r2_hidden(k4_tarski(A_96, k1_funct_1(C_97, A_96)), C_97) | ~r2_hidden(A_96, k1_relat_1(C_97)) | ~v1_funct_1(C_97) | ~v1_relat_1(C_97))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.49/1.34  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.49/1.34  tff(c_297, plain, (![A_138, C_139, A_140]: (r2_hidden(k4_tarski(A_138, k1_funct_1(C_139, A_138)), A_140) | ~m1_subset_1(C_139, k1_zfmisc_1(A_140)) | ~r2_hidden(A_138, k1_relat_1(C_139)) | ~v1_funct_1(C_139) | ~v1_relat_1(C_139))), inference(resolution, [status(thm)], [c_86, c_8])).
% 2.49/1.34  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.34  tff(c_345, plain, (![A_145, C_146, C_147, D_148]: (r2_hidden(A_145, C_146) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(C_146, D_148))) | ~r2_hidden(A_145, k1_relat_1(C_147)) | ~v1_funct_1(C_147) | ~v1_relat_1(C_147))), inference(resolution, [status(thm)], [c_297, c_6])).
% 2.49/1.34  tff(c_347, plain, (![A_145]: (r2_hidden(A_145, '#skF_5') | ~r2_hidden(A_145, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_42, c_345])).
% 2.49/1.34  tff(c_350, plain, (![A_145]: (r2_hidden(A_145, '#skF_5') | ~r2_hidden(A_145, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_46, c_347])).
% 2.49/1.34  tff(c_386, plain, (![B_151, D_152]: (r2_hidden('#skF_4'('#skF_8', B_151, k9_relat_1('#skF_8', B_151), D_152), '#skF_5') | ~v1_funct_1('#skF_8') | ~r2_hidden(D_152, k9_relat_1('#skF_8', B_151)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_382, c_350])).
% 2.49/1.34  tff(c_402, plain, (![B_155, D_156]: (r2_hidden('#skF_4'('#skF_8', B_155, k9_relat_1('#skF_8', B_155), D_156), '#skF_5') | ~r2_hidden(D_156, k9_relat_1('#skF_8', B_155)))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_46, c_386])).
% 2.49/1.34  tff(c_157, plain, (![A_106, B_107, D_108]: (r2_hidden('#skF_4'(A_106, B_107, k9_relat_1(A_106, B_107), D_108), B_107) | ~r2_hidden(D_108, k9_relat_1(A_106, B_107)) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.49/1.34  tff(c_38, plain, (![F_65]: (k1_funct_1('#skF_8', F_65)!='#skF_9' | ~r2_hidden(F_65, '#skF_7') | ~r2_hidden(F_65, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.49/1.34  tff(c_167, plain, (![A_106, D_108]: (k1_funct_1('#skF_8', '#skF_4'(A_106, '#skF_7', k9_relat_1(A_106, '#skF_7'), D_108))!='#skF_9' | ~r2_hidden('#skF_4'(A_106, '#skF_7', k9_relat_1(A_106, '#skF_7'), D_108), '#skF_5') | ~r2_hidden(D_108, k9_relat_1(A_106, '#skF_7')) | ~v1_relat_1(A_106))), inference(resolution, [status(thm)], [c_157, c_38])).
% 2.49/1.34  tff(c_406, plain, (![D_156]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_156))!='#skF_9' | ~v1_relat_1('#skF_8') | ~r2_hidden(D_156, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_402, c_167])).
% 2.49/1.34  tff(c_416, plain, (![D_157]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_157))!='#skF_9' | ~r2_hidden(D_157, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_406])).
% 2.49/1.34  tff(c_420, plain, (![D_122]: (D_122!='#skF_9' | ~r2_hidden(D_122, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~r2_hidden(D_122, k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_217, c_416])).
% 2.49/1.34  tff(c_423, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_46, c_420])).
% 2.49/1.34  tff(c_82, plain, (![A_92, B_93, C_94, D_95]: (k7_relset_1(A_92, B_93, C_94, D_95)=k9_relat_1(C_94, D_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.49/1.34  tff(c_85, plain, (![D_95]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_95)=k9_relat_1('#skF_8', D_95))), inference(resolution, [status(thm)], [c_42, c_82])).
% 2.49/1.34  tff(c_40, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.49/1.34  tff(c_115, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_40])).
% 2.49/1.34  tff(c_425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_423, c_115])).
% 2.49/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.34  
% 2.49/1.34  Inference rules
% 2.49/1.34  ----------------------
% 2.49/1.34  #Ref     : 0
% 2.49/1.34  #Sup     : 80
% 2.49/1.34  #Fact    : 0
% 2.49/1.34  #Define  : 0
% 2.49/1.34  #Split   : 1
% 2.49/1.34  #Chain   : 0
% 2.49/1.34  #Close   : 0
% 2.49/1.34  
% 2.49/1.34  Ordering : KBO
% 2.49/1.34  
% 2.49/1.34  Simplification rules
% 2.49/1.34  ----------------------
% 2.49/1.34  #Subsume      : 4
% 2.49/1.34  #Demod        : 9
% 2.49/1.34  #Tautology    : 8
% 2.49/1.34  #SimpNegUnit  : 1
% 2.49/1.34  #BackRed      : 3
% 2.49/1.34  
% 2.49/1.34  #Partial instantiations: 0
% 2.49/1.34  #Strategies tried      : 1
% 2.49/1.34  
% 2.49/1.34  Timing (in seconds)
% 2.49/1.34  ----------------------
% 2.49/1.34  Preprocessing        : 0.30
% 2.49/1.34  Parsing              : 0.15
% 2.49/1.34  CNF conversion       : 0.03
% 2.49/1.34  Main loop            : 0.28
% 2.49/1.34  Inferencing          : 0.11
% 2.49/1.34  Reduction            : 0.07
% 2.49/1.34  Demodulation         : 0.05
% 2.49/1.34  BG Simplification    : 0.02
% 2.49/1.34  Subsumption          : 0.06
% 2.49/1.34  Abstraction          : 0.02
% 2.49/1.34  MUC search           : 0.00
% 2.49/1.34  Cooper               : 0.00
% 2.49/1.34  Total                : 0.61
% 2.49/1.34  Index Insertion      : 0.00
% 2.49/1.34  Index Deletion       : 0.00
% 2.49/1.35  Index Matching       : 0.00
% 2.49/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
