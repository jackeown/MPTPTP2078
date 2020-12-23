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
% DateTime   : Thu Dec  3 10:16:32 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 203 expanded)
%              Number of leaves         :   34 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  130 ( 521 expanded)
%              Number of equality atoms :   17 (  73 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_86,plain,(
    ! [C_50,A_51,B_52] :
      ( v4_relat_1(C_50,A_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_95,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_86])).

tff(c_50,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_54,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_50])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_207,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k7_relset_1(A_86,B_87,C_88,D_89) = k9_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_218,plain,(
    ! [D_89] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_89) = k9_relat_1('#skF_6',D_89) ),
    inference(resolution,[status(thm)],[c_40,c_207])).

tff(c_38,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_221,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_38])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_2'(A_10,B_11,C_12),k1_relat_1(C_12))
      | ~ r2_hidden(A_10,k9_relat_1(C_12,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_320,plain,(
    ! [A_124,B_125,C_126] :
      ( r2_hidden(k4_tarski('#skF_2'(A_124,B_125,C_126),A_124),C_126)
      | ~ r2_hidden(A_124,k9_relat_1(C_126,B_125))
      | ~ v1_relat_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [C_18,A_16,B_17] :
      ( k1_funct_1(C_18,A_16) = B_17
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_444,plain,(
    ! [C_138,A_139,B_140] :
      ( k1_funct_1(C_138,'#skF_2'(A_139,B_140,C_138)) = A_139
      | ~ v1_funct_1(C_138)
      | ~ r2_hidden(A_139,k9_relat_1(C_138,B_140))
      | ~ v1_relat_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_320,c_24])).

tff(c_455,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_221,c_444])).

tff(c_470,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44,c_455])).

tff(c_350,plain,(
    ! [A_127,C_128] :
      ( r2_hidden(k4_tarski(A_127,k1_funct_1(C_128,A_127)),C_128)
      | ~ r2_hidden(A_127,k1_relat_1(C_128))
      | ~ v1_funct_1(C_128)
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_380,plain,(
    ! [A_127,C_128] :
      ( m1_subset_1(k4_tarski(A_127,k1_funct_1(C_128,A_127)),C_128)
      | ~ r2_hidden(A_127,k1_relat_1(C_128))
      | ~ v1_funct_1(C_128)
      | ~ v1_relat_1(C_128) ) ),
    inference(resolution,[status(thm)],[c_350,c_8])).

tff(c_477,plain,
    ( m1_subset_1(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_380])).

tff(c_484,plain,
    ( m1_subset_1(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44,c_477])).

tff(c_488,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_484])).

tff(c_494,plain,
    ( ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_488])).

tff(c_501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_221,c_494])).

tff(c_503,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_484])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_576,plain,(
    ! [B_148] :
      ( r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),B_148)
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_148) ) ),
    inference(resolution,[status(thm)],[c_503,c_2])).

tff(c_612,plain,(
    ! [B_149] :
      ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),B_149)
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_149) ) ),
    inference(resolution,[status(thm)],[c_576,c_8])).

tff(c_616,plain,(
    ! [A_8] :
      ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),A_8)
      | ~ v4_relat_1('#skF_6',A_8)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_12,c_612])).

tff(c_626,plain,(
    ! [A_150] :
      ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),A_150)
      | ~ v4_relat_1('#skF_6',A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_616])).

tff(c_180,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden('#skF_2'(A_77,B_78,C_79),B_78)
      | ~ r2_hidden(A_77,k9_relat_1(C_79,B_78))
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [F_33] :
      ( k1_funct_1('#skF_6',F_33) != '#skF_7'
      | ~ r2_hidden(F_33,'#skF_5')
      | ~ m1_subset_1(F_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_244,plain,(
    ! [A_91,C_92] :
      ( k1_funct_1('#skF_6','#skF_2'(A_91,'#skF_5',C_92)) != '#skF_7'
      | ~ m1_subset_1('#skF_2'(A_91,'#skF_5',C_92),'#skF_3')
      | ~ r2_hidden(A_91,k9_relat_1(C_92,'#skF_5'))
      | ~ v1_relat_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_180,c_36])).

tff(c_247,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_221,c_244])).

tff(c_262,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_247])).

tff(c_273,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_629,plain,(
    ~ v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_626,c_273])).

tff(c_648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_629])).

tff(c_649,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_697,plain,(
    ! [A_181,B_182,C_183] :
      ( r2_hidden(k4_tarski('#skF_2'(A_181,B_182,C_183),A_181),C_183)
      | ~ r2_hidden(A_181,k9_relat_1(C_183,B_182))
      | ~ v1_relat_1(C_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_821,plain,(
    ! [C_195,A_196,B_197] :
      ( k1_funct_1(C_195,'#skF_2'(A_196,B_197,C_195)) = A_196
      | ~ v1_funct_1(C_195)
      | ~ r2_hidden(A_196,k9_relat_1(C_195,B_197))
      | ~ v1_relat_1(C_195) ) ),
    inference(resolution,[status(thm)],[c_697,c_24])).

tff(c_832,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_221,c_821])).

tff(c_847,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44,c_832])).

tff(c_849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_649,c_847])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:15:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.45  
% 2.95/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.95/1.45  
% 2.95/1.45  %Foreground sorts:
% 2.95/1.45  
% 2.95/1.45  
% 2.95/1.45  %Background operators:
% 2.95/1.45  
% 2.95/1.45  
% 2.95/1.45  %Foreground operators:
% 2.95/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.95/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.95/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.95/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.45  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.95/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.95/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.95/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.95/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.95/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.95/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.95/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.95/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.95/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.95/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.95/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.45  
% 3.24/1.47  tff(f_96, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 3.24/1.47  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.24/1.47  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.24/1.47  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.24/1.47  tff(f_77, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.24/1.47  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.24/1.47  tff(f_63, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.24/1.47  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.24/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.24/1.47  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.24/1.47  tff(c_86, plain, (![C_50, A_51, B_52]: (v4_relat_1(C_50, A_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.24/1.47  tff(c_95, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_86])).
% 3.24/1.47  tff(c_50, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.24/1.47  tff(c_54, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_50])).
% 3.24/1.47  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.24/1.47  tff(c_207, plain, (![A_86, B_87, C_88, D_89]: (k7_relset_1(A_86, B_87, C_88, D_89)=k9_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.24/1.47  tff(c_218, plain, (![D_89]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_89)=k9_relat_1('#skF_6', D_89))), inference(resolution, [status(thm)], [c_40, c_207])).
% 3.24/1.47  tff(c_38, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.24/1.47  tff(c_221, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_38])).
% 3.24/1.47  tff(c_20, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_2'(A_10, B_11, C_12), k1_relat_1(C_12)) | ~r2_hidden(A_10, k9_relat_1(C_12, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.47  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.24/1.47  tff(c_320, plain, (![A_124, B_125, C_126]: (r2_hidden(k4_tarski('#skF_2'(A_124, B_125, C_126), A_124), C_126) | ~r2_hidden(A_124, k9_relat_1(C_126, B_125)) | ~v1_relat_1(C_126))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.47  tff(c_24, plain, (![C_18, A_16, B_17]: (k1_funct_1(C_18, A_16)=B_17 | ~r2_hidden(k4_tarski(A_16, B_17), C_18) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.24/1.47  tff(c_444, plain, (![C_138, A_139, B_140]: (k1_funct_1(C_138, '#skF_2'(A_139, B_140, C_138))=A_139 | ~v1_funct_1(C_138) | ~r2_hidden(A_139, k9_relat_1(C_138, B_140)) | ~v1_relat_1(C_138))), inference(resolution, [status(thm)], [c_320, c_24])).
% 3.24/1.47  tff(c_455, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_221, c_444])).
% 3.24/1.47  tff(c_470, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_44, c_455])).
% 3.24/1.47  tff(c_350, plain, (![A_127, C_128]: (r2_hidden(k4_tarski(A_127, k1_funct_1(C_128, A_127)), C_128) | ~r2_hidden(A_127, k1_relat_1(C_128)) | ~v1_funct_1(C_128) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.24/1.47  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.24/1.47  tff(c_380, plain, (![A_127, C_128]: (m1_subset_1(k4_tarski(A_127, k1_funct_1(C_128, A_127)), C_128) | ~r2_hidden(A_127, k1_relat_1(C_128)) | ~v1_funct_1(C_128) | ~v1_relat_1(C_128))), inference(resolution, [status(thm)], [c_350, c_8])).
% 3.24/1.47  tff(c_477, plain, (m1_subset_1(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_470, c_380])).
% 3.24/1.47  tff(c_484, plain, (m1_subset_1(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_44, c_477])).
% 3.24/1.47  tff(c_488, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_484])).
% 3.24/1.47  tff(c_494, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_488])).
% 3.24/1.47  tff(c_501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_221, c_494])).
% 3.24/1.47  tff(c_503, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_484])).
% 3.24/1.47  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.24/1.47  tff(c_576, plain, (![B_148]: (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), B_148) | ~r1_tarski(k1_relat_1('#skF_6'), B_148))), inference(resolution, [status(thm)], [c_503, c_2])).
% 3.24/1.47  tff(c_612, plain, (![B_149]: (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), B_149) | ~r1_tarski(k1_relat_1('#skF_6'), B_149))), inference(resolution, [status(thm)], [c_576, c_8])).
% 3.24/1.47  tff(c_616, plain, (![A_8]: (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), A_8) | ~v4_relat_1('#skF_6', A_8) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_12, c_612])).
% 3.24/1.47  tff(c_626, plain, (![A_150]: (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), A_150) | ~v4_relat_1('#skF_6', A_150))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_616])).
% 3.24/1.47  tff(c_180, plain, (![A_77, B_78, C_79]: (r2_hidden('#skF_2'(A_77, B_78, C_79), B_78) | ~r2_hidden(A_77, k9_relat_1(C_79, B_78)) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.47  tff(c_36, plain, (![F_33]: (k1_funct_1('#skF_6', F_33)!='#skF_7' | ~r2_hidden(F_33, '#skF_5') | ~m1_subset_1(F_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.24/1.47  tff(c_244, plain, (![A_91, C_92]: (k1_funct_1('#skF_6', '#skF_2'(A_91, '#skF_5', C_92))!='#skF_7' | ~m1_subset_1('#skF_2'(A_91, '#skF_5', C_92), '#skF_3') | ~r2_hidden(A_91, k9_relat_1(C_92, '#skF_5')) | ~v1_relat_1(C_92))), inference(resolution, [status(thm)], [c_180, c_36])).
% 3.24/1.47  tff(c_247, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_221, c_244])).
% 3.24/1.47  tff(c_262, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_247])).
% 3.24/1.47  tff(c_273, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_262])).
% 3.24/1.47  tff(c_629, plain, (~v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_626, c_273])).
% 3.24/1.47  tff(c_648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_629])).
% 3.24/1.47  tff(c_649, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7'), inference(splitRight, [status(thm)], [c_262])).
% 3.24/1.47  tff(c_697, plain, (![A_181, B_182, C_183]: (r2_hidden(k4_tarski('#skF_2'(A_181, B_182, C_183), A_181), C_183) | ~r2_hidden(A_181, k9_relat_1(C_183, B_182)) | ~v1_relat_1(C_183))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.47  tff(c_821, plain, (![C_195, A_196, B_197]: (k1_funct_1(C_195, '#skF_2'(A_196, B_197, C_195))=A_196 | ~v1_funct_1(C_195) | ~r2_hidden(A_196, k9_relat_1(C_195, B_197)) | ~v1_relat_1(C_195))), inference(resolution, [status(thm)], [c_697, c_24])).
% 3.24/1.47  tff(c_832, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_221, c_821])).
% 3.24/1.47  tff(c_847, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_44, c_832])).
% 3.24/1.47  tff(c_849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_649, c_847])).
% 3.24/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.47  
% 3.24/1.47  Inference rules
% 3.24/1.47  ----------------------
% 3.24/1.47  #Ref     : 0
% 3.24/1.47  #Sup     : 171
% 3.24/1.47  #Fact    : 0
% 3.24/1.47  #Define  : 0
% 3.24/1.47  #Split   : 6
% 3.24/1.47  #Chain   : 0
% 3.24/1.47  #Close   : 0
% 3.24/1.47  
% 3.24/1.47  Ordering : KBO
% 3.24/1.47  
% 3.24/1.47  Simplification rules
% 3.24/1.47  ----------------------
% 3.24/1.47  #Subsume      : 13
% 3.24/1.47  #Demod        : 27
% 3.24/1.47  #Tautology    : 14
% 3.24/1.47  #SimpNegUnit  : 1
% 3.24/1.47  #BackRed      : 3
% 3.24/1.47  
% 3.24/1.47  #Partial instantiations: 0
% 3.24/1.47  #Strategies tried      : 1
% 3.24/1.47  
% 3.24/1.47  Timing (in seconds)
% 3.24/1.47  ----------------------
% 3.24/1.47  Preprocessing        : 0.32
% 3.24/1.47  Parsing              : 0.17
% 3.24/1.47  CNF conversion       : 0.02
% 3.24/1.47  Main loop            : 0.40
% 3.24/1.47  Inferencing          : 0.15
% 3.24/1.47  Reduction            : 0.11
% 3.24/1.47  Demodulation         : 0.08
% 3.24/1.47  BG Simplification    : 0.02
% 3.24/1.47  Subsumption          : 0.08
% 3.24/1.47  Abstraction          : 0.02
% 3.24/1.47  MUC search           : 0.00
% 3.24/1.47  Cooper               : 0.00
% 3.24/1.47  Total                : 0.75
% 3.24/1.47  Index Insertion      : 0.00
% 3.24/1.47  Index Deletion       : 0.00
% 3.24/1.47  Index Matching       : 0.00
% 3.24/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
