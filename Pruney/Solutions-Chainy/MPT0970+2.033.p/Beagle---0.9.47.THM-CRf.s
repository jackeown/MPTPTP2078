%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:23 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 179 expanded)
%              Number of leaves         :   38 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  144 ( 468 expanded)
%              Number of equality atoms :   44 ( 145 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_56,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_106,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_relset_1(A_87,B_88,C_89) = k2_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_110,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_106])).

tff(c_54,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_111,plain,(
    k2_relat_1('#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_54])).

tff(c_234,plain,(
    ! [A_114,B_115,C_116] :
      ( m1_subset_1(k2_relset_1(A_114,B_115,C_116),k1_zfmisc_1(B_115))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_251,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_234])).

tff(c_257,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_251])).

tff(c_145,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_1'(A_102,B_103),B_103)
      | r2_hidden('#skF_2'(A_102,B_103),A_102)
      | B_103 = A_102 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_478,plain,(
    ! [A_167,B_168,A_169] :
      ( r2_hidden('#skF_2'(A_167,B_168),A_169)
      | ~ m1_subset_1(A_167,k1_zfmisc_1(A_169))
      | r2_hidden('#skF_1'(A_167,B_168),B_168)
      | B_168 = A_167 ) ),
    inference(resolution,[status(thm)],[c_145,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_503,plain,(
    ! [A_167,A_169] :
      ( ~ m1_subset_1(A_167,k1_zfmisc_1(A_169))
      | r2_hidden('#skF_1'(A_167,A_169),A_169)
      | A_169 = A_167 ) ),
    inference(resolution,[status(thm)],[c_478,c_4])).

tff(c_64,plain,(
    ! [D_69] :
      ( r2_hidden('#skF_10'(D_69),'#skF_7')
      | ~ r2_hidden(D_69,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_58,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_136,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_140,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_136])).

tff(c_570,plain,(
    ! [B_179,A_180,C_181] :
      ( k1_xboole_0 = B_179
      | k1_relset_1(A_180,B_179,C_181) = A_180
      | ~ v1_funct_2(C_181,A_180,B_179)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_180,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_577,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_570])).

tff(c_581,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_140,c_577])).

tff(c_582,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_581])).

tff(c_73,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_77,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_73])).

tff(c_60,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_62,plain,(
    ! [D_69] :
      ( k1_funct_1('#skF_9','#skF_10'(D_69)) = D_69
      | ~ r2_hidden(D_69,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_313,plain,(
    ! [A_126,D_127] :
      ( r2_hidden(k1_funct_1(A_126,D_127),k2_relat_1(A_126))
      | ~ r2_hidden(D_127,k1_relat_1(A_126))
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_321,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_69),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_69,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_313])).

tff(c_325,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_69),k1_relat_1('#skF_9'))
      | ~ r2_hidden(D_69,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_60,c_321])).

tff(c_600,plain,(
    ! [D_182] :
      ( r2_hidden(D_182,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_182),'#skF_7')
      | ~ r2_hidden(D_182,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_325])).

tff(c_610,plain,(
    ! [D_183] :
      ( r2_hidden(D_183,k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_183,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_64,c_600])).

tff(c_122,plain,(
    ! [A_97,B_98] :
      ( ~ r2_hidden('#skF_1'(A_97,B_98),A_97)
      | r2_hidden('#skF_2'(A_97,B_98),A_97)
      | B_98 = A_97 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_134,plain,(
    ! [A_97,B_98,A_5] :
      ( r2_hidden('#skF_2'(A_97,B_98),A_5)
      | ~ m1_subset_1(A_97,k1_zfmisc_1(A_5))
      | ~ r2_hidden('#skF_1'(A_97,B_98),A_97)
      | B_98 = A_97 ) ),
    inference(resolution,[status(thm)],[c_122,c_12])).

tff(c_1959,plain,(
    ! [B_322,A_323] :
      ( r2_hidden('#skF_2'(k2_relat_1('#skF_9'),B_322),A_323)
      | ~ m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1(A_323))
      | k2_relat_1('#skF_9') = B_322
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_9'),B_322),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_610,c_134])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_632,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_2'(k2_relat_1('#skF_9'),B_2),B_2)
      | k2_relat_1('#skF_9') = B_2
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_9'),B_2),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_610,c_2])).

tff(c_2006,plain,(
    ! [A_325] :
      ( ~ m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1(A_325))
      | k2_relat_1('#skF_9') = A_325
      | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_9'),A_325),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1959,c_632])).

tff(c_2028,plain,
    ( ~ m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | k2_relat_1('#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_503,c_2006])).

tff(c_2042,plain,(
    k2_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_2028])).

tff(c_2044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_2042])).

tff(c_2045,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_581])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2077,plain,(
    ! [A_326] : r1_tarski('#skF_8',A_326) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2045,c_10])).

tff(c_513,plain,(
    ! [A_170,A_171] :
      ( ~ m1_subset_1(A_170,k1_zfmisc_1(A_171))
      | r2_hidden('#skF_1'(A_170,A_171),A_171)
      | A_171 = A_170 ) ),
    inference(resolution,[status(thm)],[c_478,c_4])).

tff(c_32,plain,(
    ! [B_50,A_49] :
      ( ~ r1_tarski(B_50,A_49)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_536,plain,(
    ! [A_171,A_170] :
      ( ~ r1_tarski(A_171,'#skF_1'(A_170,A_171))
      | ~ m1_subset_1(A_170,k1_zfmisc_1(A_171))
      | A_171 = A_170 ) ),
    inference(resolution,[status(thm)],[c_513,c_32])).

tff(c_2102,plain,(
    ! [A_329] :
      ( ~ m1_subset_1(A_329,k1_zfmisc_1('#skF_8'))
      | A_329 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_2077,c_536])).

tff(c_2105,plain,(
    k2_relat_1('#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_257,c_2102])).

tff(c_2113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_2105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:24:45 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.77  
% 4.47/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.77  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 4.47/1.77  
% 4.47/1.77  %Foreground sorts:
% 4.47/1.77  
% 4.47/1.77  
% 4.47/1.77  %Background operators:
% 4.47/1.77  
% 4.47/1.77  
% 4.47/1.77  %Foreground operators:
% 4.47/1.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.47/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.47/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.47/1.77  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.47/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.47/1.77  tff('#skF_7', type, '#skF_7': $i).
% 4.47/1.77  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.47/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.47/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.47/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.47/1.77  tff('#skF_10', type, '#skF_10': $i > $i).
% 4.47/1.77  tff('#skF_9', type, '#skF_9': $i).
% 4.47/1.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.47/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.47/1.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.47/1.77  tff('#skF_8', type, '#skF_8': $i).
% 4.47/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.47/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.47/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.47/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.47/1.77  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.47/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.47/1.77  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.47/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.47/1.77  
% 4.47/1.79  tff(f_114, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 4.47/1.79  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.47/1.79  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.47/1.79  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 4.47/1.79  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.47/1.79  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.47/1.79  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.47/1.79  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.47/1.79  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 4.47/1.79  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.47/1.79  tff(f_61, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.47/1.79  tff(c_56, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.47/1.79  tff(c_106, plain, (![A_87, B_88, C_89]: (k2_relset_1(A_87, B_88, C_89)=k2_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.47/1.79  tff(c_110, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_56, c_106])).
% 4.47/1.79  tff(c_54, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.47/1.79  tff(c_111, plain, (k2_relat_1('#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_54])).
% 4.47/1.79  tff(c_234, plain, (![A_114, B_115, C_116]: (m1_subset_1(k2_relset_1(A_114, B_115, C_116), k1_zfmisc_1(B_115)) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.47/1.79  tff(c_251, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_110, c_234])).
% 4.47/1.79  tff(c_257, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_251])).
% 4.47/1.79  tff(c_145, plain, (![A_102, B_103]: (r2_hidden('#skF_1'(A_102, B_103), B_103) | r2_hidden('#skF_2'(A_102, B_103), A_102) | B_103=A_102)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.47/1.79  tff(c_12, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.47/1.79  tff(c_478, plain, (![A_167, B_168, A_169]: (r2_hidden('#skF_2'(A_167, B_168), A_169) | ~m1_subset_1(A_167, k1_zfmisc_1(A_169)) | r2_hidden('#skF_1'(A_167, B_168), B_168) | B_168=A_167)), inference(resolution, [status(thm)], [c_145, c_12])).
% 4.47/1.79  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.47/1.79  tff(c_503, plain, (![A_167, A_169]: (~m1_subset_1(A_167, k1_zfmisc_1(A_169)) | r2_hidden('#skF_1'(A_167, A_169), A_169) | A_169=A_167)), inference(resolution, [status(thm)], [c_478, c_4])).
% 4.47/1.79  tff(c_64, plain, (![D_69]: (r2_hidden('#skF_10'(D_69), '#skF_7') | ~r2_hidden(D_69, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.47/1.79  tff(c_58, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.47/1.79  tff(c_136, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.47/1.79  tff(c_140, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_56, c_136])).
% 4.47/1.79  tff(c_570, plain, (![B_179, A_180, C_181]: (k1_xboole_0=B_179 | k1_relset_1(A_180, B_179, C_181)=A_180 | ~v1_funct_2(C_181, A_180, B_179) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_180, B_179))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.47/1.79  tff(c_577, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_56, c_570])).
% 4.47/1.79  tff(c_581, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_140, c_577])).
% 4.47/1.79  tff(c_582, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_581])).
% 4.47/1.79  tff(c_73, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.47/1.79  tff(c_77, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_56, c_73])).
% 4.47/1.79  tff(c_60, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.47/1.79  tff(c_62, plain, (![D_69]: (k1_funct_1('#skF_9', '#skF_10'(D_69))=D_69 | ~r2_hidden(D_69, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.47/1.79  tff(c_313, plain, (![A_126, D_127]: (r2_hidden(k1_funct_1(A_126, D_127), k2_relat_1(A_126)) | ~r2_hidden(D_127, k1_relat_1(A_126)) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.47/1.79  tff(c_321, plain, (![D_69]: (r2_hidden(D_69, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_69), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_69, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_313])).
% 4.47/1.79  tff(c_325, plain, (![D_69]: (r2_hidden(D_69, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_69), k1_relat_1('#skF_9')) | ~r2_hidden(D_69, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_60, c_321])).
% 4.47/1.79  tff(c_600, plain, (![D_182]: (r2_hidden(D_182, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_182), '#skF_7') | ~r2_hidden(D_182, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_582, c_325])).
% 4.47/1.79  tff(c_610, plain, (![D_183]: (r2_hidden(D_183, k2_relat_1('#skF_9')) | ~r2_hidden(D_183, '#skF_8'))), inference(resolution, [status(thm)], [c_64, c_600])).
% 4.47/1.79  tff(c_122, plain, (![A_97, B_98]: (~r2_hidden('#skF_1'(A_97, B_98), A_97) | r2_hidden('#skF_2'(A_97, B_98), A_97) | B_98=A_97)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.47/1.79  tff(c_134, plain, (![A_97, B_98, A_5]: (r2_hidden('#skF_2'(A_97, B_98), A_5) | ~m1_subset_1(A_97, k1_zfmisc_1(A_5)) | ~r2_hidden('#skF_1'(A_97, B_98), A_97) | B_98=A_97)), inference(resolution, [status(thm)], [c_122, c_12])).
% 4.47/1.79  tff(c_1959, plain, (![B_322, A_323]: (r2_hidden('#skF_2'(k2_relat_1('#skF_9'), B_322), A_323) | ~m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1(A_323)) | k2_relat_1('#skF_9')=B_322 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_9'), B_322), '#skF_8'))), inference(resolution, [status(thm)], [c_610, c_134])).
% 4.47/1.79  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.47/1.79  tff(c_632, plain, (![B_2]: (~r2_hidden('#skF_2'(k2_relat_1('#skF_9'), B_2), B_2) | k2_relat_1('#skF_9')=B_2 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_9'), B_2), '#skF_8'))), inference(resolution, [status(thm)], [c_610, c_2])).
% 4.47/1.79  tff(c_2006, plain, (![A_325]: (~m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1(A_325)) | k2_relat_1('#skF_9')=A_325 | ~r2_hidden('#skF_1'(k2_relat_1('#skF_9'), A_325), '#skF_8'))), inference(resolution, [status(thm)], [c_1959, c_632])).
% 4.47/1.79  tff(c_2028, plain, (~m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | k2_relat_1('#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_503, c_2006])).
% 4.47/1.79  tff(c_2042, plain, (k2_relat_1('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_257, c_2028])).
% 4.47/1.79  tff(c_2044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_2042])).
% 4.47/1.79  tff(c_2045, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_581])).
% 4.47/1.79  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.47/1.79  tff(c_2077, plain, (![A_326]: (r1_tarski('#skF_8', A_326))), inference(demodulation, [status(thm), theory('equality')], [c_2045, c_10])).
% 4.47/1.79  tff(c_513, plain, (![A_170, A_171]: (~m1_subset_1(A_170, k1_zfmisc_1(A_171)) | r2_hidden('#skF_1'(A_170, A_171), A_171) | A_171=A_170)), inference(resolution, [status(thm)], [c_478, c_4])).
% 4.47/1.79  tff(c_32, plain, (![B_50, A_49]: (~r1_tarski(B_50, A_49) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.47/1.79  tff(c_536, plain, (![A_171, A_170]: (~r1_tarski(A_171, '#skF_1'(A_170, A_171)) | ~m1_subset_1(A_170, k1_zfmisc_1(A_171)) | A_171=A_170)), inference(resolution, [status(thm)], [c_513, c_32])).
% 4.47/1.79  tff(c_2102, plain, (![A_329]: (~m1_subset_1(A_329, k1_zfmisc_1('#skF_8')) | A_329='#skF_8')), inference(resolution, [status(thm)], [c_2077, c_536])).
% 4.47/1.79  tff(c_2105, plain, (k2_relat_1('#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_257, c_2102])).
% 4.47/1.79  tff(c_2113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_2105])).
% 4.47/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.79  
% 4.47/1.79  Inference rules
% 4.47/1.79  ----------------------
% 4.47/1.79  #Ref     : 1
% 4.47/1.79  #Sup     : 401
% 4.47/1.79  #Fact    : 0
% 4.47/1.79  #Define  : 0
% 4.47/1.79  #Split   : 9
% 4.47/1.79  #Chain   : 0
% 4.47/1.79  #Close   : 0
% 4.47/1.79  
% 4.47/1.79  Ordering : KBO
% 4.47/1.79  
% 4.47/1.79  Simplification rules
% 4.47/1.79  ----------------------
% 4.47/1.79  #Subsume      : 112
% 4.47/1.79  #Demod        : 179
% 4.47/1.79  #Tautology    : 54
% 4.47/1.79  #SimpNegUnit  : 29
% 4.47/1.79  #BackRed      : 49
% 4.47/1.79  
% 4.47/1.79  #Partial instantiations: 0
% 4.47/1.79  #Strategies tried      : 1
% 4.47/1.79  
% 4.47/1.79  Timing (in seconds)
% 4.47/1.79  ----------------------
% 4.47/1.79  Preprocessing        : 0.34
% 4.47/1.79  Parsing              : 0.17
% 4.47/1.79  CNF conversion       : 0.03
% 4.47/1.79  Main loop            : 0.70
% 4.47/1.79  Inferencing          : 0.27
% 4.47/1.79  Reduction            : 0.18
% 4.47/1.79  Demodulation         : 0.11
% 4.47/1.79  BG Simplification    : 0.03
% 4.47/1.79  Subsumption          : 0.16
% 4.47/1.79  Abstraction          : 0.03
% 4.47/1.79  MUC search           : 0.00
% 4.47/1.79  Cooper               : 0.00
% 4.47/1.79  Total                : 1.07
% 4.47/1.79  Index Insertion      : 0.00
% 4.47/1.79  Index Deletion       : 0.00
% 4.47/1.79  Index Matching       : 0.00
% 4.47/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
