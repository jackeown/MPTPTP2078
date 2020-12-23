%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:28 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 126 expanded)
%              Number of leaves         :   37 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 306 expanded)
%              Number of equality atoms :   29 (  64 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_114,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_8,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_70,plain,(
    ! [B_79,A_80] :
      ( v1_relat_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_58,c_70])).

tff(c_76,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_73])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_370,plain,(
    ! [A_152,B_153,D_154] :
      ( k1_funct_1(A_152,'#skF_4'(A_152,B_153,k9_relat_1(A_152,B_153),D_154)) = D_154
      | ~ r2_hidden(D_154,k9_relat_1(A_152,B_153))
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_60,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_84,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_88,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_84])).

tff(c_201,plain,(
    ! [B_115,A_116,C_117] :
      ( k1_xboole_0 = B_115
      | k1_relset_1(A_116,B_115,C_117) = A_116
      | ~ v1_funct_2(C_117,A_116,B_115)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_208,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_201])).

tff(c_212,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_88,c_208])).

tff(c_226,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_279,plain,(
    ! [A_134,B_135,D_136] :
      ( r2_hidden('#skF_4'(A_134,B_135,k9_relat_1(A_134,B_135),D_136),k1_relat_1(A_134))
      | ~ r2_hidden(D_136,k9_relat_1(A_134,B_135))
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_290,plain,(
    ! [B_135,D_136] :
      ( r2_hidden('#skF_4'('#skF_8',B_135,k9_relat_1('#skF_8',B_135),D_136),'#skF_5')
      | ~ r2_hidden(D_136,k9_relat_1('#skF_8',B_135))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_279])).

tff(c_296,plain,(
    ! [B_137,D_138] :
      ( r2_hidden('#skF_4'('#skF_8',B_137,k9_relat_1('#skF_8',B_137),D_138),'#skF_5')
      | ~ r2_hidden(D_138,k9_relat_1('#skF_8',B_137)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_62,c_290])).

tff(c_213,plain,(
    ! [A_118,B_119,D_120] :
      ( r2_hidden('#skF_4'(A_118,B_119,k9_relat_1(A_118,B_119),D_120),B_119)
      | ~ r2_hidden(D_120,k9_relat_1(A_118,B_119))
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,(
    ! [F_73] :
      ( k1_funct_1('#skF_8',F_73) != '#skF_9'
      | ~ r2_hidden(F_73,'#skF_7')
      | ~ r2_hidden(F_73,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_224,plain,(
    ! [A_118,D_120] :
      ( k1_funct_1('#skF_8','#skF_4'(A_118,'#skF_7',k9_relat_1(A_118,'#skF_7'),D_120)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_118,'#skF_7',k9_relat_1(A_118,'#skF_7'),D_120),'#skF_5')
      | ~ r2_hidden(D_120,k9_relat_1(A_118,'#skF_7'))
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(resolution,[status(thm)],[c_213,c_54])).

tff(c_300,plain,(
    ! [D_138] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_138)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_138,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_296,c_224])).

tff(c_308,plain,(
    ! [D_138] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_138)) != '#skF_9'
      | ~ r2_hidden(D_138,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_62,c_300])).

tff(c_380,plain,(
    ! [D_154] :
      ( D_154 != '#skF_9'
      | ~ r2_hidden(D_154,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_154,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_308])).

tff(c_391,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_62,c_380])).

tff(c_118,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k7_relset_1(A_95,B_96,C_97,D_98) = k9_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_125,plain,(
    ! [D_98] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_98) = k9_relat_1('#skF_8',D_98) ),
    inference(resolution,[status(thm)],[c_58,c_118])).

tff(c_56,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_128,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_56])).

tff(c_393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_128])).

tff(c_394,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_402,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_2])).

tff(c_89,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( m1_subset_1(k7_relset_1(A_90,B_91,C_92,D_93),k1_zfmisc_1(B_91))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_78,plain,(
    ! [C_82,A_83,B_84] :
      ( r2_hidden(C_82,A_83)
      | ~ r2_hidden(C_82,B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_81,plain,(
    ! [A_83] :
      ( r2_hidden('#skF_9',A_83)
      | ~ m1_subset_1(k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7'),k1_zfmisc_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_56,c_78])).

tff(c_97,plain,
    ( r2_hidden('#skF_9','#skF_6')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_89,c_81])).

tff(c_104,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_97])).

tff(c_34,plain,(
    ! [B_54,A_53] :
      ( ~ r1_tarski(B_54,A_53)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_112,plain,(
    ~ r1_tarski('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_104,c_34])).

tff(c_410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.39  
% 2.71/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.39  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.71/1.39  
% 2.71/1.39  %Foreground sorts:
% 2.71/1.39  
% 2.71/1.39  
% 2.71/1.39  %Background operators:
% 2.71/1.39  
% 2.71/1.39  
% 2.71/1.39  %Foreground operators:
% 2.71/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.71/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.71/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.71/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.39  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.71/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.71/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.71/1.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.71/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.71/1.39  tff('#skF_9', type, '#skF_9': $i).
% 2.71/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.71/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.71/1.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.71/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.71/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.71/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.39  
% 2.71/1.40  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.71/1.40  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 2.71/1.40  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.71/1.40  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 2.71/1.40  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.71/1.40  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.71/1.40  tff(f_77, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.71/1.40  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.71/1.40  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 2.71/1.40  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.71/1.40  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.71/1.40  tff(c_8, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.40  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.71/1.40  tff(c_70, plain, (![B_79, A_80]: (v1_relat_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.40  tff(c_73, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_70])).
% 2.71/1.40  tff(c_76, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_73])).
% 2.71/1.40  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.71/1.40  tff(c_370, plain, (![A_152, B_153, D_154]: (k1_funct_1(A_152, '#skF_4'(A_152, B_153, k9_relat_1(A_152, B_153), D_154))=D_154 | ~r2_hidden(D_154, k9_relat_1(A_152, B_153)) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.71/1.40  tff(c_60, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.71/1.40  tff(c_84, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.71/1.40  tff(c_88, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_84])).
% 2.71/1.40  tff(c_201, plain, (![B_115, A_116, C_117]: (k1_xboole_0=B_115 | k1_relset_1(A_116, B_115, C_117)=A_116 | ~v1_funct_2(C_117, A_116, B_115) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.71/1.40  tff(c_208, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_201])).
% 2.71/1.40  tff(c_212, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_88, c_208])).
% 2.71/1.40  tff(c_226, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_212])).
% 2.71/1.40  tff(c_279, plain, (![A_134, B_135, D_136]: (r2_hidden('#skF_4'(A_134, B_135, k9_relat_1(A_134, B_135), D_136), k1_relat_1(A_134)) | ~r2_hidden(D_136, k9_relat_1(A_134, B_135)) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.71/1.40  tff(c_290, plain, (![B_135, D_136]: (r2_hidden('#skF_4'('#skF_8', B_135, k9_relat_1('#skF_8', B_135), D_136), '#skF_5') | ~r2_hidden(D_136, k9_relat_1('#skF_8', B_135)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_226, c_279])).
% 2.71/1.40  tff(c_296, plain, (![B_137, D_138]: (r2_hidden('#skF_4'('#skF_8', B_137, k9_relat_1('#skF_8', B_137), D_138), '#skF_5') | ~r2_hidden(D_138, k9_relat_1('#skF_8', B_137)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_62, c_290])).
% 2.71/1.40  tff(c_213, plain, (![A_118, B_119, D_120]: (r2_hidden('#skF_4'(A_118, B_119, k9_relat_1(A_118, B_119), D_120), B_119) | ~r2_hidden(D_120, k9_relat_1(A_118, B_119)) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.71/1.40  tff(c_54, plain, (![F_73]: (k1_funct_1('#skF_8', F_73)!='#skF_9' | ~r2_hidden(F_73, '#skF_7') | ~r2_hidden(F_73, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.71/1.40  tff(c_224, plain, (![A_118, D_120]: (k1_funct_1('#skF_8', '#skF_4'(A_118, '#skF_7', k9_relat_1(A_118, '#skF_7'), D_120))!='#skF_9' | ~r2_hidden('#skF_4'(A_118, '#skF_7', k9_relat_1(A_118, '#skF_7'), D_120), '#skF_5') | ~r2_hidden(D_120, k9_relat_1(A_118, '#skF_7')) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(resolution, [status(thm)], [c_213, c_54])).
% 2.71/1.40  tff(c_300, plain, (![D_138]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_138))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_138, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_296, c_224])).
% 2.71/1.40  tff(c_308, plain, (![D_138]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_138))!='#skF_9' | ~r2_hidden(D_138, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_62, c_300])).
% 2.71/1.40  tff(c_380, plain, (![D_154]: (D_154!='#skF_9' | ~r2_hidden(D_154, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_154, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_370, c_308])).
% 2.71/1.40  tff(c_391, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_62, c_380])).
% 2.71/1.40  tff(c_118, plain, (![A_95, B_96, C_97, D_98]: (k7_relset_1(A_95, B_96, C_97, D_98)=k9_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.71/1.40  tff(c_125, plain, (![D_98]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_98)=k9_relat_1('#skF_8', D_98))), inference(resolution, [status(thm)], [c_58, c_118])).
% 2.71/1.40  tff(c_56, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.71/1.40  tff(c_128, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_56])).
% 2.71/1.40  tff(c_393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_391, c_128])).
% 2.71/1.40  tff(c_394, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_212])).
% 2.71/1.40  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.71/1.40  tff(c_402, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_394, c_2])).
% 2.71/1.40  tff(c_89, plain, (![A_90, B_91, C_92, D_93]: (m1_subset_1(k7_relset_1(A_90, B_91, C_92, D_93), k1_zfmisc_1(B_91)) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.71/1.40  tff(c_78, plain, (![C_82, A_83, B_84]: (r2_hidden(C_82, A_83) | ~r2_hidden(C_82, B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.71/1.40  tff(c_81, plain, (![A_83]: (r2_hidden('#skF_9', A_83) | ~m1_subset_1(k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'), k1_zfmisc_1(A_83)))), inference(resolution, [status(thm)], [c_56, c_78])).
% 2.71/1.40  tff(c_97, plain, (r2_hidden('#skF_9', '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_89, c_81])).
% 2.71/1.40  tff(c_104, plain, (r2_hidden('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_97])).
% 2.71/1.40  tff(c_34, plain, (![B_54, A_53]: (~r1_tarski(B_54, A_53) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.71/1.40  tff(c_112, plain, (~r1_tarski('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_104, c_34])).
% 2.71/1.40  tff(c_410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_402, c_112])).
% 2.71/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.40  
% 2.71/1.40  Inference rules
% 2.71/1.40  ----------------------
% 2.71/1.40  #Ref     : 0
% 2.71/1.40  #Sup     : 68
% 2.71/1.40  #Fact    : 0
% 2.71/1.40  #Define  : 0
% 2.71/1.40  #Split   : 3
% 2.71/1.40  #Chain   : 0
% 2.71/1.40  #Close   : 0
% 2.71/1.40  
% 2.71/1.40  Ordering : KBO
% 2.71/1.40  
% 2.71/1.40  Simplification rules
% 2.71/1.40  ----------------------
% 2.71/1.40  #Subsume      : 10
% 2.71/1.40  #Demod        : 44
% 2.71/1.40  #Tautology    : 14
% 2.71/1.40  #SimpNegUnit  : 2
% 2.71/1.40  #BackRed      : 14
% 2.71/1.40  
% 2.71/1.40  #Partial instantiations: 0
% 2.71/1.40  #Strategies tried      : 1
% 2.71/1.40  
% 2.71/1.40  Timing (in seconds)
% 2.71/1.40  ----------------------
% 2.71/1.41  Preprocessing        : 0.35
% 2.71/1.41  Parsing              : 0.17
% 2.71/1.41  CNF conversion       : 0.03
% 2.71/1.41  Main loop            : 0.29
% 2.71/1.41  Inferencing          : 0.10
% 2.71/1.41  Reduction            : 0.09
% 2.71/1.41  Demodulation         : 0.06
% 2.71/1.41  BG Simplification    : 0.02
% 2.71/1.41  Subsumption          : 0.06
% 2.71/1.41  Abstraction          : 0.02
% 2.71/1.41  MUC search           : 0.00
% 2.71/1.41  Cooper               : 0.00
% 2.71/1.41  Total                : 0.67
% 2.71/1.41  Index Insertion      : 0.00
% 2.71/1.41  Index Deletion       : 0.00
% 2.71/1.41  Index Matching       : 0.00
% 2.71/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
