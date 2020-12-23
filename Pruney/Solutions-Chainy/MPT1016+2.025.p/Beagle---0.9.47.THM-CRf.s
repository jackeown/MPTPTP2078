%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:44 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 374 expanded)
%              Number of leaves         :   33 ( 146 expanded)
%              Depth                    :   11
%              Number of atoms          :  192 (1232 expanded)
%              Number of equality atoms :   69 ( 442 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_129,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_91,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_7')) ),
    inference(resolution,[status(thm)],[c_62,c_91])).

tff(c_97,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_94])).

tff(c_66,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_98,plain,(
    ! [A_49] :
      ( '#skF_2'(A_49) != '#skF_1'(A_49)
      | v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,
    ( '#skF_10' != '#skF_9'
    | ~ v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_87,plain,(
    ~ v2_funct_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_101,plain,
    ( '#skF_2'('#skF_8') != '#skF_1'('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_98,c_87])).

tff(c_104,plain,(
    '#skF_2'('#skF_8') != '#skF_1'('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_66,c_101])).

tff(c_64,plain,(
    v1_funct_2('#skF_8','#skF_7','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_107,plain,(
    ! [A_52,B_53,C_54] :
      ( k1_relset_1(A_52,B_53,C_54) = k1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_111,plain,(
    k1_relset_1('#skF_7','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_107])).

tff(c_178,plain,(
    ! [B_71,A_72,C_73] :
      ( k1_xboole_0 = B_71
      | k1_relset_1(A_72,B_71,C_73) = A_72
      | ~ v1_funct_2(C_73,A_72,B_71)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_181,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_7','#skF_7','#skF_8') = '#skF_7'
    | ~ v1_funct_2('#skF_8','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_178])).

tff(c_184,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_111,c_181])).

tff(c_185,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_14,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_1'(A_6),k1_relat_1(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_199,plain,
    ( r2_hidden('#skF_1'('#skF_8'),'#skF_7')
    | v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_14])).

tff(c_206,plain,
    ( r2_hidden('#skF_1'('#skF_8'),'#skF_7')
    | v2_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_66,c_199])).

tff(c_207,plain,(
    r2_hidden('#skF_1'('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_206])).

tff(c_12,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),k1_relat_1(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_202,plain,
    ( r2_hidden('#skF_2'('#skF_8'),'#skF_7')
    | v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_12])).

tff(c_209,plain,
    ( r2_hidden('#skF_2'('#skF_8'),'#skF_7')
    | v2_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_66,c_202])).

tff(c_210,plain,(
    r2_hidden('#skF_2'('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_209])).

tff(c_123,plain,(
    ! [A_58] :
      ( k1_funct_1(A_58,'#skF_2'(A_58)) = k1_funct_1(A_58,'#skF_1'(A_58))
      | v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_86,plain,(
    ! [D_42,C_41] :
      ( v2_funct_1('#skF_8')
      | D_42 = C_41
      | k1_funct_1('#skF_8',D_42) != k1_funct_1('#skF_8',C_41)
      | ~ r2_hidden(D_42,'#skF_7')
      | ~ r2_hidden(C_41,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_116,plain,(
    ! [D_42,C_41] :
      ( D_42 = C_41
      | k1_funct_1('#skF_8',D_42) != k1_funct_1('#skF_8',C_41)
      | ~ r2_hidden(D_42,'#skF_7')
      | ~ r2_hidden(C_41,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_86])).

tff(c_132,plain,(
    ! [D_42] :
      ( D_42 = '#skF_2'('#skF_8')
      | k1_funct_1('#skF_8',D_42) != k1_funct_1('#skF_8','#skF_1'('#skF_8'))
      | ~ r2_hidden(D_42,'#skF_7')
      | ~ r2_hidden('#skF_2'('#skF_8'),'#skF_7')
      | v2_funct_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_116])).

tff(c_141,plain,(
    ! [D_42] :
      ( D_42 = '#skF_2'('#skF_8')
      | k1_funct_1('#skF_8',D_42) != k1_funct_1('#skF_8','#skF_1'('#skF_8'))
      | ~ r2_hidden(D_42,'#skF_7')
      | ~ r2_hidden('#skF_2'('#skF_8'),'#skF_7')
      | v2_funct_1('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_66,c_132])).

tff(c_142,plain,(
    ! [D_42] :
      ( D_42 = '#skF_2'('#skF_8')
      | k1_funct_1('#skF_8',D_42) != k1_funct_1('#skF_8','#skF_1'('#skF_8'))
      | ~ r2_hidden(D_42,'#skF_7')
      | ~ r2_hidden('#skF_2'('#skF_8'),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_141])).

tff(c_217,plain,(
    ! [D_42] :
      ( D_42 = '#skF_2'('#skF_8')
      | k1_funct_1('#skF_8',D_42) != k1_funct_1('#skF_8','#skF_1'('#skF_8'))
      | ~ r2_hidden(D_42,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_142])).

tff(c_220,plain,
    ( '#skF_2'('#skF_8') = '#skF_1'('#skF_8')
    | ~ r2_hidden('#skF_1'('#skF_8'),'#skF_7') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_217])).

tff(c_222,plain,(
    '#skF_2'('#skF_8') = '#skF_1'('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_220])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_222])).

tff(c_226,plain,(
    k1_relat_1('#skF_8') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_225,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_58,plain,(
    ! [B_35,C_36] :
      ( k1_relset_1(k1_xboole_0,B_35,C_36) = k1_xboole_0
      | ~ v1_funct_2(C_36,k1_xboole_0,B_35)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_255,plain,(
    ! [B_83,C_84] :
      ( k1_relset_1('#skF_7',B_83,C_84) = '#skF_7'
      | ~ v1_funct_2(C_84,'#skF_7',B_83)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_83))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_225,c_225,c_225,c_58])).

tff(c_258,plain,
    ( k1_relset_1('#skF_7','#skF_7','#skF_8') = '#skF_7'
    | ~ v1_funct_2('#skF_8','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_255])).

tff(c_261,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_111,c_258])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_261])).

tff(c_264,plain,(
    '#skF_10' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_265,plain,(
    v2_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_74,plain,
    ( r2_hidden('#skF_9','#skF_7')
    | ~ v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_270,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_74])).

tff(c_273,plain,(
    ! [B_89,A_90] :
      ( v1_relat_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90))
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_276,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_7')) ),
    inference(resolution,[status(thm)],[c_62,c_273])).

tff(c_279,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_276])).

tff(c_289,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_relset_1(A_94,B_95,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_293,plain,(
    k1_relset_1('#skF_7','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_289])).

tff(c_325,plain,(
    ! [B_109,A_110,C_111] :
      ( k1_xboole_0 = B_109
      | k1_relset_1(A_110,B_109,C_111) = A_110
      | ~ v1_funct_2(C_111,A_110,B_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_328,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_7','#skF_7','#skF_8') = '#skF_7'
    | ~ v1_funct_2('#skF_8','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_325])).

tff(c_331,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_293,c_328])).

tff(c_332,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_72,plain,
    ( r2_hidden('#skF_10','#skF_7')
    | ~ v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_268,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_72])).

tff(c_70,plain,
    ( k1_funct_1('#skF_8','#skF_10') = k1_funct_1('#skF_8','#skF_9')
    | ~ v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_281,plain,(
    k1_funct_1('#skF_8','#skF_10') = k1_funct_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_70])).

tff(c_388,plain,(
    ! [C_118,B_119,A_120] :
      ( C_118 = B_119
      | k1_funct_1(A_120,C_118) != k1_funct_1(A_120,B_119)
      | ~ r2_hidden(C_118,k1_relat_1(A_120))
      | ~ r2_hidden(B_119,k1_relat_1(A_120))
      | ~ v2_funct_1(A_120)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_394,plain,(
    ! [B_119] :
      ( B_119 = '#skF_10'
      | k1_funct_1('#skF_8',B_119) != k1_funct_1('#skF_8','#skF_9')
      | ~ r2_hidden('#skF_10',k1_relat_1('#skF_8'))
      | ~ r2_hidden(B_119,k1_relat_1('#skF_8'))
      | ~ v2_funct_1('#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_388])).

tff(c_401,plain,(
    ! [B_121] :
      ( B_121 = '#skF_10'
      | k1_funct_1('#skF_8',B_121) != k1_funct_1('#skF_8','#skF_9')
      | ~ r2_hidden(B_121,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_66,c_265,c_332,c_268,c_332,c_394])).

tff(c_404,plain,(
    '#skF_10' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_270,c_401])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_404])).

tff(c_413,plain,(
    k1_relat_1('#skF_8') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_412,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_454,plain,(
    ! [B_127,C_128] :
      ( k1_relset_1('#skF_7',B_127,C_128) = '#skF_7'
      | ~ v1_funct_2(C_128,'#skF_7',B_127)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_127))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_412,c_412,c_412,c_58])).

tff(c_457,plain,
    ( k1_relset_1('#skF_7','#skF_7','#skF_8') = '#skF_7'
    | ~ v1_funct_2('#skF_8','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_454])).

tff(c_460,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_293,c_457])).

tff(c_462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:55:11 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.43  
% 2.83/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.43  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 2.83/1.43  
% 2.83/1.43  %Foreground sorts:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Background operators:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Foreground operators:
% 2.83/1.43  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.83/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.83/1.43  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.83/1.43  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.83/1.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.83/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.83/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.83/1.43  tff('#skF_10', type, '#skF_10': $i).
% 2.83/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.83/1.43  tff('#skF_9', type, '#skF_9': $i).
% 2.83/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.83/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.83/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.43  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.83/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.83/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.43  
% 2.83/1.45  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.83/1.45  tff(f_129, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 2.83/1.45  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.83/1.45  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 2.83/1.45  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.83/1.45  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.83/1.45  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.83/1.45  tff(c_62, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.83/1.45  tff(c_91, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.45  tff(c_94, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_91])).
% 2.83/1.45  tff(c_97, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_94])).
% 2.83/1.45  tff(c_66, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.83/1.45  tff(c_98, plain, (![A_49]: ('#skF_2'(A_49)!='#skF_1'(A_49) | v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.45  tff(c_68, plain, ('#skF_10'!='#skF_9' | ~v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.83/1.45  tff(c_87, plain, (~v2_funct_1('#skF_8')), inference(splitLeft, [status(thm)], [c_68])).
% 2.83/1.45  tff(c_101, plain, ('#skF_2'('#skF_8')!='#skF_1'('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_98, c_87])).
% 2.83/1.45  tff(c_104, plain, ('#skF_2'('#skF_8')!='#skF_1'('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_66, c_101])).
% 2.83/1.45  tff(c_64, plain, (v1_funct_2('#skF_8', '#skF_7', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.83/1.45  tff(c_107, plain, (![A_52, B_53, C_54]: (k1_relset_1(A_52, B_53, C_54)=k1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.45  tff(c_111, plain, (k1_relset_1('#skF_7', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_107])).
% 2.83/1.45  tff(c_178, plain, (![B_71, A_72, C_73]: (k1_xboole_0=B_71 | k1_relset_1(A_72, B_71, C_73)=A_72 | ~v1_funct_2(C_73, A_72, B_71) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.83/1.45  tff(c_181, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_7', '#skF_7', '#skF_8')='#skF_7' | ~v1_funct_2('#skF_8', '#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_178])).
% 2.83/1.45  tff(c_184, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_111, c_181])).
% 2.83/1.45  tff(c_185, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(splitLeft, [status(thm)], [c_184])).
% 2.83/1.45  tff(c_14, plain, (![A_6]: (r2_hidden('#skF_1'(A_6), k1_relat_1(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.45  tff(c_199, plain, (r2_hidden('#skF_1'('#skF_8'), '#skF_7') | v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_185, c_14])).
% 2.83/1.45  tff(c_206, plain, (r2_hidden('#skF_1'('#skF_8'), '#skF_7') | v2_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_66, c_199])).
% 2.83/1.45  tff(c_207, plain, (r2_hidden('#skF_1'('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_87, c_206])).
% 2.83/1.45  tff(c_12, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), k1_relat_1(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.45  tff(c_202, plain, (r2_hidden('#skF_2'('#skF_8'), '#skF_7') | v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_185, c_12])).
% 2.83/1.45  tff(c_209, plain, (r2_hidden('#skF_2'('#skF_8'), '#skF_7') | v2_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_66, c_202])).
% 2.83/1.45  tff(c_210, plain, (r2_hidden('#skF_2'('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_87, c_209])).
% 2.83/1.45  tff(c_123, plain, (![A_58]: (k1_funct_1(A_58, '#skF_2'(A_58))=k1_funct_1(A_58, '#skF_1'(A_58)) | v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.45  tff(c_86, plain, (![D_42, C_41]: (v2_funct_1('#skF_8') | D_42=C_41 | k1_funct_1('#skF_8', D_42)!=k1_funct_1('#skF_8', C_41) | ~r2_hidden(D_42, '#skF_7') | ~r2_hidden(C_41, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.83/1.45  tff(c_116, plain, (![D_42, C_41]: (D_42=C_41 | k1_funct_1('#skF_8', D_42)!=k1_funct_1('#skF_8', C_41) | ~r2_hidden(D_42, '#skF_7') | ~r2_hidden(C_41, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_87, c_86])).
% 2.83/1.45  tff(c_132, plain, (![D_42]: (D_42='#skF_2'('#skF_8') | k1_funct_1('#skF_8', D_42)!=k1_funct_1('#skF_8', '#skF_1'('#skF_8')) | ~r2_hidden(D_42, '#skF_7') | ~r2_hidden('#skF_2'('#skF_8'), '#skF_7') | v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_116])).
% 2.83/1.45  tff(c_141, plain, (![D_42]: (D_42='#skF_2'('#skF_8') | k1_funct_1('#skF_8', D_42)!=k1_funct_1('#skF_8', '#skF_1'('#skF_8')) | ~r2_hidden(D_42, '#skF_7') | ~r2_hidden('#skF_2'('#skF_8'), '#skF_7') | v2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_66, c_132])).
% 2.83/1.45  tff(c_142, plain, (![D_42]: (D_42='#skF_2'('#skF_8') | k1_funct_1('#skF_8', D_42)!=k1_funct_1('#skF_8', '#skF_1'('#skF_8')) | ~r2_hidden(D_42, '#skF_7') | ~r2_hidden('#skF_2'('#skF_8'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_87, c_141])).
% 2.83/1.45  tff(c_217, plain, (![D_42]: (D_42='#skF_2'('#skF_8') | k1_funct_1('#skF_8', D_42)!=k1_funct_1('#skF_8', '#skF_1'('#skF_8')) | ~r2_hidden(D_42, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_142])).
% 2.83/1.45  tff(c_220, plain, ('#skF_2'('#skF_8')='#skF_1'('#skF_8') | ~r2_hidden('#skF_1'('#skF_8'), '#skF_7')), inference(reflexivity, [status(thm), theory('equality')], [c_217])).
% 2.83/1.45  tff(c_222, plain, ('#skF_2'('#skF_8')='#skF_1'('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_220])).
% 2.83/1.45  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_222])).
% 2.83/1.45  tff(c_226, plain, (k1_relat_1('#skF_8')!='#skF_7'), inference(splitRight, [status(thm)], [c_184])).
% 2.83/1.45  tff(c_225, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_184])).
% 2.83/1.45  tff(c_58, plain, (![B_35, C_36]: (k1_relset_1(k1_xboole_0, B_35, C_36)=k1_xboole_0 | ~v1_funct_2(C_36, k1_xboole_0, B_35) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_35))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.83/1.45  tff(c_255, plain, (![B_83, C_84]: (k1_relset_1('#skF_7', B_83, C_84)='#skF_7' | ~v1_funct_2(C_84, '#skF_7', B_83) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_83))))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_225, c_225, c_225, c_58])).
% 2.83/1.45  tff(c_258, plain, (k1_relset_1('#skF_7', '#skF_7', '#skF_8')='#skF_7' | ~v1_funct_2('#skF_8', '#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_255])).
% 2.83/1.45  tff(c_261, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_111, c_258])).
% 2.83/1.45  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_261])).
% 2.83/1.45  tff(c_264, plain, ('#skF_10'!='#skF_9'), inference(splitRight, [status(thm)], [c_68])).
% 2.83/1.45  tff(c_265, plain, (v2_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_68])).
% 2.83/1.45  tff(c_74, plain, (r2_hidden('#skF_9', '#skF_7') | ~v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.83/1.45  tff(c_270, plain, (r2_hidden('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_74])).
% 2.83/1.45  tff(c_273, plain, (![B_89, A_90]: (v1_relat_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.45  tff(c_276, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_273])).
% 2.83/1.45  tff(c_279, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_276])).
% 2.83/1.45  tff(c_289, plain, (![A_94, B_95, C_96]: (k1_relset_1(A_94, B_95, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.45  tff(c_293, plain, (k1_relset_1('#skF_7', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_289])).
% 2.83/1.45  tff(c_325, plain, (![B_109, A_110, C_111]: (k1_xboole_0=B_109 | k1_relset_1(A_110, B_109, C_111)=A_110 | ~v1_funct_2(C_111, A_110, B_109) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.83/1.45  tff(c_328, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_7', '#skF_7', '#skF_8')='#skF_7' | ~v1_funct_2('#skF_8', '#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_325])).
% 2.83/1.45  tff(c_331, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_293, c_328])).
% 2.83/1.45  tff(c_332, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(splitLeft, [status(thm)], [c_331])).
% 2.83/1.45  tff(c_72, plain, (r2_hidden('#skF_10', '#skF_7') | ~v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.83/1.45  tff(c_268, plain, (r2_hidden('#skF_10', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_72])).
% 2.83/1.45  tff(c_70, plain, (k1_funct_1('#skF_8', '#skF_10')=k1_funct_1('#skF_8', '#skF_9') | ~v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.83/1.45  tff(c_281, plain, (k1_funct_1('#skF_8', '#skF_10')=k1_funct_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_70])).
% 2.83/1.45  tff(c_388, plain, (![C_118, B_119, A_120]: (C_118=B_119 | k1_funct_1(A_120, C_118)!=k1_funct_1(A_120, B_119) | ~r2_hidden(C_118, k1_relat_1(A_120)) | ~r2_hidden(B_119, k1_relat_1(A_120)) | ~v2_funct_1(A_120) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.45  tff(c_394, plain, (![B_119]: (B_119='#skF_10' | k1_funct_1('#skF_8', B_119)!=k1_funct_1('#skF_8', '#skF_9') | ~r2_hidden('#skF_10', k1_relat_1('#skF_8')) | ~r2_hidden(B_119, k1_relat_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_281, c_388])).
% 2.83/1.45  tff(c_401, plain, (![B_121]: (B_121='#skF_10' | k1_funct_1('#skF_8', B_121)!=k1_funct_1('#skF_8', '#skF_9') | ~r2_hidden(B_121, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_66, c_265, c_332, c_268, c_332, c_394])).
% 2.83/1.45  tff(c_404, plain, ('#skF_10'='#skF_9'), inference(resolution, [status(thm)], [c_270, c_401])).
% 2.83/1.45  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_264, c_404])).
% 2.83/1.45  tff(c_413, plain, (k1_relat_1('#skF_8')!='#skF_7'), inference(splitRight, [status(thm)], [c_331])).
% 2.83/1.45  tff(c_412, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_331])).
% 2.83/1.45  tff(c_454, plain, (![B_127, C_128]: (k1_relset_1('#skF_7', B_127, C_128)='#skF_7' | ~v1_funct_2(C_128, '#skF_7', B_127) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_127))))), inference(demodulation, [status(thm), theory('equality')], [c_412, c_412, c_412, c_412, c_58])).
% 2.83/1.45  tff(c_457, plain, (k1_relset_1('#skF_7', '#skF_7', '#skF_8')='#skF_7' | ~v1_funct_2('#skF_8', '#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_454])).
% 2.83/1.45  tff(c_460, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_293, c_457])).
% 2.83/1.45  tff(c_462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_413, c_460])).
% 2.83/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.45  
% 2.83/1.45  Inference rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Ref     : 5
% 2.83/1.45  #Sup     : 70
% 2.83/1.45  #Fact    : 0
% 2.83/1.45  #Define  : 0
% 2.83/1.45  #Split   : 3
% 2.83/1.45  #Chain   : 0
% 2.83/1.45  #Close   : 0
% 2.83/1.45  
% 2.83/1.45  Ordering : KBO
% 2.83/1.45  
% 2.83/1.45  Simplification rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Subsume      : 14
% 2.83/1.45  #Demod        : 99
% 2.83/1.45  #Tautology    : 51
% 2.83/1.45  #SimpNegUnit  : 9
% 2.83/1.45  #BackRed      : 14
% 2.83/1.45  
% 2.83/1.45  #Partial instantiations: 0
% 2.83/1.45  #Strategies tried      : 1
% 2.83/1.45  
% 2.83/1.45  Timing (in seconds)
% 2.83/1.45  ----------------------
% 2.83/1.45  Preprocessing        : 0.38
% 2.83/1.46  Parsing              : 0.18
% 2.83/1.46  CNF conversion       : 0.03
% 2.83/1.46  Main loop            : 0.31
% 2.83/1.46  Inferencing          : 0.10
% 2.83/1.46  Reduction            : 0.09
% 2.83/1.46  Demodulation         : 0.07
% 2.83/1.46  BG Simplification    : 0.03
% 2.83/1.46  Subsumption          : 0.06
% 2.83/1.46  Abstraction          : 0.02
% 2.83/1.46  MUC search           : 0.00
% 2.83/1.46  Cooper               : 0.00
% 2.83/1.46  Total                : 0.73
% 2.83/1.46  Index Insertion      : 0.00
% 2.83/1.46  Index Deletion       : 0.00
% 2.83/1.46  Index Matching       : 0.00
% 2.83/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
