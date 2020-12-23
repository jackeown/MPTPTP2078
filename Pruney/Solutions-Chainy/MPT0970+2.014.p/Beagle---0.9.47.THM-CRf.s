%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:20 EST 2020

% Result     : Theorem 10.68s
% Output     : CNFRefutation 11.50s
% Verified   : 
% Statistics : Number of formulae       :  697 (19243 expanded)
%              Number of leaves         :   38 (6538 expanded)
%              Depth                    :   47
%              Number of atoms          : 2037 (62228 expanded)
%              Number of equality atoms :  485 (18067 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
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

tff(f_55,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_141,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_145,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_141])).

tff(c_54,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_146,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_54])).

tff(c_84,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_84])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_101,plain,(
    ! [C_85,B_86,A_87] :
      ( v5_relat_1(C_85,B_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_105,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_101])).

tff(c_62,plain,(
    ! [D_67] :
      ( k1_funct_1('#skF_8','#skF_9'(D_67)) = D_67
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_68,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73,B_74),A_73)
      | r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [A_73] : r1_tarski(A_73,A_73) ),
    inference(resolution,[status(thm)],[c_68,c_4])).

tff(c_58,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_64,plain,(
    ! [D_67] :
      ( r2_hidden('#skF_9'(D_67),'#skF_6')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_106,plain,(
    ! [C_88,B_89,A_90] :
      ( r2_hidden(C_88,B_89)
      | ~ r2_hidden(C_88,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_112,plain,(
    ! [D_67,B_89] :
      ( r2_hidden('#skF_9'(D_67),B_89)
      | ~ r1_tarski('#skF_6',B_89)
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_106])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [A_96,B_97,B_98] :
      ( r2_hidden('#skF_1'(A_96,B_97),B_98)
      | ~ r1_tarski(A_96,B_98)
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5170,plain,(
    ! [A_628,B_629,B_630,B_631] :
      ( r2_hidden('#skF_1'(A_628,B_629),B_630)
      | ~ r1_tarski(B_631,B_630)
      | ~ r1_tarski(A_628,B_631)
      | r1_tarski(A_628,B_629) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_5764,plain,(
    ! [A_713,B_714,A_715,B_716] :
      ( r2_hidden('#skF_1'(A_713,B_714),A_715)
      | ~ r1_tarski(A_713,k2_relat_1(B_716))
      | r1_tarski(A_713,B_714)
      | ~ v5_relat_1(B_716,A_715)
      | ~ v1_relat_1(B_716) ) ),
    inference(resolution,[status(thm)],[c_12,c_5170])).

tff(c_5792,plain,(
    ! [B_717,B_718,A_719] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_717),B_718),A_719)
      | r1_tarski(k2_relat_1(B_717),B_718)
      | ~ v5_relat_1(B_717,A_719)
      | ~ v1_relat_1(B_717) ) ),
    inference(resolution,[status(thm)],[c_73,c_5764])).

tff(c_132,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_136,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_132])).

tff(c_257,plain,(
    ! [B_144,A_145,C_146] :
      ( k1_xboole_0 = B_144
      | k1_relset_1(A_145,B_144,C_146) = A_145
      | ~ v1_funct_2(C_146,A_145,B_144)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_145,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_260,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_257])).

tff(c_263,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_136,c_260])).

tff(c_264,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_162,plain,(
    ! [A_109,D_110] :
      ( r2_hidden(k1_funct_1(A_109,D_110),k2_relat_1(A_109))
      | ~ r2_hidden(D_110,k1_relat_1(A_109))
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_167,plain,(
    ! [D_67] :
      ( r2_hidden(D_67,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_162])).

tff(c_171,plain,(
    ! [D_111] :
      ( r2_hidden(D_111,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_111),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_111,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_167])).

tff(c_176,plain,(
    ! [D_67] :
      ( r2_hidden(D_67,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_112,c_171])).

tff(c_177,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_265,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_177])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_265])).

tff(c_271,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_179,plain,(
    ! [A_114,B_115,B_116,B_117] :
      ( r2_hidden('#skF_1'(A_114,B_115),B_116)
      | ~ r1_tarski(B_117,B_116)
      | ~ r1_tarski(A_114,B_117)
      | r1_tarski(A_114,B_115) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_189,plain,(
    ! [A_118,B_119,A_120] :
      ( r2_hidden('#skF_1'(A_118,B_119),A_120)
      | ~ r1_tarski(A_118,k1_xboole_0)
      | r1_tarski(A_118,B_119) ) ),
    inference(resolution,[status(thm)],[c_8,c_179])).

tff(c_198,plain,(
    ! [A_121,A_122] :
      ( ~ r1_tarski(A_121,k1_xboole_0)
      | r1_tarski(A_121,A_122) ) ),
    inference(resolution,[status(thm)],[c_189,c_4])).

tff(c_214,plain,(
    ! [B_126,A_127] :
      ( r1_tarski(k2_relat_1(B_126),A_127)
      | ~ v5_relat_1(B_126,k1_xboole_0)
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_12,c_198])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( v5_relat_1(B_8,A_7)
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_228,plain,(
    ! [B_126,A_127] :
      ( v5_relat_1(B_126,A_127)
      | ~ v5_relat_1(B_126,k1_xboole_0)
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_214,c_10])).

tff(c_318,plain,(
    ! [B_152,A_153] :
      ( v5_relat_1(B_152,A_153)
      | ~ v5_relat_1(B_152,'#skF_7')
      | ~ v1_relat_1(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_228])).

tff(c_320,plain,(
    ! [A_153] :
      ( v5_relat_1('#skF_8',A_153)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_105,c_318])).

tff(c_323,plain,(
    ! [A_153] : v5_relat_1('#skF_8',A_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_320])).

tff(c_44,plain,(
    ! [C_63,A_61] :
      ( k1_xboole_0 = C_63
      | ~ v1_funct_2(C_63,A_61,k1_xboole_0)
      | k1_xboole_0 = A_61
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_364,plain,(
    ! [C_161,A_162] :
      ( C_161 = '#skF_7'
      | ~ v1_funct_2(C_161,A_162,'#skF_7')
      | A_162 = '#skF_7'
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_162,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_271,c_271,c_271,c_44])).

tff(c_367,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_56,c_364])).

tff(c_370,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_367])).

tff(c_371,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_370])).

tff(c_118,plain,(
    ! [D_94,B_95] :
      ( r2_hidden('#skF_9'(D_94),B_95)
      | ~ r1_tarski('#skF_6',B_95)
      | ~ r2_hidden(D_94,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_106])).

tff(c_151,plain,(
    ! [D_106,B_107,B_108] :
      ( r2_hidden('#skF_9'(D_106),B_107)
      | ~ r1_tarski(B_108,B_107)
      | ~ r1_tarski('#skF_6',B_108)
      | ~ r2_hidden(D_106,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_160,plain,(
    ! [D_106,A_6] :
      ( r2_hidden('#skF_9'(D_106),A_6)
      | ~ r1_tarski('#skF_6',k1_xboole_0)
      | ~ r2_hidden(D_106,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8,c_151])).

tff(c_161,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_282,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_161])).

tff(c_378,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_282])).

tff(c_394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_378])).

tff(c_395,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_370])).

tff(c_409,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_146])).

tff(c_284,plain,(
    ! [A_6] : r1_tarski('#skF_7',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_8])).

tff(c_404,plain,(
    ! [A_6] : r1_tarski('#skF_8',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_284])).

tff(c_289,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_3'(A_147,B_148),k1_relat_1(A_147))
      | r2_hidden('#skF_4'(A_147,B_148),B_148)
      | k2_relat_1(A_147) = B_148
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_294,plain,(
    ! [A_147,B_148,B_2] :
      ( r2_hidden('#skF_3'(A_147,B_148),B_2)
      | ~ r1_tarski(k1_relat_1(A_147),B_2)
      | r2_hidden('#skF_4'(A_147,B_148),B_148)
      | k2_relat_1(A_147) = B_148
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(resolution,[status(thm)],[c_289,c_2])).

tff(c_348,plain,(
    ! [A_158,B_159] :
      ( k1_funct_1(A_158,'#skF_3'(A_158,B_159)) = '#skF_2'(A_158,B_159)
      | r2_hidden('#skF_4'(A_158,B_159),B_159)
      | k2_relat_1(A_158) = B_159
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_9,D_48] :
      ( r2_hidden(k1_funct_1(A_9,D_48),k2_relat_1(A_9))
      | ~ r2_hidden(D_48,k1_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_859,plain,(
    ! [A_262,B_263] :
      ( r2_hidden('#skF_2'(A_262,B_263),k2_relat_1(A_262))
      | ~ r2_hidden('#skF_3'(A_262,B_263),k1_relat_1(A_262))
      | ~ v1_funct_1(A_262)
      | ~ v1_relat_1(A_262)
      | r2_hidden('#skF_4'(A_262,B_263),B_263)
      | k2_relat_1(A_262) = B_263
      | ~ v1_funct_1(A_262)
      | ~ v1_relat_1(A_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_14])).

tff(c_862,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_2'(A_147,B_148),k2_relat_1(A_147))
      | ~ r1_tarski(k1_relat_1(A_147),k1_relat_1(A_147))
      | r2_hidden('#skF_4'(A_147,B_148),B_148)
      | k2_relat_1(A_147) = B_148
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(resolution,[status(thm)],[c_294,c_859])).

tff(c_869,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_2'(A_147,B_148),k2_relat_1(A_147))
      | r2_hidden('#skF_4'(A_147,B_148),B_148)
      | k2_relat_1(A_147) = B_148
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_862])).

tff(c_244,plain,(
    ! [A_136,C_137] :
      ( r2_hidden('#skF_5'(A_136,k2_relat_1(A_136),C_137),k1_relat_1(A_136))
      | ~ r2_hidden(C_137,k2_relat_1(A_136))
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_247,plain,(
    ! [A_136,C_137,B_2] :
      ( r2_hidden('#skF_5'(A_136,k2_relat_1(A_136),C_137),B_2)
      | ~ r1_tarski(k1_relat_1(A_136),B_2)
      | ~ r2_hidden(C_137,k2_relat_1(A_136))
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(resolution,[status(thm)],[c_244,c_2])).

tff(c_16,plain,(
    ! [A_9,C_45] :
      ( k1_funct_1(A_9,'#skF_5'(A_9,k2_relat_1(A_9),C_45)) = C_45
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_634,plain,(
    ! [A_211,B_212,A_213,B_214] :
      ( r2_hidden('#skF_1'(A_211,B_212),A_213)
      | ~ r1_tarski(A_211,k2_relat_1(B_214))
      | r1_tarski(A_211,B_212)
      | ~ v5_relat_1(B_214,A_213)
      | ~ v1_relat_1(B_214) ) ),
    inference(resolution,[status(thm)],[c_12,c_179])).

tff(c_778,plain,(
    ! [B_247,B_248,A_249,B_250] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_247),B_248),A_249)
      | r1_tarski(k2_relat_1(B_247),B_248)
      | ~ v5_relat_1(B_250,A_249)
      | ~ v1_relat_1(B_250)
      | ~ v5_relat_1(B_247,k2_relat_1(B_250))
      | ~ v1_relat_1(B_247) ) ),
    inference(resolution,[status(thm)],[c_12,c_634])).

tff(c_780,plain,(
    ! [B_247,B_248,A_153] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_247),B_248),A_153)
      | r1_tarski(k2_relat_1(B_247),B_248)
      | ~ v1_relat_1('#skF_8')
      | ~ v5_relat_1(B_247,k2_relat_1('#skF_8'))
      | ~ v1_relat_1(B_247) ) ),
    inference(resolution,[status(thm)],[c_323,c_778])).

tff(c_787,plain,(
    ! [B_251,B_252,A_253] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_251),B_252),A_253)
      | r1_tarski(k2_relat_1(B_251),B_252)
      | ~ v5_relat_1(B_251,k2_relat_1('#skF_8'))
      | ~ v1_relat_1(B_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_780])).

tff(c_796,plain,(
    ! [B_254,A_255] :
      ( r1_tarski(k2_relat_1(B_254),A_255)
      | ~ v5_relat_1(B_254,k2_relat_1('#skF_8'))
      | ~ v1_relat_1(B_254) ) ),
    inference(resolution,[status(thm)],[c_787,c_4])).

tff(c_799,plain,(
    ! [A_255] :
      ( r1_tarski(k2_relat_1('#skF_8'),A_255)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_323,c_796])).

tff(c_805,plain,(
    ! [A_255] : r1_tarski(k2_relat_1('#skF_8'),A_255) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_799])).

tff(c_814,plain,(
    ! [A_258] : r1_tarski(k2_relat_1('#skF_8'),A_258) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_799])).

tff(c_579,plain,(
    ! [A_198,D_199,B_200] :
      ( r2_hidden(k1_funct_1(A_198,D_199),B_200)
      | ~ r1_tarski(k2_relat_1(A_198),B_200)
      | ~ r2_hidden(D_199,k1_relat_1(A_198))
      | ~ v1_funct_1(A_198)
      | ~ v1_relat_1(A_198) ) ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_591,plain,(
    ! [A_198,D_199,B_2,B_200] :
      ( r2_hidden(k1_funct_1(A_198,D_199),B_2)
      | ~ r1_tarski(B_200,B_2)
      | ~ r1_tarski(k2_relat_1(A_198),B_200)
      | ~ r2_hidden(D_199,k1_relat_1(A_198))
      | ~ v1_funct_1(A_198)
      | ~ v1_relat_1(A_198) ) ),
    inference(resolution,[status(thm)],[c_579,c_2])).

tff(c_919,plain,(
    ! [A_269,D_270,A_271] :
      ( r2_hidden(k1_funct_1(A_269,D_270),A_271)
      | ~ r1_tarski(k2_relat_1(A_269),k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_270,k1_relat_1(A_269))
      | ~ v1_funct_1(A_269)
      | ~ v1_relat_1(A_269) ) ),
    inference(resolution,[status(thm)],[c_814,c_591])).

tff(c_922,plain,(
    ! [D_270,A_271] :
      ( r2_hidden(k1_funct_1('#skF_8',D_270),A_271)
      | ~ r2_hidden(D_270,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_805,c_919])).

tff(c_940,plain,(
    ! [D_272,A_273] :
      ( r2_hidden(k1_funct_1('#skF_8',D_272),A_273)
      | ~ r2_hidden(D_272,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_922])).

tff(c_953,plain,(
    ! [C_45,A_273] :
      ( r2_hidden(C_45,A_273)
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_45),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_45,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_940])).

tff(c_957,plain,(
    ! [C_274,A_275] :
      ( r2_hidden(C_274,A_275)
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_274),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_274,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_953])).

tff(c_960,plain,(
    ! [C_137,A_275] :
      ( r2_hidden(C_137,A_275)
      | ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_137,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_247,c_957])).

tff(c_970,plain,(
    ! [C_276,A_277] :
      ( r2_hidden(C_276,A_277)
      | ~ r2_hidden(C_276,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_73,c_960])).

tff(c_976,plain,(
    ! [B_148,A_277] :
      ( r2_hidden('#skF_2'('#skF_8',B_148),A_277)
      | r2_hidden('#skF_4'('#skF_8',B_148),B_148)
      | k2_relat_1('#skF_8') = B_148
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_869,c_970])).

tff(c_1040,plain,(
    ! [B_281,A_282] :
      ( r2_hidden('#skF_2'('#skF_8',B_281),A_282)
      | r2_hidden('#skF_4'('#skF_8',B_281),B_281)
      | k2_relat_1('#skF_8') = B_281 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_976])).

tff(c_26,plain,(
    ! [A_9,B_31] :
      ( ~ r2_hidden('#skF_2'(A_9,B_31),B_31)
      | r2_hidden('#skF_4'(A_9,B_31),B_31)
      | k2_relat_1(A_9) = B_31
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1050,plain,(
    ! [A_282] :
      ( ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | r2_hidden('#skF_4'('#skF_8',A_282),A_282)
      | k2_relat_1('#skF_8') = A_282 ) ),
    inference(resolution,[status(thm)],[c_1040,c_26])).

tff(c_1069,plain,(
    ! [A_283] :
      ( r2_hidden('#skF_4'('#skF_8',A_283),A_283)
      | k2_relat_1('#skF_8') = A_283 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_1050])).

tff(c_1083,plain,(
    ! [A_285,B_286] :
      ( r2_hidden('#skF_4'('#skF_8',A_285),B_286)
      | ~ r1_tarski(A_285,B_286)
      | k2_relat_1('#skF_8') = A_285 ) ),
    inference(resolution,[status(thm)],[c_1069,c_2])).

tff(c_1099,plain,(
    ! [A_289,B_290,B_291] :
      ( r2_hidden('#skF_4'('#skF_8',A_289),B_290)
      | ~ r1_tarski(B_291,B_290)
      | ~ r1_tarski(A_289,B_291)
      | k2_relat_1('#skF_8') = A_289 ) ),
    inference(resolution,[status(thm)],[c_1083,c_2])).

tff(c_1163,plain,(
    ! [A_303,A_304,B_305] :
      ( r2_hidden('#skF_4'('#skF_8',A_303),A_304)
      | ~ r1_tarski(A_303,k2_relat_1(B_305))
      | k2_relat_1('#skF_8') = A_303
      | ~ v5_relat_1(B_305,A_304)
      | ~ v1_relat_1(B_305) ) ),
    inference(resolution,[status(thm)],[c_12,c_1099])).

tff(c_1172,plain,(
    ! [A_304,B_305] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_8'),A_304)
      | k2_relat_1('#skF_8') = '#skF_8'
      | ~ v5_relat_1(B_305,A_304)
      | ~ v1_relat_1(B_305) ) ),
    inference(resolution,[status(thm)],[c_404,c_1163])).

tff(c_1187,plain,(
    ! [A_306,B_307] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_8'),A_306)
      | ~ v5_relat_1(B_307,A_306)
      | ~ v1_relat_1(B_307) ) ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_1172])).

tff(c_1189,plain,(
    ! [A_153] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_8'),A_153)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_323,c_1187])).

tff(c_1194,plain,(
    ! [A_153] : r2_hidden('#skF_4'('#skF_8','#skF_8'),A_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1189])).

tff(c_18,plain,(
    ! [A_9,C_45] :
      ( r2_hidden('#skF_5'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_197,plain,(
    ! [A_118,A_120] :
      ( ~ r1_tarski(A_118,k1_xboole_0)
      | r1_tarski(A_118,A_120) ) ),
    inference(resolution,[status(thm)],[c_189,c_4])).

tff(c_280,plain,(
    ! [A_118,A_120] :
      ( ~ r1_tarski(A_118,'#skF_7')
      | r1_tarski(A_118,A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_197])).

tff(c_464,plain,(
    ! [A_167,A_168] :
      ( ~ r1_tarski(A_167,'#skF_8')
      | r1_tarski(A_167,A_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_280])).

tff(c_476,plain,(
    ! [B_8,A_168] :
      ( r1_tarski(k2_relat_1(B_8),A_168)
      | ~ v5_relat_1(B_8,'#skF_8')
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_464])).

tff(c_1123,plain,(
    ! [B_294,D_295,A_296] :
      ( r2_hidden(k1_funct_1(B_294,D_295),A_296)
      | ~ r2_hidden(D_295,k1_relat_1(B_294))
      | ~ v1_funct_1(B_294)
      | ~ v5_relat_1(B_294,'#skF_8')
      | ~ v1_relat_1(B_294) ) ),
    inference(resolution,[status(thm)],[c_476,c_919])).

tff(c_1273,plain,(
    ! [C_324,A_325,A_326] :
      ( r2_hidden(C_324,A_325)
      | ~ r2_hidden('#skF_5'(A_326,k2_relat_1(A_326),C_324),k1_relat_1(A_326))
      | ~ v1_funct_1(A_326)
      | ~ v5_relat_1(A_326,'#skF_8')
      | ~ v1_relat_1(A_326)
      | ~ r2_hidden(C_324,k2_relat_1(A_326))
      | ~ v1_funct_1(A_326)
      | ~ v1_relat_1(A_326) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1123])).

tff(c_1276,plain,(
    ! [C_137,A_325,A_136] :
      ( r2_hidden(C_137,A_325)
      | ~ v5_relat_1(A_136,'#skF_8')
      | ~ r1_tarski(k1_relat_1(A_136),k1_relat_1(A_136))
      | ~ r2_hidden(C_137,k2_relat_1(A_136))
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(resolution,[status(thm)],[c_247,c_1273])).

tff(c_1283,plain,(
    ! [C_327,A_328,A_329] :
      ( r2_hidden(C_327,A_328)
      | ~ v5_relat_1(A_329,'#skF_8')
      | ~ r2_hidden(C_327,k2_relat_1(A_329))
      | ~ v1_funct_1(A_329)
      | ~ v1_relat_1(A_329) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_1276])).

tff(c_1399,plain,(
    ! [A_333,B_334,A_335] :
      ( r2_hidden('#skF_2'(A_333,B_334),A_335)
      | ~ v5_relat_1(A_333,'#skF_8')
      | r2_hidden('#skF_4'(A_333,B_334),B_334)
      | k2_relat_1(A_333) = B_334
      | ~ v1_funct_1(A_333)
      | ~ v1_relat_1(A_333) ) ),
    inference(resolution,[status(thm)],[c_869,c_1283])).

tff(c_1431,plain,(
    ! [A_336,A_337] :
      ( ~ v5_relat_1(A_336,'#skF_8')
      | r2_hidden('#skF_4'(A_336,A_337),A_337)
      | k2_relat_1(A_336) = A_337
      | ~ v1_funct_1(A_336)
      | ~ v1_relat_1(A_336) ) ),
    inference(resolution,[status(thm)],[c_1399,c_26])).

tff(c_1456,plain,(
    ! [A_343,A_344,B_345] :
      ( r2_hidden('#skF_4'(A_343,A_344),B_345)
      | ~ r1_tarski(A_344,B_345)
      | ~ v5_relat_1(A_343,'#skF_8')
      | k2_relat_1(A_343) = A_344
      | ~ v1_funct_1(A_343)
      | ~ v1_relat_1(A_343) ) ),
    inference(resolution,[status(thm)],[c_1431,c_2])).

tff(c_1630,plain,(
    ! [A_376,A_377,B_378,B_379] :
      ( r2_hidden('#skF_4'(A_376,A_377),B_378)
      | ~ r1_tarski(B_379,B_378)
      | ~ r1_tarski(A_377,B_379)
      | ~ v5_relat_1(A_376,'#skF_8')
      | k2_relat_1(A_376) = A_377
      | ~ v1_funct_1(A_376)
      | ~ v1_relat_1(A_376) ) ),
    inference(resolution,[status(thm)],[c_1456,c_2])).

tff(c_2629,plain,(
    ! [A_535,A_536,A_537,B_538] :
      ( r2_hidden('#skF_4'(A_535,A_536),A_537)
      | ~ r1_tarski(A_536,k2_relat_1(B_538))
      | ~ v5_relat_1(A_535,'#skF_8')
      | k2_relat_1(A_535) = A_536
      | ~ v1_funct_1(A_535)
      | ~ v1_relat_1(A_535)
      | ~ v5_relat_1(B_538,A_537)
      | ~ v1_relat_1(B_538) ) ),
    inference(resolution,[status(thm)],[c_12,c_1630])).

tff(c_2707,plain,(
    ! [A_543,A_544,B_545] :
      ( r2_hidden('#skF_4'(A_543,'#skF_8'),A_544)
      | ~ v5_relat_1(A_543,'#skF_8')
      | k2_relat_1(A_543) = '#skF_8'
      | ~ v1_funct_1(A_543)
      | ~ v1_relat_1(A_543)
      | ~ v5_relat_1(B_545,A_544)
      | ~ v1_relat_1(B_545) ) ),
    inference(resolution,[status(thm)],[c_404,c_2629])).

tff(c_2709,plain,(
    ! [A_543,A_153] :
      ( r2_hidden('#skF_4'(A_543,'#skF_8'),A_153)
      | ~ v5_relat_1(A_543,'#skF_8')
      | k2_relat_1(A_543) = '#skF_8'
      | ~ v1_funct_1(A_543)
      | ~ v1_relat_1(A_543)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_323,c_2707])).

tff(c_2714,plain,(
    ! [A_543,A_153] :
      ( r2_hidden('#skF_4'(A_543,'#skF_8'),A_153)
      | ~ v5_relat_1(A_543,'#skF_8')
      | k2_relat_1(A_543) = '#skF_8'
      | ~ v1_funct_1(A_543)
      | ~ v1_relat_1(A_543) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2709])).

tff(c_479,plain,(
    ! [A_169,B_170,D_171] :
      ( r2_hidden('#skF_3'(A_169,B_170),k1_relat_1(A_169))
      | k1_funct_1(A_169,D_171) != '#skF_4'(A_169,B_170)
      | ~ r2_hidden(D_171,k1_relat_1(A_169))
      | k2_relat_1(A_169) = B_170
      | ~ v1_funct_1(A_169)
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_483,plain,(
    ! [A_9,B_170,C_45] :
      ( r2_hidden('#skF_3'(A_9,B_170),k1_relat_1(A_9))
      | C_45 != '#skF_4'(A_9,B_170)
      | ~ r2_hidden('#skF_5'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | k2_relat_1(A_9) = B_170
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9)
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_479])).

tff(c_2752,plain,(
    ! [A_554,B_555] :
      ( r2_hidden('#skF_3'(A_554,B_555),k1_relat_1(A_554))
      | ~ r2_hidden('#skF_5'(A_554,k2_relat_1(A_554),'#skF_4'(A_554,B_555)),k1_relat_1(A_554))
      | k2_relat_1(A_554) = B_555
      | ~ v1_funct_1(A_554)
      | ~ v1_relat_1(A_554)
      | ~ r2_hidden('#skF_4'(A_554,B_555),k2_relat_1(A_554))
      | ~ v1_funct_1(A_554)
      | ~ v1_relat_1(A_554) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_483])).

tff(c_2764,plain,(
    ! [A_136,B_555] :
      ( r2_hidden('#skF_3'(A_136,B_555),k1_relat_1(A_136))
      | k2_relat_1(A_136) = B_555
      | ~ r1_tarski(k1_relat_1(A_136),k1_relat_1(A_136))
      | ~ r2_hidden('#skF_4'(A_136,B_555),k2_relat_1(A_136))
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(resolution,[status(thm)],[c_247,c_2752])).

tff(c_2775,plain,(
    ! [A_556,B_557] :
      ( r2_hidden('#skF_3'(A_556,B_557),k1_relat_1(A_556))
      | k2_relat_1(A_556) = B_557
      | ~ r2_hidden('#skF_4'(A_556,B_557),k2_relat_1(A_556))
      | ~ v1_funct_1(A_556)
      | ~ v1_relat_1(A_556) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_2764])).

tff(c_2782,plain,(
    ! [A_558,B_559,B_560] :
      ( r2_hidden('#skF_3'(A_558,B_559),B_560)
      | ~ r1_tarski(k1_relat_1(A_558),B_560)
      | k2_relat_1(A_558) = B_559
      | ~ r2_hidden('#skF_4'(A_558,B_559),k2_relat_1(A_558))
      | ~ v1_funct_1(A_558)
      | ~ v1_relat_1(A_558) ) ),
    inference(resolution,[status(thm)],[c_2775,c_2])).

tff(c_2928,plain,(
    ! [A_543,B_560] :
      ( r2_hidden('#skF_3'(A_543,'#skF_8'),B_560)
      | ~ r1_tarski(k1_relat_1(A_543),B_560)
      | ~ v5_relat_1(A_543,'#skF_8')
      | k2_relat_1(A_543) = '#skF_8'
      | ~ v1_funct_1(A_543)
      | ~ v1_relat_1(A_543) ) ),
    inference(resolution,[status(thm)],[c_2714,c_2782])).

tff(c_530,plain,(
    ! [A_181,B_182,D_183] :
      ( k1_funct_1(A_181,'#skF_3'(A_181,B_182)) = '#skF_2'(A_181,B_182)
      | k1_funct_1(A_181,D_183) != '#skF_4'(A_181,B_182)
      | ~ r2_hidden(D_183,k1_relat_1(A_181))
      | k2_relat_1(A_181) = B_182
      | ~ v1_funct_1(A_181)
      | ~ v1_relat_1(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_536,plain,(
    ! [A_9,B_182,C_45] :
      ( k1_funct_1(A_9,'#skF_3'(A_9,B_182)) = '#skF_2'(A_9,B_182)
      | C_45 != '#skF_4'(A_9,B_182)
      | ~ r2_hidden('#skF_5'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | k2_relat_1(A_9) = B_182
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9)
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_530])).

tff(c_3091,plain,(
    ! [A_574,B_575] :
      ( k1_funct_1(A_574,'#skF_3'(A_574,B_575)) = '#skF_2'(A_574,B_575)
      | ~ r2_hidden('#skF_5'(A_574,k2_relat_1(A_574),'#skF_4'(A_574,B_575)),k1_relat_1(A_574))
      | k2_relat_1(A_574) = B_575
      | ~ v1_funct_1(A_574)
      | ~ v1_relat_1(A_574)
      | ~ r2_hidden('#skF_4'(A_574,B_575),k2_relat_1(A_574))
      | ~ v1_funct_1(A_574)
      | ~ v1_relat_1(A_574) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_536])).

tff(c_3185,plain,(
    ! [A_587,B_588] :
      ( k1_funct_1(A_587,'#skF_3'(A_587,B_588)) = '#skF_2'(A_587,B_588)
      | k2_relat_1(A_587) = B_588
      | ~ r2_hidden('#skF_4'(A_587,B_588),k2_relat_1(A_587))
      | ~ v1_funct_1(A_587)
      | ~ v1_relat_1(A_587) ) ),
    inference(resolution,[status(thm)],[c_18,c_3091])).

tff(c_3347,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1194,c_3185])).

tff(c_3434,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_3347])).

tff(c_3435,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_3434])).

tff(c_703,plain,(
    ! [A_231,D_232,B_233,B_234] :
      ( r2_hidden(k1_funct_1(A_231,D_232),B_233)
      | ~ r1_tarski(B_234,B_233)
      | ~ r1_tarski(k2_relat_1(A_231),B_234)
      | ~ r2_hidden(D_232,k1_relat_1(A_231))
      | ~ v1_funct_1(A_231)
      | ~ v1_relat_1(A_231) ) ),
    inference(resolution,[status(thm)],[c_579,c_2])).

tff(c_1827,plain,(
    ! [A_423,D_424,A_425,B_426] :
      ( r2_hidden(k1_funct_1(A_423,D_424),A_425)
      | ~ r1_tarski(k2_relat_1(A_423),k2_relat_1(B_426))
      | ~ r2_hidden(D_424,k1_relat_1(A_423))
      | ~ v1_funct_1(A_423)
      | ~ v1_relat_1(A_423)
      | ~ v5_relat_1(B_426,A_425)
      | ~ v1_relat_1(B_426) ) ),
    inference(resolution,[status(thm)],[c_12,c_703])).

tff(c_1845,plain,(
    ! [A_423,D_424,A_425] :
      ( r2_hidden(k1_funct_1(A_423,D_424),A_425)
      | ~ r2_hidden(D_424,k1_relat_1(A_423))
      | ~ v1_funct_1(A_423)
      | ~ v5_relat_1(A_423,A_425)
      | ~ v1_relat_1(A_423) ) ),
    inference(resolution,[status(thm)],[c_73,c_1827])).

tff(c_3459,plain,(
    ! [A_425] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_8'),A_425)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_425)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3435,c_1845])).

tff(c_3488,plain,(
    ! [A_425] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_8'),A_425)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_323,c_60,c_3459])).

tff(c_3502,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_3488])).

tff(c_3506,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
    | ~ v5_relat_1('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_2928,c_3502])).

tff(c_3551,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_323,c_73,c_3506])).

tff(c_3553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_3551])).

tff(c_3556,plain,(
    ! [A_593] : r2_hidden('#skF_2'('#skF_8','#skF_8'),A_593) ),
    inference(splitRight,[status(thm)],[c_3488])).

tff(c_20,plain,(
    ! [A_9,B_31,D_44] :
      ( ~ r2_hidden('#skF_2'(A_9,B_31),B_31)
      | k1_funct_1(A_9,D_44) != '#skF_4'(A_9,B_31)
      | ~ r2_hidden(D_44,k1_relat_1(A_9))
      | k2_relat_1(A_9) = B_31
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3565,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_8'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3556,c_20])).

tff(c_3578,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_3565])).

tff(c_3595,plain,(
    ! [D_594] :
      ( k1_funct_1('#skF_8',D_594) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_594,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_3578])).

tff(c_3938,plain,(
    ! [C_45] :
      ( k1_funct_1('#skF_8','#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_45)) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(C_45,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18,c_3595])).

tff(c_4622,plain,(
    ! [C_608] :
      ( k1_funct_1('#skF_8','#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_608)) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(C_608,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_3938])).

tff(c_4626,plain,(
    ! [C_45] :
      ( C_45 != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(C_45,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_45,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4622])).

tff(c_4630,plain,(
    ! [C_609] :
      ( C_609 != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(C_609,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_4626])).

tff(c_5044,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1194,c_4630])).

tff(c_5052,plain,(
    ! [D_610] :
      ( r2_hidden(D_610,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_610,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_5066,plain,(
    ! [D_614,B_615] :
      ( r2_hidden(D_614,B_615)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_615)
      | ~ r2_hidden(D_614,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5052,c_2])).

tff(c_5069,plain,(
    ! [D_614,A_7] :
      ( r2_hidden(D_614,A_7)
      | ~ r2_hidden(D_614,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_7)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_12,c_5066])).

tff(c_5075,plain,(
    ! [D_614,A_7] :
      ( r2_hidden(D_614,A_7)
      | ~ r2_hidden(D_614,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5069])).

tff(c_6158,plain,(
    ! [B_757,B_758,A_759] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_757),B_758),A_759)
      | ~ v5_relat_1('#skF_8',A_759)
      | r1_tarski(k2_relat_1(B_757),B_758)
      | ~ v5_relat_1(B_757,'#skF_7')
      | ~ v1_relat_1(B_757) ) ),
    inference(resolution,[status(thm)],[c_5792,c_5075])).

tff(c_6183,plain,(
    ! [A_759,B_757] :
      ( ~ v5_relat_1('#skF_8',A_759)
      | r1_tarski(k2_relat_1(B_757),A_759)
      | ~ v5_relat_1(B_757,'#skF_7')
      | ~ v1_relat_1(B_757) ) ),
    inference(resolution,[status(thm)],[c_6158,c_4])).

tff(c_5541,plain,(
    ! [B_678,A_679,C_680] :
      ( k1_xboole_0 = B_678
      | k1_relset_1(A_679,B_678,C_680) = A_679
      | ~ v1_funct_2(C_680,A_679,B_678)
      | ~ m1_subset_1(C_680,k1_zfmisc_1(k2_zfmisc_1(A_679,B_678))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5544,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_5541])).

tff(c_5547,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_136,c_5544])).

tff(c_5548,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_5547])).

tff(c_5719,plain,(
    ! [A_705,B_706] :
      ( r2_hidden('#skF_3'(A_705,B_706),k1_relat_1(A_705))
      | r2_hidden('#skF_4'(A_705,B_706),B_706)
      | k2_relat_1(A_705) = B_706
      | ~ v1_funct_1(A_705)
      | ~ v1_relat_1(A_705) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5728,plain,(
    ! [A_705,B_706,B_2] :
      ( r2_hidden('#skF_3'(A_705,B_706),B_2)
      | ~ r1_tarski(k1_relat_1(A_705),B_2)
      | r2_hidden('#skF_4'(A_705,B_706),B_706)
      | k2_relat_1(A_705) = B_706
      | ~ v1_funct_1(A_705)
      | ~ v1_relat_1(A_705) ) ),
    inference(resolution,[status(thm)],[c_5719,c_2])).

tff(c_28,plain,(
    ! [A_9,B_31] :
      ( k1_funct_1(A_9,'#skF_3'(A_9,B_31)) = '#skF_2'(A_9,B_31)
      | r2_hidden('#skF_4'(A_9,B_31),B_31)
      | k2_relat_1(A_9) = B_31
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6462,plain,(
    ! [A_785,B_786,D_787] :
      ( k1_funct_1(A_785,'#skF_3'(A_785,B_786)) = '#skF_2'(A_785,B_786)
      | k1_funct_1(A_785,D_787) != '#skF_4'(A_785,B_786)
      | ~ r2_hidden(D_787,k1_relat_1(A_785))
      | k2_relat_1(A_785) = B_786
      | ~ v1_funct_1(A_785)
      | ~ v1_relat_1(A_785) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6468,plain,(
    ! [B_786,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_786)) = '#skF_2'('#skF_8',B_786)
      | D_67 != '#skF_4'('#skF_8',B_786)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_786
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_6462])).

tff(c_6470,plain,(
    ! [B_786,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_786)) = '#skF_2'('#skF_8',B_786)
      | D_67 != '#skF_4'('#skF_8',B_786)
      | ~ r2_hidden('#skF_9'(D_67),'#skF_6')
      | k2_relat_1('#skF_8') = B_786
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_5548,c_6468])).

tff(c_6830,plain,(
    ! [B_841] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_841)) = '#skF_2'('#skF_8',B_841)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_841)),'#skF_6')
      | k2_relat_1('#skF_8') = B_841
      | ~ r2_hidden('#skF_4'('#skF_8',B_841),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6470])).

tff(c_6833,plain,(
    ! [B_841] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_841)) = '#skF_2'('#skF_8',B_841)
      | k2_relat_1('#skF_8') = B_841
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_841),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_112,c_6830])).

tff(c_6841,plain,(
    ! [B_842] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_842)) = '#skF_2'('#skF_8',B_842)
      | k2_relat_1('#skF_8') = B_842
      | ~ r2_hidden('#skF_4'('#skF_8',B_842),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_6833])).

tff(c_6855,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_28,c_6841])).

tff(c_6866,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_6855])).

tff(c_6867,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_6866])).

tff(c_6888,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_6867,c_14])).

tff(c_6905,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_5548,c_6888])).

tff(c_6907,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6905])).

tff(c_6913,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
    | r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_5728,c_6907])).

tff(c_6941,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_73,c_5548,c_6913])).

tff(c_6942,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_6941])).

tff(c_6318,plain,(
    ! [A_767,B_768,D_769] :
      ( r2_hidden('#skF_3'(A_767,B_768),k1_relat_1(A_767))
      | k1_funct_1(A_767,D_769) != '#skF_4'(A_767,B_768)
      | ~ r2_hidden(D_769,k1_relat_1(A_767))
      | k2_relat_1(A_767) = B_768
      | ~ v1_funct_1(A_767)
      | ~ v1_relat_1(A_767) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6324,plain,(
    ! [B_768,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_768),k1_relat_1('#skF_8'))
      | D_67 != '#skF_4'('#skF_8',B_768)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_768
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_6318])).

tff(c_6326,plain,(
    ! [B_768,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_768),'#skF_6')
      | D_67 != '#skF_4'('#skF_8',B_768)
      | ~ r2_hidden('#skF_9'(D_67),'#skF_6')
      | k2_relat_1('#skF_8') = B_768
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_5548,c_5548,c_6324])).

tff(c_6447,plain,(
    ! [B_783] :
      ( r2_hidden('#skF_3'('#skF_8',B_783),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_783)),'#skF_6')
      | k2_relat_1('#skF_8') = B_783
      | ~ r2_hidden('#skF_4'('#skF_8',B_783),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6326])).

tff(c_6450,plain,(
    ! [B_783] :
      ( r2_hidden('#skF_3'('#skF_8',B_783),'#skF_6')
      | k2_relat_1('#skF_8') = B_783
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_783),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_112,c_6447])).

tff(c_6458,plain,(
    ! [B_784] :
      ( r2_hidden('#skF_3'('#skF_8',B_784),'#skF_6')
      | k2_relat_1('#skF_8') = B_784
      | ~ r2_hidden('#skF_4'('#skF_8',B_784),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_6450])).

tff(c_6461,plain,(
    ! [B_784,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_784),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | k2_relat_1('#skF_8') = B_784
      | ~ r2_hidden('#skF_4'('#skF_8',B_784),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6458,c_2])).

tff(c_6922,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_6461,c_6907])).

tff(c_6952,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_6922])).

tff(c_6953,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_6952])).

tff(c_7036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6942,c_6953])).

tff(c_7037,plain,(
    r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_6905])).

tff(c_7057,plain,(
    ! [B_847] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_847)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_847) ) ),
    inference(resolution,[status(thm)],[c_7037,c_2])).

tff(c_7067,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_7057,c_26])).

tff(c_7080,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_7067])).

tff(c_7081,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_7080])).

tff(c_7084,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_7081])).

tff(c_7087,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_6183,c_7084])).

tff(c_7097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_105,c_7087])).

tff(c_7099,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_7081])).

tff(c_7063,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_7057,c_20])).

tff(c_7076,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_5548,c_7063])).

tff(c_7077,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,'#skF_6')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_7076])).

tff(c_7282,plain,(
    ! [D_853] :
      ( k1_funct_1('#skF_8',D_853) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_853,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7099,c_7077])).

tff(c_7418,plain,(
    ! [D_67] :
      ( k1_funct_1('#skF_8','#skF_9'(D_67)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_112,c_7282])).

tff(c_7474,plain,(
    ! [D_854] :
      ( k1_funct_1('#skF_8','#skF_9'(D_854)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_854,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_7418])).

tff(c_7478,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_7474])).

tff(c_7098,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_7081])).

tff(c_7480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7478,c_7098])).

tff(c_7481,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_5547])).

tff(c_5202,plain,(
    ! [A_633,B_634,A_635] :
      ( r2_hidden('#skF_1'(A_633,B_634),A_635)
      | ~ r1_tarski(A_633,k1_xboole_0)
      | r1_tarski(A_633,B_634) ) ),
    inference(resolution,[status(thm)],[c_8,c_5170])).

tff(c_5220,plain,(
    ! [A_636,A_637] :
      ( ~ r1_tarski(A_636,k1_xboole_0)
      | r1_tarski(A_636,A_637) ) ),
    inference(resolution,[status(thm)],[c_5202,c_4])).

tff(c_5236,plain,(
    ! [B_640,A_641] :
      ( r1_tarski(k2_relat_1(B_640),A_641)
      | ~ v5_relat_1(B_640,k1_xboole_0)
      | ~ v1_relat_1(B_640) ) ),
    inference(resolution,[status(thm)],[c_12,c_5220])).

tff(c_5059,plain,(
    ! [D_610,B_2] :
      ( r2_hidden(D_610,B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r2_hidden(D_610,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5052,c_2])).

tff(c_5244,plain,(
    ! [D_610,A_641] :
      ( r2_hidden(D_610,A_641)
      | ~ r2_hidden(D_610,'#skF_7')
      | ~ v5_relat_1('#skF_8',k1_xboole_0)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5236,c_5059])).

tff(c_5254,plain,(
    ! [D_610,A_641] :
      ( r2_hidden(D_610,A_641)
      | ~ r2_hidden(D_610,'#skF_7')
      | ~ v5_relat_1('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5244])).

tff(c_5258,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5254])).

tff(c_7492,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7481,c_5258])).

tff(c_7504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_7492])).

tff(c_7506,plain,(
    v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5254])).

tff(c_5256,plain,(
    ! [B_640,A_641] :
      ( v5_relat_1(B_640,A_641)
      | ~ v5_relat_1(B_640,k1_xboole_0)
      | ~ v1_relat_1(B_640) ) ),
    inference(resolution,[status(thm)],[c_5236,c_10])).

tff(c_7508,plain,(
    ! [A_641] :
      ( v5_relat_1('#skF_8',A_641)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_7506,c_5256])).

tff(c_7514,plain,(
    ! [A_641] : v5_relat_1('#skF_8',A_641) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_7508])).

tff(c_7839,plain,(
    ! [A_906,B_907,A_908,B_909] :
      ( r2_hidden('#skF_1'(A_906,B_907),A_908)
      | ~ r1_tarski(A_906,k2_relat_1(B_909))
      | r1_tarski(A_906,B_907)
      | ~ v5_relat_1(B_909,A_908)
      | ~ v1_relat_1(B_909) ) ),
    inference(resolution,[status(thm)],[c_12,c_5170])).

tff(c_8262,plain,(
    ! [B_986,B_987,A_988,B_989] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_986),B_987),A_988)
      | r1_tarski(k2_relat_1(B_986),B_987)
      | ~ v5_relat_1(B_989,A_988)
      | ~ v1_relat_1(B_989)
      | ~ v5_relat_1(B_986,k2_relat_1(B_989))
      | ~ v1_relat_1(B_986) ) ),
    inference(resolution,[status(thm)],[c_12,c_7839])).

tff(c_8264,plain,(
    ! [B_986,B_987,A_641] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_986),B_987),A_641)
      | r1_tarski(k2_relat_1(B_986),B_987)
      | ~ v1_relat_1('#skF_8')
      | ~ v5_relat_1(B_986,k2_relat_1('#skF_8'))
      | ~ v1_relat_1(B_986) ) ),
    inference(resolution,[status(thm)],[c_7514,c_8262])).

tff(c_8274,plain,(
    ! [B_990,B_991,A_992] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_990),B_991),A_992)
      | r1_tarski(k2_relat_1(B_990),B_991)
      | ~ v5_relat_1(B_990,k2_relat_1('#skF_8'))
      | ~ v1_relat_1(B_990) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8264])).

tff(c_8303,plain,(
    ! [B_996,A_997] :
      ( r1_tarski(k2_relat_1(B_996),A_997)
      | ~ v5_relat_1(B_996,k2_relat_1('#skF_8'))
      | ~ v1_relat_1(B_996) ) ),
    inference(resolution,[status(thm)],[c_8274,c_4])).

tff(c_8306,plain,(
    ! [A_997] :
      ( r1_tarski(k2_relat_1('#skF_8'),A_997)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_7514,c_8303])).

tff(c_8314,plain,(
    ! [A_997] : r1_tarski(k2_relat_1('#skF_8'),A_997) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8306])).

tff(c_7725,plain,(
    ! [B_886,A_887,C_888] :
      ( k1_xboole_0 = B_886
      | k1_relset_1(A_887,B_886,C_888) = A_887
      | ~ v1_funct_2(C_888,A_887,B_886)
      | ~ m1_subset_1(C_888,k1_zfmisc_1(k2_zfmisc_1(A_887,B_886))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7728,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_7725])).

tff(c_7731,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_136,c_7728])).

tff(c_7732,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_7731])).

tff(c_7912,plain,(
    ! [A_917,B_918] :
      ( r2_hidden('#skF_3'(A_917,B_918),k1_relat_1(A_917))
      | r2_hidden('#skF_4'(A_917,B_918),B_918)
      | k2_relat_1(A_917) = B_918
      | ~ v1_funct_1(A_917)
      | ~ v1_relat_1(A_917) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7920,plain,(
    ! [B_918] :
      ( r2_hidden('#skF_3'('#skF_8',B_918),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_918),B_918)
      | k2_relat_1('#skF_8') = B_918
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7732,c_7912])).

tff(c_7925,plain,(
    ! [B_919] :
      ( r2_hidden('#skF_3'('#skF_8',B_919),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_919),B_919)
      | k2_relat_1('#skF_8') = B_919 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_7920])).

tff(c_7931,plain,(
    ! [B_919,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_919),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | r2_hidden('#skF_4'('#skF_8',B_919),B_919)
      | k2_relat_1('#skF_8') = B_919 ) ),
    inference(resolution,[status(thm)],[c_7925,c_2])).

tff(c_8025,plain,(
    ! [A_938,B_939] :
      ( k1_funct_1(A_938,'#skF_3'(A_938,B_939)) = '#skF_2'(A_938,B_939)
      | r2_hidden('#skF_4'(A_938,B_939),B_939)
      | k2_relat_1(A_938) = B_939
      | ~ v1_funct_1(A_938)
      | ~ v1_relat_1(A_938) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8832,plain,(
    ! [A_1041,B_1042] :
      ( r2_hidden('#skF_2'(A_1041,B_1042),k2_relat_1(A_1041))
      | ~ r2_hidden('#skF_3'(A_1041,B_1042),k1_relat_1(A_1041))
      | ~ v1_funct_1(A_1041)
      | ~ v1_relat_1(A_1041)
      | r2_hidden('#skF_4'(A_1041,B_1042),B_1042)
      | k2_relat_1(A_1041) = B_1042
      | ~ v1_funct_1(A_1041)
      | ~ v1_relat_1(A_1041) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8025,c_14])).

tff(c_8852,plain,(
    ! [B_919] :
      ( r2_hidden('#skF_2'('#skF_8',B_919),k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | r2_hidden('#skF_4'('#skF_8',B_919),B_919)
      | k2_relat_1('#skF_8') = B_919 ) ),
    inference(resolution,[status(thm)],[c_7931,c_8832])).

tff(c_8879,plain,(
    ! [B_1043] :
      ( r2_hidden('#skF_2'('#skF_8',B_1043),k2_relat_1('#skF_8'))
      | r2_hidden('#skF_4'('#skF_8',B_1043),B_1043)
      | k2_relat_1('#skF_8') = B_1043 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_7732,c_88,c_60,c_8852])).

tff(c_8890,plain,(
    ! [B_1043,B_2] :
      ( r2_hidden('#skF_2'('#skF_8',B_1043),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | r2_hidden('#skF_4'('#skF_8',B_1043),B_1043)
      | k2_relat_1('#skF_8') = B_1043 ) ),
    inference(resolution,[status(thm)],[c_8879,c_2])).

tff(c_8908,plain,(
    ! [B_1044,B_1045] :
      ( r2_hidden('#skF_2'('#skF_8',B_1044),B_1045)
      | r2_hidden('#skF_4'('#skF_8',B_1044),B_1044)
      | k2_relat_1('#skF_8') = B_1044 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8314,c_8890])).

tff(c_8918,plain,(
    ! [B_1045] :
      ( ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | r2_hidden('#skF_4'('#skF_8',B_1045),B_1045)
      | k2_relat_1('#skF_8') = B_1045 ) ),
    inference(resolution,[status(thm)],[c_8908,c_26])).

tff(c_8942,plain,(
    ! [B_1046] :
      ( r2_hidden('#skF_4'('#skF_8',B_1046),B_1046)
      | k2_relat_1('#skF_8') = B_1046 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_8918])).

tff(c_7505,plain,(
    ! [D_610,A_641] :
      ( r2_hidden(D_610,A_641)
      | ~ r2_hidden(D_610,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_5254])).

tff(c_8948,plain,(
    ! [A_641] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_7'),A_641)
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_8942,c_7505])).

tff(c_8955,plain,(
    ! [A_641] : r2_hidden('#skF_4'('#skF_8','#skF_7'),A_641) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_8948])).

tff(c_8292,plain,(
    ! [A_993,B_994,D_995] :
      ( r2_hidden('#skF_3'(A_993,B_994),k1_relat_1(A_993))
      | k1_funct_1(A_993,D_995) != '#skF_4'(A_993,B_994)
      | ~ r2_hidden(D_995,k1_relat_1(A_993))
      | k2_relat_1(A_993) = B_994
      | ~ v1_funct_1(A_993)
      | ~ v1_relat_1(A_993) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8300,plain,(
    ! [B_994,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_994),k1_relat_1('#skF_8'))
      | D_67 != '#skF_4'('#skF_8',B_994)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_994
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_8292])).

tff(c_8302,plain,(
    ! [B_994,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_994),'#skF_6')
      | D_67 != '#skF_4'('#skF_8',B_994)
      | ~ r2_hidden('#skF_9'(D_67),'#skF_6')
      | k2_relat_1('#skF_8') = B_994
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_7732,c_7732,c_8300])).

tff(c_8767,plain,(
    ! [B_1031] :
      ( r2_hidden('#skF_3'('#skF_8',B_1031),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1031)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1031
      | ~ r2_hidden('#skF_4'('#skF_8',B_1031),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8302])).

tff(c_8770,plain,(
    ! [B_1031] :
      ( r2_hidden('#skF_3'('#skF_8',B_1031),'#skF_6')
      | k2_relat_1('#skF_8') = B_1031
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_1031),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_112,c_8767])).

tff(c_8778,plain,(
    ! [B_1032] :
      ( r2_hidden('#skF_3'('#skF_8',B_1032),'#skF_6')
      | k2_relat_1('#skF_8') = B_1032
      | ~ r2_hidden('#skF_4'('#skF_8',B_1032),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_8770])).

tff(c_8781,plain,(
    ! [B_1032,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1032),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | k2_relat_1('#skF_8') = B_1032
      | ~ r2_hidden('#skF_4'('#skF_8',B_1032),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8778,c_2])).

tff(c_8434,plain,(
    ! [A_1006,B_1007,D_1008] :
      ( k1_funct_1(A_1006,'#skF_3'(A_1006,B_1007)) = '#skF_2'(A_1006,B_1007)
      | k1_funct_1(A_1006,D_1008) != '#skF_4'(A_1006,B_1007)
      | ~ r2_hidden(D_1008,k1_relat_1(A_1006))
      | k2_relat_1(A_1006) = B_1007
      | ~ v1_funct_1(A_1006)
      | ~ v1_relat_1(A_1006) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8442,plain,(
    ! [B_1007,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1007)) = '#skF_2'('#skF_8',B_1007)
      | D_67 != '#skF_4'('#skF_8',B_1007)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1007
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_8434])).

tff(c_8444,plain,(
    ! [B_1007,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1007)) = '#skF_2'('#skF_8',B_1007)
      | D_67 != '#skF_4'('#skF_8',B_1007)
      | ~ r2_hidden('#skF_9'(D_67),'#skF_6')
      | k2_relat_1('#skF_8') = B_1007
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_7732,c_8442])).

tff(c_9047,plain,(
    ! [B_1062] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1062)) = '#skF_2'('#skF_8',B_1062)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1062)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1062
      | ~ r2_hidden('#skF_4'('#skF_8',B_1062),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8444])).

tff(c_9050,plain,(
    ! [B_1062] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1062)) = '#skF_2'('#skF_8',B_1062)
      | k2_relat_1('#skF_8') = B_1062
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_1062),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_112,c_9047])).

tff(c_9058,plain,(
    ! [B_1063] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1063)) = '#skF_2'('#skF_8',B_1063)
      | k2_relat_1('#skF_8') = B_1063
      | ~ r2_hidden('#skF_4'('#skF_8',B_1063),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_9050])).

tff(c_9098,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_28,c_9058])).

tff(c_9120,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_9098])).

tff(c_9121,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_9120])).

tff(c_7823,plain,(
    ! [A_903,D_904,B_905] :
      ( r2_hidden(k1_funct_1(A_903,D_904),B_905)
      | ~ r1_tarski(k2_relat_1(A_903),B_905)
      | ~ r2_hidden(D_904,k1_relat_1(A_903))
      | ~ v1_funct_1(A_903)
      | ~ v1_relat_1(A_903) ) ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_8161,plain,(
    ! [A_968,D_969,B_970,B_971] :
      ( r2_hidden(k1_funct_1(A_968,D_969),B_970)
      | ~ r1_tarski(B_971,B_970)
      | ~ r1_tarski(k2_relat_1(A_968),B_971)
      | ~ r2_hidden(D_969,k1_relat_1(A_968))
      | ~ v1_funct_1(A_968)
      | ~ v1_relat_1(A_968) ) ),
    inference(resolution,[status(thm)],[c_7823,c_2])).

tff(c_8179,plain,(
    ! [A_968,D_969,A_6] :
      ( r2_hidden(k1_funct_1(A_968,D_969),A_6)
      | ~ r1_tarski(k2_relat_1(A_968),k1_xboole_0)
      | ~ r2_hidden(D_969,k1_relat_1(A_968))
      | ~ v1_funct_1(A_968)
      | ~ v1_relat_1(A_968) ) ),
    inference(resolution,[status(thm)],[c_8,c_8161])).

tff(c_9140,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),A_6)
      | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9121,c_8179])).

tff(c_9165,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),A_6)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_7732,c_8314,c_9140])).

tff(c_9181,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9165])).

tff(c_9184,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_8781,c_9181])).

tff(c_9193,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8955,c_73,c_9184])).

tff(c_9195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_9193])).

tff(c_9198,plain,(
    ! [A_1067] : r2_hidden('#skF_2'('#skF_8','#skF_7'),A_1067) ),
    inference(splitRight,[status(thm)],[c_9165])).

tff(c_9204,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_9198,c_20])).

tff(c_9218,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_7732,c_9204])).

tff(c_9250,plain,(
    ! [D_1069] :
      ( k1_funct_1('#skF_8',D_1069) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1069,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_9218])).

tff(c_9415,plain,(
    ! [D_1073] :
      ( k1_funct_1('#skF_8','#skF_9'(D_1073)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1073,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_9250])).

tff(c_9429,plain,(
    ! [D_1077] :
      ( D_1077 != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1077,'#skF_7')
      | ~ r2_hidden(D_1077,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_9415])).

tff(c_9450,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_8955,c_9429])).

tff(c_9522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8955,c_9450])).

tff(c_9523,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7731])).

tff(c_9570,plain,(
    ! [C_1084,A_1085] :
      ( C_1084 = '#skF_7'
      | ~ v1_funct_2(C_1084,A_1085,'#skF_7')
      | A_1085 = '#skF_7'
      | ~ m1_subset_1(C_1084,k1_zfmisc_1(k2_zfmisc_1(A_1085,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9523,c_9523,c_9523,c_9523,c_44])).

tff(c_9573,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_56,c_9570])).

tff(c_9576,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_9573])).

tff(c_9577,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_9576])).

tff(c_5077,plain,(
    ! [D_616,A_617] :
      ( r2_hidden(D_616,A_617)
      | ~ r2_hidden(D_616,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_617) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5069])).

tff(c_5088,plain,(
    ! [D_67,A_617] :
      ( r2_hidden('#skF_9'(D_67),A_617)
      | ~ v5_relat_1('#skF_8',A_617)
      | ~ r1_tarski('#skF_6','#skF_7')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_112,c_5077])).

tff(c_5101,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_5088])).

tff(c_9593,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9577,c_5101])).

tff(c_9607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_9593])).

tff(c_9608,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_9576])).

tff(c_5128,plain,(
    ! [B_625,A_626] :
      ( r2_hidden('#skF_1'('#skF_7',B_625),A_626)
      | ~ v5_relat_1('#skF_8',A_626)
      | r1_tarski('#skF_7',B_625) ) ),
    inference(resolution,[status(thm)],[c_6,c_5077])).

tff(c_5149,plain,(
    ! [A_626] :
      ( ~ v5_relat_1('#skF_8',A_626)
      | r1_tarski('#skF_7',A_626) ) ),
    inference(resolution,[status(thm)],[c_5128,c_4])).

tff(c_7518,plain,(
    ! [A_626] : r1_tarski('#skF_7',A_626) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7514,c_5149])).

tff(c_9628,plain,(
    ! [A_626] : r1_tarski('#skF_8',A_626) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9608,c_7518])).

tff(c_111,plain,(
    ! [A_1,B_2,B_89] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_89)
      | ~ r1_tarski(A_1,B_89)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_7562,plain,(
    ! [D_862,A_863] :
      ( r2_hidden(D_862,A_863)
      | ~ r2_hidden(D_862,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_5254])).

tff(c_7593,plain,(
    ! [A_866,B_867,A_868] :
      ( r2_hidden('#skF_1'(A_866,B_867),A_868)
      | ~ r1_tarski(A_866,'#skF_7')
      | r1_tarski(A_866,B_867) ) ),
    inference(resolution,[status(thm)],[c_111,c_7562])).

tff(c_7611,plain,(
    ! [A_869,A_870] :
      ( ~ r1_tarski(A_869,'#skF_7')
      | r1_tarski(A_869,A_870) ) ),
    inference(resolution,[status(thm)],[c_7593,c_4])).

tff(c_7630,plain,(
    ! [B_8,A_870] :
      ( r1_tarski(k2_relat_1(B_8),A_870)
      | ~ v5_relat_1(B_8,'#skF_7')
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_7611])).

tff(c_9625,plain,(
    ! [B_8,A_870] :
      ( r1_tarski(k2_relat_1(B_8),A_870)
      | ~ v5_relat_1(B_8,'#skF_8')
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9608,c_7630])).

tff(c_9638,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9608,c_146])).

tff(c_9757,plain,(
    ! [A_1100,B_1101] :
      ( r2_hidden('#skF_3'(A_1100,B_1101),k1_relat_1(A_1100))
      | r2_hidden('#skF_4'(A_1100,B_1101),B_1101)
      | k2_relat_1(A_1100) = B_1101
      | ~ v1_funct_1(A_1100)
      | ~ v1_relat_1(A_1100) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_9764,plain,(
    ! [A_1100,B_1101,B_2] :
      ( r2_hidden('#skF_4'(A_1100,B_1101),B_2)
      | ~ r1_tarski(B_1101,B_2)
      | r2_hidden('#skF_3'(A_1100,B_1101),k1_relat_1(A_1100))
      | k2_relat_1(A_1100) = B_1101
      | ~ v1_funct_1(A_1100)
      | ~ v1_relat_1(A_1100) ) ),
    inference(resolution,[status(thm)],[c_9757,c_2])).

tff(c_5046,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_9641,plain,(
    ! [D_67,B_89] :
      ( r2_hidden('#skF_9'(D_67),B_89)
      | ~ r1_tarski('#skF_6',B_89)
      | ~ r2_hidden(D_67,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9608,c_112])).

tff(c_9642,plain,(
    ! [D_67] :
      ( k1_funct_1('#skF_8','#skF_9'(D_67)) = D_67
      | ~ r2_hidden(D_67,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9608,c_62])).

tff(c_10052,plain,(
    ! [A_1168,B_1169,D_1170] :
      ( k1_funct_1(A_1168,'#skF_3'(A_1168,B_1169)) = '#skF_2'(A_1168,B_1169)
      | k1_funct_1(A_1168,D_1170) != '#skF_4'(A_1168,B_1169)
      | ~ r2_hidden(D_1170,k1_relat_1(A_1168))
      | k2_relat_1(A_1168) = B_1169
      | ~ v1_funct_1(A_1168)
      | ~ v1_relat_1(A_1168) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10056,plain,(
    ! [B_1169,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1169)) = '#skF_2'('#skF_8',B_1169)
      | D_67 != '#skF_4'('#skF_8',B_1169)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1169
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9642,c_10052])).

tff(c_10060,plain,(
    ! [B_1169,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1169)) = '#skF_2'('#skF_8',B_1169)
      | D_67 != '#skF_4'('#skF_8',B_1169)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1169
      | ~ r2_hidden(D_67,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_10056])).

tff(c_10245,plain,(
    ! [B_1205] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1205)) = '#skF_2'('#skF_8',B_1205)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1205)),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1205
      | ~ r2_hidden('#skF_4'('#skF_8',B_1205),'#skF_8') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10060])).

tff(c_10251,plain,(
    ! [B_1205] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1205)) = '#skF_2'('#skF_8',B_1205)
      | k2_relat_1('#skF_8') = B_1205
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_4'('#skF_8',B_1205),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_9641,c_10245])).

tff(c_10406,plain,(
    ! [B_1216] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1216)) = '#skF_2'('#skF_8',B_1216)
      | k2_relat_1('#skF_8') = B_1216
      | ~ r2_hidden('#skF_4'('#skF_8',B_1216),'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5046,c_10251])).

tff(c_10414,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_28,c_10406])).

tff(c_10419,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_10414])).

tff(c_10420,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_9638,c_10419])).

tff(c_168,plain,(
    ! [A_109,D_110,B_2] :
      ( r2_hidden(k1_funct_1(A_109,D_110),B_2)
      | ~ r1_tarski(k2_relat_1(A_109),B_2)
      | ~ r2_hidden(D_110,k1_relat_1(A_109))
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_10429,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_8'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10420,c_168])).

tff(c_10444,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_8'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_10429])).

tff(c_10572,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_10444])).

tff(c_10578,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_8'),B_2)
      | ~ r1_tarski('#skF_8',B_2)
      | k2_relat_1('#skF_8') = '#skF_8'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_9764,c_10572])).

tff(c_10594,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_8'),B_2)
      | k2_relat_1('#skF_8') = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_9628,c_10578])).

tff(c_10595,plain,(
    ! [B_2] : r2_hidden('#skF_4'('#skF_8','#skF_8'),B_2) ),
    inference(negUnitSimplification,[status(thm)],[c_9638,c_10594])).

tff(c_121,plain,(
    ! [D_94,B_2,B_95] :
      ( r2_hidden('#skF_9'(D_94),B_2)
      | ~ r1_tarski(B_95,B_2)
      | ~ r1_tarski('#skF_6',B_95)
      | ~ r2_hidden(D_94,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_5048,plain,(
    ! [D_94] :
      ( r2_hidden('#skF_9'(D_94),k1_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden(D_94,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5046,c_121])).

tff(c_5061,plain,(
    ! [D_611] :
      ( r2_hidden('#skF_9'(D_611),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_611,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_5048])).

tff(c_5064,plain,(
    ! [D_611,B_2] :
      ( r2_hidden('#skF_9'(D_611),B_2)
      | ~ r1_tarski(k1_relat_1('#skF_8'),B_2)
      | ~ r2_hidden(D_611,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5061,c_2])).

tff(c_9632,plain,(
    ! [D_611,B_2] :
      ( r2_hidden('#skF_9'(D_611),B_2)
      | ~ r1_tarski(k1_relat_1('#skF_8'),B_2)
      | ~ r2_hidden(D_611,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9608,c_5064])).

tff(c_9946,plain,(
    ! [A_1140,B_1141,D_1142] :
      ( r2_hidden('#skF_3'(A_1140,B_1141),k1_relat_1(A_1140))
      | k1_funct_1(A_1140,D_1142) != '#skF_4'(A_1140,B_1141)
      | ~ r2_hidden(D_1142,k1_relat_1(A_1140))
      | k2_relat_1(A_1140) = B_1141
      | ~ v1_funct_1(A_1140)
      | ~ v1_relat_1(A_1140) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_9950,plain,(
    ! [B_1141,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_1141),k1_relat_1('#skF_8'))
      | D_67 != '#skF_4'('#skF_8',B_1141)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1141
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9642,c_9946])).

tff(c_9954,plain,(
    ! [B_1141,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_1141),k1_relat_1('#skF_8'))
      | D_67 != '#skF_4'('#skF_8',B_1141)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1141
      | ~ r2_hidden(D_67,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_9950])).

tff(c_10149,plain,(
    ! [B_1187] :
      ( r2_hidden('#skF_3'('#skF_8',B_1187),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1187)),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1187
      | ~ r2_hidden('#skF_4'('#skF_8',B_1187),'#skF_8') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_9954])).

tff(c_10152,plain,(
    ! [B_1187] :
      ( r2_hidden('#skF_3'('#skF_8',B_1187),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1187
      | ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_4'('#skF_8',B_1187),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_9632,c_10149])).

tff(c_10167,plain,(
    ! [B_1189] :
      ( r2_hidden('#skF_3'('#skF_8',B_1189),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1189
      | ~ r2_hidden('#skF_4'('#skF_8',B_1189),'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_10152])).

tff(c_10170,plain,(
    ! [B_1189,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1189),B_2)
      | ~ r1_tarski(k1_relat_1('#skF_8'),B_2)
      | k2_relat_1('#skF_8') = B_1189
      | ~ r2_hidden('#skF_4'('#skF_8',B_1189),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10167,c_2])).

tff(c_10581,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_10170,c_10572])).

tff(c_10598,plain,
    ( k2_relat_1('#skF_8') = '#skF_8'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_10581])).

tff(c_10599,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_9638,c_10598])).

tff(c_10640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10595,c_10599])).

tff(c_10696,plain,(
    ! [B_1226] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_8'),B_1226)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1226) ) ),
    inference(splitRight,[status(thm)],[c_10444])).

tff(c_10706,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_10696,c_26])).

tff(c_10716,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_10706])).

tff(c_10717,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_9638,c_10716])).

tff(c_10719,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_10717])).

tff(c_10722,plain,
    ( ~ v5_relat_1('#skF_8','#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_9625,c_10719])).

tff(c_10729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_7514,c_10722])).

tff(c_10730,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_10717])).

tff(c_10833,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_8'),B_2)
      | ~ r1_tarski('#skF_8',B_2) ) ),
    inference(resolution,[status(thm)],[c_10730,c_2])).

tff(c_10840,plain,(
    ! [B_2] : r2_hidden('#skF_4'('#skF_8','#skF_8'),B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9628,c_10833])).

tff(c_5051,plain,(
    ! [D_94] :
      ( r2_hidden('#skF_9'(D_94),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_94,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_5048])).

tff(c_9636,plain,(
    ! [D_94] :
      ( r2_hidden('#skF_9'(D_94),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_94,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9608,c_5051])).

tff(c_10731,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_10717])).

tff(c_7610,plain,(
    ! [A_866,A_868] :
      ( ~ r1_tarski(A_866,'#skF_7')
      | r1_tarski(A_866,A_868) ) ),
    inference(resolution,[status(thm)],[c_7593,c_4])).

tff(c_9626,plain,(
    ! [A_866,A_868] :
      ( ~ r1_tarski(A_866,'#skF_8')
      | r1_tarski(A_866,A_868) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9608,c_7610])).

tff(c_10761,plain,(
    ! [A_868] : r1_tarski(k2_relat_1('#skF_8'),A_868) ),
    inference(resolution,[status(thm)],[c_10731,c_9626])).

tff(c_10641,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_8'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2) ) ),
    inference(splitRight,[status(thm)],[c_10444])).

tff(c_10842,plain,(
    ! [B_1228] : r2_hidden('#skF_2'('#skF_8','#skF_8'),B_1228) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10761,c_10641])).

tff(c_10845,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_8'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10842,c_20])).

tff(c_10857,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_10845])).

tff(c_10931,plain,(
    ! [D_1233] :
      ( k1_funct_1('#skF_8',D_1233) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_1233,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9638,c_10857])).

tff(c_11086,plain,(
    ! [D_1237] :
      ( k1_funct_1('#skF_8','#skF_9'(D_1237)) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_1237,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_9636,c_10931])).

tff(c_11091,plain,(
    ! [D_1238] :
      ( D_1238 != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_1238,'#skF_8')
      | ~ r2_hidden(D_1238,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9642,c_11086])).

tff(c_11097,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_10840,c_11091])).

tff(c_11147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10840,c_11097])).

tff(c_11149,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_5088])).

tff(c_5090,plain,(
    ! [A_618] :
      ( r1_tarski(A_618,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_618,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5052,c_4])).

tff(c_5099,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,'#skF_7')
      | r1_tarski(A_1,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_111,c_5090])).

tff(c_11322,plain,(
    ! [A_1267,B_1268,B_1269,B_1270] :
      ( r2_hidden('#skF_1'(A_1267,B_1268),B_1269)
      | ~ r1_tarski(B_1270,B_1269)
      | ~ r1_tarski(A_1267,B_1270)
      | r1_tarski(A_1267,B_1268) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_12019,plain,(
    ! [A_1346,B_1347,A_1348] :
      ( r2_hidden('#skF_1'(A_1346,B_1347),k2_relat_1('#skF_8'))
      | ~ r1_tarski(A_1346,A_1348)
      | r1_tarski(A_1346,B_1347)
      | ~ r1_tarski(A_1348,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5099,c_11322])).

tff(c_12031,plain,(
    ! [B_1347] :
      ( r2_hidden('#skF_1'('#skF_6',B_1347),k2_relat_1('#skF_8'))
      | r1_tarski('#skF_6',B_1347)
      | ~ r1_tarski('#skF_7','#skF_7') ) ),
    inference(resolution,[status(thm)],[c_11149,c_12019])).

tff(c_12052,plain,(
    ! [B_1349] :
      ( r2_hidden('#skF_1'('#skF_6',B_1349),k2_relat_1('#skF_8'))
      | r1_tarski('#skF_6',B_1349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_12031])).

tff(c_12098,plain,(
    ! [B_1350,B_1351] :
      ( r2_hidden('#skF_1'('#skF_6',B_1350),B_1351)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1351)
      | r1_tarski('#skF_6',B_1350) ) ),
    inference(resolution,[status(thm)],[c_12052,c_2])).

tff(c_12114,plain,(
    ! [B_1350,A_7] :
      ( r2_hidden('#skF_1'('#skF_6',B_1350),A_7)
      | ~ v5_relat_1('#skF_8',A_7)
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7')
      | r1_tarski('#skF_6',B_1350) ) ),
    inference(resolution,[status(thm)],[c_12098,c_5075])).

tff(c_12325,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_12114])).

tff(c_12334,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_12325])).

tff(c_12342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_105,c_12334])).

tff(c_12344,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_12114])).

tff(c_11583,plain,(
    ! [B_1296,A_1297,C_1298] :
      ( k1_xboole_0 = B_1296
      | k1_relset_1(A_1297,B_1296,C_1298) = A_1297
      | ~ v1_funct_2(C_1298,A_1297,B_1296)
      | ~ m1_subset_1(C_1298,k1_zfmisc_1(k2_zfmisc_1(A_1297,B_1296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_11586,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_11583])).

tff(c_11589,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_136,c_11586])).

tff(c_11590,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_11589])).

tff(c_11978,plain,(
    ! [A_1340,B_1341] :
      ( r2_hidden('#skF_3'(A_1340,B_1341),k1_relat_1(A_1340))
      | r2_hidden('#skF_4'(A_1340,B_1341),B_1341)
      | k2_relat_1(A_1340) = B_1341
      | ~ v1_funct_1(A_1340)
      | ~ v1_relat_1(A_1340) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_11987,plain,(
    ! [A_1340,B_1341,B_2] :
      ( r2_hidden('#skF_3'(A_1340,B_1341),B_2)
      | ~ r1_tarski(k1_relat_1(A_1340),B_2)
      | r2_hidden('#skF_4'(A_1340,B_1341),B_1341)
      | k2_relat_1(A_1340) = B_1341
      | ~ v1_funct_1(A_1340)
      | ~ v1_relat_1(A_1340) ) ),
    inference(resolution,[status(thm)],[c_11978,c_2])).

tff(c_12802,plain,(
    ! [A_1393,B_1394,D_1395] :
      ( k1_funct_1(A_1393,'#skF_3'(A_1393,B_1394)) = '#skF_2'(A_1393,B_1394)
      | k1_funct_1(A_1393,D_1395) != '#skF_4'(A_1393,B_1394)
      | ~ r2_hidden(D_1395,k1_relat_1(A_1393))
      | k2_relat_1(A_1393) = B_1394
      | ~ v1_funct_1(A_1393)
      | ~ v1_relat_1(A_1393) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12808,plain,(
    ! [B_1394,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1394)) = '#skF_2'('#skF_8',B_1394)
      | D_67 != '#skF_4'('#skF_8',B_1394)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1394
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_12802])).

tff(c_12810,plain,(
    ! [B_1394,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1394)) = '#skF_2'('#skF_8',B_1394)
      | D_67 != '#skF_4'('#skF_8',B_1394)
      | ~ r2_hidden('#skF_9'(D_67),'#skF_6')
      | k2_relat_1('#skF_8') = B_1394
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_11590,c_12808])).

tff(c_13522,plain,(
    ! [B_1460] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1460)) = '#skF_2'('#skF_8',B_1460)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1460)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1460
      | ~ r2_hidden('#skF_4'('#skF_8',B_1460),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_12810])).

tff(c_13534,plain,(
    ! [B_1460] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1460)) = '#skF_2'('#skF_8',B_1460)
      | k2_relat_1('#skF_8') = B_1460
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_1460),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_112,c_13522])).

tff(c_13604,plain,(
    ! [B_1470] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1470)) = '#skF_2'('#skF_8',B_1470)
      | k2_relat_1('#skF_8') = B_1470
      | ~ r2_hidden('#skF_4'('#skF_8',B_1470),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_13534])).

tff(c_13618,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_28,c_13604])).

tff(c_13625,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_13618])).

tff(c_13626,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_13625])).

tff(c_13638,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_13626,c_14])).

tff(c_13649,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_11590,c_13638])).

tff(c_13651,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_13649])).

tff(c_13654,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
    | r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_11987,c_13651])).

tff(c_13678,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_73,c_11590,c_13654])).

tff(c_13679,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_13678])).

tff(c_12622,plain,(
    ! [A_1381,B_1382,D_1383] :
      ( r2_hidden('#skF_3'(A_1381,B_1382),k1_relat_1(A_1381))
      | k1_funct_1(A_1381,D_1383) != '#skF_4'(A_1381,B_1382)
      | ~ r2_hidden(D_1383,k1_relat_1(A_1381))
      | k2_relat_1(A_1381) = B_1382
      | ~ v1_funct_1(A_1381)
      | ~ v1_relat_1(A_1381) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12628,plain,(
    ! [B_1382,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_1382),k1_relat_1('#skF_8'))
      | D_67 != '#skF_4'('#skF_8',B_1382)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1382
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_12622])).

tff(c_12630,plain,(
    ! [B_1382,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_1382),'#skF_6')
      | D_67 != '#skF_4'('#skF_8',B_1382)
      | ~ r2_hidden('#skF_9'(D_67),'#skF_6')
      | k2_relat_1('#skF_8') = B_1382
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_11590,c_11590,c_12628])).

tff(c_13256,plain,(
    ! [B_1444] :
      ( r2_hidden('#skF_3'('#skF_8',B_1444),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1444)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1444
      | ~ r2_hidden('#skF_4'('#skF_8',B_1444),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_12630])).

tff(c_13268,plain,(
    ! [B_1444] :
      ( r2_hidden('#skF_3'('#skF_8',B_1444),'#skF_6')
      | k2_relat_1('#skF_8') = B_1444
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_1444),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_112,c_13256])).

tff(c_13416,plain,(
    ! [B_1447] :
      ( r2_hidden('#skF_3'('#skF_8',B_1447),'#skF_6')
      | k2_relat_1('#skF_8') = B_1447
      | ~ r2_hidden('#skF_4'('#skF_8',B_1447),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_13268])).

tff(c_13419,plain,(
    ! [B_1447,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1447),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | k2_relat_1('#skF_8') = B_1447
      | ~ r2_hidden('#skF_4'('#skF_8',B_1447),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_13416,c_2])).

tff(c_13660,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_13419,c_13651])).

tff(c_13684,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_13660])).

tff(c_13685,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_13684])).

tff(c_13714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13679,c_13685])).

tff(c_13716,plain,(
    r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_13649])).

tff(c_13630,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13626,c_168])).

tff(c_13643,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_11590,c_13630])).

tff(c_13800,plain,(
    ! [B_1476] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_1476)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13716,c_13643])).

tff(c_13806,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_13800,c_20])).

tff(c_13819,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12344,c_88,c_60,c_11590,c_13806])).

tff(c_13969,plain,(
    ! [D_1482] :
      ( k1_funct_1('#skF_8',D_1482) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1482,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_13819])).

tff(c_14210,plain,(
    ! [D_1483] :
      ( k1_funct_1('#skF_8','#skF_9'(D_1483)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1483,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_13969])).

tff(c_14214,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_14210])).

tff(c_13810,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_13800,c_26])).

tff(c_13823,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12344,c_88,c_60,c_13810])).

tff(c_13824,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_13823])).

tff(c_14216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14214,c_13824])).

tff(c_14217,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_11589])).

tff(c_11151,plain,(
    ! [D_94] :
      ( r2_hidden('#skF_9'(D_94),'#skF_7')
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden(D_94,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_11149,c_121])).

tff(c_11173,plain,(
    ! [D_1240] :
      ( r2_hidden('#skF_9'(D_1240),'#skF_7')
      | ~ r2_hidden(D_1240,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_11151])).

tff(c_11196,plain,(
    ! [D_1247,B_1248] :
      ( r2_hidden('#skF_9'(D_1247),B_1248)
      | ~ r1_tarski('#skF_7',B_1248)
      | ~ r2_hidden(D_1247,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_11173,c_2])).

tff(c_11297,plain,(
    ! [D_1264,B_1265,B_1266] :
      ( r2_hidden('#skF_9'(D_1264),B_1265)
      | ~ r1_tarski(B_1266,B_1265)
      | ~ r1_tarski('#skF_7',B_1266)
      | ~ r2_hidden(D_1264,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_11196,c_2])).

tff(c_11320,plain,(
    ! [D_1264,A_6] :
      ( r2_hidden('#skF_9'(D_1264),A_6)
      | ~ r1_tarski('#skF_7',k1_xboole_0)
      | ~ r2_hidden(D_1264,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8,c_11297])).

tff(c_11321,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_11320])).

tff(c_14224,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14217,c_11321])).

tff(c_14234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_14224])).

tff(c_14236,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11320])).

tff(c_14272,plain,(
    ! [A_1488,B_1489,B_1490,B_1491] :
      ( r2_hidden('#skF_1'(A_1488,B_1489),B_1490)
      | ~ r1_tarski(B_1491,B_1490)
      | ~ r1_tarski(A_1488,B_1491)
      | r1_tarski(A_1488,B_1489) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_14433,plain,(
    ! [A_1514,B_1515] :
      ( r2_hidden('#skF_1'(A_1514,B_1515),k1_xboole_0)
      | ~ r1_tarski(A_1514,'#skF_7')
      | r1_tarski(A_1514,B_1515) ) ),
    inference(resolution,[status(thm)],[c_14236,c_14272])).

tff(c_14444,plain,(
    ! [A_1516] :
      ( ~ r1_tarski(A_1516,'#skF_7')
      | r1_tarski(A_1516,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14433,c_4])).

tff(c_14454,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_14444,c_161])).

tff(c_14465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11149,c_14454])).

tff(c_14466,plain,(
    ! [D_106,A_6] :
      ( r2_hidden('#skF_9'(D_106),A_6)
      | ~ r2_hidden(D_106,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_14478,plain,(
    ! [A_1522,D_1523] :
      ( r2_hidden(k1_funct_1(A_1522,D_1523),k2_relat_1(A_1522))
      | ~ r2_hidden(D_1523,k1_relat_1(A_1522))
      | ~ v1_funct_1(A_1522)
      | ~ v1_relat_1(A_1522) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14483,plain,(
    ! [D_67] :
      ( r2_hidden(D_67,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_14478])).

tff(c_14487,plain,(
    ! [D_1524] :
      ( r2_hidden(D_1524,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_1524),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_1524,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_14483])).

tff(c_14493,plain,(
    ! [D_1525] :
      ( r2_hidden(D_1525,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_1525,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14466,c_14487])).

tff(c_14527,plain,(
    ! [A_1532] :
      ( r1_tarski(A_1532,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_1532,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14493,c_4])).

tff(c_14537,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_14527])).

tff(c_14536,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,'#skF_7')
      | r1_tarski(A_1,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_111,c_14527])).

tff(c_14591,plain,(
    ! [A_1538,B_1539,B_1540,B_1541] :
      ( r2_hidden('#skF_1'(A_1538,B_1539),B_1540)
      | ~ r1_tarski(B_1541,B_1540)
      | ~ r1_tarski(A_1538,B_1541)
      | r1_tarski(A_1538,B_1539) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_14825,plain,(
    ! [A_1571,B_1572,A_1573] :
      ( r2_hidden('#skF_1'(A_1571,B_1572),k2_relat_1('#skF_8'))
      | ~ r1_tarski(A_1571,A_1573)
      | r1_tarski(A_1571,B_1572)
      | ~ r1_tarski(A_1573,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14536,c_14591])).

tff(c_14847,plain,(
    ! [B_1572] :
      ( r2_hidden('#skF_1'('#skF_7',B_1572),k2_relat_1('#skF_8'))
      | r1_tarski('#skF_7',B_1572)
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14537,c_14825])).

tff(c_14852,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_14847])).

tff(c_14861,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_14852])).

tff(c_14871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_105,c_14861])).

tff(c_14873,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_14847])).

tff(c_15108,plain,(
    ! [B_1592,A_1593,C_1594] :
      ( k1_xboole_0 = B_1592
      | k1_relset_1(A_1593,B_1592,C_1594) = A_1593
      | ~ v1_funct_2(C_1594,A_1593,B_1592)
      | ~ m1_subset_1(C_1594,k1_zfmisc_1(k2_zfmisc_1(A_1593,B_1592))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_15111,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_15108])).

tff(c_15114,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_136,c_15111])).

tff(c_15115,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_15114])).

tff(c_14467,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_14611,plain,(
    ! [A_1544,B_1545,A_1546] :
      ( r2_hidden('#skF_1'(A_1544,B_1545),A_1546)
      | ~ r1_tarski(A_1544,k1_xboole_0)
      | r1_tarski(A_1544,B_1545) ) ),
    inference(resolution,[status(thm)],[c_8,c_14591])).

tff(c_14629,plain,(
    ! [A_1547,A_1548] :
      ( ~ r1_tarski(A_1547,k1_xboole_0)
      | r1_tarski(A_1547,A_1548) ) ),
    inference(resolution,[status(thm)],[c_14611,c_4])).

tff(c_14641,plain,(
    ! [A_1548] : r1_tarski('#skF_6',A_1548) ),
    inference(resolution,[status(thm)],[c_14467,c_14629])).

tff(c_16025,plain,(
    ! [A_1693,B_1694,D_1695] :
      ( r2_hidden('#skF_3'(A_1693,B_1694),k1_relat_1(A_1693))
      | k1_funct_1(A_1693,D_1695) != '#skF_4'(A_1693,B_1694)
      | ~ r2_hidden(D_1695,k1_relat_1(A_1693))
      | k2_relat_1(A_1693) = B_1694
      | ~ v1_funct_1(A_1693)
      | ~ v1_relat_1(A_1693) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16031,plain,(
    ! [B_1694,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_1694),k1_relat_1('#skF_8'))
      | D_67 != '#skF_4'('#skF_8',B_1694)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1694
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_16025])).

tff(c_16033,plain,(
    ! [B_1694,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_1694),'#skF_6')
      | D_67 != '#skF_4'('#skF_8',B_1694)
      | ~ r2_hidden('#skF_9'(D_67),'#skF_6')
      | k2_relat_1('#skF_8') = B_1694
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_15115,c_15115,c_16031])).

tff(c_16428,plain,(
    ! [B_1727] :
      ( r2_hidden('#skF_3'('#skF_8',B_1727),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1727)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1727
      | ~ r2_hidden('#skF_4'('#skF_8',B_1727),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16033])).

tff(c_16433,plain,(
    ! [B_1728] :
      ( r2_hidden('#skF_3'('#skF_8',B_1728),'#skF_6')
      | k2_relat_1('#skF_8') = B_1728
      | ~ r2_hidden('#skF_4'('#skF_8',B_1728),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14466,c_16428])).

tff(c_16435,plain,(
    ! [B_1728,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1728),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | k2_relat_1('#skF_8') = B_1728
      | ~ r2_hidden('#skF_4'('#skF_8',B_1728),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16433,c_2])).

tff(c_16438,plain,(
    ! [B_1728,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1728),B_2)
      | k2_relat_1('#skF_8') = B_1728
      | ~ r2_hidden('#skF_4'('#skF_8',B_1728),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14641,c_16435])).

tff(c_16316,plain,(
    ! [A_1714,B_1715,D_1716] :
      ( k1_funct_1(A_1714,'#skF_3'(A_1714,B_1715)) = '#skF_2'(A_1714,B_1715)
      | k1_funct_1(A_1714,D_1716) != '#skF_4'(A_1714,B_1715)
      | ~ r2_hidden(D_1716,k1_relat_1(A_1714))
      | k2_relat_1(A_1714) = B_1715
      | ~ v1_funct_1(A_1714)
      | ~ v1_relat_1(A_1714) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16322,plain,(
    ! [B_1715,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1715)) = '#skF_2'('#skF_8',B_1715)
      | D_67 != '#skF_4'('#skF_8',B_1715)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1715
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_16316])).

tff(c_16324,plain,(
    ! [B_1715,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1715)) = '#skF_2'('#skF_8',B_1715)
      | D_67 != '#skF_4'('#skF_8',B_1715)
      | ~ r2_hidden('#skF_9'(D_67),'#skF_6')
      | k2_relat_1('#skF_8') = B_1715
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_15115,c_16322])).

tff(c_16519,plain,(
    ! [B_1739] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1739)) = '#skF_2'('#skF_8',B_1739)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1739)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1739
      | ~ r2_hidden('#skF_4'('#skF_8',B_1739),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16324])).

tff(c_16524,plain,(
    ! [B_1740] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1740)) = '#skF_2'('#skF_8',B_1740)
      | k2_relat_1('#skF_8') = B_1740
      | ~ r2_hidden('#skF_4'('#skF_8',B_1740),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14466,c_16519])).

tff(c_16532,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_28,c_16524])).

tff(c_16541,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_16532])).

tff(c_16542,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_16541])).

tff(c_16554,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_16542,c_14])).

tff(c_16565,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_15115,c_16554])).

tff(c_16567,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_16565])).

tff(c_16573,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_16438,c_16567])).

tff(c_16584,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_16573])).

tff(c_15396,plain,(
    ! [A_1630,B_1631] :
      ( r2_hidden('#skF_3'(A_1630,B_1631),k1_relat_1(A_1630))
      | r2_hidden('#skF_4'(A_1630,B_1631),B_1631)
      | k2_relat_1(A_1630) = B_1631
      | ~ v1_funct_1(A_1630)
      | ~ v1_relat_1(A_1630) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16603,plain,(
    ! [A_1741,B_1742,B_1743] :
      ( r2_hidden('#skF_3'(A_1741,B_1742),B_1743)
      | ~ r1_tarski(k1_relat_1(A_1741),B_1743)
      | r2_hidden('#skF_4'(A_1741,B_1742),B_1742)
      | k2_relat_1(A_1741) = B_1742
      | ~ v1_funct_1(A_1741)
      | ~ v1_relat_1(A_1741) ) ),
    inference(resolution,[status(thm)],[c_15396,c_2])).

tff(c_16606,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
    | r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_16603,c_16567])).

tff(c_16626,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_14641,c_15115,c_16606])).

tff(c_16628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_16584,c_16626])).

tff(c_16630,plain,(
    r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_16565])).

tff(c_16632,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_3'('#skF_8','#skF_7'),B_2)
      | ~ r1_tarski('#skF_6',B_2) ) ),
    inference(resolution,[status(thm)],[c_16630,c_2])).

tff(c_16635,plain,(
    ! [B_2] : r2_hidden('#skF_3'('#skF_8','#skF_7'),B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14641,c_16632])).

tff(c_14484,plain,(
    ! [A_1522,D_1523,B_2] :
      ( r2_hidden(k1_funct_1(A_1522,D_1523),B_2)
      | ~ r1_tarski(k2_relat_1(A_1522),B_2)
      | ~ r2_hidden(D_1523,k1_relat_1(A_1522))
      | ~ v1_funct_1(A_1522)
      | ~ v1_relat_1(A_1522) ) ),
    inference(resolution,[status(thm)],[c_14478,c_2])).

tff(c_16551,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16542,c_14484])).

tff(c_16563,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_15115,c_16551])).

tff(c_16656,plain,(
    ! [B_1745] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_1745)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1745) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16635,c_16563])).

tff(c_16662,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16656,c_20])).

tff(c_16675,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14873,c_88,c_60,c_15115,c_16662])).

tff(c_16792,plain,(
    ! [D_1752] :
      ( k1_funct_1('#skF_8',D_1752) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1752,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_16675])).

tff(c_16931,plain,(
    ! [D_1753] :
      ( k1_funct_1('#skF_8','#skF_9'(D_1753)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1753,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14466,c_16792])).

tff(c_16935,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_16931])).

tff(c_16666,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_16656,c_26])).

tff(c_16679,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14873,c_88,c_60,c_16666])).

tff(c_16680,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_16679])).

tff(c_16937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16935,c_16680])).

tff(c_16938,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_15114])).

tff(c_14657,plain,(
    ! [B_1550,A_1551] :
      ( r1_tarski(k2_relat_1(B_1550),A_1551)
      | ~ v5_relat_1(B_1550,k1_xboole_0)
      | ~ v1_relat_1(B_1550) ) ),
    inference(resolution,[status(thm)],[c_12,c_14629])).

tff(c_14500,plain,(
    ! [D_1525,B_2] :
      ( r2_hidden(D_1525,B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r2_hidden(D_1525,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14493,c_2])).

tff(c_14665,plain,(
    ! [D_1525,A_1551] :
      ( r2_hidden(D_1525,A_1551)
      | ~ r2_hidden(D_1525,'#skF_7')
      | ~ v5_relat_1('#skF_8',k1_xboole_0)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14657,c_14500])).

tff(c_14673,plain,(
    ! [D_1525,A_1551] :
      ( r2_hidden(D_1525,A_1551)
      | ~ r2_hidden(D_1525,'#skF_7')
      | ~ v5_relat_1('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_14665])).

tff(c_14676,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_14673])).

tff(c_16944,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16938,c_14676])).

tff(c_16954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_16944])).

tff(c_16956,plain,(
    v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_14673])).

tff(c_14674,plain,(
    ! [B_1550,A_1551] :
      ( v5_relat_1(B_1550,A_1551)
      | ~ v5_relat_1(B_1550,k1_xboole_0)
      | ~ v1_relat_1(B_1550) ) ),
    inference(resolution,[status(thm)],[c_14657,c_10])).

tff(c_16958,plain,(
    ! [A_1551] :
      ( v5_relat_1('#skF_8',A_1551)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_16956,c_14674])).

tff(c_16964,plain,(
    ! [A_1551] : v5_relat_1('#skF_8',A_1551) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_16958])).

tff(c_14503,plain,(
    ! [D_1528,B_1529] :
      ( r2_hidden(D_1528,B_1529)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1529)
      | ~ r2_hidden(D_1528,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14493,c_2])).

tff(c_14506,plain,(
    ! [D_1528,A_7] :
      ( r2_hidden(D_1528,A_7)
      | ~ r2_hidden(D_1528,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_7)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_12,c_14503])).

tff(c_14514,plain,(
    ! [D_1530,A_1531] :
      ( r2_hidden(D_1530,A_1531)
      | ~ r2_hidden(D_1530,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_1531) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_14506])).

tff(c_14549,plain,(
    ! [B_1535,A_1536] :
      ( r2_hidden('#skF_1'('#skF_7',B_1535),A_1536)
      | ~ v5_relat_1('#skF_8',A_1536)
      | r1_tarski('#skF_7',B_1535) ) ),
    inference(resolution,[status(thm)],[c_6,c_14514])).

tff(c_14570,plain,(
    ! [A_1536] :
      ( ~ v5_relat_1('#skF_8',A_1536)
      | r1_tarski('#skF_7',A_1536) ) ),
    inference(resolution,[status(thm)],[c_14549,c_4])).

tff(c_16968,plain,(
    ! [A_1536] : r1_tarski('#skF_7',A_1536) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16964,c_14570])).

tff(c_17267,plain,(
    ! [B_1793,A_1794,C_1795] :
      ( k1_xboole_0 = B_1793
      | k1_relset_1(A_1794,B_1793,C_1795) = A_1794
      | ~ v1_funct_2(C_1795,A_1794,B_1793)
      | ~ m1_subset_1(C_1795,k1_zfmisc_1(k2_zfmisc_1(A_1794,B_1793))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_17270,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_17267])).

tff(c_17273,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_136,c_17270])).

tff(c_17280,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_17273])).

tff(c_17415,plain,(
    ! [A_1816,B_1817] :
      ( r2_hidden('#skF_3'(A_1816,B_1817),k1_relat_1(A_1816))
      | r2_hidden('#skF_4'(A_1816,B_1817),B_1817)
      | k2_relat_1(A_1816) = B_1817
      | ~ v1_funct_1(A_1816)
      | ~ v1_relat_1(A_1816) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_17423,plain,(
    ! [B_1817] :
      ( r2_hidden('#skF_3'('#skF_8',B_1817),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_1817),B_1817)
      | k2_relat_1('#skF_8') = B_1817
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17280,c_17415])).

tff(c_17428,plain,(
    ! [B_1818] :
      ( r2_hidden('#skF_3'('#skF_8',B_1818),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_1818),B_1818)
      | k2_relat_1('#skF_8') = B_1818 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_17423])).

tff(c_17450,plain,(
    ! [B_1821,B_1822] :
      ( r2_hidden('#skF_4'('#skF_8',B_1821),B_1822)
      | ~ r1_tarski(B_1821,B_1822)
      | r2_hidden('#skF_3'('#skF_8',B_1821),'#skF_6')
      | k2_relat_1('#skF_8') = B_1821 ) ),
    inference(resolution,[status(thm)],[c_17428,c_2])).

tff(c_17455,plain,(
    ! [B_1821,B_2,B_1822] :
      ( r2_hidden('#skF_3'('#skF_8',B_1821),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | r2_hidden('#skF_4'('#skF_8',B_1821),B_1822)
      | ~ r1_tarski(B_1821,B_1822)
      | k2_relat_1('#skF_8') = B_1821 ) ),
    inference(resolution,[status(thm)],[c_17450,c_2])).

tff(c_17459,plain,(
    ! [B_1821,B_2,B_1822] :
      ( r2_hidden('#skF_3'('#skF_8',B_1821),B_2)
      | r2_hidden('#skF_4'('#skF_8',B_1821),B_1822)
      | ~ r1_tarski(B_1821,B_1822)
      | k2_relat_1('#skF_8') = B_1821 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14641,c_17455])).

tff(c_17007,plain,(
    ! [A_1760,B_1761] :
      ( r2_hidden('#skF_1'(A_1760,B_1761),k1_xboole_0)
      | ~ r1_tarski(A_1760,'#skF_6')
      | r1_tarski(A_1760,B_1761) ) ),
    inference(resolution,[status(thm)],[c_14467,c_14591])).

tff(c_17018,plain,(
    ! [A_1762] :
      ( ~ r1_tarski(A_1762,'#skF_6')
      | r1_tarski(A_1762,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_17007,c_4])).

tff(c_129,plain,(
    ! [A_96,B_97,B_2,B_98] :
      ( r2_hidden('#skF_1'(A_96,B_97),B_2)
      | ~ r1_tarski(B_98,B_2)
      | ~ r1_tarski(A_96,B_98)
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_17234,plain,(
    ! [A_1788,B_1789,A_1790] :
      ( r2_hidden('#skF_1'(A_1788,B_1789),k1_xboole_0)
      | ~ r1_tarski(A_1788,A_1790)
      | r1_tarski(A_1788,B_1789)
      | ~ r1_tarski(A_1790,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_17018,c_129])).

tff(c_17713,plain,(
    ! [B_1864,B_1865,A_1866] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_1864),B_1865),k1_xboole_0)
      | r1_tarski(k2_relat_1(B_1864),B_1865)
      | ~ r1_tarski(A_1866,'#skF_6')
      | ~ v5_relat_1(B_1864,A_1866)
      | ~ v1_relat_1(B_1864) ) ),
    inference(resolution,[status(thm)],[c_12,c_17234])).

tff(c_17715,plain,(
    ! [B_1865,A_1551] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_1865),k1_xboole_0)
      | r1_tarski(k2_relat_1('#skF_8'),B_1865)
      | ~ r1_tarski(A_1551,'#skF_6')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_16964,c_17713])).

tff(c_17722,plain,(
    ! [B_1865,A_1551] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_1865),k1_xboole_0)
      | r1_tarski(k2_relat_1('#skF_8'),B_1865)
      | ~ r1_tarski(A_1551,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_17715])).

tff(c_17727,plain,(
    ! [A_1870] : ~ r1_tarski(A_1870,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_17722])).

tff(c_17756,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_16968,c_17727])).

tff(c_17758,plain,(
    ! [B_1871] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_1871),k1_xboole_0)
      | r1_tarski(k2_relat_1('#skF_8'),B_1871) ) ),
    inference(splitRight,[status(thm)],[c_17722])).

tff(c_17768,plain,(
    r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_17758,c_4])).

tff(c_14628,plain,(
    ! [A_1544,A_1546] :
      ( ~ r1_tarski(A_1544,k1_xboole_0)
      | r1_tarski(A_1544,A_1546) ) ),
    inference(resolution,[status(thm)],[c_14611,c_4])).

tff(c_17826,plain,(
    ! [A_1546] : r1_tarski(k2_relat_1('#skF_8'),A_1546) ),
    inference(resolution,[status(thm)],[c_17768,c_14628])).

tff(c_18079,plain,(
    ! [A_1892,B_1893,D_1894] :
      ( k1_funct_1(A_1892,'#skF_3'(A_1892,B_1893)) = '#skF_2'(A_1892,B_1893)
      | k1_funct_1(A_1892,D_1894) != '#skF_4'(A_1892,B_1893)
      | ~ r2_hidden(D_1894,k1_relat_1(A_1892))
      | k2_relat_1(A_1892) = B_1893
      | ~ v1_funct_1(A_1892)
      | ~ v1_relat_1(A_1892) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18087,plain,(
    ! [B_1893,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1893)) = '#skF_2'('#skF_8',B_1893)
      | D_67 != '#skF_4'('#skF_8',B_1893)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1893
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_18079])).

tff(c_18089,plain,(
    ! [B_1893,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1893)) = '#skF_2'('#skF_8',B_1893)
      | D_67 != '#skF_4'('#skF_8',B_1893)
      | ~ r2_hidden('#skF_9'(D_67),'#skF_6')
      | k2_relat_1('#skF_8') = B_1893
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_17280,c_18087])).

tff(c_18251,plain,(
    ! [B_1928] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1928)) = '#skF_2'('#skF_8',B_1928)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1928)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1928
      | ~ r2_hidden('#skF_4'('#skF_8',B_1928),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_18089])).

tff(c_18256,plain,(
    ! [B_1929] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1929)) = '#skF_2'('#skF_8',B_1929)
      | k2_relat_1('#skF_8') = B_1929
      | ~ r2_hidden('#skF_4'('#skF_8',B_1929),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14466,c_18251])).

tff(c_18272,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_28,c_18256])).

tff(c_18287,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_18272])).

tff(c_18288,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_18287])).

tff(c_17309,plain,(
    ! [A_1802,D_1803,B_1804] :
      ( r2_hidden(k1_funct_1(A_1802,D_1803),B_1804)
      | ~ r1_tarski(k2_relat_1(A_1802),B_1804)
      | ~ r2_hidden(D_1803,k1_relat_1(A_1802))
      | ~ v1_funct_1(A_1802)
      | ~ v1_relat_1(A_1802) ) ),
    inference(resolution,[status(thm)],[c_14478,c_2])).

tff(c_18201,plain,(
    ! [A_1921,D_1922,B_1923,B_1924] :
      ( r2_hidden(k1_funct_1(A_1921,D_1922),B_1923)
      | ~ r1_tarski(B_1924,B_1923)
      | ~ r1_tarski(k2_relat_1(A_1921),B_1924)
      | ~ r2_hidden(D_1922,k1_relat_1(A_1921))
      | ~ v1_funct_1(A_1921)
      | ~ v1_relat_1(A_1921) ) ),
    inference(resolution,[status(thm)],[c_17309,c_2])).

tff(c_18228,plain,(
    ! [A_1921,D_1922,A_6] :
      ( r2_hidden(k1_funct_1(A_1921,D_1922),A_6)
      | ~ r1_tarski(k2_relat_1(A_1921),k1_xboole_0)
      | ~ r2_hidden(D_1922,k1_relat_1(A_1921))
      | ~ v1_funct_1(A_1921)
      | ~ v1_relat_1(A_1921) ) ),
    inference(resolution,[status(thm)],[c_8,c_18201])).

tff(c_18292,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),A_6)
      | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18288,c_18228])).

tff(c_18313,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),A_6)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_17280,c_17826,c_18292])).

tff(c_18326,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_18313])).

tff(c_18344,plain,(
    ! [B_1822] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_7'),B_1822)
      | ~ r1_tarski('#skF_7',B_1822)
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_17459,c_18326])).

tff(c_18369,plain,(
    ! [B_1822] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_7'),B_1822)
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16968,c_18344])).

tff(c_18370,plain,(
    ! [B_1822] : r2_hidden('#skF_4'('#skF_8','#skF_7'),B_1822) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_18369])).

tff(c_17962,plain,(
    ! [A_1878,B_1879,D_1880] :
      ( r2_hidden('#skF_3'(A_1878,B_1879),k1_relat_1(A_1878))
      | k1_funct_1(A_1878,D_1880) != '#skF_4'(A_1878,B_1879)
      | ~ r2_hidden(D_1880,k1_relat_1(A_1878))
      | k2_relat_1(A_1878) = B_1879
      | ~ v1_funct_1(A_1878)
      | ~ v1_relat_1(A_1878) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_17970,plain,(
    ! [B_1879,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_1879),k1_relat_1('#skF_8'))
      | D_67 != '#skF_4'('#skF_8',B_1879)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1879
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_17962])).

tff(c_17972,plain,(
    ! [B_1879,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_1879),'#skF_6')
      | D_67 != '#skF_4'('#skF_8',B_1879)
      | ~ r2_hidden('#skF_9'(D_67),'#skF_6')
      | k2_relat_1('#skF_8') = B_1879
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_17280,c_17280,c_17970])).

tff(c_18133,plain,(
    ! [B_1907] :
      ( r2_hidden('#skF_3'('#skF_8',B_1907),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1907)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1907
      | ~ r2_hidden('#skF_4'('#skF_8',B_1907),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_17972])).

tff(c_18138,plain,(
    ! [B_1908] :
      ( r2_hidden('#skF_3'('#skF_8',B_1908),'#skF_6')
      | k2_relat_1('#skF_8') = B_1908
      | ~ r2_hidden('#skF_4'('#skF_8',B_1908),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14466,c_18133])).

tff(c_18140,plain,(
    ! [B_1908,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1908),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | k2_relat_1('#skF_8') = B_1908
      | ~ r2_hidden('#skF_4'('#skF_8',B_1908),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_18138,c_2])).

tff(c_18143,plain,(
    ! [B_1908,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1908),B_2)
      | k2_relat_1('#skF_8') = B_1908
      | ~ r2_hidden('#skF_4'('#skF_8',B_1908),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14641,c_18140])).

tff(c_18329,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_18143,c_18326])).

tff(c_18350,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_18329])).

tff(c_18420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18370,c_18350])).

tff(c_18423,plain,(
    ! [A_1933] : r2_hidden('#skF_2'('#skF_8','#skF_7'),A_1933) ),
    inference(splitRight,[status(thm)],[c_18313])).

tff(c_18430,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_18423,c_26])).

tff(c_18442,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_18430])).

tff(c_18443,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_18442])).

tff(c_16955,plain,(
    ! [D_1525,A_1551] :
      ( r2_hidden(D_1525,A_1551)
      | ~ r2_hidden(D_1525,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_14673])).

tff(c_18458,plain,(
    ! [A_1551] : r2_hidden('#skF_4'('#skF_8','#skF_7'),A_1551) ),
    inference(resolution,[status(thm)],[c_18443,c_16955])).

tff(c_18426,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18423,c_20])).

tff(c_18438,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_44,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_17280,c_18426])).

tff(c_18497,plain,(
    ! [D_1936] :
      ( k1_funct_1('#skF_8',D_1936) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1936,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_18438])).

tff(c_18647,plain,(
    ! [D_1940] :
      ( k1_funct_1('#skF_8','#skF_9'(D_1940)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1940,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14466,c_18497])).

tff(c_18656,plain,(
    ! [D_1941] :
      ( D_1941 != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1941,'#skF_7')
      | ~ r2_hidden(D_1941,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_18647])).

tff(c_18663,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_18458,c_18656])).

tff(c_18739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18458,c_18663])).

tff(c_18741,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_17273])).

tff(c_18740,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_17273])).

tff(c_18784,plain,(
    ! [C_1946,A_1947] :
      ( C_1946 = '#skF_7'
      | ~ v1_funct_2(C_1946,A_1947,'#skF_7')
      | A_1947 = '#skF_7'
      | ~ m1_subset_1(C_1946,k1_zfmisc_1(k2_zfmisc_1(A_1947,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18740,c_18740,c_18740,c_18740,c_44])).

tff(c_18787,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_56,c_18784])).

tff(c_18790,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_18787])).

tff(c_18791,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_18790])).

tff(c_18810,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18791,c_58])).

tff(c_18807,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18791,c_136])).

tff(c_18809,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18791,c_56])).

tff(c_50,plain,(
    ! [B_62,C_63] :
      ( k1_relset_1(k1_xboole_0,B_62,C_63) = k1_xboole_0
      | ~ v1_funct_2(C_63,k1_xboole_0,B_62)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18746,plain,(
    ! [B_62,C_63] :
      ( k1_relset_1('#skF_7',B_62,C_63) = '#skF_7'
      | ~ v1_funct_2(C_63,'#skF_7',B_62)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_62))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18740,c_18740,c_18740,c_18740,c_50])).

tff(c_18944,plain,(
    ! [B_1966,C_1967] :
      ( k1_relset_1('#skF_6',B_1966,C_1967) = '#skF_6'
      | ~ v1_funct_2(C_1967,'#skF_6',B_1966)
      | ~ m1_subset_1(C_1967,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_1966))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18791,c_18791,c_18791,c_18791,c_18746])).

tff(c_18947,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_18809,c_18944])).

tff(c_18950,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18810,c_18807,c_18947])).

tff(c_18952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18741,c_18950])).

tff(c_18953,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_18790])).

tff(c_18968,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18953,c_146])).

tff(c_18759,plain,(
    ! [A_1942,B_1943] :
      ( r2_hidden('#skF_3'(A_1942,B_1943),k1_relat_1(A_1942))
      | r2_hidden('#skF_4'(A_1942,B_1943),B_1943)
      | k2_relat_1(A_1942) = B_1943
      | ~ v1_funct_1(A_1942)
      | ~ v1_relat_1(A_1942) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18765,plain,(
    ! [A_1942,B_1943,B_2] :
      ( r2_hidden('#skF_3'(A_1942,B_1943),B_2)
      | ~ r1_tarski(k1_relat_1(A_1942),B_2)
      | r2_hidden('#skF_4'(A_1942,B_1943),B_1943)
      | k2_relat_1(A_1942) = B_1943
      | ~ v1_funct_1(A_1942)
      | ~ v1_relat_1(A_1942) ) ),
    inference(resolution,[status(thm)],[c_18759,c_2])).

tff(c_18964,plain,(
    ! [A_1536] : r1_tarski('#skF_8',A_1536) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18953,c_16968])).

tff(c_18958,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18953,c_18740])).

tff(c_17258,plain,(
    ! [B_8,B_1789,A_7] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_8),B_1789),k1_xboole_0)
      | r1_tarski(k2_relat_1(B_8),B_1789)
      | ~ r1_tarski(A_7,'#skF_6')
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_17234])).

tff(c_19447,plain,(
    ! [B_2049,B_2050,A_2051] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_2049),B_2050),'#skF_8')
      | r1_tarski(k2_relat_1(B_2049),B_2050)
      | ~ r1_tarski(A_2051,'#skF_6')
      | ~ v5_relat_1(B_2049,A_2051)
      | ~ v1_relat_1(B_2049) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18958,c_17258])).

tff(c_19451,plain,(
    ! [B_2050,A_1551] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_2050),'#skF_8')
      | r1_tarski(k2_relat_1('#skF_8'),B_2050)
      | ~ r1_tarski(A_1551,'#skF_6')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_16964,c_19447])).

tff(c_19457,plain,(
    ! [B_2050,A_1551] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_2050),'#skF_8')
      | r1_tarski(k2_relat_1('#skF_8'),B_2050)
      | ~ r1_tarski(A_1551,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_19451])).

tff(c_19468,plain,(
    ! [A_2055] : ~ r1_tarski(A_2055,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_19457])).

tff(c_19490,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18964,c_19468])).

tff(c_19492,plain,(
    ! [B_2056] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_8'),B_2056),'#skF_8')
      | r1_tarski(k2_relat_1('#skF_8'),B_2056) ) ),
    inference(splitRight,[status(thm)],[c_19457])).

tff(c_19511,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_19492,c_4])).

tff(c_16993,plain,(
    ! [D_1758,A_1759] :
      ( r2_hidden(D_1758,A_1759)
      | ~ r2_hidden(D_1758,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_14673])).

tff(c_17107,plain,(
    ! [A_1773,B_1774,A_1775] :
      ( r2_hidden('#skF_1'(A_1773,B_1774),A_1775)
      | ~ r1_tarski(A_1773,'#skF_7')
      | r1_tarski(A_1773,B_1774) ) ),
    inference(resolution,[status(thm)],[c_111,c_16993])).

tff(c_17124,plain,(
    ! [A_1773,A_1775] :
      ( ~ r1_tarski(A_1773,'#skF_7')
      | r1_tarski(A_1773,A_1775) ) ),
    inference(resolution,[status(thm)],[c_17107,c_4])).

tff(c_18962,plain,(
    ! [A_1773,A_1775] :
      ( ~ r1_tarski(A_1773,'#skF_8')
      | r1_tarski(A_1773,A_1775) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18953,c_17124])).

tff(c_19537,plain,(
    ! [A_1775] : r1_tarski(k2_relat_1('#skF_8'),A_1775) ),
    inference(resolution,[status(thm)],[c_19511,c_18962])).

tff(c_18967,plain,(
    ! [D_106,A_6] :
      ( r2_hidden('#skF_9'(D_106),A_6)
      | ~ r2_hidden(D_106,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18953,c_14466])).

tff(c_18971,plain,(
    ! [D_67] :
      ( k1_funct_1('#skF_8','#skF_9'(D_67)) = D_67
      | ~ r2_hidden(D_67,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18953,c_62])).

tff(c_19231,plain,(
    ! [A_2006,B_2007,D_2008] :
      ( k1_funct_1(A_2006,'#skF_3'(A_2006,B_2007)) = '#skF_2'(A_2006,B_2007)
      | k1_funct_1(A_2006,D_2008) != '#skF_4'(A_2006,B_2007)
      | ~ r2_hidden(D_2008,k1_relat_1(A_2006))
      | k2_relat_1(A_2006) = B_2007
      | ~ v1_funct_1(A_2006)
      | ~ v1_relat_1(A_2006) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_19233,plain,(
    ! [B_2007,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_2007)) = '#skF_2'('#skF_8',B_2007)
      | D_67 != '#skF_4'('#skF_8',B_2007)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_2007
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18971,c_19231])).

tff(c_19239,plain,(
    ! [B_2007,D_67] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_2007)) = '#skF_2'('#skF_8',B_2007)
      | D_67 != '#skF_4'('#skF_8',B_2007)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_2007
      | ~ r2_hidden(D_67,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_19233])).

tff(c_19512,plain,(
    ! [B_2057] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_2057)) = '#skF_2'('#skF_8',B_2057)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_2057)),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_2057
      | ~ r2_hidden('#skF_4'('#skF_8',B_2057),'#skF_8') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_19239])).

tff(c_19707,plain,(
    ! [B_2069] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_2069)) = '#skF_2'('#skF_8',B_2069)
      | k2_relat_1('#skF_8') = B_2069
      | ~ r2_hidden('#skF_4'('#skF_8',B_2069),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18967,c_19512])).

tff(c_19715,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_28,c_19707])).

tff(c_19720,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_19715])).

tff(c_19721,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_18968,c_19720])).

tff(c_19257,plain,(
    ! [A_2015,D_2016,B_2017] :
      ( r2_hidden(k1_funct_1(A_2015,D_2016),B_2017)
      | ~ r1_tarski(k2_relat_1(A_2015),B_2017)
      | ~ r2_hidden(D_2016,k1_relat_1(A_2015))
      | ~ v1_funct_1(A_2015)
      | ~ v1_relat_1(A_2015) ) ),
    inference(resolution,[status(thm)],[c_14478,c_2])).

tff(c_18963,plain,(
    ! [D_1525,A_1551] :
      ( r2_hidden(D_1525,A_1551)
      | ~ r2_hidden(D_1525,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18953,c_16955])).

tff(c_19272,plain,(
    ! [A_2015,D_2016,A_1551] :
      ( r2_hidden(k1_funct_1(A_2015,D_2016),A_1551)
      | ~ r1_tarski(k2_relat_1(A_2015),'#skF_8')
      | ~ r2_hidden(D_2016,k1_relat_1(A_2015))
      | ~ v1_funct_1(A_2015)
      | ~ v1_relat_1(A_2015) ) ),
    inference(resolution,[status(thm)],[c_19257,c_18963])).

tff(c_19758,plain,(
    ! [A_1551] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_8'),A_1551)
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8')
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19721,c_19272])).

tff(c_19774,plain,(
    ! [A_1551] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_8'),A_1551)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_19537,c_19758])).

tff(c_19800,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_19774])).

tff(c_19803,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
    | r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_18765,c_19800])).

tff(c_19818,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_73,c_19803])).

tff(c_19819,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_18968,c_19818])).

tff(c_19154,plain,(
    ! [A_1988,B_1989,D_1990] :
      ( r2_hidden('#skF_3'(A_1988,B_1989),k1_relat_1(A_1988))
      | k1_funct_1(A_1988,D_1990) != '#skF_4'(A_1988,B_1989)
      | ~ r2_hidden(D_1990,k1_relat_1(A_1988))
      | k2_relat_1(A_1988) = B_1989
      | ~ v1_funct_1(A_1988)
      | ~ v1_relat_1(A_1988) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_19156,plain,(
    ! [B_1989,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_1989),k1_relat_1('#skF_8'))
      | D_67 != '#skF_4'('#skF_8',B_1989)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1989
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_67,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18971,c_19154])).

tff(c_19162,plain,(
    ! [B_1989,D_67] :
      ( r2_hidden('#skF_3'('#skF_8',B_1989),k1_relat_1('#skF_8'))
      | D_67 != '#skF_4'('#skF_8',B_1989)
      | ~ r2_hidden('#skF_9'(D_67),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1989
      | ~ r2_hidden(D_67,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_19156])).

tff(c_19428,plain,(
    ! [B_2045] :
      ( r2_hidden('#skF_3'('#skF_8',B_2045),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_2045)),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_2045
      | ~ r2_hidden('#skF_4'('#skF_8',B_2045),'#skF_8') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_19162])).

tff(c_19432,plain,(
    ! [B_2045] :
      ( r2_hidden('#skF_3'('#skF_8',B_2045),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_2045
      | ~ r2_hidden('#skF_4'('#skF_8',B_2045),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18967,c_19428])).

tff(c_19812,plain,
    ( k2_relat_1('#skF_8') = '#skF_8'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_19432,c_19800])).

tff(c_19830,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_18968,c_19812])).

tff(c_19897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19819,c_19830])).

tff(c_20012,plain,(
    ! [A_2082] : r2_hidden('#skF_2'('#skF_8','#skF_8'),A_2082) ),
    inference(splitRight,[status(thm)],[c_19774])).

tff(c_20022,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_20012,c_26])).

tff(c_20033,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_20022])).

tff(c_20034,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_18968,c_20033])).

tff(c_20048,plain,(
    ! [A_1551] : r2_hidden('#skF_4'('#skF_8','#skF_8'),A_1551) ),
    inference(resolution,[status(thm)],[c_20034,c_18963])).

tff(c_20015,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_8'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_20012,c_20])).

tff(c_20027,plain,(
    ! [D_44] :
      ( k1_funct_1('#skF_8',D_44) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_44,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_60,c_20015])).

tff(c_20129,plain,(
    ! [D_2088] :
      ( k1_funct_1('#skF_8',D_2088) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_2088,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18968,c_20027])).

tff(c_20243,plain,(
    ! [D_2089] :
      ( k1_funct_1('#skF_8','#skF_9'(D_2089)) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_2089,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18967,c_20129])).

tff(c_20248,plain,(
    ! [D_2090] :
      ( D_2090 != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_2090,'#skF_8')
      | ~ r2_hidden(D_2090,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18971,c_20243])).

tff(c_20257,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_20048,c_20248])).

tff(c_20299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20048,c_20257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.68/4.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.18/4.26  
% 11.18/4.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.18/4.26  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 11.18/4.26  
% 11.18/4.26  %Foreground sorts:
% 11.18/4.26  
% 11.18/4.26  
% 11.18/4.26  %Background operators:
% 11.18/4.26  
% 11.18/4.26  
% 11.18/4.26  %Foreground operators:
% 11.18/4.26  tff('#skF_9', type, '#skF_9': $i > $i).
% 11.18/4.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.18/4.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.18/4.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.18/4.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.18/4.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.18/4.26  tff('#skF_7', type, '#skF_7': $i).
% 11.18/4.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.18/4.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.18/4.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.18/4.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.18/4.26  tff('#skF_6', type, '#skF_6': $i).
% 11.18/4.26  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.18/4.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.18/4.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.18/4.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.18/4.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.18/4.26  tff('#skF_8', type, '#skF_8': $i).
% 11.18/4.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.18/4.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.18/4.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.18/4.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.18/4.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.18/4.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.18/4.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.18/4.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.18/4.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.18/4.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.18/4.26  
% 11.18/4.33  tff(f_110, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 11.18/4.33  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.18/4.33  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.18/4.33  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.18/4.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.18/4.33  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 11.18/4.33  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.18/4.33  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.18/4.33  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 11.18/4.33  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.18/4.33  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.18/4.33  tff(c_141, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.18/4.33  tff(c_145, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_141])).
% 11.18/4.33  tff(c_54, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.18/4.33  tff(c_146, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_54])).
% 11.18/4.33  tff(c_84, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.18/4.33  tff(c_88, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_84])).
% 11.18/4.33  tff(c_60, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.18/4.33  tff(c_101, plain, (![C_85, B_86, A_87]: (v5_relat_1(C_85, B_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.18/4.33  tff(c_105, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_101])).
% 11.18/4.33  tff(c_62, plain, (![D_67]: (k1_funct_1('#skF_8', '#skF_9'(D_67))=D_67 | ~r2_hidden(D_67, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.18/4.33  tff(c_68, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73, B_74), A_73) | r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.18/4.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.18/4.33  tff(c_73, plain, (![A_73]: (r1_tarski(A_73, A_73))), inference(resolution, [status(thm)], [c_68, c_4])).
% 11.18/4.33  tff(c_58, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.18/4.33  tff(c_64, plain, (![D_67]: (r2_hidden('#skF_9'(D_67), '#skF_6') | ~r2_hidden(D_67, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.18/4.33  tff(c_106, plain, (![C_88, B_89, A_90]: (r2_hidden(C_88, B_89) | ~r2_hidden(C_88, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.18/4.33  tff(c_112, plain, (![D_67, B_89]: (r2_hidden('#skF_9'(D_67), B_89) | ~r1_tarski('#skF_6', B_89) | ~r2_hidden(D_67, '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_106])).
% 11.18/4.33  tff(c_12, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.18/4.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.18/4.33  tff(c_122, plain, (![A_96, B_97, B_98]: (r2_hidden('#skF_1'(A_96, B_97), B_98) | ~r1_tarski(A_96, B_98) | r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_6, c_106])).
% 11.18/4.33  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.18/4.33  tff(c_5170, plain, (![A_628, B_629, B_630, B_631]: (r2_hidden('#skF_1'(A_628, B_629), B_630) | ~r1_tarski(B_631, B_630) | ~r1_tarski(A_628, B_631) | r1_tarski(A_628, B_629))), inference(resolution, [status(thm)], [c_122, c_2])).
% 11.18/4.33  tff(c_5764, plain, (![A_713, B_714, A_715, B_716]: (r2_hidden('#skF_1'(A_713, B_714), A_715) | ~r1_tarski(A_713, k2_relat_1(B_716)) | r1_tarski(A_713, B_714) | ~v5_relat_1(B_716, A_715) | ~v1_relat_1(B_716))), inference(resolution, [status(thm)], [c_12, c_5170])).
% 11.18/4.33  tff(c_5792, plain, (![B_717, B_718, A_719]: (r2_hidden('#skF_1'(k2_relat_1(B_717), B_718), A_719) | r1_tarski(k2_relat_1(B_717), B_718) | ~v5_relat_1(B_717, A_719) | ~v1_relat_1(B_717))), inference(resolution, [status(thm)], [c_73, c_5764])).
% 11.18/4.33  tff(c_132, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.18/4.33  tff(c_136, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_132])).
% 11.18/4.33  tff(c_257, plain, (![B_144, A_145, C_146]: (k1_xboole_0=B_144 | k1_relset_1(A_145, B_144, C_146)=A_145 | ~v1_funct_2(C_146, A_145, B_144) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_145, B_144))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.18/4.33  tff(c_260, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_257])).
% 11.18/4.33  tff(c_263, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_136, c_260])).
% 11.18/4.33  tff(c_264, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_263])).
% 11.18/4.33  tff(c_162, plain, (![A_109, D_110]: (r2_hidden(k1_funct_1(A_109, D_110), k2_relat_1(A_109)) | ~r2_hidden(D_110, k1_relat_1(A_109)) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_167, plain, (![D_67]: (r2_hidden(D_67, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_162])).
% 11.18/4.33  tff(c_171, plain, (![D_111]: (r2_hidden(D_111, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_111), k1_relat_1('#skF_8')) | ~r2_hidden(D_111, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_167])).
% 11.18/4.33  tff(c_176, plain, (![D_67]: (r2_hidden(D_67, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_67, '#skF_7'))), inference(resolution, [status(thm)], [c_112, c_171])).
% 11.18/4.33  tff(c_177, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_176])).
% 11.18/4.33  tff(c_265, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_177])).
% 11.18/4.33  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_265])).
% 11.18/4.33  tff(c_271, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_263])).
% 11.18/4.33  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.18/4.33  tff(c_179, plain, (![A_114, B_115, B_116, B_117]: (r2_hidden('#skF_1'(A_114, B_115), B_116) | ~r1_tarski(B_117, B_116) | ~r1_tarski(A_114, B_117) | r1_tarski(A_114, B_115))), inference(resolution, [status(thm)], [c_122, c_2])).
% 11.18/4.33  tff(c_189, plain, (![A_118, B_119, A_120]: (r2_hidden('#skF_1'(A_118, B_119), A_120) | ~r1_tarski(A_118, k1_xboole_0) | r1_tarski(A_118, B_119))), inference(resolution, [status(thm)], [c_8, c_179])).
% 11.18/4.33  tff(c_198, plain, (![A_121, A_122]: (~r1_tarski(A_121, k1_xboole_0) | r1_tarski(A_121, A_122))), inference(resolution, [status(thm)], [c_189, c_4])).
% 11.18/4.33  tff(c_214, plain, (![B_126, A_127]: (r1_tarski(k2_relat_1(B_126), A_127) | ~v5_relat_1(B_126, k1_xboole_0) | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_12, c_198])).
% 11.18/4.33  tff(c_10, plain, (![B_8, A_7]: (v5_relat_1(B_8, A_7) | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.18/4.33  tff(c_228, plain, (![B_126, A_127]: (v5_relat_1(B_126, A_127) | ~v5_relat_1(B_126, k1_xboole_0) | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_214, c_10])).
% 11.18/4.33  tff(c_318, plain, (![B_152, A_153]: (v5_relat_1(B_152, A_153) | ~v5_relat_1(B_152, '#skF_7') | ~v1_relat_1(B_152))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_228])).
% 11.18/4.33  tff(c_320, plain, (![A_153]: (v5_relat_1('#skF_8', A_153) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_105, c_318])).
% 11.18/4.33  tff(c_323, plain, (![A_153]: (v5_relat_1('#skF_8', A_153))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_320])).
% 11.18/4.33  tff(c_44, plain, (![C_63, A_61]: (k1_xboole_0=C_63 | ~v1_funct_2(C_63, A_61, k1_xboole_0) | k1_xboole_0=A_61 | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.18/4.33  tff(c_364, plain, (![C_161, A_162]: (C_161='#skF_7' | ~v1_funct_2(C_161, A_162, '#skF_7') | A_162='#skF_7' | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_162, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_271, c_271, c_271, c_44])).
% 11.18/4.33  tff(c_367, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_56, c_364])).
% 11.18/4.33  tff(c_370, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_367])).
% 11.18/4.33  tff(c_371, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_370])).
% 11.18/4.33  tff(c_118, plain, (![D_94, B_95]: (r2_hidden('#skF_9'(D_94), B_95) | ~r1_tarski('#skF_6', B_95) | ~r2_hidden(D_94, '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_106])).
% 11.18/4.33  tff(c_151, plain, (![D_106, B_107, B_108]: (r2_hidden('#skF_9'(D_106), B_107) | ~r1_tarski(B_108, B_107) | ~r1_tarski('#skF_6', B_108) | ~r2_hidden(D_106, '#skF_7'))), inference(resolution, [status(thm)], [c_118, c_2])).
% 11.18/4.33  tff(c_160, plain, (![D_106, A_6]: (r2_hidden('#skF_9'(D_106), A_6) | ~r1_tarski('#skF_6', k1_xboole_0) | ~r2_hidden(D_106, '#skF_7'))), inference(resolution, [status(thm)], [c_8, c_151])).
% 11.18/4.33  tff(c_161, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_160])).
% 11.18/4.33  tff(c_282, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_161])).
% 11.18/4.33  tff(c_378, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_371, c_282])).
% 11.18/4.33  tff(c_394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_378])).
% 11.18/4.33  tff(c_395, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_370])).
% 11.18/4.33  tff(c_409, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_395, c_146])).
% 11.18/4.33  tff(c_284, plain, (![A_6]: (r1_tarski('#skF_7', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_8])).
% 11.18/4.33  tff(c_404, plain, (![A_6]: (r1_tarski('#skF_8', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_395, c_284])).
% 11.18/4.33  tff(c_289, plain, (![A_147, B_148]: (r2_hidden('#skF_3'(A_147, B_148), k1_relat_1(A_147)) | r2_hidden('#skF_4'(A_147, B_148), B_148) | k2_relat_1(A_147)=B_148 | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_294, plain, (![A_147, B_148, B_2]: (r2_hidden('#skF_3'(A_147, B_148), B_2) | ~r1_tarski(k1_relat_1(A_147), B_2) | r2_hidden('#skF_4'(A_147, B_148), B_148) | k2_relat_1(A_147)=B_148 | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(resolution, [status(thm)], [c_289, c_2])).
% 11.18/4.33  tff(c_348, plain, (![A_158, B_159]: (k1_funct_1(A_158, '#skF_3'(A_158, B_159))='#skF_2'(A_158, B_159) | r2_hidden('#skF_4'(A_158, B_159), B_159) | k2_relat_1(A_158)=B_159 | ~v1_funct_1(A_158) | ~v1_relat_1(A_158))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_14, plain, (![A_9, D_48]: (r2_hidden(k1_funct_1(A_9, D_48), k2_relat_1(A_9)) | ~r2_hidden(D_48, k1_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_859, plain, (![A_262, B_263]: (r2_hidden('#skF_2'(A_262, B_263), k2_relat_1(A_262)) | ~r2_hidden('#skF_3'(A_262, B_263), k1_relat_1(A_262)) | ~v1_funct_1(A_262) | ~v1_relat_1(A_262) | r2_hidden('#skF_4'(A_262, B_263), B_263) | k2_relat_1(A_262)=B_263 | ~v1_funct_1(A_262) | ~v1_relat_1(A_262))), inference(superposition, [status(thm), theory('equality')], [c_348, c_14])).
% 11.18/4.33  tff(c_862, plain, (![A_147, B_148]: (r2_hidden('#skF_2'(A_147, B_148), k2_relat_1(A_147)) | ~r1_tarski(k1_relat_1(A_147), k1_relat_1(A_147)) | r2_hidden('#skF_4'(A_147, B_148), B_148) | k2_relat_1(A_147)=B_148 | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(resolution, [status(thm)], [c_294, c_859])).
% 11.18/4.33  tff(c_869, plain, (![A_147, B_148]: (r2_hidden('#skF_2'(A_147, B_148), k2_relat_1(A_147)) | r2_hidden('#skF_4'(A_147, B_148), B_148) | k2_relat_1(A_147)=B_148 | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_862])).
% 11.18/4.33  tff(c_244, plain, (![A_136, C_137]: (r2_hidden('#skF_5'(A_136, k2_relat_1(A_136), C_137), k1_relat_1(A_136)) | ~r2_hidden(C_137, k2_relat_1(A_136)) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_247, plain, (![A_136, C_137, B_2]: (r2_hidden('#skF_5'(A_136, k2_relat_1(A_136), C_137), B_2) | ~r1_tarski(k1_relat_1(A_136), B_2) | ~r2_hidden(C_137, k2_relat_1(A_136)) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(resolution, [status(thm)], [c_244, c_2])).
% 11.18/4.33  tff(c_16, plain, (![A_9, C_45]: (k1_funct_1(A_9, '#skF_5'(A_9, k2_relat_1(A_9), C_45))=C_45 | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_634, plain, (![A_211, B_212, A_213, B_214]: (r2_hidden('#skF_1'(A_211, B_212), A_213) | ~r1_tarski(A_211, k2_relat_1(B_214)) | r1_tarski(A_211, B_212) | ~v5_relat_1(B_214, A_213) | ~v1_relat_1(B_214))), inference(resolution, [status(thm)], [c_12, c_179])).
% 11.18/4.33  tff(c_778, plain, (![B_247, B_248, A_249, B_250]: (r2_hidden('#skF_1'(k2_relat_1(B_247), B_248), A_249) | r1_tarski(k2_relat_1(B_247), B_248) | ~v5_relat_1(B_250, A_249) | ~v1_relat_1(B_250) | ~v5_relat_1(B_247, k2_relat_1(B_250)) | ~v1_relat_1(B_247))), inference(resolution, [status(thm)], [c_12, c_634])).
% 11.18/4.33  tff(c_780, plain, (![B_247, B_248, A_153]: (r2_hidden('#skF_1'(k2_relat_1(B_247), B_248), A_153) | r1_tarski(k2_relat_1(B_247), B_248) | ~v1_relat_1('#skF_8') | ~v5_relat_1(B_247, k2_relat_1('#skF_8')) | ~v1_relat_1(B_247))), inference(resolution, [status(thm)], [c_323, c_778])).
% 11.18/4.33  tff(c_787, plain, (![B_251, B_252, A_253]: (r2_hidden('#skF_1'(k2_relat_1(B_251), B_252), A_253) | r1_tarski(k2_relat_1(B_251), B_252) | ~v5_relat_1(B_251, k2_relat_1('#skF_8')) | ~v1_relat_1(B_251))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_780])).
% 11.18/4.33  tff(c_796, plain, (![B_254, A_255]: (r1_tarski(k2_relat_1(B_254), A_255) | ~v5_relat_1(B_254, k2_relat_1('#skF_8')) | ~v1_relat_1(B_254))), inference(resolution, [status(thm)], [c_787, c_4])).
% 11.18/4.33  tff(c_799, plain, (![A_255]: (r1_tarski(k2_relat_1('#skF_8'), A_255) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_323, c_796])).
% 11.18/4.33  tff(c_805, plain, (![A_255]: (r1_tarski(k2_relat_1('#skF_8'), A_255))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_799])).
% 11.18/4.33  tff(c_814, plain, (![A_258]: (r1_tarski(k2_relat_1('#skF_8'), A_258))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_799])).
% 11.18/4.33  tff(c_579, plain, (![A_198, D_199, B_200]: (r2_hidden(k1_funct_1(A_198, D_199), B_200) | ~r1_tarski(k2_relat_1(A_198), B_200) | ~r2_hidden(D_199, k1_relat_1(A_198)) | ~v1_funct_1(A_198) | ~v1_relat_1(A_198))), inference(resolution, [status(thm)], [c_162, c_2])).
% 11.18/4.33  tff(c_591, plain, (![A_198, D_199, B_2, B_200]: (r2_hidden(k1_funct_1(A_198, D_199), B_2) | ~r1_tarski(B_200, B_2) | ~r1_tarski(k2_relat_1(A_198), B_200) | ~r2_hidden(D_199, k1_relat_1(A_198)) | ~v1_funct_1(A_198) | ~v1_relat_1(A_198))), inference(resolution, [status(thm)], [c_579, c_2])).
% 11.18/4.33  tff(c_919, plain, (![A_269, D_270, A_271]: (r2_hidden(k1_funct_1(A_269, D_270), A_271) | ~r1_tarski(k2_relat_1(A_269), k2_relat_1('#skF_8')) | ~r2_hidden(D_270, k1_relat_1(A_269)) | ~v1_funct_1(A_269) | ~v1_relat_1(A_269))), inference(resolution, [status(thm)], [c_814, c_591])).
% 11.18/4.33  tff(c_922, plain, (![D_270, A_271]: (r2_hidden(k1_funct_1('#skF_8', D_270), A_271) | ~r2_hidden(D_270, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_805, c_919])).
% 11.18/4.33  tff(c_940, plain, (![D_272, A_273]: (r2_hidden(k1_funct_1('#skF_8', D_272), A_273) | ~r2_hidden(D_272, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_922])).
% 11.18/4.33  tff(c_953, plain, (![C_45, A_273]: (r2_hidden(C_45, A_273) | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_45), k1_relat_1('#skF_8')) | ~r2_hidden(C_45, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_940])).
% 11.18/4.33  tff(c_957, plain, (![C_274, A_275]: (r2_hidden(C_274, A_275) | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_274), k1_relat_1('#skF_8')) | ~r2_hidden(C_274, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_953])).
% 11.18/4.33  tff(c_960, plain, (![C_137, A_275]: (r2_hidden(C_137, A_275) | ~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | ~r2_hidden(C_137, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_247, c_957])).
% 11.18/4.33  tff(c_970, plain, (![C_276, A_277]: (r2_hidden(C_276, A_277) | ~r2_hidden(C_276, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_73, c_960])).
% 11.18/4.33  tff(c_976, plain, (![B_148, A_277]: (r2_hidden('#skF_2'('#skF_8', B_148), A_277) | r2_hidden('#skF_4'('#skF_8', B_148), B_148) | k2_relat_1('#skF_8')=B_148 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_869, c_970])).
% 11.18/4.33  tff(c_1040, plain, (![B_281, A_282]: (r2_hidden('#skF_2'('#skF_8', B_281), A_282) | r2_hidden('#skF_4'('#skF_8', B_281), B_281) | k2_relat_1('#skF_8')=B_281)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_976])).
% 11.18/4.33  tff(c_26, plain, (![A_9, B_31]: (~r2_hidden('#skF_2'(A_9, B_31), B_31) | r2_hidden('#skF_4'(A_9, B_31), B_31) | k2_relat_1(A_9)=B_31 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_1050, plain, (![A_282]: (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | r2_hidden('#skF_4'('#skF_8', A_282), A_282) | k2_relat_1('#skF_8')=A_282)), inference(resolution, [status(thm)], [c_1040, c_26])).
% 11.18/4.33  tff(c_1069, plain, (![A_283]: (r2_hidden('#skF_4'('#skF_8', A_283), A_283) | k2_relat_1('#skF_8')=A_283)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_1050])).
% 11.18/4.33  tff(c_1083, plain, (![A_285, B_286]: (r2_hidden('#skF_4'('#skF_8', A_285), B_286) | ~r1_tarski(A_285, B_286) | k2_relat_1('#skF_8')=A_285)), inference(resolution, [status(thm)], [c_1069, c_2])).
% 11.18/4.33  tff(c_1099, plain, (![A_289, B_290, B_291]: (r2_hidden('#skF_4'('#skF_8', A_289), B_290) | ~r1_tarski(B_291, B_290) | ~r1_tarski(A_289, B_291) | k2_relat_1('#skF_8')=A_289)), inference(resolution, [status(thm)], [c_1083, c_2])).
% 11.18/4.33  tff(c_1163, plain, (![A_303, A_304, B_305]: (r2_hidden('#skF_4'('#skF_8', A_303), A_304) | ~r1_tarski(A_303, k2_relat_1(B_305)) | k2_relat_1('#skF_8')=A_303 | ~v5_relat_1(B_305, A_304) | ~v1_relat_1(B_305))), inference(resolution, [status(thm)], [c_12, c_1099])).
% 11.18/4.33  tff(c_1172, plain, (![A_304, B_305]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), A_304) | k2_relat_1('#skF_8')='#skF_8' | ~v5_relat_1(B_305, A_304) | ~v1_relat_1(B_305))), inference(resolution, [status(thm)], [c_404, c_1163])).
% 11.18/4.33  tff(c_1187, plain, (![A_306, B_307]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), A_306) | ~v5_relat_1(B_307, A_306) | ~v1_relat_1(B_307))), inference(negUnitSimplification, [status(thm)], [c_409, c_1172])).
% 11.18/4.33  tff(c_1189, plain, (![A_153]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), A_153) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_323, c_1187])).
% 11.18/4.33  tff(c_1194, plain, (![A_153]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), A_153))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1189])).
% 11.18/4.33  tff(c_18, plain, (![A_9, C_45]: (r2_hidden('#skF_5'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_197, plain, (![A_118, A_120]: (~r1_tarski(A_118, k1_xboole_0) | r1_tarski(A_118, A_120))), inference(resolution, [status(thm)], [c_189, c_4])).
% 11.18/4.33  tff(c_280, plain, (![A_118, A_120]: (~r1_tarski(A_118, '#skF_7') | r1_tarski(A_118, A_120))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_197])).
% 11.18/4.33  tff(c_464, plain, (![A_167, A_168]: (~r1_tarski(A_167, '#skF_8') | r1_tarski(A_167, A_168))), inference(demodulation, [status(thm), theory('equality')], [c_395, c_280])).
% 11.18/4.33  tff(c_476, plain, (![B_8, A_168]: (r1_tarski(k2_relat_1(B_8), A_168) | ~v5_relat_1(B_8, '#skF_8') | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_12, c_464])).
% 11.18/4.33  tff(c_1123, plain, (![B_294, D_295, A_296]: (r2_hidden(k1_funct_1(B_294, D_295), A_296) | ~r2_hidden(D_295, k1_relat_1(B_294)) | ~v1_funct_1(B_294) | ~v5_relat_1(B_294, '#skF_8') | ~v1_relat_1(B_294))), inference(resolution, [status(thm)], [c_476, c_919])).
% 11.18/4.33  tff(c_1273, plain, (![C_324, A_325, A_326]: (r2_hidden(C_324, A_325) | ~r2_hidden('#skF_5'(A_326, k2_relat_1(A_326), C_324), k1_relat_1(A_326)) | ~v1_funct_1(A_326) | ~v5_relat_1(A_326, '#skF_8') | ~v1_relat_1(A_326) | ~r2_hidden(C_324, k2_relat_1(A_326)) | ~v1_funct_1(A_326) | ~v1_relat_1(A_326))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1123])).
% 11.18/4.33  tff(c_1276, plain, (![C_137, A_325, A_136]: (r2_hidden(C_137, A_325) | ~v5_relat_1(A_136, '#skF_8') | ~r1_tarski(k1_relat_1(A_136), k1_relat_1(A_136)) | ~r2_hidden(C_137, k2_relat_1(A_136)) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(resolution, [status(thm)], [c_247, c_1273])).
% 11.18/4.33  tff(c_1283, plain, (![C_327, A_328, A_329]: (r2_hidden(C_327, A_328) | ~v5_relat_1(A_329, '#skF_8') | ~r2_hidden(C_327, k2_relat_1(A_329)) | ~v1_funct_1(A_329) | ~v1_relat_1(A_329))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_1276])).
% 11.18/4.33  tff(c_1399, plain, (![A_333, B_334, A_335]: (r2_hidden('#skF_2'(A_333, B_334), A_335) | ~v5_relat_1(A_333, '#skF_8') | r2_hidden('#skF_4'(A_333, B_334), B_334) | k2_relat_1(A_333)=B_334 | ~v1_funct_1(A_333) | ~v1_relat_1(A_333))), inference(resolution, [status(thm)], [c_869, c_1283])).
% 11.18/4.33  tff(c_1431, plain, (![A_336, A_337]: (~v5_relat_1(A_336, '#skF_8') | r2_hidden('#skF_4'(A_336, A_337), A_337) | k2_relat_1(A_336)=A_337 | ~v1_funct_1(A_336) | ~v1_relat_1(A_336))), inference(resolution, [status(thm)], [c_1399, c_26])).
% 11.18/4.33  tff(c_1456, plain, (![A_343, A_344, B_345]: (r2_hidden('#skF_4'(A_343, A_344), B_345) | ~r1_tarski(A_344, B_345) | ~v5_relat_1(A_343, '#skF_8') | k2_relat_1(A_343)=A_344 | ~v1_funct_1(A_343) | ~v1_relat_1(A_343))), inference(resolution, [status(thm)], [c_1431, c_2])).
% 11.18/4.33  tff(c_1630, plain, (![A_376, A_377, B_378, B_379]: (r2_hidden('#skF_4'(A_376, A_377), B_378) | ~r1_tarski(B_379, B_378) | ~r1_tarski(A_377, B_379) | ~v5_relat_1(A_376, '#skF_8') | k2_relat_1(A_376)=A_377 | ~v1_funct_1(A_376) | ~v1_relat_1(A_376))), inference(resolution, [status(thm)], [c_1456, c_2])).
% 11.18/4.33  tff(c_2629, plain, (![A_535, A_536, A_537, B_538]: (r2_hidden('#skF_4'(A_535, A_536), A_537) | ~r1_tarski(A_536, k2_relat_1(B_538)) | ~v5_relat_1(A_535, '#skF_8') | k2_relat_1(A_535)=A_536 | ~v1_funct_1(A_535) | ~v1_relat_1(A_535) | ~v5_relat_1(B_538, A_537) | ~v1_relat_1(B_538))), inference(resolution, [status(thm)], [c_12, c_1630])).
% 11.18/4.33  tff(c_2707, plain, (![A_543, A_544, B_545]: (r2_hidden('#skF_4'(A_543, '#skF_8'), A_544) | ~v5_relat_1(A_543, '#skF_8') | k2_relat_1(A_543)='#skF_8' | ~v1_funct_1(A_543) | ~v1_relat_1(A_543) | ~v5_relat_1(B_545, A_544) | ~v1_relat_1(B_545))), inference(resolution, [status(thm)], [c_404, c_2629])).
% 11.18/4.33  tff(c_2709, plain, (![A_543, A_153]: (r2_hidden('#skF_4'(A_543, '#skF_8'), A_153) | ~v5_relat_1(A_543, '#skF_8') | k2_relat_1(A_543)='#skF_8' | ~v1_funct_1(A_543) | ~v1_relat_1(A_543) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_323, c_2707])).
% 11.18/4.33  tff(c_2714, plain, (![A_543, A_153]: (r2_hidden('#skF_4'(A_543, '#skF_8'), A_153) | ~v5_relat_1(A_543, '#skF_8') | k2_relat_1(A_543)='#skF_8' | ~v1_funct_1(A_543) | ~v1_relat_1(A_543))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2709])).
% 11.18/4.33  tff(c_479, plain, (![A_169, B_170, D_171]: (r2_hidden('#skF_3'(A_169, B_170), k1_relat_1(A_169)) | k1_funct_1(A_169, D_171)!='#skF_4'(A_169, B_170) | ~r2_hidden(D_171, k1_relat_1(A_169)) | k2_relat_1(A_169)=B_170 | ~v1_funct_1(A_169) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_483, plain, (![A_9, B_170, C_45]: (r2_hidden('#skF_3'(A_9, B_170), k1_relat_1(A_9)) | C_45!='#skF_4'(A_9, B_170) | ~r2_hidden('#skF_5'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | k2_relat_1(A_9)=B_170 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_16, c_479])).
% 11.18/4.33  tff(c_2752, plain, (![A_554, B_555]: (r2_hidden('#skF_3'(A_554, B_555), k1_relat_1(A_554)) | ~r2_hidden('#skF_5'(A_554, k2_relat_1(A_554), '#skF_4'(A_554, B_555)), k1_relat_1(A_554)) | k2_relat_1(A_554)=B_555 | ~v1_funct_1(A_554) | ~v1_relat_1(A_554) | ~r2_hidden('#skF_4'(A_554, B_555), k2_relat_1(A_554)) | ~v1_funct_1(A_554) | ~v1_relat_1(A_554))), inference(reflexivity, [status(thm), theory('equality')], [c_483])).
% 11.18/4.33  tff(c_2764, plain, (![A_136, B_555]: (r2_hidden('#skF_3'(A_136, B_555), k1_relat_1(A_136)) | k2_relat_1(A_136)=B_555 | ~r1_tarski(k1_relat_1(A_136), k1_relat_1(A_136)) | ~r2_hidden('#skF_4'(A_136, B_555), k2_relat_1(A_136)) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(resolution, [status(thm)], [c_247, c_2752])).
% 11.18/4.33  tff(c_2775, plain, (![A_556, B_557]: (r2_hidden('#skF_3'(A_556, B_557), k1_relat_1(A_556)) | k2_relat_1(A_556)=B_557 | ~r2_hidden('#skF_4'(A_556, B_557), k2_relat_1(A_556)) | ~v1_funct_1(A_556) | ~v1_relat_1(A_556))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_2764])).
% 11.18/4.33  tff(c_2782, plain, (![A_558, B_559, B_560]: (r2_hidden('#skF_3'(A_558, B_559), B_560) | ~r1_tarski(k1_relat_1(A_558), B_560) | k2_relat_1(A_558)=B_559 | ~r2_hidden('#skF_4'(A_558, B_559), k2_relat_1(A_558)) | ~v1_funct_1(A_558) | ~v1_relat_1(A_558))), inference(resolution, [status(thm)], [c_2775, c_2])).
% 11.18/4.33  tff(c_2928, plain, (![A_543, B_560]: (r2_hidden('#skF_3'(A_543, '#skF_8'), B_560) | ~r1_tarski(k1_relat_1(A_543), B_560) | ~v5_relat_1(A_543, '#skF_8') | k2_relat_1(A_543)='#skF_8' | ~v1_funct_1(A_543) | ~v1_relat_1(A_543))), inference(resolution, [status(thm)], [c_2714, c_2782])).
% 11.18/4.33  tff(c_530, plain, (![A_181, B_182, D_183]: (k1_funct_1(A_181, '#skF_3'(A_181, B_182))='#skF_2'(A_181, B_182) | k1_funct_1(A_181, D_183)!='#skF_4'(A_181, B_182) | ~r2_hidden(D_183, k1_relat_1(A_181)) | k2_relat_1(A_181)=B_182 | ~v1_funct_1(A_181) | ~v1_relat_1(A_181))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_536, plain, (![A_9, B_182, C_45]: (k1_funct_1(A_9, '#skF_3'(A_9, B_182))='#skF_2'(A_9, B_182) | C_45!='#skF_4'(A_9, B_182) | ~r2_hidden('#skF_5'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | k2_relat_1(A_9)=B_182 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_16, c_530])).
% 11.18/4.33  tff(c_3091, plain, (![A_574, B_575]: (k1_funct_1(A_574, '#skF_3'(A_574, B_575))='#skF_2'(A_574, B_575) | ~r2_hidden('#skF_5'(A_574, k2_relat_1(A_574), '#skF_4'(A_574, B_575)), k1_relat_1(A_574)) | k2_relat_1(A_574)=B_575 | ~v1_funct_1(A_574) | ~v1_relat_1(A_574) | ~r2_hidden('#skF_4'(A_574, B_575), k2_relat_1(A_574)) | ~v1_funct_1(A_574) | ~v1_relat_1(A_574))), inference(reflexivity, [status(thm), theory('equality')], [c_536])).
% 11.18/4.33  tff(c_3185, plain, (![A_587, B_588]: (k1_funct_1(A_587, '#skF_3'(A_587, B_588))='#skF_2'(A_587, B_588) | k2_relat_1(A_587)=B_588 | ~r2_hidden('#skF_4'(A_587, B_588), k2_relat_1(A_587)) | ~v1_funct_1(A_587) | ~v1_relat_1(A_587))), inference(resolution, [status(thm)], [c_18, c_3091])).
% 11.18/4.33  tff(c_3347, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1194, c_3185])).
% 11.18/4.33  tff(c_3434, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_3347])).
% 11.18/4.33  tff(c_3435, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_409, c_3434])).
% 11.18/4.33  tff(c_703, plain, (![A_231, D_232, B_233, B_234]: (r2_hidden(k1_funct_1(A_231, D_232), B_233) | ~r1_tarski(B_234, B_233) | ~r1_tarski(k2_relat_1(A_231), B_234) | ~r2_hidden(D_232, k1_relat_1(A_231)) | ~v1_funct_1(A_231) | ~v1_relat_1(A_231))), inference(resolution, [status(thm)], [c_579, c_2])).
% 11.18/4.33  tff(c_1827, plain, (![A_423, D_424, A_425, B_426]: (r2_hidden(k1_funct_1(A_423, D_424), A_425) | ~r1_tarski(k2_relat_1(A_423), k2_relat_1(B_426)) | ~r2_hidden(D_424, k1_relat_1(A_423)) | ~v1_funct_1(A_423) | ~v1_relat_1(A_423) | ~v5_relat_1(B_426, A_425) | ~v1_relat_1(B_426))), inference(resolution, [status(thm)], [c_12, c_703])).
% 11.18/4.33  tff(c_1845, plain, (![A_423, D_424, A_425]: (r2_hidden(k1_funct_1(A_423, D_424), A_425) | ~r2_hidden(D_424, k1_relat_1(A_423)) | ~v1_funct_1(A_423) | ~v5_relat_1(A_423, A_425) | ~v1_relat_1(A_423))), inference(resolution, [status(thm)], [c_73, c_1827])).
% 11.18/4.33  tff(c_3459, plain, (![A_425]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), A_425) | ~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_425) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3435, c_1845])).
% 11.18/4.33  tff(c_3488, plain, (![A_425]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), A_425) | ~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_323, c_60, c_3459])).
% 11.18/4.33  tff(c_3502, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_3488])).
% 11.18/4.33  tff(c_3506, plain, (~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | ~v5_relat_1('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_2928, c_3502])).
% 11.18/4.33  tff(c_3551, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_323, c_73, c_3506])).
% 11.18/4.33  tff(c_3553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_409, c_3551])).
% 11.18/4.33  tff(c_3556, plain, (![A_593]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), A_593))), inference(splitRight, [status(thm)], [c_3488])).
% 11.18/4.33  tff(c_20, plain, (![A_9, B_31, D_44]: (~r2_hidden('#skF_2'(A_9, B_31), B_31) | k1_funct_1(A_9, D_44)!='#skF_4'(A_9, B_31) | ~r2_hidden(D_44, k1_relat_1(A_9)) | k2_relat_1(A_9)=B_31 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_3565, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_3556, c_20])).
% 11.18/4.33  tff(c_3578, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_3565])).
% 11.18/4.33  tff(c_3595, plain, (![D_594]: (k1_funct_1('#skF_8', D_594)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_594, k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_409, c_3578])).
% 11.18/4.33  tff(c_3938, plain, (![C_45]: (k1_funct_1('#skF_8', '#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_45))!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(C_45, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_18, c_3595])).
% 11.18/4.33  tff(c_4622, plain, (![C_608]: (k1_funct_1('#skF_8', '#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_608))!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(C_608, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_3938])).
% 11.18/4.33  tff(c_4626, plain, (![C_45]: (C_45!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(C_45, k2_relat_1('#skF_8')) | ~r2_hidden(C_45, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_4622])).
% 11.18/4.33  tff(c_4630, plain, (![C_609]: (C_609!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(C_609, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_4626])).
% 11.18/4.33  tff(c_5044, plain, $false, inference(resolution, [status(thm)], [c_1194, c_4630])).
% 11.18/4.33  tff(c_5052, plain, (![D_610]: (r2_hidden(D_610, k2_relat_1('#skF_8')) | ~r2_hidden(D_610, '#skF_7'))), inference(splitRight, [status(thm)], [c_176])).
% 11.18/4.33  tff(c_5066, plain, (![D_614, B_615]: (r2_hidden(D_614, B_615) | ~r1_tarski(k2_relat_1('#skF_8'), B_615) | ~r2_hidden(D_614, '#skF_7'))), inference(resolution, [status(thm)], [c_5052, c_2])).
% 11.18/4.33  tff(c_5069, plain, (![D_614, A_7]: (r2_hidden(D_614, A_7) | ~r2_hidden(D_614, '#skF_7') | ~v5_relat_1('#skF_8', A_7) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_12, c_5066])).
% 11.18/4.33  tff(c_5075, plain, (![D_614, A_7]: (r2_hidden(D_614, A_7) | ~r2_hidden(D_614, '#skF_7') | ~v5_relat_1('#skF_8', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5069])).
% 11.18/4.33  tff(c_6158, plain, (![B_757, B_758, A_759]: (r2_hidden('#skF_1'(k2_relat_1(B_757), B_758), A_759) | ~v5_relat_1('#skF_8', A_759) | r1_tarski(k2_relat_1(B_757), B_758) | ~v5_relat_1(B_757, '#skF_7') | ~v1_relat_1(B_757))), inference(resolution, [status(thm)], [c_5792, c_5075])).
% 11.18/4.33  tff(c_6183, plain, (![A_759, B_757]: (~v5_relat_1('#skF_8', A_759) | r1_tarski(k2_relat_1(B_757), A_759) | ~v5_relat_1(B_757, '#skF_7') | ~v1_relat_1(B_757))), inference(resolution, [status(thm)], [c_6158, c_4])).
% 11.18/4.33  tff(c_5541, plain, (![B_678, A_679, C_680]: (k1_xboole_0=B_678 | k1_relset_1(A_679, B_678, C_680)=A_679 | ~v1_funct_2(C_680, A_679, B_678) | ~m1_subset_1(C_680, k1_zfmisc_1(k2_zfmisc_1(A_679, B_678))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.18/4.33  tff(c_5544, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_5541])).
% 11.18/4.33  tff(c_5547, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_136, c_5544])).
% 11.18/4.33  tff(c_5548, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_5547])).
% 11.18/4.33  tff(c_5719, plain, (![A_705, B_706]: (r2_hidden('#skF_3'(A_705, B_706), k1_relat_1(A_705)) | r2_hidden('#skF_4'(A_705, B_706), B_706) | k2_relat_1(A_705)=B_706 | ~v1_funct_1(A_705) | ~v1_relat_1(A_705))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_5728, plain, (![A_705, B_706, B_2]: (r2_hidden('#skF_3'(A_705, B_706), B_2) | ~r1_tarski(k1_relat_1(A_705), B_2) | r2_hidden('#skF_4'(A_705, B_706), B_706) | k2_relat_1(A_705)=B_706 | ~v1_funct_1(A_705) | ~v1_relat_1(A_705))), inference(resolution, [status(thm)], [c_5719, c_2])).
% 11.18/4.33  tff(c_28, plain, (![A_9, B_31]: (k1_funct_1(A_9, '#skF_3'(A_9, B_31))='#skF_2'(A_9, B_31) | r2_hidden('#skF_4'(A_9, B_31), B_31) | k2_relat_1(A_9)=B_31 | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_6462, plain, (![A_785, B_786, D_787]: (k1_funct_1(A_785, '#skF_3'(A_785, B_786))='#skF_2'(A_785, B_786) | k1_funct_1(A_785, D_787)!='#skF_4'(A_785, B_786) | ~r2_hidden(D_787, k1_relat_1(A_785)) | k2_relat_1(A_785)=B_786 | ~v1_funct_1(A_785) | ~v1_relat_1(A_785))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_6468, plain, (![B_786, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_786))='#skF_2'('#skF_8', B_786) | D_67!='#skF_4'('#skF_8', B_786) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_786 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_6462])).
% 11.18/4.33  tff(c_6470, plain, (![B_786, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_786))='#skF_2'('#skF_8', B_786) | D_67!='#skF_4'('#skF_8', B_786) | ~r2_hidden('#skF_9'(D_67), '#skF_6') | k2_relat_1('#skF_8')=B_786 | ~r2_hidden(D_67, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_5548, c_6468])).
% 11.18/4.33  tff(c_6830, plain, (![B_841]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_841))='#skF_2'('#skF_8', B_841) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_841)), '#skF_6') | k2_relat_1('#skF_8')=B_841 | ~r2_hidden('#skF_4'('#skF_8', B_841), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_6470])).
% 11.18/4.33  tff(c_6833, plain, (![B_841]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_841))='#skF_2'('#skF_8', B_841) | k2_relat_1('#skF_8')=B_841 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_841), '#skF_7'))), inference(resolution, [status(thm)], [c_112, c_6830])).
% 11.18/4.33  tff(c_6841, plain, (![B_842]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_842))='#skF_2'('#skF_8', B_842) | k2_relat_1('#skF_8')=B_842 | ~r2_hidden('#skF_4'('#skF_8', B_842), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_6833])).
% 11.18/4.33  tff(c_6855, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_28, c_6841])).
% 11.18/4.33  tff(c_6866, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_6855])).
% 11.18/4.33  tff(c_6867, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_6866])).
% 11.18/4.33  tff(c_6888, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_6867, c_14])).
% 11.18/4.33  tff(c_6905, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_5548, c_6888])).
% 11.18/4.33  tff(c_6907, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_6905])).
% 11.18/4.33  tff(c_6913, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_5728, c_6907])).
% 11.18/4.33  tff(c_6941, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_73, c_5548, c_6913])).
% 11.18/4.33  tff(c_6942, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_6941])).
% 11.18/4.33  tff(c_6318, plain, (![A_767, B_768, D_769]: (r2_hidden('#skF_3'(A_767, B_768), k1_relat_1(A_767)) | k1_funct_1(A_767, D_769)!='#skF_4'(A_767, B_768) | ~r2_hidden(D_769, k1_relat_1(A_767)) | k2_relat_1(A_767)=B_768 | ~v1_funct_1(A_767) | ~v1_relat_1(A_767))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_6324, plain, (![B_768, D_67]: (r2_hidden('#skF_3'('#skF_8', B_768), k1_relat_1('#skF_8')) | D_67!='#skF_4'('#skF_8', B_768) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_768 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_6318])).
% 11.18/4.33  tff(c_6326, plain, (![B_768, D_67]: (r2_hidden('#skF_3'('#skF_8', B_768), '#skF_6') | D_67!='#skF_4'('#skF_8', B_768) | ~r2_hidden('#skF_9'(D_67), '#skF_6') | k2_relat_1('#skF_8')=B_768 | ~r2_hidden(D_67, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_5548, c_5548, c_6324])).
% 11.18/4.33  tff(c_6447, plain, (![B_783]: (r2_hidden('#skF_3'('#skF_8', B_783), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_783)), '#skF_6') | k2_relat_1('#skF_8')=B_783 | ~r2_hidden('#skF_4'('#skF_8', B_783), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_6326])).
% 11.18/4.33  tff(c_6450, plain, (![B_783]: (r2_hidden('#skF_3'('#skF_8', B_783), '#skF_6') | k2_relat_1('#skF_8')=B_783 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_783), '#skF_7'))), inference(resolution, [status(thm)], [c_112, c_6447])).
% 11.18/4.33  tff(c_6458, plain, (![B_784]: (r2_hidden('#skF_3'('#skF_8', B_784), '#skF_6') | k2_relat_1('#skF_8')=B_784 | ~r2_hidden('#skF_4'('#skF_8', B_784), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_6450])).
% 11.18/4.33  tff(c_6461, plain, (![B_784, B_2]: (r2_hidden('#skF_3'('#skF_8', B_784), B_2) | ~r1_tarski('#skF_6', B_2) | k2_relat_1('#skF_8')=B_784 | ~r2_hidden('#skF_4'('#skF_8', B_784), '#skF_7'))), inference(resolution, [status(thm)], [c_6458, c_2])).
% 11.18/4.33  tff(c_6922, plain, (~r1_tarski('#skF_6', '#skF_6') | k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_6461, c_6907])).
% 11.18/4.33  tff(c_6952, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_6922])).
% 11.18/4.33  tff(c_6953, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_6952])).
% 11.18/4.33  tff(c_7036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6942, c_6953])).
% 11.18/4.33  tff(c_7037, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_6905])).
% 11.18/4.33  tff(c_7057, plain, (![B_847]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_847) | ~r1_tarski(k2_relat_1('#skF_8'), B_847))), inference(resolution, [status(thm)], [c_7037, c_2])).
% 11.18/4.33  tff(c_7067, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_7057, c_26])).
% 11.18/4.33  tff(c_7080, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_7067])).
% 11.18/4.33  tff(c_7081, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_7080])).
% 11.18/4.33  tff(c_7084, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_7081])).
% 11.18/4.33  tff(c_7087, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_6183, c_7084])).
% 11.18/4.33  tff(c_7097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_105, c_7087])).
% 11.18/4.33  tff(c_7099, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_7081])).
% 11.18/4.33  tff(c_7063, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_7057, c_20])).
% 11.18/4.33  tff(c_7076, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_44, '#skF_6') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_5548, c_7063])).
% 11.18/4.33  tff(c_7077, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_44, '#skF_6') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_146, c_7076])).
% 11.18/4.33  tff(c_7282, plain, (![D_853]: (k1_funct_1('#skF_8', D_853)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_853, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7099, c_7077])).
% 11.18/4.33  tff(c_7418, plain, (![D_67]: (k1_funct_1('#skF_8', '#skF_9'(D_67))!='#skF_4'('#skF_8', '#skF_7') | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden(D_67, '#skF_7'))), inference(resolution, [status(thm)], [c_112, c_7282])).
% 11.18/4.33  tff(c_7474, plain, (![D_854]: (k1_funct_1('#skF_8', '#skF_9'(D_854))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_854, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_7418])).
% 11.18/4.33  tff(c_7478, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_62, c_7474])).
% 11.18/4.33  tff(c_7098, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_7081])).
% 11.18/4.33  tff(c_7480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7478, c_7098])).
% 11.18/4.33  tff(c_7481, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_5547])).
% 11.18/4.33  tff(c_5202, plain, (![A_633, B_634, A_635]: (r2_hidden('#skF_1'(A_633, B_634), A_635) | ~r1_tarski(A_633, k1_xboole_0) | r1_tarski(A_633, B_634))), inference(resolution, [status(thm)], [c_8, c_5170])).
% 11.18/4.33  tff(c_5220, plain, (![A_636, A_637]: (~r1_tarski(A_636, k1_xboole_0) | r1_tarski(A_636, A_637))), inference(resolution, [status(thm)], [c_5202, c_4])).
% 11.18/4.33  tff(c_5236, plain, (![B_640, A_641]: (r1_tarski(k2_relat_1(B_640), A_641) | ~v5_relat_1(B_640, k1_xboole_0) | ~v1_relat_1(B_640))), inference(resolution, [status(thm)], [c_12, c_5220])).
% 11.18/4.33  tff(c_5059, plain, (![D_610, B_2]: (r2_hidden(D_610, B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r2_hidden(D_610, '#skF_7'))), inference(resolution, [status(thm)], [c_5052, c_2])).
% 11.18/4.33  tff(c_5244, plain, (![D_610, A_641]: (r2_hidden(D_610, A_641) | ~r2_hidden(D_610, '#skF_7') | ~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_5236, c_5059])).
% 11.18/4.33  tff(c_5254, plain, (![D_610, A_641]: (r2_hidden(D_610, A_641) | ~r2_hidden(D_610, '#skF_7') | ~v5_relat_1('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5244])).
% 11.18/4.33  tff(c_5258, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_5254])).
% 11.18/4.33  tff(c_7492, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7481, c_5258])).
% 11.18/4.33  tff(c_7504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_7492])).
% 11.18/4.33  tff(c_7506, plain, (v5_relat_1('#skF_8', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5254])).
% 11.18/4.33  tff(c_5256, plain, (![B_640, A_641]: (v5_relat_1(B_640, A_641) | ~v5_relat_1(B_640, k1_xboole_0) | ~v1_relat_1(B_640))), inference(resolution, [status(thm)], [c_5236, c_10])).
% 11.18/4.33  tff(c_7508, plain, (![A_641]: (v5_relat_1('#skF_8', A_641) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_7506, c_5256])).
% 11.18/4.33  tff(c_7514, plain, (![A_641]: (v5_relat_1('#skF_8', A_641))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_7508])).
% 11.18/4.33  tff(c_7839, plain, (![A_906, B_907, A_908, B_909]: (r2_hidden('#skF_1'(A_906, B_907), A_908) | ~r1_tarski(A_906, k2_relat_1(B_909)) | r1_tarski(A_906, B_907) | ~v5_relat_1(B_909, A_908) | ~v1_relat_1(B_909))), inference(resolution, [status(thm)], [c_12, c_5170])).
% 11.18/4.33  tff(c_8262, plain, (![B_986, B_987, A_988, B_989]: (r2_hidden('#skF_1'(k2_relat_1(B_986), B_987), A_988) | r1_tarski(k2_relat_1(B_986), B_987) | ~v5_relat_1(B_989, A_988) | ~v1_relat_1(B_989) | ~v5_relat_1(B_986, k2_relat_1(B_989)) | ~v1_relat_1(B_986))), inference(resolution, [status(thm)], [c_12, c_7839])).
% 11.18/4.33  tff(c_8264, plain, (![B_986, B_987, A_641]: (r2_hidden('#skF_1'(k2_relat_1(B_986), B_987), A_641) | r1_tarski(k2_relat_1(B_986), B_987) | ~v1_relat_1('#skF_8') | ~v5_relat_1(B_986, k2_relat_1('#skF_8')) | ~v1_relat_1(B_986))), inference(resolution, [status(thm)], [c_7514, c_8262])).
% 11.18/4.33  tff(c_8274, plain, (![B_990, B_991, A_992]: (r2_hidden('#skF_1'(k2_relat_1(B_990), B_991), A_992) | r1_tarski(k2_relat_1(B_990), B_991) | ~v5_relat_1(B_990, k2_relat_1('#skF_8')) | ~v1_relat_1(B_990))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8264])).
% 11.18/4.33  tff(c_8303, plain, (![B_996, A_997]: (r1_tarski(k2_relat_1(B_996), A_997) | ~v5_relat_1(B_996, k2_relat_1('#skF_8')) | ~v1_relat_1(B_996))), inference(resolution, [status(thm)], [c_8274, c_4])).
% 11.18/4.33  tff(c_8306, plain, (![A_997]: (r1_tarski(k2_relat_1('#skF_8'), A_997) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_7514, c_8303])).
% 11.18/4.33  tff(c_8314, plain, (![A_997]: (r1_tarski(k2_relat_1('#skF_8'), A_997))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8306])).
% 11.18/4.33  tff(c_7725, plain, (![B_886, A_887, C_888]: (k1_xboole_0=B_886 | k1_relset_1(A_887, B_886, C_888)=A_887 | ~v1_funct_2(C_888, A_887, B_886) | ~m1_subset_1(C_888, k1_zfmisc_1(k2_zfmisc_1(A_887, B_886))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.18/4.33  tff(c_7728, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_7725])).
% 11.18/4.33  tff(c_7731, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_136, c_7728])).
% 11.18/4.33  tff(c_7732, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_7731])).
% 11.18/4.33  tff(c_7912, plain, (![A_917, B_918]: (r2_hidden('#skF_3'(A_917, B_918), k1_relat_1(A_917)) | r2_hidden('#skF_4'(A_917, B_918), B_918) | k2_relat_1(A_917)=B_918 | ~v1_funct_1(A_917) | ~v1_relat_1(A_917))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_7920, plain, (![B_918]: (r2_hidden('#skF_3'('#skF_8', B_918), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_918), B_918) | k2_relat_1('#skF_8')=B_918 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_7732, c_7912])).
% 11.18/4.33  tff(c_7925, plain, (![B_919]: (r2_hidden('#skF_3'('#skF_8', B_919), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_919), B_919) | k2_relat_1('#skF_8')=B_919)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_7920])).
% 11.18/4.33  tff(c_7931, plain, (![B_919, B_2]: (r2_hidden('#skF_3'('#skF_8', B_919), B_2) | ~r1_tarski('#skF_6', B_2) | r2_hidden('#skF_4'('#skF_8', B_919), B_919) | k2_relat_1('#skF_8')=B_919)), inference(resolution, [status(thm)], [c_7925, c_2])).
% 11.18/4.33  tff(c_8025, plain, (![A_938, B_939]: (k1_funct_1(A_938, '#skF_3'(A_938, B_939))='#skF_2'(A_938, B_939) | r2_hidden('#skF_4'(A_938, B_939), B_939) | k2_relat_1(A_938)=B_939 | ~v1_funct_1(A_938) | ~v1_relat_1(A_938))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_8832, plain, (![A_1041, B_1042]: (r2_hidden('#skF_2'(A_1041, B_1042), k2_relat_1(A_1041)) | ~r2_hidden('#skF_3'(A_1041, B_1042), k1_relat_1(A_1041)) | ~v1_funct_1(A_1041) | ~v1_relat_1(A_1041) | r2_hidden('#skF_4'(A_1041, B_1042), B_1042) | k2_relat_1(A_1041)=B_1042 | ~v1_funct_1(A_1041) | ~v1_relat_1(A_1041))), inference(superposition, [status(thm), theory('equality')], [c_8025, c_14])).
% 11.18/4.33  tff(c_8852, plain, (![B_919]: (r2_hidden('#skF_2'('#skF_8', B_919), k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | r2_hidden('#skF_4'('#skF_8', B_919), B_919) | k2_relat_1('#skF_8')=B_919)), inference(resolution, [status(thm)], [c_7931, c_8832])).
% 11.18/4.33  tff(c_8879, plain, (![B_1043]: (r2_hidden('#skF_2'('#skF_8', B_1043), k2_relat_1('#skF_8')) | r2_hidden('#skF_4'('#skF_8', B_1043), B_1043) | k2_relat_1('#skF_8')=B_1043)), inference(demodulation, [status(thm), theory('equality')], [c_73, c_7732, c_88, c_60, c_8852])).
% 11.18/4.33  tff(c_8890, plain, (![B_1043, B_2]: (r2_hidden('#skF_2'('#skF_8', B_1043), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | r2_hidden('#skF_4'('#skF_8', B_1043), B_1043) | k2_relat_1('#skF_8')=B_1043)), inference(resolution, [status(thm)], [c_8879, c_2])).
% 11.18/4.33  tff(c_8908, plain, (![B_1044, B_1045]: (r2_hidden('#skF_2'('#skF_8', B_1044), B_1045) | r2_hidden('#skF_4'('#skF_8', B_1044), B_1044) | k2_relat_1('#skF_8')=B_1044)), inference(demodulation, [status(thm), theory('equality')], [c_8314, c_8890])).
% 11.18/4.33  tff(c_8918, plain, (![B_1045]: (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | r2_hidden('#skF_4'('#skF_8', B_1045), B_1045) | k2_relat_1('#skF_8')=B_1045)), inference(resolution, [status(thm)], [c_8908, c_26])).
% 11.18/4.33  tff(c_8942, plain, (![B_1046]: (r2_hidden('#skF_4'('#skF_8', B_1046), B_1046) | k2_relat_1('#skF_8')=B_1046)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_8918])).
% 11.18/4.33  tff(c_7505, plain, (![D_610, A_641]: (r2_hidden(D_610, A_641) | ~r2_hidden(D_610, '#skF_7'))), inference(splitRight, [status(thm)], [c_5254])).
% 11.18/4.33  tff(c_8948, plain, (![A_641]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), A_641) | k2_relat_1('#skF_8')='#skF_7')), inference(resolution, [status(thm)], [c_8942, c_7505])).
% 11.18/4.33  tff(c_8955, plain, (![A_641]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), A_641))), inference(negUnitSimplification, [status(thm)], [c_146, c_8948])).
% 11.18/4.33  tff(c_8292, plain, (![A_993, B_994, D_995]: (r2_hidden('#skF_3'(A_993, B_994), k1_relat_1(A_993)) | k1_funct_1(A_993, D_995)!='#skF_4'(A_993, B_994) | ~r2_hidden(D_995, k1_relat_1(A_993)) | k2_relat_1(A_993)=B_994 | ~v1_funct_1(A_993) | ~v1_relat_1(A_993))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_8300, plain, (![B_994, D_67]: (r2_hidden('#skF_3'('#skF_8', B_994), k1_relat_1('#skF_8')) | D_67!='#skF_4'('#skF_8', B_994) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_994 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_8292])).
% 11.18/4.33  tff(c_8302, plain, (![B_994, D_67]: (r2_hidden('#skF_3'('#skF_8', B_994), '#skF_6') | D_67!='#skF_4'('#skF_8', B_994) | ~r2_hidden('#skF_9'(D_67), '#skF_6') | k2_relat_1('#skF_8')=B_994 | ~r2_hidden(D_67, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_7732, c_7732, c_8300])).
% 11.18/4.33  tff(c_8767, plain, (![B_1031]: (r2_hidden('#skF_3'('#skF_8', B_1031), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1031)), '#skF_6') | k2_relat_1('#skF_8')=B_1031 | ~r2_hidden('#skF_4'('#skF_8', B_1031), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_8302])).
% 11.18/4.33  tff(c_8770, plain, (![B_1031]: (r2_hidden('#skF_3'('#skF_8', B_1031), '#skF_6') | k2_relat_1('#skF_8')=B_1031 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_1031), '#skF_7'))), inference(resolution, [status(thm)], [c_112, c_8767])).
% 11.18/4.33  tff(c_8778, plain, (![B_1032]: (r2_hidden('#skF_3'('#skF_8', B_1032), '#skF_6') | k2_relat_1('#skF_8')=B_1032 | ~r2_hidden('#skF_4'('#skF_8', B_1032), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_8770])).
% 11.18/4.33  tff(c_8781, plain, (![B_1032, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1032), B_2) | ~r1_tarski('#skF_6', B_2) | k2_relat_1('#skF_8')=B_1032 | ~r2_hidden('#skF_4'('#skF_8', B_1032), '#skF_7'))), inference(resolution, [status(thm)], [c_8778, c_2])).
% 11.18/4.33  tff(c_8434, plain, (![A_1006, B_1007, D_1008]: (k1_funct_1(A_1006, '#skF_3'(A_1006, B_1007))='#skF_2'(A_1006, B_1007) | k1_funct_1(A_1006, D_1008)!='#skF_4'(A_1006, B_1007) | ~r2_hidden(D_1008, k1_relat_1(A_1006)) | k2_relat_1(A_1006)=B_1007 | ~v1_funct_1(A_1006) | ~v1_relat_1(A_1006))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_8442, plain, (![B_1007, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1007))='#skF_2'('#skF_8', B_1007) | D_67!='#skF_4'('#skF_8', B_1007) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1007 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_8434])).
% 11.18/4.33  tff(c_8444, plain, (![B_1007, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1007))='#skF_2'('#skF_8', B_1007) | D_67!='#skF_4'('#skF_8', B_1007) | ~r2_hidden('#skF_9'(D_67), '#skF_6') | k2_relat_1('#skF_8')=B_1007 | ~r2_hidden(D_67, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_7732, c_8442])).
% 11.18/4.33  tff(c_9047, plain, (![B_1062]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1062))='#skF_2'('#skF_8', B_1062) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1062)), '#skF_6') | k2_relat_1('#skF_8')=B_1062 | ~r2_hidden('#skF_4'('#skF_8', B_1062), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_8444])).
% 11.18/4.33  tff(c_9050, plain, (![B_1062]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1062))='#skF_2'('#skF_8', B_1062) | k2_relat_1('#skF_8')=B_1062 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_1062), '#skF_7'))), inference(resolution, [status(thm)], [c_112, c_9047])).
% 11.18/4.33  tff(c_9058, plain, (![B_1063]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1063))='#skF_2'('#skF_8', B_1063) | k2_relat_1('#skF_8')=B_1063 | ~r2_hidden('#skF_4'('#skF_8', B_1063), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_9050])).
% 11.18/4.33  tff(c_9098, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_28, c_9058])).
% 11.18/4.33  tff(c_9120, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_9098])).
% 11.18/4.33  tff(c_9121, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_9120])).
% 11.18/4.33  tff(c_7823, plain, (![A_903, D_904, B_905]: (r2_hidden(k1_funct_1(A_903, D_904), B_905) | ~r1_tarski(k2_relat_1(A_903), B_905) | ~r2_hidden(D_904, k1_relat_1(A_903)) | ~v1_funct_1(A_903) | ~v1_relat_1(A_903))), inference(resolution, [status(thm)], [c_162, c_2])).
% 11.18/4.33  tff(c_8161, plain, (![A_968, D_969, B_970, B_971]: (r2_hidden(k1_funct_1(A_968, D_969), B_970) | ~r1_tarski(B_971, B_970) | ~r1_tarski(k2_relat_1(A_968), B_971) | ~r2_hidden(D_969, k1_relat_1(A_968)) | ~v1_funct_1(A_968) | ~v1_relat_1(A_968))), inference(resolution, [status(thm)], [c_7823, c_2])).
% 11.18/4.33  tff(c_8179, plain, (![A_968, D_969, A_6]: (r2_hidden(k1_funct_1(A_968, D_969), A_6) | ~r1_tarski(k2_relat_1(A_968), k1_xboole_0) | ~r2_hidden(D_969, k1_relat_1(A_968)) | ~v1_funct_1(A_968) | ~v1_relat_1(A_968))), inference(resolution, [status(thm)], [c_8, c_8161])).
% 11.18/4.33  tff(c_9140, plain, (![A_6]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), A_6) | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9121, c_8179])).
% 11.18/4.33  tff(c_9165, plain, (![A_6]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), A_6) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_7732, c_8314, c_9140])).
% 11.18/4.33  tff(c_9181, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_9165])).
% 11.18/4.33  tff(c_9184, plain, (~r1_tarski('#skF_6', '#skF_6') | k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_8781, c_9181])).
% 11.18/4.33  tff(c_9193, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_8955, c_73, c_9184])).
% 11.18/4.33  tff(c_9195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_9193])).
% 11.18/4.33  tff(c_9198, plain, (![A_1067]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), A_1067))), inference(splitRight, [status(thm)], [c_9165])).
% 11.18/4.33  tff(c_9204, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_9198, c_20])).
% 11.18/4.33  tff(c_9218, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_44, '#skF_6') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_7732, c_9204])).
% 11.18/4.33  tff(c_9250, plain, (![D_1069]: (k1_funct_1('#skF_8', D_1069)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1069, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_146, c_9218])).
% 11.18/4.33  tff(c_9415, plain, (![D_1073]: (k1_funct_1('#skF_8', '#skF_9'(D_1073))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1073, '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_9250])).
% 11.18/4.33  tff(c_9429, plain, (![D_1077]: (D_1077!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1077, '#skF_7') | ~r2_hidden(D_1077, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_9415])).
% 11.18/4.33  tff(c_9450, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_8955, c_9429])).
% 11.18/4.33  tff(c_9522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8955, c_9450])).
% 11.18/4.33  tff(c_9523, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_7731])).
% 11.18/4.33  tff(c_9570, plain, (![C_1084, A_1085]: (C_1084='#skF_7' | ~v1_funct_2(C_1084, A_1085, '#skF_7') | A_1085='#skF_7' | ~m1_subset_1(C_1084, k1_zfmisc_1(k2_zfmisc_1(A_1085, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_9523, c_9523, c_9523, c_9523, c_44])).
% 11.18/4.33  tff(c_9573, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_56, c_9570])).
% 11.18/4.33  tff(c_9576, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_9573])).
% 11.18/4.33  tff(c_9577, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_9576])).
% 11.18/4.33  tff(c_5077, plain, (![D_616, A_617]: (r2_hidden(D_616, A_617) | ~r2_hidden(D_616, '#skF_7') | ~v5_relat_1('#skF_8', A_617))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5069])).
% 11.18/4.33  tff(c_5088, plain, (![D_67, A_617]: (r2_hidden('#skF_9'(D_67), A_617) | ~v5_relat_1('#skF_8', A_617) | ~r1_tarski('#skF_6', '#skF_7') | ~r2_hidden(D_67, '#skF_7'))), inference(resolution, [status(thm)], [c_112, c_5077])).
% 11.18/4.33  tff(c_5101, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_5088])).
% 11.18/4.33  tff(c_9593, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9577, c_5101])).
% 11.18/4.33  tff(c_9607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_9593])).
% 11.18/4.33  tff(c_9608, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_9576])).
% 11.18/4.33  tff(c_5128, plain, (![B_625, A_626]: (r2_hidden('#skF_1'('#skF_7', B_625), A_626) | ~v5_relat_1('#skF_8', A_626) | r1_tarski('#skF_7', B_625))), inference(resolution, [status(thm)], [c_6, c_5077])).
% 11.18/4.33  tff(c_5149, plain, (![A_626]: (~v5_relat_1('#skF_8', A_626) | r1_tarski('#skF_7', A_626))), inference(resolution, [status(thm)], [c_5128, c_4])).
% 11.18/4.33  tff(c_7518, plain, (![A_626]: (r1_tarski('#skF_7', A_626))), inference(demodulation, [status(thm), theory('equality')], [c_7514, c_5149])).
% 11.18/4.33  tff(c_9628, plain, (![A_626]: (r1_tarski('#skF_8', A_626))), inference(demodulation, [status(thm), theory('equality')], [c_9608, c_7518])).
% 11.18/4.33  tff(c_111, plain, (![A_1, B_2, B_89]: (r2_hidden('#skF_1'(A_1, B_2), B_89) | ~r1_tarski(A_1, B_89) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_106])).
% 11.18/4.33  tff(c_7562, plain, (![D_862, A_863]: (r2_hidden(D_862, A_863) | ~r2_hidden(D_862, '#skF_7'))), inference(splitRight, [status(thm)], [c_5254])).
% 11.18/4.33  tff(c_7593, plain, (![A_866, B_867, A_868]: (r2_hidden('#skF_1'(A_866, B_867), A_868) | ~r1_tarski(A_866, '#skF_7') | r1_tarski(A_866, B_867))), inference(resolution, [status(thm)], [c_111, c_7562])).
% 11.18/4.33  tff(c_7611, plain, (![A_869, A_870]: (~r1_tarski(A_869, '#skF_7') | r1_tarski(A_869, A_870))), inference(resolution, [status(thm)], [c_7593, c_4])).
% 11.18/4.33  tff(c_7630, plain, (![B_8, A_870]: (r1_tarski(k2_relat_1(B_8), A_870) | ~v5_relat_1(B_8, '#skF_7') | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_12, c_7611])).
% 11.18/4.33  tff(c_9625, plain, (![B_8, A_870]: (r1_tarski(k2_relat_1(B_8), A_870) | ~v5_relat_1(B_8, '#skF_8') | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_9608, c_7630])).
% 11.18/4.33  tff(c_9638, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9608, c_146])).
% 11.18/4.33  tff(c_9757, plain, (![A_1100, B_1101]: (r2_hidden('#skF_3'(A_1100, B_1101), k1_relat_1(A_1100)) | r2_hidden('#skF_4'(A_1100, B_1101), B_1101) | k2_relat_1(A_1100)=B_1101 | ~v1_funct_1(A_1100) | ~v1_relat_1(A_1100))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_9764, plain, (![A_1100, B_1101, B_2]: (r2_hidden('#skF_4'(A_1100, B_1101), B_2) | ~r1_tarski(B_1101, B_2) | r2_hidden('#skF_3'(A_1100, B_1101), k1_relat_1(A_1100)) | k2_relat_1(A_1100)=B_1101 | ~v1_funct_1(A_1100) | ~v1_relat_1(A_1100))), inference(resolution, [status(thm)], [c_9757, c_2])).
% 11.18/4.33  tff(c_5046, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_176])).
% 11.18/4.33  tff(c_9641, plain, (![D_67, B_89]: (r2_hidden('#skF_9'(D_67), B_89) | ~r1_tarski('#skF_6', B_89) | ~r2_hidden(D_67, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9608, c_112])).
% 11.18/4.33  tff(c_9642, plain, (![D_67]: (k1_funct_1('#skF_8', '#skF_9'(D_67))=D_67 | ~r2_hidden(D_67, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9608, c_62])).
% 11.18/4.33  tff(c_10052, plain, (![A_1168, B_1169, D_1170]: (k1_funct_1(A_1168, '#skF_3'(A_1168, B_1169))='#skF_2'(A_1168, B_1169) | k1_funct_1(A_1168, D_1170)!='#skF_4'(A_1168, B_1169) | ~r2_hidden(D_1170, k1_relat_1(A_1168)) | k2_relat_1(A_1168)=B_1169 | ~v1_funct_1(A_1168) | ~v1_relat_1(A_1168))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_10056, plain, (![B_1169, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1169))='#skF_2'('#skF_8', B_1169) | D_67!='#skF_4'('#skF_8', B_1169) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1169 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9642, c_10052])).
% 11.18/4.33  tff(c_10060, plain, (![B_1169, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1169))='#skF_2'('#skF_8', B_1169) | D_67!='#skF_4'('#skF_8', B_1169) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1169 | ~r2_hidden(D_67, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_10056])).
% 11.18/4.33  tff(c_10245, plain, (![B_1205]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1205))='#skF_2'('#skF_8', B_1205) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1205)), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1205 | ~r2_hidden('#skF_4'('#skF_8', B_1205), '#skF_8'))), inference(reflexivity, [status(thm), theory('equality')], [c_10060])).
% 11.18/4.33  tff(c_10251, plain, (![B_1205]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1205))='#skF_2'('#skF_8', B_1205) | k2_relat_1('#skF_8')=B_1205 | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', B_1205), '#skF_8'))), inference(resolution, [status(thm)], [c_9641, c_10245])).
% 11.18/4.33  tff(c_10406, plain, (![B_1216]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1216))='#skF_2'('#skF_8', B_1216) | k2_relat_1('#skF_8')=B_1216 | ~r2_hidden('#skF_4'('#skF_8', B_1216), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5046, c_10251])).
% 11.18/4.33  tff(c_10414, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_28, c_10406])).
% 11.18/4.33  tff(c_10419, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_10414])).
% 11.18/4.33  tff(c_10420, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_9638, c_10419])).
% 11.18/4.33  tff(c_168, plain, (![A_109, D_110, B_2]: (r2_hidden(k1_funct_1(A_109, D_110), B_2) | ~r1_tarski(k2_relat_1(A_109), B_2) | ~r2_hidden(D_110, k1_relat_1(A_109)) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(resolution, [status(thm)], [c_162, c_2])).
% 11.18/4.33  tff(c_10429, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10420, c_168])).
% 11.18/4.33  tff(c_10444, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_10429])).
% 11.18/4.33  tff(c_10572, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_10444])).
% 11.18/4.33  tff(c_10578, plain, (![B_2]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), B_2) | ~r1_tarski('#skF_8', B_2) | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_9764, c_10572])).
% 11.18/4.33  tff(c_10594, plain, (![B_2]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), B_2) | k2_relat_1('#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_9628, c_10578])).
% 11.18/4.33  tff(c_10595, plain, (![B_2]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), B_2))), inference(negUnitSimplification, [status(thm)], [c_9638, c_10594])).
% 11.18/4.33  tff(c_121, plain, (![D_94, B_2, B_95]: (r2_hidden('#skF_9'(D_94), B_2) | ~r1_tarski(B_95, B_2) | ~r1_tarski('#skF_6', B_95) | ~r2_hidden(D_94, '#skF_7'))), inference(resolution, [status(thm)], [c_118, c_2])).
% 11.18/4.33  tff(c_5048, plain, (![D_94]: (r2_hidden('#skF_9'(D_94), k1_relat_1('#skF_8')) | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden(D_94, '#skF_7'))), inference(resolution, [status(thm)], [c_5046, c_121])).
% 11.18/4.33  tff(c_5061, plain, (![D_611]: (r2_hidden('#skF_9'(D_611), k1_relat_1('#skF_8')) | ~r2_hidden(D_611, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_5048])).
% 11.18/4.33  tff(c_5064, plain, (![D_611, B_2]: (r2_hidden('#skF_9'(D_611), B_2) | ~r1_tarski(k1_relat_1('#skF_8'), B_2) | ~r2_hidden(D_611, '#skF_7'))), inference(resolution, [status(thm)], [c_5061, c_2])).
% 11.18/4.33  tff(c_9632, plain, (![D_611, B_2]: (r2_hidden('#skF_9'(D_611), B_2) | ~r1_tarski(k1_relat_1('#skF_8'), B_2) | ~r2_hidden(D_611, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9608, c_5064])).
% 11.18/4.33  tff(c_9946, plain, (![A_1140, B_1141, D_1142]: (r2_hidden('#skF_3'(A_1140, B_1141), k1_relat_1(A_1140)) | k1_funct_1(A_1140, D_1142)!='#skF_4'(A_1140, B_1141) | ~r2_hidden(D_1142, k1_relat_1(A_1140)) | k2_relat_1(A_1140)=B_1141 | ~v1_funct_1(A_1140) | ~v1_relat_1(A_1140))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.18/4.33  tff(c_9950, plain, (![B_1141, D_67]: (r2_hidden('#skF_3'('#skF_8', B_1141), k1_relat_1('#skF_8')) | D_67!='#skF_4'('#skF_8', B_1141) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1141 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9642, c_9946])).
% 11.18/4.33  tff(c_9954, plain, (![B_1141, D_67]: (r2_hidden('#skF_3'('#skF_8', B_1141), k1_relat_1('#skF_8')) | D_67!='#skF_4'('#skF_8', B_1141) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1141 | ~r2_hidden(D_67, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_9950])).
% 11.18/4.33  tff(c_10149, plain, (![B_1187]: (r2_hidden('#skF_3'('#skF_8', B_1187), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1187)), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1187 | ~r2_hidden('#skF_4'('#skF_8', B_1187), '#skF_8'))), inference(reflexivity, [status(thm), theory('equality')], [c_9954])).
% 11.18/4.33  tff(c_10152, plain, (![B_1187]: (r2_hidden('#skF_3'('#skF_8', B_1187), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1187 | ~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', B_1187), '#skF_8'))), inference(resolution, [status(thm)], [c_9632, c_10149])).
% 11.18/4.33  tff(c_10167, plain, (![B_1189]: (r2_hidden('#skF_3'('#skF_8', B_1189), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1189 | ~r2_hidden('#skF_4'('#skF_8', B_1189), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_10152])).
% 11.18/4.33  tff(c_10170, plain, (![B_1189, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1189), B_2) | ~r1_tarski(k1_relat_1('#skF_8'), B_2) | k2_relat_1('#skF_8')=B_1189 | ~r2_hidden('#skF_4'('#skF_8', B_1189), '#skF_8'))), inference(resolution, [status(thm)], [c_10167, c_2])).
% 11.18/4.33  tff(c_10581, plain, (~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8' | ~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_10170, c_10572])).
% 11.18/4.33  tff(c_10598, plain, (k2_relat_1('#skF_8')='#skF_8' | ~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_10581])).
% 11.18/4.33  tff(c_10599, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_9638, c_10598])).
% 11.18/4.33  tff(c_10640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10595, c_10599])).
% 11.18/4.33  tff(c_10696, plain, (![B_1226]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), B_1226) | ~r1_tarski(k2_relat_1('#skF_8'), B_1226))), inference(splitRight, [status(thm)], [c_10444])).
% 11.18/4.33  tff(c_10706, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_10696, c_26])).
% 11.18/4.33  tff(c_10716, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_10706])).
% 11.18/4.33  tff(c_10717, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_9638, c_10716])).
% 11.18/4.33  tff(c_10719, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_10717])).
% 11.18/4.33  tff(c_10722, plain, (~v5_relat_1('#skF_8', '#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_9625, c_10719])).
% 11.18/4.33  tff(c_10729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_7514, c_10722])).
% 11.18/4.33  tff(c_10730, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_10717])).
% 11.18/4.33  tff(c_10833, plain, (![B_2]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), B_2) | ~r1_tarski('#skF_8', B_2))), inference(resolution, [status(thm)], [c_10730, c_2])).
% 11.18/4.33  tff(c_10840, plain, (![B_2]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_9628, c_10833])).
% 11.18/4.33  tff(c_5051, plain, (![D_94]: (r2_hidden('#skF_9'(D_94), k1_relat_1('#skF_8')) | ~r2_hidden(D_94, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_5048])).
% 11.18/4.33  tff(c_9636, plain, (![D_94]: (r2_hidden('#skF_9'(D_94), k1_relat_1('#skF_8')) | ~r2_hidden(D_94, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9608, c_5051])).
% 11.18/4.33  tff(c_10731, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_10717])).
% 11.18/4.33  tff(c_7610, plain, (![A_866, A_868]: (~r1_tarski(A_866, '#skF_7') | r1_tarski(A_866, A_868))), inference(resolution, [status(thm)], [c_7593, c_4])).
% 11.18/4.33  tff(c_9626, plain, (![A_866, A_868]: (~r1_tarski(A_866, '#skF_8') | r1_tarski(A_866, A_868))), inference(demodulation, [status(thm), theory('equality')], [c_9608, c_7610])).
% 11.18/4.33  tff(c_10761, plain, (![A_868]: (r1_tarski(k2_relat_1('#skF_8'), A_868))), inference(resolution, [status(thm)], [c_10731, c_9626])).
% 11.18/4.33  tff(c_10641, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2))), inference(splitRight, [status(thm)], [c_10444])).
% 11.18/4.33  tff(c_10842, plain, (![B_1228]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), B_1228))), inference(demodulation, [status(thm), theory('equality')], [c_10761, c_10641])).
% 11.18/4.33  tff(c_10845, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_10842, c_20])).
% 11.18/4.33  tff(c_10857, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_10845])).
% 11.18/4.33  tff(c_10931, plain, (![D_1233]: (k1_funct_1('#skF_8', D_1233)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_1233, k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_9638, c_10857])).
% 11.18/4.33  tff(c_11086, plain, (![D_1237]: (k1_funct_1('#skF_8', '#skF_9'(D_1237))!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_1237, '#skF_8'))), inference(resolution, [status(thm)], [c_9636, c_10931])).
% 11.18/4.33  tff(c_11091, plain, (![D_1238]: (D_1238!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_1238, '#skF_8') | ~r2_hidden(D_1238, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9642, c_11086])).
% 11.18/4.33  tff(c_11097, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_10840, c_11091])).
% 11.18/4.33  tff(c_11147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10840, c_11097])).
% 11.18/4.33  tff(c_11149, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_5088])).
% 11.18/4.33  tff(c_5090, plain, (![A_618]: (r1_tarski(A_618, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_618, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_5052, c_4])).
% 11.18/4.33  tff(c_5099, plain, (![A_1]: (~r1_tarski(A_1, '#skF_7') | r1_tarski(A_1, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_111, c_5090])).
% 11.18/4.33  tff(c_11322, plain, (![A_1267, B_1268, B_1269, B_1270]: (r2_hidden('#skF_1'(A_1267, B_1268), B_1269) | ~r1_tarski(B_1270, B_1269) | ~r1_tarski(A_1267, B_1270) | r1_tarski(A_1267, B_1268))), inference(resolution, [status(thm)], [c_122, c_2])).
% 11.18/4.33  tff(c_12019, plain, (![A_1346, B_1347, A_1348]: (r2_hidden('#skF_1'(A_1346, B_1347), k2_relat_1('#skF_8')) | ~r1_tarski(A_1346, A_1348) | r1_tarski(A_1346, B_1347) | ~r1_tarski(A_1348, '#skF_7'))), inference(resolution, [status(thm)], [c_5099, c_11322])).
% 11.18/4.33  tff(c_12031, plain, (![B_1347]: (r2_hidden('#skF_1'('#skF_6', B_1347), k2_relat_1('#skF_8')) | r1_tarski('#skF_6', B_1347) | ~r1_tarski('#skF_7', '#skF_7'))), inference(resolution, [status(thm)], [c_11149, c_12019])).
% 11.18/4.33  tff(c_12052, plain, (![B_1349]: (r2_hidden('#skF_1'('#skF_6', B_1349), k2_relat_1('#skF_8')) | r1_tarski('#skF_6', B_1349))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_12031])).
% 11.18/4.33  tff(c_12098, plain, (![B_1350, B_1351]: (r2_hidden('#skF_1'('#skF_6', B_1350), B_1351) | ~r1_tarski(k2_relat_1('#skF_8'), B_1351) | r1_tarski('#skF_6', B_1350))), inference(resolution, [status(thm)], [c_12052, c_2])).
% 11.50/4.33  tff(c_12114, plain, (![B_1350, A_7]: (r2_hidden('#skF_1'('#skF_6', B_1350), A_7) | ~v5_relat_1('#skF_8', A_7) | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7') | r1_tarski('#skF_6', B_1350))), inference(resolution, [status(thm)], [c_12098, c_5075])).
% 11.50/4.33  tff(c_12325, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_12114])).
% 11.50/4.33  tff(c_12334, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12, c_12325])).
% 11.50/4.33  tff(c_12342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_105, c_12334])).
% 11.50/4.33  tff(c_12344, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_12114])).
% 11.50/4.33  tff(c_11583, plain, (![B_1296, A_1297, C_1298]: (k1_xboole_0=B_1296 | k1_relset_1(A_1297, B_1296, C_1298)=A_1297 | ~v1_funct_2(C_1298, A_1297, B_1296) | ~m1_subset_1(C_1298, k1_zfmisc_1(k2_zfmisc_1(A_1297, B_1296))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.50/4.33  tff(c_11586, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_11583])).
% 11.50/4.33  tff(c_11589, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_136, c_11586])).
% 11.50/4.33  tff(c_11590, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_11589])).
% 11.50/4.33  tff(c_11978, plain, (![A_1340, B_1341]: (r2_hidden('#skF_3'(A_1340, B_1341), k1_relat_1(A_1340)) | r2_hidden('#skF_4'(A_1340, B_1341), B_1341) | k2_relat_1(A_1340)=B_1341 | ~v1_funct_1(A_1340) | ~v1_relat_1(A_1340))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.50/4.33  tff(c_11987, plain, (![A_1340, B_1341, B_2]: (r2_hidden('#skF_3'(A_1340, B_1341), B_2) | ~r1_tarski(k1_relat_1(A_1340), B_2) | r2_hidden('#skF_4'(A_1340, B_1341), B_1341) | k2_relat_1(A_1340)=B_1341 | ~v1_funct_1(A_1340) | ~v1_relat_1(A_1340))), inference(resolution, [status(thm)], [c_11978, c_2])).
% 11.50/4.33  tff(c_12802, plain, (![A_1393, B_1394, D_1395]: (k1_funct_1(A_1393, '#skF_3'(A_1393, B_1394))='#skF_2'(A_1393, B_1394) | k1_funct_1(A_1393, D_1395)!='#skF_4'(A_1393, B_1394) | ~r2_hidden(D_1395, k1_relat_1(A_1393)) | k2_relat_1(A_1393)=B_1394 | ~v1_funct_1(A_1393) | ~v1_relat_1(A_1393))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.50/4.33  tff(c_12808, plain, (![B_1394, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1394))='#skF_2'('#skF_8', B_1394) | D_67!='#skF_4'('#skF_8', B_1394) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1394 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_12802])).
% 11.50/4.33  tff(c_12810, plain, (![B_1394, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1394))='#skF_2'('#skF_8', B_1394) | D_67!='#skF_4'('#skF_8', B_1394) | ~r2_hidden('#skF_9'(D_67), '#skF_6') | k2_relat_1('#skF_8')=B_1394 | ~r2_hidden(D_67, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_11590, c_12808])).
% 11.50/4.33  tff(c_13522, plain, (![B_1460]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1460))='#skF_2'('#skF_8', B_1460) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1460)), '#skF_6') | k2_relat_1('#skF_8')=B_1460 | ~r2_hidden('#skF_4'('#skF_8', B_1460), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_12810])).
% 11.50/4.33  tff(c_13534, plain, (![B_1460]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1460))='#skF_2'('#skF_8', B_1460) | k2_relat_1('#skF_8')=B_1460 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_1460), '#skF_7'))), inference(resolution, [status(thm)], [c_112, c_13522])).
% 11.50/4.33  tff(c_13604, plain, (![B_1470]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1470))='#skF_2'('#skF_8', B_1470) | k2_relat_1('#skF_8')=B_1470 | ~r2_hidden('#skF_4'('#skF_8', B_1470), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_13534])).
% 11.50/4.33  tff(c_13618, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_28, c_13604])).
% 11.50/4.33  tff(c_13625, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_13618])).
% 11.50/4.33  tff(c_13626, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_13625])).
% 11.50/4.33  tff(c_13638, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_13626, c_14])).
% 11.50/4.33  tff(c_13649, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_11590, c_13638])).
% 11.50/4.33  tff(c_13651, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_13649])).
% 11.50/4.33  tff(c_13654, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_11987, c_13651])).
% 11.50/4.33  tff(c_13678, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_73, c_11590, c_13654])).
% 11.50/4.33  tff(c_13679, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_13678])).
% 11.50/4.33  tff(c_12622, plain, (![A_1381, B_1382, D_1383]: (r2_hidden('#skF_3'(A_1381, B_1382), k1_relat_1(A_1381)) | k1_funct_1(A_1381, D_1383)!='#skF_4'(A_1381, B_1382) | ~r2_hidden(D_1383, k1_relat_1(A_1381)) | k2_relat_1(A_1381)=B_1382 | ~v1_funct_1(A_1381) | ~v1_relat_1(A_1381))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.50/4.33  tff(c_12628, plain, (![B_1382, D_67]: (r2_hidden('#skF_3'('#skF_8', B_1382), k1_relat_1('#skF_8')) | D_67!='#skF_4'('#skF_8', B_1382) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1382 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_12622])).
% 11.50/4.33  tff(c_12630, plain, (![B_1382, D_67]: (r2_hidden('#skF_3'('#skF_8', B_1382), '#skF_6') | D_67!='#skF_4'('#skF_8', B_1382) | ~r2_hidden('#skF_9'(D_67), '#skF_6') | k2_relat_1('#skF_8')=B_1382 | ~r2_hidden(D_67, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_11590, c_11590, c_12628])).
% 11.50/4.33  tff(c_13256, plain, (![B_1444]: (r2_hidden('#skF_3'('#skF_8', B_1444), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1444)), '#skF_6') | k2_relat_1('#skF_8')=B_1444 | ~r2_hidden('#skF_4'('#skF_8', B_1444), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_12630])).
% 11.50/4.33  tff(c_13268, plain, (![B_1444]: (r2_hidden('#skF_3'('#skF_8', B_1444), '#skF_6') | k2_relat_1('#skF_8')=B_1444 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_1444), '#skF_7'))), inference(resolution, [status(thm)], [c_112, c_13256])).
% 11.50/4.33  tff(c_13416, plain, (![B_1447]: (r2_hidden('#skF_3'('#skF_8', B_1447), '#skF_6') | k2_relat_1('#skF_8')=B_1447 | ~r2_hidden('#skF_4'('#skF_8', B_1447), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_13268])).
% 11.50/4.33  tff(c_13419, plain, (![B_1447, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1447), B_2) | ~r1_tarski('#skF_6', B_2) | k2_relat_1('#skF_8')=B_1447 | ~r2_hidden('#skF_4'('#skF_8', B_1447), '#skF_7'))), inference(resolution, [status(thm)], [c_13416, c_2])).
% 11.50/4.33  tff(c_13660, plain, (~r1_tarski('#skF_6', '#skF_6') | k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_13419, c_13651])).
% 11.50/4.33  tff(c_13684, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_13660])).
% 11.50/4.33  tff(c_13685, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_13684])).
% 11.50/4.33  tff(c_13714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13679, c_13685])).
% 11.50/4.33  tff(c_13716, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_13649])).
% 11.50/4.33  tff(c_13630, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_13626, c_168])).
% 11.50/4.33  tff(c_13643, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_11590, c_13630])).
% 11.50/4.33  tff(c_13800, plain, (![B_1476]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_1476) | ~r1_tarski(k2_relat_1('#skF_8'), B_1476))), inference(demodulation, [status(thm), theory('equality')], [c_13716, c_13643])).
% 11.50/4.33  tff(c_13806, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_13800, c_20])).
% 11.50/4.33  tff(c_13819, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_44, '#skF_6') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12344, c_88, c_60, c_11590, c_13806])).
% 11.50/4.33  tff(c_13969, plain, (![D_1482]: (k1_funct_1('#skF_8', D_1482)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1482, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_146, c_13819])).
% 11.50/4.33  tff(c_14210, plain, (![D_1483]: (k1_funct_1('#skF_8', '#skF_9'(D_1483))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1483, '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_13969])).
% 11.50/4.33  tff(c_14214, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_62, c_14210])).
% 11.50/4.33  tff(c_13810, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_13800, c_26])).
% 11.50/4.33  tff(c_13823, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_12344, c_88, c_60, c_13810])).
% 11.50/4.33  tff(c_13824, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_13823])).
% 11.50/4.33  tff(c_14216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14214, c_13824])).
% 11.50/4.33  tff(c_14217, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_11589])).
% 11.50/4.33  tff(c_11151, plain, (![D_94]: (r2_hidden('#skF_9'(D_94), '#skF_7') | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden(D_94, '#skF_7'))), inference(resolution, [status(thm)], [c_11149, c_121])).
% 11.50/4.33  tff(c_11173, plain, (![D_1240]: (r2_hidden('#skF_9'(D_1240), '#skF_7') | ~r2_hidden(D_1240, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_11151])).
% 11.50/4.33  tff(c_11196, plain, (![D_1247, B_1248]: (r2_hidden('#skF_9'(D_1247), B_1248) | ~r1_tarski('#skF_7', B_1248) | ~r2_hidden(D_1247, '#skF_7'))), inference(resolution, [status(thm)], [c_11173, c_2])).
% 11.50/4.33  tff(c_11297, plain, (![D_1264, B_1265, B_1266]: (r2_hidden('#skF_9'(D_1264), B_1265) | ~r1_tarski(B_1266, B_1265) | ~r1_tarski('#skF_7', B_1266) | ~r2_hidden(D_1264, '#skF_7'))), inference(resolution, [status(thm)], [c_11196, c_2])).
% 11.50/4.33  tff(c_11320, plain, (![D_1264, A_6]: (r2_hidden('#skF_9'(D_1264), A_6) | ~r1_tarski('#skF_7', k1_xboole_0) | ~r2_hidden(D_1264, '#skF_7'))), inference(resolution, [status(thm)], [c_8, c_11297])).
% 11.50/4.33  tff(c_11321, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_11320])).
% 11.50/4.33  tff(c_14224, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14217, c_11321])).
% 11.50/4.33  tff(c_14234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_14224])).
% 11.50/4.33  tff(c_14236, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_11320])).
% 11.50/4.33  tff(c_14272, plain, (![A_1488, B_1489, B_1490, B_1491]: (r2_hidden('#skF_1'(A_1488, B_1489), B_1490) | ~r1_tarski(B_1491, B_1490) | ~r1_tarski(A_1488, B_1491) | r1_tarski(A_1488, B_1489))), inference(resolution, [status(thm)], [c_122, c_2])).
% 11.50/4.33  tff(c_14433, plain, (![A_1514, B_1515]: (r2_hidden('#skF_1'(A_1514, B_1515), k1_xboole_0) | ~r1_tarski(A_1514, '#skF_7') | r1_tarski(A_1514, B_1515))), inference(resolution, [status(thm)], [c_14236, c_14272])).
% 11.50/4.33  tff(c_14444, plain, (![A_1516]: (~r1_tarski(A_1516, '#skF_7') | r1_tarski(A_1516, k1_xboole_0))), inference(resolution, [status(thm)], [c_14433, c_4])).
% 11.50/4.33  tff(c_14454, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_14444, c_161])).
% 11.50/4.33  tff(c_14465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11149, c_14454])).
% 11.50/4.33  tff(c_14466, plain, (![D_106, A_6]: (r2_hidden('#skF_9'(D_106), A_6) | ~r2_hidden(D_106, '#skF_7'))), inference(splitRight, [status(thm)], [c_160])).
% 11.50/4.33  tff(c_14478, plain, (![A_1522, D_1523]: (r2_hidden(k1_funct_1(A_1522, D_1523), k2_relat_1(A_1522)) | ~r2_hidden(D_1523, k1_relat_1(A_1522)) | ~v1_funct_1(A_1522) | ~v1_relat_1(A_1522))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.50/4.33  tff(c_14483, plain, (![D_67]: (r2_hidden(D_67, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_14478])).
% 11.50/4.33  tff(c_14487, plain, (![D_1524]: (r2_hidden(D_1524, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_1524), k1_relat_1('#skF_8')) | ~r2_hidden(D_1524, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_14483])).
% 11.50/4.33  tff(c_14493, plain, (![D_1525]: (r2_hidden(D_1525, k2_relat_1('#skF_8')) | ~r2_hidden(D_1525, '#skF_7'))), inference(resolution, [status(thm)], [c_14466, c_14487])).
% 11.50/4.33  tff(c_14527, plain, (![A_1532]: (r1_tarski(A_1532, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_1532, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_14493, c_4])).
% 11.50/4.33  tff(c_14537, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_14527])).
% 11.50/4.33  tff(c_14536, plain, (![A_1]: (~r1_tarski(A_1, '#skF_7') | r1_tarski(A_1, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_111, c_14527])).
% 11.50/4.33  tff(c_14591, plain, (![A_1538, B_1539, B_1540, B_1541]: (r2_hidden('#skF_1'(A_1538, B_1539), B_1540) | ~r1_tarski(B_1541, B_1540) | ~r1_tarski(A_1538, B_1541) | r1_tarski(A_1538, B_1539))), inference(resolution, [status(thm)], [c_122, c_2])).
% 11.50/4.33  tff(c_14825, plain, (![A_1571, B_1572, A_1573]: (r2_hidden('#skF_1'(A_1571, B_1572), k2_relat_1('#skF_8')) | ~r1_tarski(A_1571, A_1573) | r1_tarski(A_1571, B_1572) | ~r1_tarski(A_1573, '#skF_7'))), inference(resolution, [status(thm)], [c_14536, c_14591])).
% 11.50/4.33  tff(c_14847, plain, (![B_1572]: (r2_hidden('#skF_1'('#skF_7', B_1572), k2_relat_1('#skF_8')) | r1_tarski('#skF_7', B_1572) | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_14537, c_14825])).
% 11.50/4.33  tff(c_14852, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_14847])).
% 11.50/4.33  tff(c_14861, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12, c_14852])).
% 11.50/4.33  tff(c_14871, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_105, c_14861])).
% 11.50/4.33  tff(c_14873, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_14847])).
% 11.50/4.33  tff(c_15108, plain, (![B_1592, A_1593, C_1594]: (k1_xboole_0=B_1592 | k1_relset_1(A_1593, B_1592, C_1594)=A_1593 | ~v1_funct_2(C_1594, A_1593, B_1592) | ~m1_subset_1(C_1594, k1_zfmisc_1(k2_zfmisc_1(A_1593, B_1592))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.50/4.33  tff(c_15111, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_15108])).
% 11.50/4.33  tff(c_15114, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_136, c_15111])).
% 11.50/4.33  tff(c_15115, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_15114])).
% 11.50/4.33  tff(c_14467, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_160])).
% 11.50/4.33  tff(c_14611, plain, (![A_1544, B_1545, A_1546]: (r2_hidden('#skF_1'(A_1544, B_1545), A_1546) | ~r1_tarski(A_1544, k1_xboole_0) | r1_tarski(A_1544, B_1545))), inference(resolution, [status(thm)], [c_8, c_14591])).
% 11.50/4.33  tff(c_14629, plain, (![A_1547, A_1548]: (~r1_tarski(A_1547, k1_xboole_0) | r1_tarski(A_1547, A_1548))), inference(resolution, [status(thm)], [c_14611, c_4])).
% 11.50/4.33  tff(c_14641, plain, (![A_1548]: (r1_tarski('#skF_6', A_1548))), inference(resolution, [status(thm)], [c_14467, c_14629])).
% 11.50/4.33  tff(c_16025, plain, (![A_1693, B_1694, D_1695]: (r2_hidden('#skF_3'(A_1693, B_1694), k1_relat_1(A_1693)) | k1_funct_1(A_1693, D_1695)!='#skF_4'(A_1693, B_1694) | ~r2_hidden(D_1695, k1_relat_1(A_1693)) | k2_relat_1(A_1693)=B_1694 | ~v1_funct_1(A_1693) | ~v1_relat_1(A_1693))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.50/4.33  tff(c_16031, plain, (![B_1694, D_67]: (r2_hidden('#skF_3'('#skF_8', B_1694), k1_relat_1('#skF_8')) | D_67!='#skF_4'('#skF_8', B_1694) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1694 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_16025])).
% 11.50/4.33  tff(c_16033, plain, (![B_1694, D_67]: (r2_hidden('#skF_3'('#skF_8', B_1694), '#skF_6') | D_67!='#skF_4'('#skF_8', B_1694) | ~r2_hidden('#skF_9'(D_67), '#skF_6') | k2_relat_1('#skF_8')=B_1694 | ~r2_hidden(D_67, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_15115, c_15115, c_16031])).
% 11.50/4.33  tff(c_16428, plain, (![B_1727]: (r2_hidden('#skF_3'('#skF_8', B_1727), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1727)), '#skF_6') | k2_relat_1('#skF_8')=B_1727 | ~r2_hidden('#skF_4'('#skF_8', B_1727), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_16033])).
% 11.50/4.33  tff(c_16433, plain, (![B_1728]: (r2_hidden('#skF_3'('#skF_8', B_1728), '#skF_6') | k2_relat_1('#skF_8')=B_1728 | ~r2_hidden('#skF_4'('#skF_8', B_1728), '#skF_7'))), inference(resolution, [status(thm)], [c_14466, c_16428])).
% 11.50/4.33  tff(c_16435, plain, (![B_1728, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1728), B_2) | ~r1_tarski('#skF_6', B_2) | k2_relat_1('#skF_8')=B_1728 | ~r2_hidden('#skF_4'('#skF_8', B_1728), '#skF_7'))), inference(resolution, [status(thm)], [c_16433, c_2])).
% 11.50/4.33  tff(c_16438, plain, (![B_1728, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1728), B_2) | k2_relat_1('#skF_8')=B_1728 | ~r2_hidden('#skF_4'('#skF_8', B_1728), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_14641, c_16435])).
% 11.50/4.33  tff(c_16316, plain, (![A_1714, B_1715, D_1716]: (k1_funct_1(A_1714, '#skF_3'(A_1714, B_1715))='#skF_2'(A_1714, B_1715) | k1_funct_1(A_1714, D_1716)!='#skF_4'(A_1714, B_1715) | ~r2_hidden(D_1716, k1_relat_1(A_1714)) | k2_relat_1(A_1714)=B_1715 | ~v1_funct_1(A_1714) | ~v1_relat_1(A_1714))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.50/4.33  tff(c_16322, plain, (![B_1715, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1715))='#skF_2'('#skF_8', B_1715) | D_67!='#skF_4'('#skF_8', B_1715) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1715 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_16316])).
% 11.50/4.33  tff(c_16324, plain, (![B_1715, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1715))='#skF_2'('#skF_8', B_1715) | D_67!='#skF_4'('#skF_8', B_1715) | ~r2_hidden('#skF_9'(D_67), '#skF_6') | k2_relat_1('#skF_8')=B_1715 | ~r2_hidden(D_67, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_15115, c_16322])).
% 11.50/4.33  tff(c_16519, plain, (![B_1739]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1739))='#skF_2'('#skF_8', B_1739) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1739)), '#skF_6') | k2_relat_1('#skF_8')=B_1739 | ~r2_hidden('#skF_4'('#skF_8', B_1739), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_16324])).
% 11.50/4.33  tff(c_16524, plain, (![B_1740]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1740))='#skF_2'('#skF_8', B_1740) | k2_relat_1('#skF_8')=B_1740 | ~r2_hidden('#skF_4'('#skF_8', B_1740), '#skF_7'))), inference(resolution, [status(thm)], [c_14466, c_16519])).
% 11.50/4.33  tff(c_16532, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_28, c_16524])).
% 11.50/4.33  tff(c_16541, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_16532])).
% 11.50/4.33  tff(c_16542, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_16541])).
% 11.50/4.33  tff(c_16554, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_16542, c_14])).
% 11.50/4.33  tff(c_16565, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_15115, c_16554])).
% 11.50/4.33  tff(c_16567, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_16565])).
% 11.50/4.33  tff(c_16573, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_16438, c_16567])).
% 11.50/4.33  tff(c_16584, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_16573])).
% 11.50/4.33  tff(c_15396, plain, (![A_1630, B_1631]: (r2_hidden('#skF_3'(A_1630, B_1631), k1_relat_1(A_1630)) | r2_hidden('#skF_4'(A_1630, B_1631), B_1631) | k2_relat_1(A_1630)=B_1631 | ~v1_funct_1(A_1630) | ~v1_relat_1(A_1630))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.50/4.33  tff(c_16603, plain, (![A_1741, B_1742, B_1743]: (r2_hidden('#skF_3'(A_1741, B_1742), B_1743) | ~r1_tarski(k1_relat_1(A_1741), B_1743) | r2_hidden('#skF_4'(A_1741, B_1742), B_1742) | k2_relat_1(A_1741)=B_1742 | ~v1_funct_1(A_1741) | ~v1_relat_1(A_1741))), inference(resolution, [status(thm)], [c_15396, c_2])).
% 11.50/4.33  tff(c_16606, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_16603, c_16567])).
% 11.50/4.33  tff(c_16626, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_14641, c_15115, c_16606])).
% 11.50/4.33  tff(c_16628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_16584, c_16626])).
% 11.50/4.33  tff(c_16630, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_16565])).
% 11.50/4.33  tff(c_16632, plain, (![B_2]: (r2_hidden('#skF_3'('#skF_8', '#skF_7'), B_2) | ~r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_16630, c_2])).
% 11.50/4.33  tff(c_16635, plain, (![B_2]: (r2_hidden('#skF_3'('#skF_8', '#skF_7'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_14641, c_16632])).
% 11.50/4.33  tff(c_14484, plain, (![A_1522, D_1523, B_2]: (r2_hidden(k1_funct_1(A_1522, D_1523), B_2) | ~r1_tarski(k2_relat_1(A_1522), B_2) | ~r2_hidden(D_1523, k1_relat_1(A_1522)) | ~v1_funct_1(A_1522) | ~v1_relat_1(A_1522))), inference(resolution, [status(thm)], [c_14478, c_2])).
% 11.50/4.33  tff(c_16551, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16542, c_14484])).
% 11.50/4.33  tff(c_16563, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_15115, c_16551])).
% 11.50/4.33  tff(c_16656, plain, (![B_1745]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_1745) | ~r1_tarski(k2_relat_1('#skF_8'), B_1745))), inference(demodulation, [status(thm), theory('equality')], [c_16635, c_16563])).
% 11.50/4.33  tff(c_16662, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_16656, c_20])).
% 11.50/4.33  tff(c_16675, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_44, '#skF_6') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14873, c_88, c_60, c_15115, c_16662])).
% 11.50/4.33  tff(c_16792, plain, (![D_1752]: (k1_funct_1('#skF_8', D_1752)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1752, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_146, c_16675])).
% 11.50/4.33  tff(c_16931, plain, (![D_1753]: (k1_funct_1('#skF_8', '#skF_9'(D_1753))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1753, '#skF_7'))), inference(resolution, [status(thm)], [c_14466, c_16792])).
% 11.50/4.33  tff(c_16935, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_62, c_16931])).
% 11.50/4.33  tff(c_16666, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_16656, c_26])).
% 11.50/4.33  tff(c_16679, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14873, c_88, c_60, c_16666])).
% 11.50/4.33  tff(c_16680, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_16679])).
% 11.50/4.33  tff(c_16937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16935, c_16680])).
% 11.50/4.33  tff(c_16938, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_15114])).
% 11.50/4.33  tff(c_14657, plain, (![B_1550, A_1551]: (r1_tarski(k2_relat_1(B_1550), A_1551) | ~v5_relat_1(B_1550, k1_xboole_0) | ~v1_relat_1(B_1550))), inference(resolution, [status(thm)], [c_12, c_14629])).
% 11.50/4.33  tff(c_14500, plain, (![D_1525, B_2]: (r2_hidden(D_1525, B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r2_hidden(D_1525, '#skF_7'))), inference(resolution, [status(thm)], [c_14493, c_2])).
% 11.50/4.33  tff(c_14665, plain, (![D_1525, A_1551]: (r2_hidden(D_1525, A_1551) | ~r2_hidden(D_1525, '#skF_7') | ~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_14657, c_14500])).
% 11.50/4.33  tff(c_14673, plain, (![D_1525, A_1551]: (r2_hidden(D_1525, A_1551) | ~r2_hidden(D_1525, '#skF_7') | ~v5_relat_1('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_14665])).
% 11.50/4.33  tff(c_14676, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_14673])).
% 11.50/4.33  tff(c_16944, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16938, c_14676])).
% 11.50/4.33  tff(c_16954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_16944])).
% 11.50/4.33  tff(c_16956, plain, (v5_relat_1('#skF_8', k1_xboole_0)), inference(splitRight, [status(thm)], [c_14673])).
% 11.50/4.33  tff(c_14674, plain, (![B_1550, A_1551]: (v5_relat_1(B_1550, A_1551) | ~v5_relat_1(B_1550, k1_xboole_0) | ~v1_relat_1(B_1550))), inference(resolution, [status(thm)], [c_14657, c_10])).
% 11.50/4.33  tff(c_16958, plain, (![A_1551]: (v5_relat_1('#skF_8', A_1551) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_16956, c_14674])).
% 11.50/4.33  tff(c_16964, plain, (![A_1551]: (v5_relat_1('#skF_8', A_1551))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_16958])).
% 11.50/4.33  tff(c_14503, plain, (![D_1528, B_1529]: (r2_hidden(D_1528, B_1529) | ~r1_tarski(k2_relat_1('#skF_8'), B_1529) | ~r2_hidden(D_1528, '#skF_7'))), inference(resolution, [status(thm)], [c_14493, c_2])).
% 11.50/4.33  tff(c_14506, plain, (![D_1528, A_7]: (r2_hidden(D_1528, A_7) | ~r2_hidden(D_1528, '#skF_7') | ~v5_relat_1('#skF_8', A_7) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_12, c_14503])).
% 11.50/4.33  tff(c_14514, plain, (![D_1530, A_1531]: (r2_hidden(D_1530, A_1531) | ~r2_hidden(D_1530, '#skF_7') | ~v5_relat_1('#skF_8', A_1531))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_14506])).
% 11.50/4.33  tff(c_14549, plain, (![B_1535, A_1536]: (r2_hidden('#skF_1'('#skF_7', B_1535), A_1536) | ~v5_relat_1('#skF_8', A_1536) | r1_tarski('#skF_7', B_1535))), inference(resolution, [status(thm)], [c_6, c_14514])).
% 11.50/4.33  tff(c_14570, plain, (![A_1536]: (~v5_relat_1('#skF_8', A_1536) | r1_tarski('#skF_7', A_1536))), inference(resolution, [status(thm)], [c_14549, c_4])).
% 11.50/4.33  tff(c_16968, plain, (![A_1536]: (r1_tarski('#skF_7', A_1536))), inference(demodulation, [status(thm), theory('equality')], [c_16964, c_14570])).
% 11.50/4.33  tff(c_17267, plain, (![B_1793, A_1794, C_1795]: (k1_xboole_0=B_1793 | k1_relset_1(A_1794, B_1793, C_1795)=A_1794 | ~v1_funct_2(C_1795, A_1794, B_1793) | ~m1_subset_1(C_1795, k1_zfmisc_1(k2_zfmisc_1(A_1794, B_1793))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.50/4.33  tff(c_17270, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_17267])).
% 11.50/4.33  tff(c_17273, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_136, c_17270])).
% 11.50/4.33  tff(c_17280, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_17273])).
% 11.50/4.33  tff(c_17415, plain, (![A_1816, B_1817]: (r2_hidden('#skF_3'(A_1816, B_1817), k1_relat_1(A_1816)) | r2_hidden('#skF_4'(A_1816, B_1817), B_1817) | k2_relat_1(A_1816)=B_1817 | ~v1_funct_1(A_1816) | ~v1_relat_1(A_1816))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.50/4.33  tff(c_17423, plain, (![B_1817]: (r2_hidden('#skF_3'('#skF_8', B_1817), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_1817), B_1817) | k2_relat_1('#skF_8')=B_1817 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_17280, c_17415])).
% 11.50/4.33  tff(c_17428, plain, (![B_1818]: (r2_hidden('#skF_3'('#skF_8', B_1818), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_1818), B_1818) | k2_relat_1('#skF_8')=B_1818)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_17423])).
% 11.50/4.33  tff(c_17450, plain, (![B_1821, B_1822]: (r2_hidden('#skF_4'('#skF_8', B_1821), B_1822) | ~r1_tarski(B_1821, B_1822) | r2_hidden('#skF_3'('#skF_8', B_1821), '#skF_6') | k2_relat_1('#skF_8')=B_1821)), inference(resolution, [status(thm)], [c_17428, c_2])).
% 11.50/4.33  tff(c_17455, plain, (![B_1821, B_2, B_1822]: (r2_hidden('#skF_3'('#skF_8', B_1821), B_2) | ~r1_tarski('#skF_6', B_2) | r2_hidden('#skF_4'('#skF_8', B_1821), B_1822) | ~r1_tarski(B_1821, B_1822) | k2_relat_1('#skF_8')=B_1821)), inference(resolution, [status(thm)], [c_17450, c_2])).
% 11.50/4.33  tff(c_17459, plain, (![B_1821, B_2, B_1822]: (r2_hidden('#skF_3'('#skF_8', B_1821), B_2) | r2_hidden('#skF_4'('#skF_8', B_1821), B_1822) | ~r1_tarski(B_1821, B_1822) | k2_relat_1('#skF_8')=B_1821)), inference(demodulation, [status(thm), theory('equality')], [c_14641, c_17455])).
% 11.50/4.33  tff(c_17007, plain, (![A_1760, B_1761]: (r2_hidden('#skF_1'(A_1760, B_1761), k1_xboole_0) | ~r1_tarski(A_1760, '#skF_6') | r1_tarski(A_1760, B_1761))), inference(resolution, [status(thm)], [c_14467, c_14591])).
% 11.50/4.33  tff(c_17018, plain, (![A_1762]: (~r1_tarski(A_1762, '#skF_6') | r1_tarski(A_1762, k1_xboole_0))), inference(resolution, [status(thm)], [c_17007, c_4])).
% 11.50/4.33  tff(c_129, plain, (![A_96, B_97, B_2, B_98]: (r2_hidden('#skF_1'(A_96, B_97), B_2) | ~r1_tarski(B_98, B_2) | ~r1_tarski(A_96, B_98) | r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_122, c_2])).
% 11.50/4.33  tff(c_17234, plain, (![A_1788, B_1789, A_1790]: (r2_hidden('#skF_1'(A_1788, B_1789), k1_xboole_0) | ~r1_tarski(A_1788, A_1790) | r1_tarski(A_1788, B_1789) | ~r1_tarski(A_1790, '#skF_6'))), inference(resolution, [status(thm)], [c_17018, c_129])).
% 11.50/4.33  tff(c_17713, plain, (![B_1864, B_1865, A_1866]: (r2_hidden('#skF_1'(k2_relat_1(B_1864), B_1865), k1_xboole_0) | r1_tarski(k2_relat_1(B_1864), B_1865) | ~r1_tarski(A_1866, '#skF_6') | ~v5_relat_1(B_1864, A_1866) | ~v1_relat_1(B_1864))), inference(resolution, [status(thm)], [c_12, c_17234])).
% 11.50/4.33  tff(c_17715, plain, (![B_1865, A_1551]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_1865), k1_xboole_0) | r1_tarski(k2_relat_1('#skF_8'), B_1865) | ~r1_tarski(A_1551, '#skF_6') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_16964, c_17713])).
% 11.50/4.33  tff(c_17722, plain, (![B_1865, A_1551]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_1865), k1_xboole_0) | r1_tarski(k2_relat_1('#skF_8'), B_1865) | ~r1_tarski(A_1551, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_17715])).
% 11.50/4.33  tff(c_17727, plain, (![A_1870]: (~r1_tarski(A_1870, '#skF_6'))), inference(splitLeft, [status(thm)], [c_17722])).
% 11.50/4.33  tff(c_17756, plain, $false, inference(resolution, [status(thm)], [c_16968, c_17727])).
% 11.50/4.33  tff(c_17758, plain, (![B_1871]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_1871), k1_xboole_0) | r1_tarski(k2_relat_1('#skF_8'), B_1871))), inference(splitRight, [status(thm)], [c_17722])).
% 11.50/4.33  tff(c_17768, plain, (r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(resolution, [status(thm)], [c_17758, c_4])).
% 11.50/4.33  tff(c_14628, plain, (![A_1544, A_1546]: (~r1_tarski(A_1544, k1_xboole_0) | r1_tarski(A_1544, A_1546))), inference(resolution, [status(thm)], [c_14611, c_4])).
% 11.50/4.33  tff(c_17826, plain, (![A_1546]: (r1_tarski(k2_relat_1('#skF_8'), A_1546))), inference(resolution, [status(thm)], [c_17768, c_14628])).
% 11.50/4.33  tff(c_18079, plain, (![A_1892, B_1893, D_1894]: (k1_funct_1(A_1892, '#skF_3'(A_1892, B_1893))='#skF_2'(A_1892, B_1893) | k1_funct_1(A_1892, D_1894)!='#skF_4'(A_1892, B_1893) | ~r2_hidden(D_1894, k1_relat_1(A_1892)) | k2_relat_1(A_1892)=B_1893 | ~v1_funct_1(A_1892) | ~v1_relat_1(A_1892))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.50/4.33  tff(c_18087, plain, (![B_1893, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1893))='#skF_2'('#skF_8', B_1893) | D_67!='#skF_4'('#skF_8', B_1893) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1893 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_18079])).
% 11.50/4.33  tff(c_18089, plain, (![B_1893, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1893))='#skF_2'('#skF_8', B_1893) | D_67!='#skF_4'('#skF_8', B_1893) | ~r2_hidden('#skF_9'(D_67), '#skF_6') | k2_relat_1('#skF_8')=B_1893 | ~r2_hidden(D_67, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_17280, c_18087])).
% 11.50/4.33  tff(c_18251, plain, (![B_1928]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1928))='#skF_2'('#skF_8', B_1928) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1928)), '#skF_6') | k2_relat_1('#skF_8')=B_1928 | ~r2_hidden('#skF_4'('#skF_8', B_1928), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_18089])).
% 11.50/4.33  tff(c_18256, plain, (![B_1929]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1929))='#skF_2'('#skF_8', B_1929) | k2_relat_1('#skF_8')=B_1929 | ~r2_hidden('#skF_4'('#skF_8', B_1929), '#skF_7'))), inference(resolution, [status(thm)], [c_14466, c_18251])).
% 11.50/4.33  tff(c_18272, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_28, c_18256])).
% 11.50/4.33  tff(c_18287, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_18272])).
% 11.50/4.33  tff(c_18288, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_18287])).
% 11.50/4.33  tff(c_17309, plain, (![A_1802, D_1803, B_1804]: (r2_hidden(k1_funct_1(A_1802, D_1803), B_1804) | ~r1_tarski(k2_relat_1(A_1802), B_1804) | ~r2_hidden(D_1803, k1_relat_1(A_1802)) | ~v1_funct_1(A_1802) | ~v1_relat_1(A_1802))), inference(resolution, [status(thm)], [c_14478, c_2])).
% 11.50/4.33  tff(c_18201, plain, (![A_1921, D_1922, B_1923, B_1924]: (r2_hidden(k1_funct_1(A_1921, D_1922), B_1923) | ~r1_tarski(B_1924, B_1923) | ~r1_tarski(k2_relat_1(A_1921), B_1924) | ~r2_hidden(D_1922, k1_relat_1(A_1921)) | ~v1_funct_1(A_1921) | ~v1_relat_1(A_1921))), inference(resolution, [status(thm)], [c_17309, c_2])).
% 11.50/4.33  tff(c_18228, plain, (![A_1921, D_1922, A_6]: (r2_hidden(k1_funct_1(A_1921, D_1922), A_6) | ~r1_tarski(k2_relat_1(A_1921), k1_xboole_0) | ~r2_hidden(D_1922, k1_relat_1(A_1921)) | ~v1_funct_1(A_1921) | ~v1_relat_1(A_1921))), inference(resolution, [status(thm)], [c_8, c_18201])).
% 11.50/4.33  tff(c_18292, plain, (![A_6]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), A_6) | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18288, c_18228])).
% 11.50/4.33  tff(c_18313, plain, (![A_6]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), A_6) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_17280, c_17826, c_18292])).
% 11.50/4.33  tff(c_18326, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_18313])).
% 11.50/4.33  tff(c_18344, plain, (![B_1822]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), B_1822) | ~r1_tarski('#skF_7', B_1822) | k2_relat_1('#skF_8')='#skF_7')), inference(resolution, [status(thm)], [c_17459, c_18326])).
% 11.50/4.33  tff(c_18369, plain, (![B_1822]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), B_1822) | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16968, c_18344])).
% 11.50/4.33  tff(c_18370, plain, (![B_1822]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), B_1822))), inference(negUnitSimplification, [status(thm)], [c_146, c_18369])).
% 11.50/4.33  tff(c_17962, plain, (![A_1878, B_1879, D_1880]: (r2_hidden('#skF_3'(A_1878, B_1879), k1_relat_1(A_1878)) | k1_funct_1(A_1878, D_1880)!='#skF_4'(A_1878, B_1879) | ~r2_hidden(D_1880, k1_relat_1(A_1878)) | k2_relat_1(A_1878)=B_1879 | ~v1_funct_1(A_1878) | ~v1_relat_1(A_1878))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.50/4.33  tff(c_17970, plain, (![B_1879, D_67]: (r2_hidden('#skF_3'('#skF_8', B_1879), k1_relat_1('#skF_8')) | D_67!='#skF_4'('#skF_8', B_1879) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1879 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_17962])).
% 11.50/4.33  tff(c_17972, plain, (![B_1879, D_67]: (r2_hidden('#skF_3'('#skF_8', B_1879), '#skF_6') | D_67!='#skF_4'('#skF_8', B_1879) | ~r2_hidden('#skF_9'(D_67), '#skF_6') | k2_relat_1('#skF_8')=B_1879 | ~r2_hidden(D_67, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_17280, c_17280, c_17970])).
% 11.50/4.33  tff(c_18133, plain, (![B_1907]: (r2_hidden('#skF_3'('#skF_8', B_1907), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1907)), '#skF_6') | k2_relat_1('#skF_8')=B_1907 | ~r2_hidden('#skF_4'('#skF_8', B_1907), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_17972])).
% 11.50/4.33  tff(c_18138, plain, (![B_1908]: (r2_hidden('#skF_3'('#skF_8', B_1908), '#skF_6') | k2_relat_1('#skF_8')=B_1908 | ~r2_hidden('#skF_4'('#skF_8', B_1908), '#skF_7'))), inference(resolution, [status(thm)], [c_14466, c_18133])).
% 11.50/4.33  tff(c_18140, plain, (![B_1908, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1908), B_2) | ~r1_tarski('#skF_6', B_2) | k2_relat_1('#skF_8')=B_1908 | ~r2_hidden('#skF_4'('#skF_8', B_1908), '#skF_7'))), inference(resolution, [status(thm)], [c_18138, c_2])).
% 11.50/4.33  tff(c_18143, plain, (![B_1908, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1908), B_2) | k2_relat_1('#skF_8')=B_1908 | ~r2_hidden('#skF_4'('#skF_8', B_1908), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_14641, c_18140])).
% 11.50/4.33  tff(c_18329, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_18143, c_18326])).
% 11.50/4.33  tff(c_18350, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_18329])).
% 11.50/4.33  tff(c_18420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18370, c_18350])).
% 11.50/4.33  tff(c_18423, plain, (![A_1933]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), A_1933))), inference(splitRight, [status(thm)], [c_18313])).
% 11.50/4.33  tff(c_18430, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_18423, c_26])).
% 11.50/4.33  tff(c_18442, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_18430])).
% 11.50/4.33  tff(c_18443, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_146, c_18442])).
% 11.50/4.33  tff(c_16955, plain, (![D_1525, A_1551]: (r2_hidden(D_1525, A_1551) | ~r2_hidden(D_1525, '#skF_7'))), inference(splitRight, [status(thm)], [c_14673])).
% 11.50/4.33  tff(c_18458, plain, (![A_1551]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), A_1551))), inference(resolution, [status(thm)], [c_18443, c_16955])).
% 11.50/4.33  tff(c_18426, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_18423, c_20])).
% 11.50/4.33  tff(c_18438, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_44, '#skF_6') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_17280, c_18426])).
% 11.50/4.33  tff(c_18497, plain, (![D_1936]: (k1_funct_1('#skF_8', D_1936)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1936, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_146, c_18438])).
% 11.50/4.33  tff(c_18647, plain, (![D_1940]: (k1_funct_1('#skF_8', '#skF_9'(D_1940))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1940, '#skF_7'))), inference(resolution, [status(thm)], [c_14466, c_18497])).
% 11.50/4.33  tff(c_18656, plain, (![D_1941]: (D_1941!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1941, '#skF_7') | ~r2_hidden(D_1941, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_18647])).
% 11.50/4.33  tff(c_18663, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_18458, c_18656])).
% 11.50/4.33  tff(c_18739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18458, c_18663])).
% 11.50/4.33  tff(c_18741, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_17273])).
% 11.50/4.33  tff(c_18740, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_17273])).
% 11.50/4.33  tff(c_18784, plain, (![C_1946, A_1947]: (C_1946='#skF_7' | ~v1_funct_2(C_1946, A_1947, '#skF_7') | A_1947='#skF_7' | ~m1_subset_1(C_1946, k1_zfmisc_1(k2_zfmisc_1(A_1947, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_18740, c_18740, c_18740, c_18740, c_44])).
% 11.50/4.33  tff(c_18787, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_56, c_18784])).
% 11.50/4.33  tff(c_18790, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_18787])).
% 11.50/4.33  tff(c_18791, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_18790])).
% 11.50/4.33  tff(c_18810, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18791, c_58])).
% 11.50/4.33  tff(c_18807, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18791, c_136])).
% 11.50/4.33  tff(c_18809, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_18791, c_56])).
% 11.50/4.33  tff(c_50, plain, (![B_62, C_63]: (k1_relset_1(k1_xboole_0, B_62, C_63)=k1_xboole_0 | ~v1_funct_2(C_63, k1_xboole_0, B_62) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_62))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.50/4.33  tff(c_18746, plain, (![B_62, C_63]: (k1_relset_1('#skF_7', B_62, C_63)='#skF_7' | ~v1_funct_2(C_63, '#skF_7', B_62) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_62))))), inference(demodulation, [status(thm), theory('equality')], [c_18740, c_18740, c_18740, c_18740, c_50])).
% 11.50/4.33  tff(c_18944, plain, (![B_1966, C_1967]: (k1_relset_1('#skF_6', B_1966, C_1967)='#skF_6' | ~v1_funct_2(C_1967, '#skF_6', B_1966) | ~m1_subset_1(C_1967, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_1966))))), inference(demodulation, [status(thm), theory('equality')], [c_18791, c_18791, c_18791, c_18791, c_18746])).
% 11.50/4.33  tff(c_18947, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_18809, c_18944])).
% 11.50/4.33  tff(c_18950, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_18810, c_18807, c_18947])).
% 11.50/4.33  tff(c_18952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18741, c_18950])).
% 11.50/4.33  tff(c_18953, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_18790])).
% 11.50/4.33  tff(c_18968, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_18953, c_146])).
% 11.50/4.33  tff(c_18759, plain, (![A_1942, B_1943]: (r2_hidden('#skF_3'(A_1942, B_1943), k1_relat_1(A_1942)) | r2_hidden('#skF_4'(A_1942, B_1943), B_1943) | k2_relat_1(A_1942)=B_1943 | ~v1_funct_1(A_1942) | ~v1_relat_1(A_1942))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.50/4.33  tff(c_18765, plain, (![A_1942, B_1943, B_2]: (r2_hidden('#skF_3'(A_1942, B_1943), B_2) | ~r1_tarski(k1_relat_1(A_1942), B_2) | r2_hidden('#skF_4'(A_1942, B_1943), B_1943) | k2_relat_1(A_1942)=B_1943 | ~v1_funct_1(A_1942) | ~v1_relat_1(A_1942))), inference(resolution, [status(thm)], [c_18759, c_2])).
% 11.50/4.33  tff(c_18964, plain, (![A_1536]: (r1_tarski('#skF_8', A_1536))), inference(demodulation, [status(thm), theory('equality')], [c_18953, c_16968])).
% 11.50/4.33  tff(c_18958, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_18953, c_18740])).
% 11.50/4.33  tff(c_17258, plain, (![B_8, B_1789, A_7]: (r2_hidden('#skF_1'(k2_relat_1(B_8), B_1789), k1_xboole_0) | r1_tarski(k2_relat_1(B_8), B_1789) | ~r1_tarski(A_7, '#skF_6') | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_12, c_17234])).
% 11.50/4.33  tff(c_19447, plain, (![B_2049, B_2050, A_2051]: (r2_hidden('#skF_1'(k2_relat_1(B_2049), B_2050), '#skF_8') | r1_tarski(k2_relat_1(B_2049), B_2050) | ~r1_tarski(A_2051, '#skF_6') | ~v5_relat_1(B_2049, A_2051) | ~v1_relat_1(B_2049))), inference(demodulation, [status(thm), theory('equality')], [c_18958, c_17258])).
% 11.50/4.33  tff(c_19451, plain, (![B_2050, A_1551]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_2050), '#skF_8') | r1_tarski(k2_relat_1('#skF_8'), B_2050) | ~r1_tarski(A_1551, '#skF_6') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_16964, c_19447])).
% 11.50/4.33  tff(c_19457, plain, (![B_2050, A_1551]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_2050), '#skF_8') | r1_tarski(k2_relat_1('#skF_8'), B_2050) | ~r1_tarski(A_1551, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_19451])).
% 11.50/4.33  tff(c_19468, plain, (![A_2055]: (~r1_tarski(A_2055, '#skF_6'))), inference(splitLeft, [status(thm)], [c_19457])).
% 11.50/4.33  tff(c_19490, plain, $false, inference(resolution, [status(thm)], [c_18964, c_19468])).
% 11.50/4.33  tff(c_19492, plain, (![B_2056]: (r2_hidden('#skF_1'(k2_relat_1('#skF_8'), B_2056), '#skF_8') | r1_tarski(k2_relat_1('#skF_8'), B_2056))), inference(splitRight, [status(thm)], [c_19457])).
% 11.50/4.33  tff(c_19511, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_19492, c_4])).
% 11.50/4.33  tff(c_16993, plain, (![D_1758, A_1759]: (r2_hidden(D_1758, A_1759) | ~r2_hidden(D_1758, '#skF_7'))), inference(splitRight, [status(thm)], [c_14673])).
% 11.50/4.33  tff(c_17107, plain, (![A_1773, B_1774, A_1775]: (r2_hidden('#skF_1'(A_1773, B_1774), A_1775) | ~r1_tarski(A_1773, '#skF_7') | r1_tarski(A_1773, B_1774))), inference(resolution, [status(thm)], [c_111, c_16993])).
% 11.50/4.33  tff(c_17124, plain, (![A_1773, A_1775]: (~r1_tarski(A_1773, '#skF_7') | r1_tarski(A_1773, A_1775))), inference(resolution, [status(thm)], [c_17107, c_4])).
% 11.50/4.33  tff(c_18962, plain, (![A_1773, A_1775]: (~r1_tarski(A_1773, '#skF_8') | r1_tarski(A_1773, A_1775))), inference(demodulation, [status(thm), theory('equality')], [c_18953, c_17124])).
% 11.50/4.33  tff(c_19537, plain, (![A_1775]: (r1_tarski(k2_relat_1('#skF_8'), A_1775))), inference(resolution, [status(thm)], [c_19511, c_18962])).
% 11.50/4.33  tff(c_18967, plain, (![D_106, A_6]: (r2_hidden('#skF_9'(D_106), A_6) | ~r2_hidden(D_106, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_18953, c_14466])).
% 11.50/4.33  tff(c_18971, plain, (![D_67]: (k1_funct_1('#skF_8', '#skF_9'(D_67))=D_67 | ~r2_hidden(D_67, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_18953, c_62])).
% 11.50/4.33  tff(c_19231, plain, (![A_2006, B_2007, D_2008]: (k1_funct_1(A_2006, '#skF_3'(A_2006, B_2007))='#skF_2'(A_2006, B_2007) | k1_funct_1(A_2006, D_2008)!='#skF_4'(A_2006, B_2007) | ~r2_hidden(D_2008, k1_relat_1(A_2006)) | k2_relat_1(A_2006)=B_2007 | ~v1_funct_1(A_2006) | ~v1_relat_1(A_2006))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.50/4.33  tff(c_19233, plain, (![B_2007, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_2007))='#skF_2'('#skF_8', B_2007) | D_67!='#skF_4'('#skF_8', B_2007) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_2007 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18971, c_19231])).
% 11.50/4.33  tff(c_19239, plain, (![B_2007, D_67]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_2007))='#skF_2'('#skF_8', B_2007) | D_67!='#skF_4'('#skF_8', B_2007) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_2007 | ~r2_hidden(D_67, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_19233])).
% 11.50/4.33  tff(c_19512, plain, (![B_2057]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_2057))='#skF_2'('#skF_8', B_2057) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_2057)), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_2057 | ~r2_hidden('#skF_4'('#skF_8', B_2057), '#skF_8'))), inference(reflexivity, [status(thm), theory('equality')], [c_19239])).
% 11.50/4.33  tff(c_19707, plain, (![B_2069]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_2069))='#skF_2'('#skF_8', B_2069) | k2_relat_1('#skF_8')=B_2069 | ~r2_hidden('#skF_4'('#skF_8', B_2069), '#skF_8'))), inference(resolution, [status(thm)], [c_18967, c_19512])).
% 11.50/4.33  tff(c_19715, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_28, c_19707])).
% 11.50/4.33  tff(c_19720, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_19715])).
% 11.50/4.33  tff(c_19721, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_18968, c_19720])).
% 11.50/4.33  tff(c_19257, plain, (![A_2015, D_2016, B_2017]: (r2_hidden(k1_funct_1(A_2015, D_2016), B_2017) | ~r1_tarski(k2_relat_1(A_2015), B_2017) | ~r2_hidden(D_2016, k1_relat_1(A_2015)) | ~v1_funct_1(A_2015) | ~v1_relat_1(A_2015))), inference(resolution, [status(thm)], [c_14478, c_2])).
% 11.50/4.33  tff(c_18963, plain, (![D_1525, A_1551]: (r2_hidden(D_1525, A_1551) | ~r2_hidden(D_1525, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_18953, c_16955])).
% 11.50/4.33  tff(c_19272, plain, (![A_2015, D_2016, A_1551]: (r2_hidden(k1_funct_1(A_2015, D_2016), A_1551) | ~r1_tarski(k2_relat_1(A_2015), '#skF_8') | ~r2_hidden(D_2016, k1_relat_1(A_2015)) | ~v1_funct_1(A_2015) | ~v1_relat_1(A_2015))), inference(resolution, [status(thm)], [c_19257, c_18963])).
% 11.50/4.33  tff(c_19758, plain, (![A_1551]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), A_1551) | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_8') | ~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_19721, c_19272])).
% 11.50/4.33  tff(c_19774, plain, (![A_1551]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), A_1551) | ~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_19537, c_19758])).
% 11.50/4.33  tff(c_19800, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_19774])).
% 11.50/4.33  tff(c_19803, plain, (~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_18765, c_19800])).
% 11.50/4.33  tff(c_19818, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_73, c_19803])).
% 11.50/4.33  tff(c_19819, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_18968, c_19818])).
% 11.50/4.33  tff(c_19154, plain, (![A_1988, B_1989, D_1990]: (r2_hidden('#skF_3'(A_1988, B_1989), k1_relat_1(A_1988)) | k1_funct_1(A_1988, D_1990)!='#skF_4'(A_1988, B_1989) | ~r2_hidden(D_1990, k1_relat_1(A_1988)) | k2_relat_1(A_1988)=B_1989 | ~v1_funct_1(A_1988) | ~v1_relat_1(A_1988))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.50/4.33  tff(c_19156, plain, (![B_1989, D_67]: (r2_hidden('#skF_3'('#skF_8', B_1989), k1_relat_1('#skF_8')) | D_67!='#skF_4'('#skF_8', B_1989) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1989 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_67, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18971, c_19154])).
% 11.50/4.33  tff(c_19162, plain, (![B_1989, D_67]: (r2_hidden('#skF_3'('#skF_8', B_1989), k1_relat_1('#skF_8')) | D_67!='#skF_4'('#skF_8', B_1989) | ~r2_hidden('#skF_9'(D_67), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1989 | ~r2_hidden(D_67, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_19156])).
% 11.50/4.33  tff(c_19428, plain, (![B_2045]: (r2_hidden('#skF_3'('#skF_8', B_2045), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_2045)), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_2045 | ~r2_hidden('#skF_4'('#skF_8', B_2045), '#skF_8'))), inference(reflexivity, [status(thm), theory('equality')], [c_19162])).
% 11.50/4.33  tff(c_19432, plain, (![B_2045]: (r2_hidden('#skF_3'('#skF_8', B_2045), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_2045 | ~r2_hidden('#skF_4'('#skF_8', B_2045), '#skF_8'))), inference(resolution, [status(thm)], [c_18967, c_19428])).
% 11.50/4.33  tff(c_19812, plain, (k2_relat_1('#skF_8')='#skF_8' | ~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_19432, c_19800])).
% 11.50/4.33  tff(c_19830, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_18968, c_19812])).
% 11.50/4.33  tff(c_19897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19819, c_19830])).
% 11.50/4.33  tff(c_20012, plain, (![A_2082]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), A_2082))), inference(splitRight, [status(thm)], [c_19774])).
% 11.50/4.33  tff(c_20022, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_20012, c_26])).
% 11.50/4.33  tff(c_20033, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_20022])).
% 11.50/4.33  tff(c_20034, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_18968, c_20033])).
% 11.50/4.33  tff(c_20048, plain, (![A_1551]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), A_1551))), inference(resolution, [status(thm)], [c_20034, c_18963])).
% 11.50/4.33  tff(c_20015, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_20012, c_20])).
% 11.50/4.33  tff(c_20027, plain, (![D_44]: (k1_funct_1('#skF_8', D_44)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_44, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_60, c_20015])).
% 11.50/4.33  tff(c_20129, plain, (![D_2088]: (k1_funct_1('#skF_8', D_2088)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_2088, k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_18968, c_20027])).
% 11.50/4.33  tff(c_20243, plain, (![D_2089]: (k1_funct_1('#skF_8', '#skF_9'(D_2089))!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_2089, '#skF_8'))), inference(resolution, [status(thm)], [c_18967, c_20129])).
% 11.50/4.33  tff(c_20248, plain, (![D_2090]: (D_2090!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_2090, '#skF_8') | ~r2_hidden(D_2090, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18971, c_20243])).
% 11.50/4.33  tff(c_20257, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_20048, c_20248])).
% 11.50/4.33  tff(c_20299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20048, c_20257])).
% 11.50/4.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.50/4.33  
% 11.50/4.33  Inference rules
% 11.50/4.33  ----------------------
% 11.50/4.33  #Ref     : 21
% 11.50/4.33  #Sup     : 4328
% 11.50/4.33  #Fact    : 0
% 11.50/4.33  #Define  : 0
% 11.50/4.33  #Split   : 70
% 11.50/4.33  #Chain   : 0
% 11.50/4.33  #Close   : 0
% 11.50/4.33  
% 11.50/4.33  Ordering : KBO
% 11.50/4.33  
% 11.50/4.33  Simplification rules
% 11.50/4.33  ----------------------
% 11.50/4.33  #Subsume      : 1711
% 11.50/4.33  #Demod        : 2349
% 11.50/4.33  #Tautology    : 749
% 11.50/4.33  #SimpNegUnit  : 137
% 11.50/4.33  #BackRed      : 251
% 11.50/4.33  
% 11.50/4.33  #Partial instantiations: 0
% 11.50/4.33  #Strategies tried      : 1
% 11.50/4.33  
% 11.50/4.33  Timing (in seconds)
% 11.50/4.33  ----------------------
% 11.50/4.33  Preprocessing        : 0.36
% 11.50/4.33  Parsing              : 0.18
% 11.50/4.33  CNF conversion       : 0.03
% 11.50/4.33  Main loop            : 3.02
% 11.50/4.33  Inferencing          : 1.02
% 11.50/4.33  Reduction            : 0.81
% 11.50/4.33  Demodulation         : 0.53
% 11.50/4.33  BG Simplification    : 0.08
% 11.50/4.33  Subsumption          : 0.90
% 11.50/4.33  Abstraction          : 0.13
% 11.50/4.33  MUC search           : 0.00
% 11.50/4.33  Cooper               : 0.00
% 11.50/4.33  Total                : 3.60
% 11.50/4.33  Index Insertion      : 0.00
% 11.50/4.33  Index Deletion       : 0.00
% 11.50/4.33  Index Matching       : 0.00
% 11.50/4.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
