%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0707+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:44 EST 2020

% Result     : Theorem 16.25s
% Output     : CNFRefutation 16.69s
% Verified   : 
% Statistics : Number of formulae       :  287 (11912 expanded)
%              Number of leaves         :   27 (4174 expanded)
%              Depth                    :   37
%              Number of atoms          :  844 (32602 expanded)
%              Number of equality atoms :  130 (6593 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_5

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_41,axiom,(
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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_28,plain,(
    ! [A_43] : v1_funct_1(k6_relat_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_43] : v1_relat_1(k6_relat_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_39872,plain,(
    ! [A_1278,B_1279,C_1280] :
      ( r2_hidden('#skF_2'(A_1278,B_1279,C_1280),B_1279)
      | r2_hidden('#skF_3'(A_1278,B_1279,C_1280),C_1280)
      | k9_relat_1(A_1278,B_1279) = C_1280
      | ~ v1_funct_1(A_1278)
      | ~ v1_relat_1(A_1278) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    k9_relat_1(k6_relat_1('#skF_6'),'#skF_7') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_167,plain,(
    ! [A_95,B_96,C_97] :
      ( r2_hidden('#skF_2'(A_95,B_96,C_97),B_96)
      | r2_hidden('#skF_3'(A_95,B_96,C_97),C_97)
      | k9_relat_1(A_95,B_96) = C_97
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_81,plain,(
    ! [A_67,C_68,B_69] :
      ( m1_subset_1(A_67,C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_84,plain,(
    ! [A_67] :
      ( m1_subset_1(A_67,'#skF_6')
      | ~ r2_hidden(A_67,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_81])).

tff(c_174,plain,(
    ! [A_95,C_97] :
      ( m1_subset_1('#skF_2'(A_95,'#skF_7',C_97),'#skF_6')
      | r2_hidden('#skF_3'(A_95,'#skF_7',C_97),C_97)
      | k9_relat_1(A_95,'#skF_7') = C_97
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_167,c_84])).

tff(c_76,plain,(
    ! [C_64,B_65,A_66] :
      ( ~ v1_xboole_0(C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_79,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_66,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_76])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_38,plain,(
    ! [A_46] :
      ( k1_relat_1(k6_relat_1(A_46)) = A_46
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ! [A_46] :
      ( k1_relat_1(k6_relat_1(A_46)) = A_46
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_54,plain,(
    ! [A_46] : k1_relat_1(k6_relat_1(A_46)) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_48])).

tff(c_2,plain,(
    ! [A_1,E_42,B_24] :
      ( r2_hidden(k1_funct_1(A_1,E_42),k9_relat_1(A_1,B_24))
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,k1_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,(
    ! [A_84,B_85,D_86] :
      ( r2_hidden('#skF_4'(A_84,B_85,k9_relat_1(A_84,B_85),D_86),k1_relat_1(A_84))
      | ~ r2_hidden(D_86,k9_relat_1(A_84,B_85))
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_133,plain,(
    ! [A_46,B_85,D_86] :
      ( r2_hidden('#skF_4'(k6_relat_1(A_46),B_85,k9_relat_1(k6_relat_1(A_46),B_85),D_86),A_46)
      | ~ r2_hidden(D_86,k9_relat_1(k6_relat_1(A_46),B_85))
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_130])).

tff(c_135,plain,(
    ! [A_46,B_85,D_86] :
      ( r2_hidden('#skF_4'(k6_relat_1(A_46),B_85,k9_relat_1(k6_relat_1(A_46),B_85),D_86),A_46)
      | ~ r2_hidden(D_86,k9_relat_1(k6_relat_1(A_46),B_85)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_133])).

tff(c_143,plain,(
    ! [A_92,B_93,D_94] :
      ( k1_funct_1(A_92,'#skF_4'(A_92,B_93,k9_relat_1(A_92,B_93),D_94)) = D_94
      | ~ r2_hidden(D_94,k9_relat_1(A_92,B_93))
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [A_46,C_50] :
      ( k1_funct_1(k6_relat_1(A_46),C_50) = C_50
      | ~ r2_hidden(C_50,A_46)
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    ! [A_46,C_50] :
      ( k1_funct_1(k6_relat_1(A_46),C_50) = C_50
      | ~ r2_hidden(C_50,A_46)
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36])).

tff(c_52,plain,(
    ! [A_46,C_50] :
      ( k1_funct_1(k6_relat_1(A_46),C_50) = C_50
      | ~ r2_hidden(C_50,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_50])).

tff(c_153,plain,(
    ! [A_46,B_93,D_94] :
      ( '#skF_4'(k6_relat_1(A_46),B_93,k9_relat_1(k6_relat_1(A_46),B_93),D_94) = D_94
      | ~ r2_hidden('#skF_4'(k6_relat_1(A_46),B_93,k9_relat_1(k6_relat_1(A_46),B_93),D_94),A_46)
      | ~ r2_hidden(D_94,k9_relat_1(k6_relat_1(A_46),B_93))
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_52])).

tff(c_926,plain,(
    ! [A_181,B_182,D_183] :
      ( '#skF_4'(k6_relat_1(A_181),B_182,k9_relat_1(k6_relat_1(A_181),B_182),D_183) = D_183
      | ~ r2_hidden('#skF_4'(k6_relat_1(A_181),B_182,k9_relat_1(k6_relat_1(A_181),B_182),D_183),A_181)
      | ~ r2_hidden(D_183,k9_relat_1(k6_relat_1(A_181),B_182)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_153])).

tff(c_952,plain,(
    ! [A_184,B_185,D_186] :
      ( '#skF_4'(k6_relat_1(A_184),B_185,k9_relat_1(k6_relat_1(A_184),B_185),D_186) = D_186
      | ~ r2_hidden(D_186,k9_relat_1(k6_relat_1(A_184),B_185)) ) ),
    inference(resolution,[status(thm)],[c_135,c_926])).

tff(c_116,plain,(
    ! [A_73,B_74,D_75] :
      ( r2_hidden('#skF_4'(A_73,B_74,k9_relat_1(A_73,B_74),D_75),B_74)
      | ~ r2_hidden(D_75,k9_relat_1(A_73,B_74))
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_121,plain,(
    ! [A_73,D_75] :
      ( m1_subset_1('#skF_4'(A_73,'#skF_7',k9_relat_1(A_73,'#skF_7'),D_75),'#skF_6')
      | ~ r2_hidden(D_75,k9_relat_1(A_73,'#skF_7'))
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_116,c_84])).

tff(c_972,plain,(
    ! [D_186,A_184] :
      ( m1_subset_1(D_186,'#skF_6')
      | ~ r2_hidden(D_186,k9_relat_1(k6_relat_1(A_184),'#skF_7'))
      | ~ v1_funct_1(k6_relat_1(A_184))
      | ~ v1_relat_1(k6_relat_1(A_184))
      | ~ r2_hidden(D_186,k9_relat_1(k6_relat_1(A_184),'#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_121])).

tff(c_1078,plain,(
    ! [D_190,A_191] :
      ( m1_subset_1(D_190,'#skF_6')
      | ~ r2_hidden(D_190,k9_relat_1(k6_relat_1(A_191),'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_972])).

tff(c_1136,plain,(
    ! [A_191,E_42] :
      ( m1_subset_1(k1_funct_1(k6_relat_1(A_191),E_42),'#skF_6')
      | ~ r2_hidden(E_42,'#skF_7')
      | ~ r2_hidden(E_42,k1_relat_1(k6_relat_1(A_191)))
      | ~ v1_funct_1(k6_relat_1(A_191))
      | ~ v1_relat_1(k6_relat_1(A_191)) ) ),
    inference(resolution,[status(thm)],[c_2,c_1078])).

tff(c_1160,plain,(
    ! [A_191,E_42] :
      ( m1_subset_1(k1_funct_1(k6_relat_1(A_191),E_42),'#skF_6')
      | ~ r2_hidden(E_42,'#skF_7')
      | ~ r2_hidden(E_42,A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_1136])).

tff(c_30,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,B_45)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_193,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_hidden('#skF_2'(A_104,B_105,C_106),k1_relat_1(A_104))
      | r2_hidden('#skF_3'(A_104,B_105,C_106),C_106)
      | k9_relat_1(A_104,B_105) = C_106
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_198,plain,(
    ! [A_46,B_105,C_106] :
      ( r2_hidden('#skF_2'(k6_relat_1(A_46),B_105,C_106),A_46)
      | r2_hidden('#skF_3'(k6_relat_1(A_46),B_105,C_106),C_106)
      | k9_relat_1(k6_relat_1(A_46),B_105) = C_106
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_193])).

tff(c_230,plain,(
    ! [A_110,B_111,C_112] :
      ( r2_hidden('#skF_2'(k6_relat_1(A_110),B_111,C_112),A_110)
      | r2_hidden('#skF_3'(k6_relat_1(A_110),B_111,C_112),C_112)
      | k9_relat_1(k6_relat_1(A_110),B_111) = C_112 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_198])).

tff(c_237,plain,(
    ! [B_111,C_112] :
      ( m1_subset_1('#skF_2'(k6_relat_1('#skF_7'),B_111,C_112),'#skF_6')
      | r2_hidden('#skF_3'(k6_relat_1('#skF_7'),B_111,C_112),C_112)
      | k9_relat_1(k6_relat_1('#skF_7'),B_111) = C_112 ) ),
    inference(resolution,[status(thm)],[c_230,c_84])).

tff(c_22,plain,(
    ! [A_1,B_24,C_25] :
      ( r2_hidden('#skF_2'(A_1,B_24,C_25),B_24)
      | r2_hidden('#skF_3'(A_1,B_24,C_25),C_25)
      | k9_relat_1(A_1,B_24) = C_25
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_285,plain,(
    ! [A_121,B_122,C_123,E_124] :
      ( r2_hidden('#skF_2'(A_121,B_122,C_123),B_122)
      | k1_funct_1(A_121,E_124) != '#skF_3'(A_121,B_122,C_123)
      | ~ r2_hidden(E_124,B_122)
      | ~ r2_hidden(E_124,k1_relat_1(A_121))
      | k9_relat_1(A_121,B_122) = C_123
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_293,plain,(
    ! [A_46,B_122,C_123,C_50] :
      ( r2_hidden('#skF_2'(k6_relat_1(A_46),B_122,C_123),B_122)
      | C_50 != '#skF_3'(k6_relat_1(A_46),B_122,C_123)
      | ~ r2_hidden(C_50,B_122)
      | ~ r2_hidden(C_50,k1_relat_1(k6_relat_1(A_46)))
      | k9_relat_1(k6_relat_1(A_46),B_122) = C_123
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ r2_hidden(C_50,A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_285])).

tff(c_295,plain,(
    ! [A_46,B_122,C_123,C_50] :
      ( r2_hidden('#skF_2'(k6_relat_1(A_46),B_122,C_123),B_122)
      | C_50 != '#skF_3'(k6_relat_1(A_46),B_122,C_123)
      | ~ r2_hidden(C_50,B_122)
      | k9_relat_1(k6_relat_1(A_46),B_122) = C_123
      | ~ r2_hidden(C_50,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_293])).

tff(c_301,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_hidden('#skF_2'(k6_relat_1(A_129),B_130,C_131),B_130)
      | ~ r2_hidden('#skF_3'(k6_relat_1(A_129),B_130,C_131),B_130)
      | k9_relat_1(k6_relat_1(A_129),B_130) = C_131
      | ~ r2_hidden('#skF_3'(k6_relat_1(A_129),B_130,C_131),A_129) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_295])).

tff(c_316,plain,(
    ! [C_25,B_24] :
      ( ~ r2_hidden('#skF_3'(k6_relat_1(C_25),B_24,C_25),B_24)
      | r2_hidden('#skF_2'(k6_relat_1(C_25),B_24,C_25),B_24)
      | k9_relat_1(k6_relat_1(C_25),B_24) = C_25
      | ~ v1_funct_1(k6_relat_1(C_25))
      | ~ v1_relat_1(k6_relat_1(C_25)) ) ),
    inference(resolution,[status(thm)],[c_22,c_301])).

tff(c_335,plain,(
    ! [C_132,B_133] :
      ( ~ r2_hidden('#skF_3'(k6_relat_1(C_132),B_133,C_132),B_133)
      | r2_hidden('#skF_2'(k6_relat_1(C_132),B_133,C_132),B_133)
      | k9_relat_1(k6_relat_1(C_132),B_133) = C_132 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_316])).

tff(c_341,plain,(
    ! [C_134] :
      ( m1_subset_1('#skF_2'(k6_relat_1(C_134),'#skF_7',C_134),'#skF_6')
      | ~ r2_hidden('#skF_3'(k6_relat_1(C_134),'#skF_7',C_134),'#skF_7')
      | k9_relat_1(k6_relat_1(C_134),'#skF_7') = C_134 ) ),
    inference(resolution,[status(thm)],[c_335,c_84])).

tff(c_368,plain,
    ( m1_subset_1('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_6')
    | k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_237,c_341])).

tff(c_374,plain,(
    k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_396,plain,(
    ! [E_42] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_42),'#skF_7')
      | ~ r2_hidden(E_42,'#skF_7')
      | ~ r2_hidden(E_42,k1_relat_1(k6_relat_1('#skF_7')))
      | ~ v1_funct_1(k6_relat_1('#skF_7'))
      | ~ v1_relat_1(k6_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_2])).

tff(c_415,plain,(
    ! [E_135] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_135),'#skF_7')
      | ~ r2_hidden(E_135,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_396])).

tff(c_435,plain,(
    ! [E_135] :
      ( m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),E_135),'#skF_6')
      | ~ r2_hidden(E_135,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_415,c_84])).

tff(c_122,plain,(
    ! [A_76,E_77,B_78] :
      ( r2_hidden(k1_funct_1(A_76,E_77),k9_relat_1(A_76,B_78))
      | ~ r2_hidden(E_77,B_78)
      | ~ r2_hidden(E_77,k1_relat_1(A_76))
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_125,plain,(
    ! [C_50,A_46,B_78] :
      ( r2_hidden(C_50,k9_relat_1(k6_relat_1(A_46),B_78))
      | ~ r2_hidden(C_50,B_78)
      | ~ r2_hidden(C_50,k1_relat_1(k6_relat_1(A_46)))
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ r2_hidden(C_50,A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_122])).

tff(c_127,plain,(
    ! [C_50,A_46,B_78] :
      ( r2_hidden(C_50,k9_relat_1(k6_relat_1(A_46),B_78))
      | ~ r2_hidden(C_50,B_78)
      | ~ r2_hidden(C_50,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_125])).

tff(c_3979,plain,(
    ! [D_320,A_321,B_322,B_323] :
      ( r2_hidden(D_320,k9_relat_1(A_321,B_322))
      | ~ r2_hidden('#skF_4'(A_321,B_323,k9_relat_1(A_321,B_323),D_320),B_322)
      | ~ r2_hidden('#skF_4'(A_321,B_323,k9_relat_1(A_321,B_323),D_320),k1_relat_1(A_321))
      | ~ v1_funct_1(A_321)
      | ~ v1_relat_1(A_321)
      | ~ r2_hidden(D_320,k9_relat_1(A_321,B_323))
      | ~ v1_funct_1(A_321)
      | ~ v1_relat_1(A_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_2])).

tff(c_3985,plain,(
    ! [D_86,A_46,B_85] :
      ( r2_hidden(D_86,k9_relat_1(k6_relat_1(A_46),A_46))
      | ~ r2_hidden('#skF_4'(k6_relat_1(A_46),B_85,k9_relat_1(k6_relat_1(A_46),B_85),D_86),k1_relat_1(k6_relat_1(A_46)))
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ r2_hidden(D_86,k9_relat_1(k6_relat_1(A_46),B_85)) ) ),
    inference(resolution,[status(thm)],[c_135,c_3979])).

tff(c_12358,plain,(
    ! [D_554,A_555,B_556] :
      ( r2_hidden(D_554,k9_relat_1(k6_relat_1(A_555),A_555))
      | ~ r2_hidden('#skF_4'(k6_relat_1(A_555),B_556,k9_relat_1(k6_relat_1(A_555),B_556),D_554),A_555)
      | ~ r2_hidden(D_554,k9_relat_1(k6_relat_1(A_555),B_556)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_3985])).

tff(c_12387,plain,(
    ! [D_557,A_558,B_559] :
      ( r2_hidden(D_557,k9_relat_1(k6_relat_1(A_558),A_558))
      | ~ r2_hidden(D_557,k9_relat_1(k6_relat_1(A_558),B_559)) ) ),
    inference(resolution,[status(thm)],[c_135,c_12358])).

tff(c_12575,plain,(
    ! [C_560,A_561,B_562] :
      ( r2_hidden(C_560,k9_relat_1(k6_relat_1(A_561),A_561))
      | ~ r2_hidden(C_560,B_562)
      | ~ r2_hidden(C_560,A_561) ) ),
    inference(resolution,[status(thm)],[c_127,c_12387])).

tff(c_12738,plain,(
    ! [A_563,A_564,B_565] :
      ( r2_hidden(A_563,k9_relat_1(k6_relat_1(A_564),A_564))
      | ~ r2_hidden(A_563,A_564)
      | v1_xboole_0(B_565)
      | ~ m1_subset_1(A_563,B_565) ) ),
    inference(resolution,[status(thm)],[c_30,c_12575])).

tff(c_12768,plain,(
    ! [E_135,A_564] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_135),k9_relat_1(k6_relat_1(A_564),A_564))
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_135),A_564)
      | v1_xboole_0('#skF_6')
      | ~ r2_hidden(E_135,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_435,c_12738])).

tff(c_12843,plain,(
    ! [E_566,A_567] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_566),k9_relat_1(k6_relat_1(A_567),A_567))
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_566),A_567)
      | ~ r2_hidden(E_566,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_12768])).

tff(c_14400,plain,(
    ! [C_601,A_602] :
      ( r2_hidden(C_601,k9_relat_1(k6_relat_1(A_602),A_602))
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),C_601),A_602)
      | ~ r2_hidden(C_601,'#skF_7')
      | ~ r2_hidden(C_601,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_12843])).

tff(c_14501,plain,(
    ! [C_603,B_604] :
      ( r2_hidden(C_603,k9_relat_1(k6_relat_1(B_604),B_604))
      | ~ r2_hidden(C_603,'#skF_7')
      | v1_xboole_0(B_604)
      | ~ m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),C_603),B_604) ) ),
    inference(resolution,[status(thm)],[c_30,c_14400])).

tff(c_6,plain,(
    ! [A_1,B_24,D_39] :
      ( r2_hidden('#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39),B_24)
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_975,plain,(
    ! [D_186,B_185,A_184] :
      ( r2_hidden(D_186,B_185)
      | ~ r2_hidden(D_186,k9_relat_1(k6_relat_1(A_184),B_185))
      | ~ v1_funct_1(k6_relat_1(A_184))
      | ~ v1_relat_1(k6_relat_1(A_184))
      | ~ r2_hidden(D_186,k9_relat_1(k6_relat_1(A_184),B_185)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_6])).

tff(c_990,plain,(
    ! [D_186,B_185,A_184] :
      ( r2_hidden(D_186,B_185)
      | ~ r2_hidden(D_186,k9_relat_1(k6_relat_1(A_184),B_185)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_975])).

tff(c_14722,plain,(
    ! [C_609,B_610] :
      ( r2_hidden(C_609,B_610)
      | ~ r2_hidden(C_609,'#skF_7')
      | v1_xboole_0(B_610)
      | ~ m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),C_609),B_610) ) ),
    inference(resolution,[status(thm)],[c_14501,c_990])).

tff(c_14759,plain,(
    ! [E_42] :
      ( r2_hidden(E_42,'#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ r2_hidden(E_42,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1160,c_14722])).

tff(c_14808,plain,(
    ! [E_611] :
      ( r2_hidden(E_611,'#skF_6')
      | ~ r2_hidden(E_611,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_14759])).

tff(c_19047,plain,(
    ! [A_653] :
      ( r2_hidden('#skF_3'(A_653,'#skF_7','#skF_7'),'#skF_6')
      | m1_subset_1('#skF_2'(A_653,'#skF_7','#skF_7'),'#skF_6')
      | k9_relat_1(A_653,'#skF_7') = '#skF_7'
      | ~ v1_funct_1(A_653)
      | ~ v1_relat_1(A_653) ) ),
    inference(resolution,[status(thm)],[c_174,c_14808])).

tff(c_299,plain,(
    ! [A_46,B_122,C_123] :
      ( r2_hidden('#skF_2'(k6_relat_1(A_46),B_122,C_123),B_122)
      | ~ r2_hidden('#skF_3'(k6_relat_1(A_46),B_122,C_123),B_122)
      | k9_relat_1(k6_relat_1(A_46),B_122) = C_123
      | ~ r2_hidden('#skF_3'(k6_relat_1(A_46),B_122,C_123),A_46) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_295])).

tff(c_19088,plain,
    ( r2_hidden('#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | m1_subset_1('#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_6')
    | k9_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7'
    | ~ v1_funct_1(k6_relat_1('#skF_6'))
    | ~ v1_relat_1(k6_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_19047,c_299])).

tff(c_19110,plain,
    ( r2_hidden('#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | m1_subset_1('#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_6')
    | k9_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_19088])).

tff(c_19111,plain,
    ( r2_hidden('#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | m1_subset_1('#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_19110])).

tff(c_21565,plain,(
    ~ r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_19111])).

tff(c_200,plain,(
    ! [A_46,B_105,C_106] :
      ( r2_hidden('#skF_2'(k6_relat_1(A_46),B_105,C_106),A_46)
      | r2_hidden('#skF_3'(k6_relat_1(A_46),B_105,C_106),C_106)
      | k9_relat_1(k6_relat_1(A_46),B_105) = C_106 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_198])).

tff(c_201,plain,(
    ! [A_107,B_108,C_109] :
      ( k1_funct_1(A_107,'#skF_2'(A_107,B_108,C_109)) = '#skF_1'(A_107,B_108,C_109)
      | r2_hidden('#skF_3'(A_107,B_108,C_109),C_109)
      | k9_relat_1(A_107,B_108) = C_109
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_222,plain,(
    ! [A_46,B_108,C_109] :
      ( '#skF_1'(k6_relat_1(A_46),B_108,C_109) = '#skF_2'(k6_relat_1(A_46),B_108,C_109)
      | r2_hidden('#skF_3'(k6_relat_1(A_46),B_108,C_109),C_109)
      | k9_relat_1(k6_relat_1(A_46),B_108) = C_109
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ r2_hidden('#skF_2'(k6_relat_1(A_46),B_108,C_109),A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_201])).

tff(c_1685,plain,(
    ! [A_226,B_227,C_228] :
      ( '#skF_1'(k6_relat_1(A_226),B_227,C_228) = '#skF_2'(k6_relat_1(A_226),B_227,C_228)
      | r2_hidden('#skF_3'(k6_relat_1(A_226),B_227,C_228),C_228)
      | k9_relat_1(k6_relat_1(A_226),B_227) = C_228
      | ~ r2_hidden('#skF_2'(k6_relat_1(A_226),B_227,C_228),A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_222])).

tff(c_1704,plain,(
    ! [A_46,B_105,C_106] :
      ( '#skF_1'(k6_relat_1(A_46),B_105,C_106) = '#skF_2'(k6_relat_1(A_46),B_105,C_106)
      | r2_hidden('#skF_3'(k6_relat_1(A_46),B_105,C_106),C_106)
      | k9_relat_1(k6_relat_1(A_46),B_105) = C_106 ) ),
    inference(resolution,[status(thm)],[c_200,c_1685])).

tff(c_21568,plain,
    ( '#skF_1'(k6_relat_1('#skF_6'),'#skF_7','#skF_7') = '#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7')
    | k9_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1704,c_21565])).

tff(c_21585,plain,(
    '#skF_1'(k6_relat_1('#skF_6'),'#skF_7','#skF_7') = '#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_21568])).

tff(c_18,plain,(
    ! [A_1,B_24,C_25] :
      ( ~ r2_hidden('#skF_1'(A_1,B_24,C_25),C_25)
      | r2_hidden('#skF_3'(A_1,B_24,C_25),C_25)
      | k9_relat_1(A_1,B_24) = C_25
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_21635,plain,
    ( ~ r2_hidden('#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | k9_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7'
    | ~ v1_funct_1(k6_relat_1('#skF_6'))
    | ~ v1_relat_1(k6_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21585,c_18])).

tff(c_21654,plain,
    ( ~ r2_hidden('#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | k9_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_21635])).

tff(c_21655,plain,(
    ~ r2_hidden('#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_21565,c_21654])).

tff(c_21659,plain,
    ( r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | k9_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7'
    | ~ v1_funct_1(k6_relat_1('#skF_6'))
    | ~ v1_relat_1(k6_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_22,c_21655])).

tff(c_21665,plain,
    ( r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | k9_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_21659])).

tff(c_21667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_21565,c_21665])).

tff(c_21669,plain,(
    r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_19111])).

tff(c_14798,plain,(
    ! [E_42] :
      ( r2_hidden(E_42,'#skF_6')
      | ~ r2_hidden(E_42,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_14759])).

tff(c_21719,plain,(
    r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_21669,c_14798])).

tff(c_21973,plain,
    ( r2_hidden('#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | k9_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_21719,c_299])).

tff(c_22004,plain,
    ( r2_hidden('#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | k9_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21669,c_21973])).

tff(c_22005,plain,(
    r2_hidden('#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_22004])).

tff(c_785,plain,(
    ! [A_168,B_169,C_170,E_171] :
      ( k1_funct_1(A_168,'#skF_2'(A_168,B_169,C_170)) = '#skF_1'(A_168,B_169,C_170)
      | k1_funct_1(A_168,E_171) != '#skF_3'(A_168,B_169,C_170)
      | ~ r2_hidden(E_171,B_169)
      | ~ r2_hidden(E_171,k1_relat_1(A_168))
      | k9_relat_1(A_168,B_169) = C_170
      | ~ v1_funct_1(A_168)
      | ~ v1_relat_1(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_795,plain,(
    ! [A_46,B_169,C_170,C_50] :
      ( k1_funct_1(k6_relat_1(A_46),'#skF_2'(k6_relat_1(A_46),B_169,C_170)) = '#skF_1'(k6_relat_1(A_46),B_169,C_170)
      | C_50 != '#skF_3'(k6_relat_1(A_46),B_169,C_170)
      | ~ r2_hidden(C_50,B_169)
      | ~ r2_hidden(C_50,k1_relat_1(k6_relat_1(A_46)))
      | k9_relat_1(k6_relat_1(A_46),B_169) = C_170
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ r2_hidden(C_50,A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_785])).

tff(c_799,plain,(
    ! [A_46,B_169,C_170,C_50] :
      ( k1_funct_1(k6_relat_1(A_46),'#skF_2'(k6_relat_1(A_46),B_169,C_170)) = '#skF_1'(k6_relat_1(A_46),B_169,C_170)
      | C_50 != '#skF_3'(k6_relat_1(A_46),B_169,C_170)
      | ~ r2_hidden(C_50,B_169)
      | k9_relat_1(k6_relat_1(A_46),B_169) = C_170
      | ~ r2_hidden(C_50,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_795])).

tff(c_2723,plain,(
    ! [A_46,B_169,C_170] :
      ( k1_funct_1(k6_relat_1(A_46),'#skF_2'(k6_relat_1(A_46),B_169,C_170)) = '#skF_1'(k6_relat_1(A_46),B_169,C_170)
      | ~ r2_hidden('#skF_3'(k6_relat_1(A_46),B_169,C_170),B_169)
      | k9_relat_1(k6_relat_1(A_46),B_169) = C_170
      | ~ r2_hidden('#skF_3'(k6_relat_1(A_46),B_169,C_170),A_46) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_799])).

tff(c_21671,plain,
    ( k1_funct_1(k6_relat_1('#skF_6'),'#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7')) = '#skF_1'(k6_relat_1('#skF_6'),'#skF_7','#skF_7')
    | k9_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7'
    | ~ r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_21669,c_2723])).

tff(c_21718,plain,
    ( k1_funct_1(k6_relat_1('#skF_6'),'#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7')) = '#skF_1'(k6_relat_1('#skF_6'),'#skF_7','#skF_7')
    | ~ r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_21671])).

tff(c_23001,plain,(
    k1_funct_1(k6_relat_1('#skF_6'),'#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7')) = '#skF_1'(k6_relat_1('#skF_6'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21719,c_21718])).

tff(c_411,plain,(
    ! [E_42] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_42),'#skF_7')
      | ~ r2_hidden(E_42,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_396])).

tff(c_15003,plain,(
    ! [E_612] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_612),'#skF_6')
      | ~ r2_hidden(E_612,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_411,c_14808])).

tff(c_12976,plain,(
    ! [C_50,A_567] :
      ( r2_hidden(C_50,k9_relat_1(k6_relat_1(A_567),A_567))
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),C_50),A_567)
      | ~ r2_hidden(C_50,'#skF_7')
      | ~ r2_hidden(C_50,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_12843])).

tff(c_15129,plain,(
    ! [E_613] :
      ( r2_hidden(E_613,k9_relat_1(k6_relat_1('#skF_6'),'#skF_6'))
      | ~ r2_hidden(E_613,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_15003,c_12976])).

tff(c_12514,plain,(
    ! [A_558,E_42,B_24] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_558),E_42),k9_relat_1(k6_relat_1(A_558),A_558))
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,k1_relat_1(k6_relat_1(A_558)))
      | ~ v1_funct_1(k6_relat_1(A_558))
      | ~ v1_relat_1(k6_relat_1(A_558)) ) ),
    inference(resolution,[status(thm)],[c_2,c_12387])).

tff(c_12572,plain,(
    ! [A_558,E_42,B_24] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_558),E_42),k9_relat_1(k6_relat_1(A_558),A_558))
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,A_558) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_12514])).

tff(c_16787,plain,(
    ! [A_628,E_629] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_628),E_629),k9_relat_1(k6_relat_1(A_628),A_628))
      | ~ r2_hidden(E_629,A_628)
      | ~ r2_hidden(E_629,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_15129,c_12572])).

tff(c_8,plain,(
    ! [A_1,B_24,D_39] :
      ( r2_hidden('#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39),k1_relat_1(A_1))
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_968,plain,(
    ! [D_186,A_184,B_185] :
      ( r2_hidden(D_186,k1_relat_1(k6_relat_1(A_184)))
      | ~ r2_hidden(D_186,k9_relat_1(k6_relat_1(A_184),B_185))
      | ~ v1_funct_1(k6_relat_1(A_184))
      | ~ v1_relat_1(k6_relat_1(A_184))
      | ~ r2_hidden(D_186,k9_relat_1(k6_relat_1(A_184),B_185)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_8])).

tff(c_993,plain,(
    ! [D_187,A_188,B_189] :
      ( r2_hidden(D_187,A_188)
      | ~ r2_hidden(D_187,k9_relat_1(k6_relat_1(A_188),B_189)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_968])).

tff(c_1051,plain,(
    ! [A_188,E_42,B_24] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_188),E_42),A_188)
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,k1_relat_1(k6_relat_1(A_188)))
      | ~ v1_funct_1(k6_relat_1(A_188))
      | ~ v1_relat_1(k6_relat_1(A_188)) ) ),
    inference(resolution,[status(thm)],[c_2,c_993])).

tff(c_1363,plain,(
    ! [A_202,E_203,B_204] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_202),E_203),A_202)
      | ~ r2_hidden(E_203,B_204)
      | ~ r2_hidden(E_203,A_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_1051])).

tff(c_1554,plain,(
    ! [A_219,A_220,B_221] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_219),A_220),A_219)
      | ~ r2_hidden(A_220,A_219)
      | v1_xboole_0(B_221)
      | ~ m1_subset_1(A_220,B_221) ) ),
    inference(resolution,[status(thm)],[c_30,c_1363])).

tff(c_1564,plain,(
    ! [A_219,E_135] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_219),k1_funct_1(k6_relat_1('#skF_7'),E_135)),A_219)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_135),A_219)
      | v1_xboole_0('#skF_6')
      | ~ r2_hidden(E_135,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_435,c_1554])).

tff(c_1932,plain,(
    ! [A_240,E_241] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_240),k1_funct_1(k6_relat_1('#skF_7'),E_241)),A_240)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_241),A_240)
      | ~ r2_hidden(E_241,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1564])).

tff(c_2168,plain,(
    ! [A_251,C_252] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_251),C_252),A_251)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),C_252),A_251)
      | ~ r2_hidden(C_252,'#skF_7')
      | ~ r2_hidden(C_252,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1932])).

tff(c_2193,plain,(
    ! [B_24,E_42] :
      ( r2_hidden(k1_funct_1(k6_relat_1(k9_relat_1(k6_relat_1('#skF_7'),B_24)),E_42),k9_relat_1(k6_relat_1('#skF_7'),B_24))
      | ~ r2_hidden(E_42,'#skF_7')
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,k1_relat_1(k6_relat_1('#skF_7')))
      | ~ v1_funct_1(k6_relat_1('#skF_7'))
      | ~ v1_relat_1(k6_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2,c_2168])).

tff(c_2301,plain,(
    ! [B_255,E_256] :
      ( r2_hidden(k1_funct_1(k6_relat_1(k9_relat_1(k6_relat_1('#skF_7'),B_255)),E_256),k9_relat_1(k6_relat_1('#skF_7'),B_255))
      | ~ r2_hidden(E_256,B_255)
      | ~ r2_hidden(E_256,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_2193])).

tff(c_1168,plain,(
    ! [D_194,B_195,A_196] :
      ( r2_hidden(D_194,B_195)
      | ~ r2_hidden(D_194,k9_relat_1(k6_relat_1(A_196),B_195)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_975])).

tff(c_1226,plain,(
    ! [A_196,E_42,B_24] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_196),E_42),B_24)
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,k1_relat_1(k6_relat_1(A_196)))
      | ~ v1_funct_1(k6_relat_1(A_196))
      | ~ v1_relat_1(k6_relat_1(A_196)) ) ),
    inference(resolution,[status(thm)],[c_2,c_1168])).

tff(c_1430,plain,(
    ! [A_205,E_206,B_207] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_205),E_206),B_207)
      | ~ r2_hidden(E_206,B_207)
      | ~ r2_hidden(E_206,A_205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_1226])).

tff(c_988,plain,(
    ! [D_186,A_184] :
      ( m1_subset_1(D_186,'#skF_6')
      | ~ r2_hidden(D_186,k9_relat_1(k6_relat_1(A_184),'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_972])).

tff(c_1478,plain,(
    ! [A_205,E_206,A_184] :
      ( m1_subset_1(k1_funct_1(k6_relat_1(A_205),E_206),'#skF_6')
      | ~ r2_hidden(E_206,k9_relat_1(k6_relat_1(A_184),'#skF_7'))
      | ~ r2_hidden(E_206,A_205) ) ),
    inference(resolution,[status(thm)],[c_1430,c_988])).

tff(c_2310,plain,(
    ! [A_205,E_256] :
      ( m1_subset_1(k1_funct_1(k6_relat_1(A_205),k1_funct_1(k6_relat_1(k9_relat_1(k6_relat_1('#skF_7'),'#skF_7')),E_256)),'#skF_6')
      | ~ r2_hidden(k1_funct_1(k6_relat_1(k9_relat_1(k6_relat_1('#skF_7'),'#skF_7')),E_256),A_205)
      | ~ r2_hidden(E_256,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2301,c_1478])).

tff(c_2359,plain,(
    ! [A_205,E_256] :
      ( m1_subset_1(k1_funct_1(k6_relat_1(A_205),k1_funct_1(k6_relat_1('#skF_7'),E_256)),'#skF_6')
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_256),A_205)
      | ~ r2_hidden(E_256,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_374,c_2310])).

tff(c_1710,plain,(
    ! [A_229,E_230,B_231,A_232] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_229),E_230),B_231)
      | ~ r2_hidden(E_230,k9_relat_1(k6_relat_1(A_232),B_231))
      | ~ r2_hidden(E_230,A_229) ) ),
    inference(resolution,[status(thm)],[c_1430,c_990])).

tff(c_1759,plain,(
    ! [A_229,A_232,E_42,B_24] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_229),k1_funct_1(k6_relat_1(A_232),E_42)),B_24)
      | ~ r2_hidden(k1_funct_1(k6_relat_1(A_232),E_42),A_229)
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,k1_relat_1(k6_relat_1(A_232)))
      | ~ v1_funct_1(k6_relat_1(A_232))
      | ~ v1_relat_1(k6_relat_1(A_232)) ) ),
    inference(resolution,[status(thm)],[c_2,c_1710])).

tff(c_4837,plain,(
    ! [A_355,A_356,E_357,B_358] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_355),k1_funct_1(k6_relat_1(A_356),E_357)),B_358)
      | ~ r2_hidden(k1_funct_1(k6_relat_1(A_356),E_357),A_355)
      | ~ r2_hidden(E_357,B_358)
      | ~ r2_hidden(E_357,A_356) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_1759])).

tff(c_5615,plain,(
    ! [A_374,C_375,B_376,A_377] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_374),C_375),B_376)
      | ~ r2_hidden(k1_funct_1(k6_relat_1(A_377),C_375),A_374)
      | ~ r2_hidden(C_375,B_376)
      | ~ r2_hidden(C_375,A_377)
      | ~ r2_hidden(C_375,A_377) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4837])).

tff(c_5822,plain,(
    ! [B_387,C_388,B_389,A_390] :
      ( r2_hidden(k1_funct_1(k6_relat_1(B_387),C_388),B_389)
      | ~ r2_hidden(C_388,B_389)
      | ~ r2_hidden(C_388,A_390)
      | v1_xboole_0(B_387)
      | ~ m1_subset_1(k1_funct_1(k6_relat_1(A_390),C_388),B_387) ) ),
    inference(resolution,[status(thm)],[c_30,c_5615])).

tff(c_5840,plain,(
    ! [E_256,B_389,A_205] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_6'),k1_funct_1(k6_relat_1('#skF_7'),E_256)),B_389)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_256),B_389)
      | v1_xboole_0('#skF_6')
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_256),A_205)
      | ~ r2_hidden(E_256,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2359,c_5822])).

tff(c_8262,plain,(
    ! [E_465,B_466,A_467] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_6'),k1_funct_1(k6_relat_1('#skF_7'),E_465)),B_466)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_465),B_466)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_465),A_467)
      | ~ r2_hidden(E_465,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_5840])).

tff(c_8351,plain,(
    ! [E_468,B_469] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_6'),k1_funct_1(k6_relat_1('#skF_7'),E_468)),B_469)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_468),B_469)
      | ~ r2_hidden(E_468,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_411,c_8262])).

tff(c_8474,plain,(
    ! [C_50,B_469] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_6'),C_50),B_469)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),C_50),B_469)
      | ~ r2_hidden(C_50,'#skF_7')
      | ~ r2_hidden(C_50,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_8351])).

tff(c_16830,plain,(
    ! [E_629] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_6'),E_629),k9_relat_1(k6_relat_1('#skF_7'),'#skF_7'))
      | ~ r2_hidden(E_629,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16787,c_8474])).

tff(c_16975,plain,(
    ! [E_629] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_6'),E_629),'#skF_7')
      | ~ r2_hidden(E_629,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_16830])).

tff(c_23026,plain,
    ( r2_hidden('#skF_1'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_2'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_23001,c_16975])).

tff(c_23186,plain,(
    r2_hidden('#skF_1'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22005,c_23026])).

tff(c_10,plain,(
    ! [A_1,B_24,C_25,E_38] :
      ( ~ r2_hidden('#skF_1'(A_1,B_24,C_25),C_25)
      | k1_funct_1(A_1,E_38) != '#skF_3'(A_1,B_24,C_25)
      | ~ r2_hidden(E_38,B_24)
      | ~ r2_hidden(E_38,k1_relat_1(A_1))
      | k9_relat_1(A_1,B_24) = C_25
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_23508,plain,(
    ! [E_38] :
      ( k1_funct_1(k6_relat_1('#skF_6'),E_38) != '#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7')
      | ~ r2_hidden(E_38,'#skF_7')
      | ~ r2_hidden(E_38,k1_relat_1(k6_relat_1('#skF_6')))
      | k9_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7'
      | ~ v1_funct_1(k6_relat_1('#skF_6'))
      | ~ v1_relat_1(k6_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_23186,c_10])).

tff(c_23547,plain,(
    ! [E_38] :
      ( k1_funct_1(k6_relat_1('#skF_6'),E_38) != '#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7')
      | ~ r2_hidden(E_38,'#skF_7')
      | ~ r2_hidden(E_38,'#skF_6')
      | k9_relat_1(k6_relat_1('#skF_6'),'#skF_7') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_23508])).

tff(c_23676,plain,(
    ! [E_685] :
      ( k1_funct_1(k6_relat_1('#skF_6'),E_685) != '#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7')
      | ~ r2_hidden(E_685,'#skF_7')
      | ~ r2_hidden(E_685,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_23547])).

tff(c_23723,plain,(
    ! [C_50] :
      ( C_50 != '#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7')
      | ~ r2_hidden(C_50,'#skF_7')
      | ~ r2_hidden(C_50,'#skF_6')
      | ~ r2_hidden(C_50,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_23676])).

tff(c_24399,plain,
    ( ~ r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_7')
    | ~ r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_3'(k6_relat_1('#skF_6'),'#skF_7','#skF_7'),'#skF_6') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_23723])).

tff(c_24402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21719,c_21719,c_21669,c_24399])).

tff(c_24404,plain,(
    k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_332,plain,(
    ! [C_25,B_24] :
      ( ~ r2_hidden('#skF_3'(k6_relat_1(C_25),B_24,C_25),B_24)
      | r2_hidden('#skF_2'(k6_relat_1(C_25),B_24,C_25),B_24)
      | k9_relat_1(k6_relat_1(C_25),B_24) = C_25 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_316])).

tff(c_24403,plain,(
    m1_subset_1('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_160,plain,(
    ! [A_46,B_93,D_94] :
      ( '#skF_4'(k6_relat_1(A_46),B_93,k9_relat_1(k6_relat_1(A_46),B_93),D_94) = D_94
      | ~ r2_hidden(D_94,k9_relat_1(k6_relat_1(A_46),B_93))
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ r2_hidden('#skF_4'(k6_relat_1(A_46),B_93,k9_relat_1(k6_relat_1(A_46),B_93),D_94),A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_143])).

tff(c_24416,plain,(
    ! [A_699,B_700,D_701] :
      ( '#skF_4'(k6_relat_1(A_699),B_700,k9_relat_1(k6_relat_1(A_699),B_700),D_701) = D_701
      | ~ r2_hidden(D_701,k9_relat_1(k6_relat_1(A_699),B_700))
      | ~ r2_hidden('#skF_4'(k6_relat_1(A_699),B_700,k9_relat_1(k6_relat_1(A_699),B_700),D_701),A_699) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_160])).

tff(c_24438,plain,(
    ! [A_702,B_703,D_704] :
      ( '#skF_4'(k6_relat_1(A_702),B_703,k9_relat_1(k6_relat_1(A_702),B_703),D_704) = D_704
      | ~ r2_hidden(D_704,k9_relat_1(k6_relat_1(A_702),B_703)) ) ),
    inference(resolution,[status(thm)],[c_135,c_24416])).

tff(c_24454,plain,(
    ! [D_704,A_702,B_703] :
      ( r2_hidden(D_704,k1_relat_1(k6_relat_1(A_702)))
      | ~ r2_hidden(D_704,k9_relat_1(k6_relat_1(A_702),B_703))
      | ~ v1_funct_1(k6_relat_1(A_702))
      | ~ v1_relat_1(k6_relat_1(A_702))
      | ~ r2_hidden(D_704,k9_relat_1(k6_relat_1(A_702),B_703)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24438,c_8])).

tff(c_24475,plain,(
    ! [D_705,A_706,B_707] :
      ( r2_hidden(D_705,A_706)
      | ~ r2_hidden(D_705,k9_relat_1(k6_relat_1(A_706),B_707)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_24454])).

tff(c_24526,plain,(
    ! [A_706,E_42,B_24] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_706),E_42),A_706)
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,k1_relat_1(k6_relat_1(A_706)))
      | ~ v1_funct_1(k6_relat_1(A_706))
      | ~ v1_relat_1(k6_relat_1(A_706)) ) ),
    inference(resolution,[status(thm)],[c_2,c_24475])).

tff(c_24847,plain,(
    ! [A_718,E_719,B_720] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_718),E_719),A_718)
      | ~ r2_hidden(E_719,B_720)
      | ~ r2_hidden(E_719,A_718) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_24526])).

tff(c_24993,plain,(
    ! [A_740,A_741,B_742] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_740),A_741),A_740)
      | ~ r2_hidden(A_741,A_740)
      | v1_xboole_0(B_742)
      | ~ m1_subset_1(A_741,B_742) ) ),
    inference(resolution,[status(thm)],[c_30,c_24847])).

tff(c_24999,plain,(
    ! [A_740] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_740),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),A_740)
      | ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),A_740)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24403,c_24993])).

tff(c_25248,plain,(
    ! [A_758] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_758),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),A_758)
      | ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),A_758) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_24999])).

tff(c_25304,plain,
    ( m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),'#skF_6')
    | ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_25248,c_84])).

tff(c_25434,plain,(
    ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_25304])).

tff(c_25442,plain,
    ( ~ r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7')
    | k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_332,c_25434])).

tff(c_25454,plain,(
    ~ r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_24404,c_25442])).

tff(c_25445,plain,
    ( r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7')
    | k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_200,c_25434])).

tff(c_25457,plain,(
    r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_24404,c_25445])).

tff(c_25493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25454,c_25457])).

tff(c_25495,plain,(
    r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_25304])).

tff(c_20,plain,(
    ! [A_1,B_24,C_25] :
      ( k1_funct_1(A_1,'#skF_2'(A_1,B_24,C_25)) = '#skF_1'(A_1,B_24,C_25)
      | r2_hidden('#skF_3'(A_1,B_24,C_25),C_25)
      | k9_relat_1(A_1,B_24) = C_25
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25494,plain,(
    m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_25304])).

tff(c_25517,plain,
    ( m1_subset_1('#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_6')
    | r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7')
    | k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') = '#skF_7'
    | ~ v1_funct_1(k6_relat_1('#skF_7'))
    | ~ v1_relat_1(k6_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_25494])).

tff(c_25528,plain,
    ( m1_subset_1('#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_6')
    | r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7')
    | k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_25517])).

tff(c_25529,plain,
    ( m1_subset_1('#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_6')
    | r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_24404,c_25528])).

tff(c_25538,plain,(
    r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_25529])).

tff(c_28112,plain,(
    ! [D_903,A_904,B_905,B_906] :
      ( r2_hidden(D_903,k9_relat_1(A_904,B_905))
      | ~ r2_hidden('#skF_4'(A_904,B_906,k9_relat_1(A_904,B_906),D_903),B_905)
      | ~ r2_hidden('#skF_4'(A_904,B_906,k9_relat_1(A_904,B_906),D_903),k1_relat_1(A_904))
      | ~ v1_funct_1(A_904)
      | ~ v1_relat_1(A_904)
      | ~ r2_hidden(D_903,k9_relat_1(A_904,B_906))
      | ~ v1_funct_1(A_904)
      | ~ v1_relat_1(A_904) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_2])).

tff(c_28116,plain,(
    ! [D_86,A_46,B_85] :
      ( r2_hidden(D_86,k9_relat_1(k6_relat_1(A_46),A_46))
      | ~ r2_hidden('#skF_4'(k6_relat_1(A_46),B_85,k9_relat_1(k6_relat_1(A_46),B_85),D_86),k1_relat_1(k6_relat_1(A_46)))
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ r2_hidden(D_86,k9_relat_1(k6_relat_1(A_46),B_85)) ) ),
    inference(resolution,[status(thm)],[c_135,c_28112])).

tff(c_33207,plain,(
    ! [D_1025,A_1026,B_1027] :
      ( r2_hidden(D_1025,k9_relat_1(k6_relat_1(A_1026),A_1026))
      | ~ r2_hidden('#skF_4'(k6_relat_1(A_1026),B_1027,k9_relat_1(k6_relat_1(A_1026),B_1027),D_1025),A_1026)
      | ~ r2_hidden(D_1025,k9_relat_1(k6_relat_1(A_1026),B_1027)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_28116])).

tff(c_33232,plain,(
    ! [D_1028,A_1029,B_1030] :
      ( r2_hidden(D_1028,k9_relat_1(k6_relat_1(A_1029),A_1029))
      | ~ r2_hidden(D_1028,k9_relat_1(k6_relat_1(A_1029),B_1030)) ) ),
    inference(resolution,[status(thm)],[c_135,c_33207])).

tff(c_33334,plain,(
    ! [A_1029,E_42,B_24] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_1029),E_42),k9_relat_1(k6_relat_1(A_1029),A_1029))
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,k1_relat_1(k6_relat_1(A_1029)))
      | ~ v1_funct_1(k6_relat_1(A_1029))
      | ~ v1_relat_1(k6_relat_1(A_1029)) ) ),
    inference(resolution,[status(thm)],[c_2,c_33232])).

tff(c_33653,plain,(
    ! [A_1042,E_1043,B_1044] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_1042),E_1043),k9_relat_1(k6_relat_1(A_1042),A_1042))
      | ~ r2_hidden(E_1043,B_1044)
      | ~ r2_hidden(E_1043,A_1042) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_33334])).

tff(c_34089,plain,(
    ! [A_1053,A_1054,B_1055] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_1053),A_1054),k9_relat_1(k6_relat_1(A_1053),A_1053))
      | ~ r2_hidden(A_1054,A_1053)
      | v1_xboole_0(B_1055)
      | ~ m1_subset_1(A_1054,B_1055) ) ),
    inference(resolution,[status(thm)],[c_30,c_33653])).

tff(c_34127,plain,(
    ! [A_1053] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_1053),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),k9_relat_1(k6_relat_1(A_1053),A_1053))
      | ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),A_1053)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24403,c_34089])).

tff(c_34688,plain,(
    ! [A_1067] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_1067),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),k9_relat_1(k6_relat_1(A_1067),A_1067))
      | ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),A_1067) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_34127])).

tff(c_25020,plain,(
    ! [A_740] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_740),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),A_740)
      | ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),A_740) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_24999])).

tff(c_136,plain,(
    ! [A_87,B_88,D_89] :
      ( r2_hidden('#skF_4'(k6_relat_1(A_87),B_88,k9_relat_1(k6_relat_1(A_87),B_88),D_89),A_87)
      | ~ r2_hidden(D_89,k9_relat_1(k6_relat_1(A_87),B_88)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_133])).

tff(c_141,plain,(
    ! [B_88,D_89] :
      ( m1_subset_1('#skF_4'(k6_relat_1('#skF_7'),B_88,k9_relat_1(k6_relat_1('#skF_7'),B_88),D_89),'#skF_6')
      | ~ r2_hidden(D_89,k9_relat_1(k6_relat_1('#skF_7'),B_88)) ) ),
    inference(resolution,[status(thm)],[c_136,c_84])).

tff(c_24552,plain,(
    ! [D_708,B_709] :
      ( m1_subset_1(D_708,'#skF_6')
      | ~ r2_hidden(D_708,k9_relat_1(k6_relat_1('#skF_7'),B_709))
      | ~ r2_hidden(D_708,k9_relat_1(k6_relat_1('#skF_7'),B_709)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24438,c_141])).

tff(c_24591,plain,(
    ! [E_42,B_24] :
      ( m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),E_42),'#skF_6')
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_42),k9_relat_1(k6_relat_1('#skF_7'),B_24))
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,k1_relat_1(k6_relat_1('#skF_7')))
      | ~ v1_funct_1(k6_relat_1('#skF_7'))
      | ~ v1_relat_1(k6_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2,c_24552])).

tff(c_26133,plain,(
    ! [E_813,B_814] :
      ( m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),E_813),'#skF_6')
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),E_813),k9_relat_1(k6_relat_1('#skF_7'),B_814))
      | ~ r2_hidden(E_813,B_814)
      | ~ r2_hidden(E_813,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_24591])).

tff(c_26157,plain,(
    ! [E_42,B_24] :
      ( m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),E_42),'#skF_6')
      | ~ r2_hidden(E_42,'#skF_7')
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,k1_relat_1(k6_relat_1('#skF_7')))
      | ~ v1_funct_1(k6_relat_1('#skF_7'))
      | ~ v1_relat_1(k6_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2,c_26133])).

tff(c_26177,plain,(
    ! [E_815,B_816] :
      ( m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),E_815),'#skF_6')
      | ~ r2_hidden(E_815,B_816)
      | ~ r2_hidden(E_815,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_26157])).

tff(c_26254,plain,(
    ! [A_817,B_818] :
      ( m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),A_817),'#skF_6')
      | ~ r2_hidden(A_817,'#skF_7')
      | v1_xboole_0(B_818)
      | ~ m1_subset_1(A_817,B_818) ) ),
    inference(resolution,[status(thm)],[c_30,c_26177])).

tff(c_26262,plain,
    ( m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'))),'#skF_6')
    | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),'#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_25494,c_26254])).

tff(c_26293,plain,
    ( m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'))),'#skF_6')
    | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_26262])).

tff(c_30635,plain,(
    ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_26293])).

tff(c_30641,plain,(
    ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_25020,c_30635])).

tff(c_30662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25495,c_30641])).

tff(c_30664,plain,(
    r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_26293])).

tff(c_30663,plain,(
    m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'))),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_26293])).

tff(c_24461,plain,(
    ! [D_704,B_703,A_702] :
      ( r2_hidden(D_704,B_703)
      | ~ r2_hidden(D_704,k9_relat_1(k6_relat_1(A_702),B_703))
      | ~ v1_funct_1(k6_relat_1(A_702))
      | ~ v1_relat_1(k6_relat_1(A_702))
      | ~ r2_hidden(D_704,k9_relat_1(k6_relat_1(A_702),B_703)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24438,c_6])).

tff(c_24693,plain,(
    ! [D_712,B_713,A_714] :
      ( r2_hidden(D_712,B_713)
      | ~ r2_hidden(D_712,k9_relat_1(k6_relat_1(A_714),B_713)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_24461])).

tff(c_24744,plain,(
    ! [A_714,E_42,B_24] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_714),E_42),B_24)
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,k1_relat_1(k6_relat_1(A_714)))
      | ~ v1_funct_1(k6_relat_1(A_714))
      | ~ v1_relat_1(k6_relat_1(A_714)) ) ),
    inference(resolution,[status(thm)],[c_2,c_24693])).

tff(c_24935,plain,(
    ! [A_727,E_728,B_729] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_727),E_728),B_729)
      | ~ r2_hidden(E_728,B_729)
      | ~ r2_hidden(E_728,A_727) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_24744])).

tff(c_24473,plain,(
    ! [D_704,B_703,A_702] :
      ( r2_hidden(D_704,B_703)
      | ~ r2_hidden(D_704,k9_relat_1(k6_relat_1(A_702),B_703)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_24461])).

tff(c_25182,plain,(
    ! [A_754,E_755,B_756,A_757] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_754),E_755),B_756)
      | ~ r2_hidden(E_755,k9_relat_1(k6_relat_1(A_757),B_756))
      | ~ r2_hidden(E_755,A_754) ) ),
    inference(resolution,[status(thm)],[c_24935,c_24473])).

tff(c_25223,plain,(
    ! [A_754,A_757,E_42,B_24] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_754),k1_funct_1(k6_relat_1(A_757),E_42)),B_24)
      | ~ r2_hidden(k1_funct_1(k6_relat_1(A_757),E_42),A_754)
      | ~ r2_hidden(E_42,B_24)
      | ~ r2_hidden(E_42,k1_relat_1(k6_relat_1(A_757)))
      | ~ v1_funct_1(k6_relat_1(A_757))
      | ~ v1_relat_1(k6_relat_1(A_757)) ) ),
    inference(resolution,[status(thm)],[c_2,c_25182])).

tff(c_26675,plain,(
    ! [A_839,A_840,E_841,B_842] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_839),k1_funct_1(k6_relat_1(A_840),E_841)),B_842)
      | ~ r2_hidden(k1_funct_1(k6_relat_1(A_840),E_841),A_839)
      | ~ r2_hidden(E_841,B_842)
      | ~ r2_hidden(E_841,A_840) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_25223])).

tff(c_27373,plain,(
    ! [A_867,C_868,B_869,A_870] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_867),C_868),B_869)
      | ~ r2_hidden(k1_funct_1(k6_relat_1(A_870),C_868),A_867)
      | ~ r2_hidden(C_868,B_869)
      | ~ r2_hidden(C_868,A_870)
      | ~ r2_hidden(C_868,A_870) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_26675])).

tff(c_27416,plain,(
    ! [B_45,C_868,B_869,A_870] :
      ( r2_hidden(k1_funct_1(k6_relat_1(B_45),C_868),B_869)
      | ~ r2_hidden(C_868,B_869)
      | ~ r2_hidden(C_868,A_870)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(k1_funct_1(k6_relat_1(A_870),C_868),B_45) ) ),
    inference(resolution,[status(thm)],[c_30,c_27373])).

tff(c_30786,plain,(
    ! [B_869] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_6'),k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'))),B_869)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),B_869)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),'#skF_7')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30663,c_27416])).

tff(c_30824,plain,(
    ! [B_869] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_6'),k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'))),B_869)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),B_869)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30664,c_30786])).

tff(c_31944,plain,(
    ! [B_1009] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_6'),k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'))),B_1009)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),B_1009) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_30824])).

tff(c_32040,plain,(
    ! [B_1009] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_6'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),B_1009)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),B_1009)
      | ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_31944])).

tff(c_32093,plain,(
    ! [B_1009] :
      ( r2_hidden(k1_funct_1(k6_relat_1('#skF_6'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),B_1009)
      | ~ r2_hidden(k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),B_1009) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25495,c_32040])).

tff(c_34704,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1('#skF_6'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),k9_relat_1(k6_relat_1('#skF_7'),'#skF_7'))
    | ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_34688,c_32093])).

tff(c_34805,plain,(
    r2_hidden(k1_funct_1(k6_relat_1('#skF_6'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),k9_relat_1(k6_relat_1('#skF_7'),'#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25495,c_34704])).

tff(c_34945,plain,
    ( r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),k9_relat_1(k6_relat_1('#skF_7'),'#skF_7'))
    | ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_34805])).

tff(c_35678,plain,(
    ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34945])).

tff(c_35681,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_35678])).

tff(c_35684,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24403,c_35681])).

tff(c_35686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_35684])).

tff(c_35687,plain,(
    r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),k9_relat_1(k6_relat_1('#skF_7'),'#skF_7')) ),
    inference(splitRight,[status(thm)],[c_34945])).

tff(c_4,plain,(
    ! [A_1,B_24,D_39] :
      ( k1_funct_1(A_1,'#skF_4'(A_1,B_24,k9_relat_1(A_1,B_24),D_39)) = D_39
      | ~ r2_hidden(D_39,k9_relat_1(A_1,B_24))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24444,plain,(
    ! [A_702,D_704,B_703] :
      ( k1_funct_1(k6_relat_1(A_702),D_704) = D_704
      | ~ r2_hidden(D_704,k9_relat_1(k6_relat_1(A_702),B_703))
      | ~ v1_funct_1(k6_relat_1(A_702))
      | ~ v1_relat_1(k6_relat_1(A_702))
      | ~ r2_hidden(D_704,k9_relat_1(k6_relat_1(A_702),B_703)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24438,c_4])).

tff(c_24467,plain,(
    ! [A_702,D_704,B_703] :
      ( k1_funct_1(k6_relat_1(A_702),D_704) = D_704
      | ~ r2_hidden(D_704,k9_relat_1(k6_relat_1(A_702),B_703)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_24444])).

tff(c_36058,plain,(
    k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')) = '#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_35687,c_24467])).

tff(c_25038,plain,(
    ! [A_743,B_744,C_745,E_746] :
      ( k1_funct_1(A_743,'#skF_2'(A_743,B_744,C_745)) = '#skF_1'(A_743,B_744,C_745)
      | k1_funct_1(A_743,E_746) != '#skF_3'(A_743,B_744,C_745)
      | ~ r2_hidden(E_746,B_744)
      | ~ r2_hidden(E_746,k1_relat_1(A_743))
      | k9_relat_1(A_743,B_744) = C_745
      | ~ v1_funct_1(A_743)
      | ~ v1_relat_1(A_743) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25046,plain,(
    ! [A_46,B_744,C_745,C_50] :
      ( k1_funct_1(k6_relat_1(A_46),'#skF_2'(k6_relat_1(A_46),B_744,C_745)) = '#skF_1'(k6_relat_1(A_46),B_744,C_745)
      | C_50 != '#skF_3'(k6_relat_1(A_46),B_744,C_745)
      | ~ r2_hidden(C_50,B_744)
      | ~ r2_hidden(C_50,k1_relat_1(k6_relat_1(A_46)))
      | k9_relat_1(k6_relat_1(A_46),B_744) = C_745
      | ~ v1_funct_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ r2_hidden(C_50,A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_25038])).

tff(c_25048,plain,(
    ! [A_46,B_744,C_745,C_50] :
      ( k1_funct_1(k6_relat_1(A_46),'#skF_2'(k6_relat_1(A_46),B_744,C_745)) = '#skF_1'(k6_relat_1(A_46),B_744,C_745)
      | C_50 != '#skF_3'(k6_relat_1(A_46),B_744,C_745)
      | ~ r2_hidden(C_50,B_744)
      | k9_relat_1(k6_relat_1(A_46),B_744) = C_745
      | ~ r2_hidden(C_50,A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_25046])).

tff(c_38061,plain,(
    ! [A_1104,B_1105,C_1106] :
      ( k1_funct_1(k6_relat_1(A_1104),'#skF_2'(k6_relat_1(A_1104),B_1105,C_1106)) = '#skF_1'(k6_relat_1(A_1104),B_1105,C_1106)
      | ~ r2_hidden('#skF_3'(k6_relat_1(A_1104),B_1105,C_1106),B_1105)
      | k9_relat_1(k6_relat_1(A_1104),B_1105) = C_1106
      | ~ r2_hidden('#skF_3'(k6_relat_1(A_1104),B_1105,C_1106),A_1104) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_25048])).

tff(c_38069,plain,
    ( k1_funct_1(k6_relat_1('#skF_7'),'#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')) = '#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')
    | k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') = '#skF_7'
    | ~ r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_25538,c_38061])).

tff(c_38101,plain,
    ( '#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7') = '#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')
    | k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25538,c_36058,c_38069])).

tff(c_38102,plain,(
    '#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7') = '#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_24404,c_38101])).

tff(c_38130,plain,(
    ! [E_38] :
      ( ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7')
      | k1_funct_1(k6_relat_1('#skF_7'),E_38) != '#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')
      | ~ r2_hidden(E_38,'#skF_7')
      | ~ r2_hidden(E_38,k1_relat_1(k6_relat_1('#skF_7')))
      | k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') = '#skF_7'
      | ~ v1_funct_1(k6_relat_1('#skF_7'))
      | ~ v1_relat_1(k6_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38102,c_10])).

tff(c_38149,plain,(
    ! [E_38] :
      ( k1_funct_1(k6_relat_1('#skF_7'),E_38) != '#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')
      | ~ r2_hidden(E_38,'#skF_7')
      | k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_54,c_25495,c_38130])).

tff(c_38155,plain,(
    ! [E_1107] :
      ( k1_funct_1(k6_relat_1('#skF_7'),E_1107) != '#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')
      | ~ r2_hidden(E_1107,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_24404,c_38149])).

tff(c_38185,plain,(
    ~ r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_38155])).

tff(c_38187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38185,c_25538])).

tff(c_38189,plain,(
    ~ r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_25529])).

tff(c_39177,plain,(
    ! [A_1162,B_1163,C_1164] :
      ( '#skF_1'(k6_relat_1(A_1162),B_1163,C_1164) = '#skF_2'(k6_relat_1(A_1162),B_1163,C_1164)
      | r2_hidden('#skF_3'(k6_relat_1(A_1162),B_1163,C_1164),C_1164)
      | k9_relat_1(k6_relat_1(A_1162),B_1163) = C_1164
      | ~ r2_hidden('#skF_2'(k6_relat_1(A_1162),B_1163,C_1164),A_1162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_222])).

tff(c_39179,plain,
    ( '#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7') = '#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')
    | r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7')
    | k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_25495,c_39177])).

tff(c_39196,plain,(
    '#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7') = '#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_24404,c_38189,c_39179])).

tff(c_38188,plain,(
    m1_subset_1('#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_25529])).

tff(c_24901,plain,(
    ! [A_718,A_44,B_45] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_718),A_44),A_718)
      | ~ r2_hidden(A_44,A_718)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_30,c_24847])).

tff(c_38191,plain,(
    ! [A_718] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_718),'#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),A_718)
      | ~ r2_hidden('#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),A_718)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38188,c_24901])).

tff(c_38224,plain,(
    ! [A_1108] :
      ( r2_hidden(k1_funct_1(k6_relat_1(A_1108),'#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),A_1108)
      | ~ r2_hidden('#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),A_1108) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_38191])).

tff(c_38278,plain,
    ( m1_subset_1(k1_funct_1(k6_relat_1('#skF_7'),'#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7')),'#skF_6')
    | ~ r2_hidden('#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_38224,c_84])).

tff(c_38338,plain,(
    ~ r2_hidden('#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_38278])).

tff(c_39204,plain,(
    ~ r2_hidden('#skF_2'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39196,c_38338])).

tff(c_39209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25495,c_39204])).

tff(c_39211,plain,(
    r2_hidden('#skF_1'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_38278])).

tff(c_39222,plain,
    ( r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7')
    | k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') = '#skF_7'
    | ~ v1_funct_1(k6_relat_1('#skF_7'))
    | ~ v1_relat_1(k6_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_39211,c_18])).

tff(c_39235,plain,
    ( r2_hidden('#skF_3'(k6_relat_1('#skF_7'),'#skF_7','#skF_7'),'#skF_7')
    | k9_relat_1(k6_relat_1('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_39222])).

tff(c_39237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24404,c_38189,c_39235])).

tff(c_39238,plain,(
    ! [A_66] : ~ r2_hidden(A_66,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_40070,plain,(
    ! [A_1281,C_1282] :
      ( r2_hidden('#skF_3'(A_1281,'#skF_7',C_1282),C_1282)
      | k9_relat_1(A_1281,'#skF_7') = C_1282
      | ~ v1_funct_1(A_1281)
      | ~ v1_relat_1(A_1281) ) ),
    inference(resolution,[status(thm)],[c_39872,c_39238])).

tff(c_40171,plain,(
    ! [A_1283] :
      ( k9_relat_1(A_1283,'#skF_7') = '#skF_7'
      | ~ v1_funct_1(A_1283)
      | ~ v1_relat_1(A_1283) ) ),
    inference(resolution,[status(thm)],[c_40070,c_39238])).

tff(c_40174,plain,(
    ! [A_43] :
      ( k9_relat_1(k6_relat_1(A_43),'#skF_7') = '#skF_7'
      | ~ v1_funct_1(k6_relat_1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_26,c_40171])).

tff(c_40177,plain,(
    ! [A_43] : k9_relat_1(k6_relat_1(A_43),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_40174])).

tff(c_40180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40177,c_44])).

%------------------------------------------------------------------------------
