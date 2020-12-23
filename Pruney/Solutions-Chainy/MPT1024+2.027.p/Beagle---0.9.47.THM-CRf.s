%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:25 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 136 expanded)
%              Number of leaves         :   34 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  140 ( 350 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_58,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_62,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_58])).

tff(c_56,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_713,plain,(
    ! [A_239,B_240,D_241] :
      ( r2_hidden('#skF_4'(A_239,B_240,k9_relat_1(A_239,B_240),D_241),k1_relat_1(A_239))
      | ~ r2_hidden(D_241,k9_relat_1(A_239,B_240))
      | ~ v1_funct_1(A_239)
      | ~ v1_relat_1(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_487,plain,(
    ! [A_190,C_191] :
      ( r2_hidden(k4_tarski(A_190,k1_funct_1(C_191,A_190)),C_191)
      | ~ r2_hidden(A_190,k1_relat_1(C_191))
      | ~ v1_funct_1(C_191)
      | ~ v1_relat_1(C_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [A_13,B_36,D_51] :
      ( k1_funct_1(A_13,'#skF_4'(A_13,B_36,k9_relat_1(A_13,B_36),D_51)) = D_51
      | ~ r2_hidden(D_51,k9_relat_1(A_13,B_36))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_339,plain,(
    ! [A_147,B_148,D_149] :
      ( r2_hidden('#skF_4'(A_147,B_148,k9_relat_1(A_147,B_148),D_149),k1_relat_1(A_147))
      | ~ r2_hidden(D_149,k9_relat_1(A_147,B_148))
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_55,C_57] :
      ( r2_hidden(k4_tarski(A_55,k1_funct_1(C_57,A_55)),C_57)
      | ~ r2_hidden(A_55,k1_relat_1(C_57))
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_63,plain,(
    ! [C_75,B_76,A_77] :
      ( ~ v1_xboole_0(C_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(C_75))
      | ~ r2_hidden(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,(
    ! [A_77] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_77,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_63])).

tff(c_67,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_84,plain,(
    ! [A_87,C_88,B_89] :
      ( m1_subset_1(A_87,C_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(C_88))
      | ~ r2_hidden(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_87,plain,(
    ! [A_87] :
      ( m1_subset_1(A_87,k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_87,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_84])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_79,C_80,B_81,D_82] :
      ( r2_hidden(A_79,C_80)
      | ~ r2_hidden(k4_tarski(A_79,B_81),k2_zfmisc_1(C_80,D_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_194,plain,(
    ! [A_117,C_118,D_119,B_120] :
      ( r2_hidden(A_117,C_118)
      | v1_xboole_0(k2_zfmisc_1(C_118,D_119))
      | ~ m1_subset_1(k4_tarski(A_117,B_120),k2_zfmisc_1(C_118,D_119)) ) ),
    inference(resolution,[status(thm)],[c_8,c_74])).

tff(c_198,plain,(
    ! [A_117,B_120] :
      ( r2_hidden(A_117,'#skF_5')
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_117,B_120),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_87,c_194])).

tff(c_202,plain,(
    ! [A_121,B_122] :
      ( r2_hidden(A_121,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_121,B_122),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_198])).

tff(c_206,plain,(
    ! [A_55] :
      ( r2_hidden(A_55,'#skF_5')
      | ~ r2_hidden(A_55,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_202])).

tff(c_212,plain,(
    ! [A_55] :
      ( r2_hidden(A_55,'#skF_5')
      | ~ r2_hidden(A_55,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_206])).

tff(c_351,plain,(
    ! [B_148,D_149] :
      ( r2_hidden('#skF_4'('#skF_8',B_148,k9_relat_1('#skF_8',B_148),D_149),'#skF_5')
      | ~ r2_hidden(D_149,k9_relat_1('#skF_8',B_148))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_339,c_212])).

tff(c_393,plain,(
    ! [B_157,D_158] :
      ( r2_hidden('#skF_4'('#skF_8',B_157,k9_relat_1('#skF_8',B_157),D_158),'#skF_5')
      | ~ r2_hidden(D_158,k9_relat_1('#skF_8',B_157)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_351])).

tff(c_255,plain,(
    ! [A_136,B_137,D_138] :
      ( r2_hidden('#skF_4'(A_136,B_137,k9_relat_1(A_136,B_137),D_138),B_137)
      | ~ r2_hidden(D_138,k9_relat_1(A_136,B_137))
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48,plain,(
    ! [F_69] :
      ( k1_funct_1('#skF_8',F_69) != '#skF_9'
      | ~ r2_hidden(F_69,'#skF_7')
      | ~ r2_hidden(F_69,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_275,plain,(
    ! [A_136,D_138] :
      ( k1_funct_1('#skF_8','#skF_4'(A_136,'#skF_7',k9_relat_1(A_136,'#skF_7'),D_138)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_136,'#skF_7',k9_relat_1(A_136,'#skF_7'),D_138),'#skF_5')
      | ~ r2_hidden(D_138,k9_relat_1(A_136,'#skF_7'))
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(resolution,[status(thm)],[c_255,c_48])).

tff(c_397,plain,(
    ! [D_158] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_158)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_158,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_393,c_275])).

tff(c_405,plain,(
    ! [D_159] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_159)) != '#skF_9'
      | ~ r2_hidden(D_159,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_397])).

tff(c_409,plain,(
    ! [D_51] :
      ( D_51 != '#skF_9'
      | ~ r2_hidden(D_51,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_51,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_405])).

tff(c_412,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_409])).

tff(c_127,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( k7_relset_1(A_103,B_104,C_105,D_106) = k9_relat_1(C_105,D_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_130,plain,(
    ! [D_106] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_106) = k9_relat_1('#skF_8',D_106) ),
    inference(resolution,[status(thm)],[c_52,c_127])).

tff(c_50,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_131,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_50])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_131])).

tff(c_415,plain,(
    ! [A_77] : ~ r2_hidden(A_77,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_509,plain,(
    ! [A_190] :
      ( ~ r2_hidden(A_190,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_487,c_415])).

tff(c_522,plain,(
    ! [A_190] : ~ r2_hidden(A_190,k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_509])).

tff(c_725,plain,(
    ! [D_241,B_240] :
      ( ~ r2_hidden(D_241,k9_relat_1('#skF_8',B_240))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_713,c_522])).

tff(c_730,plain,(
    ! [D_241,B_240] : ~ r2_hidden(D_241,k9_relat_1('#skF_8',B_240)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_725])).

tff(c_483,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( k7_relset_1(A_186,B_187,C_188,D_189) = k9_relat_1(C_188,D_189)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_486,plain,(
    ! [D_189] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_189) = k9_relat_1('#skF_8',D_189) ),
    inference(resolution,[status(thm)],[c_52,c_483])).

tff(c_537,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_50])).

tff(c_732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_730,c_537])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:12:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.43  
% 2.73/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.43  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.73/1.43  
% 2.73/1.43  %Foreground sorts:
% 2.73/1.43  
% 2.73/1.43  
% 2.73/1.43  %Background operators:
% 2.73/1.43  
% 2.73/1.43  
% 2.73/1.43  %Foreground operators:
% 2.73/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.73/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.73/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.73/1.43  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.73/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.73/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.73/1.43  tff('#skF_9', type, '#skF_9': $i).
% 2.73/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.73/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.73/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.43  
% 2.73/1.45  tff(f_104, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 2.73/1.45  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.73/1.45  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 2.73/1.45  tff(f_77, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.73/1.45  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.73/1.45  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.73/1.45  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.73/1.45  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.73/1.45  tff(f_85, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.73/1.45  tff(c_52, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.73/1.45  tff(c_58, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.73/1.45  tff(c_62, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_52, c_58])).
% 2.73/1.45  tff(c_56, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.73/1.45  tff(c_713, plain, (![A_239, B_240, D_241]: (r2_hidden('#skF_4'(A_239, B_240, k9_relat_1(A_239, B_240), D_241), k1_relat_1(A_239)) | ~r2_hidden(D_241, k9_relat_1(A_239, B_240)) | ~v1_funct_1(A_239) | ~v1_relat_1(A_239))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.45  tff(c_487, plain, (![A_190, C_191]: (r2_hidden(k4_tarski(A_190, k1_funct_1(C_191, A_190)), C_191) | ~r2_hidden(A_190, k1_relat_1(C_191)) | ~v1_funct_1(C_191) | ~v1_relat_1(C_191))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.73/1.45  tff(c_16, plain, (![A_13, B_36, D_51]: (k1_funct_1(A_13, '#skF_4'(A_13, B_36, k9_relat_1(A_13, B_36), D_51))=D_51 | ~r2_hidden(D_51, k9_relat_1(A_13, B_36)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.45  tff(c_339, plain, (![A_147, B_148, D_149]: (r2_hidden('#skF_4'(A_147, B_148, k9_relat_1(A_147, B_148), D_149), k1_relat_1(A_147)) | ~r2_hidden(D_149, k9_relat_1(A_147, B_148)) | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.45  tff(c_38, plain, (![A_55, C_57]: (r2_hidden(k4_tarski(A_55, k1_funct_1(C_57, A_55)), C_57) | ~r2_hidden(A_55, k1_relat_1(C_57)) | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.73/1.45  tff(c_63, plain, (![C_75, B_76, A_77]: (~v1_xboole_0(C_75) | ~m1_subset_1(B_76, k1_zfmisc_1(C_75)) | ~r2_hidden(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.73/1.45  tff(c_66, plain, (![A_77]: (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(A_77, '#skF_8'))), inference(resolution, [status(thm)], [c_52, c_63])).
% 2.73/1.45  tff(c_67, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_66])).
% 2.73/1.45  tff(c_84, plain, (![A_87, C_88, B_89]: (m1_subset_1(A_87, C_88) | ~m1_subset_1(B_89, k1_zfmisc_1(C_88)) | ~r2_hidden(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.45  tff(c_87, plain, (![A_87]: (m1_subset_1(A_87, k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(A_87, '#skF_8'))), inference(resolution, [status(thm)], [c_52, c_84])).
% 2.73/1.45  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.45  tff(c_74, plain, (![A_79, C_80, B_81, D_82]: (r2_hidden(A_79, C_80) | ~r2_hidden(k4_tarski(A_79, B_81), k2_zfmisc_1(C_80, D_82)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.45  tff(c_194, plain, (![A_117, C_118, D_119, B_120]: (r2_hidden(A_117, C_118) | v1_xboole_0(k2_zfmisc_1(C_118, D_119)) | ~m1_subset_1(k4_tarski(A_117, B_120), k2_zfmisc_1(C_118, D_119)))), inference(resolution, [status(thm)], [c_8, c_74])).
% 2.73/1.45  tff(c_198, plain, (![A_117, B_120]: (r2_hidden(A_117, '#skF_5') | v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(k4_tarski(A_117, B_120), '#skF_8'))), inference(resolution, [status(thm)], [c_87, c_194])).
% 2.73/1.45  tff(c_202, plain, (![A_121, B_122]: (r2_hidden(A_121, '#skF_5') | ~r2_hidden(k4_tarski(A_121, B_122), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_67, c_198])).
% 2.73/1.45  tff(c_206, plain, (![A_55]: (r2_hidden(A_55, '#skF_5') | ~r2_hidden(A_55, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_202])).
% 2.73/1.45  tff(c_212, plain, (![A_55]: (r2_hidden(A_55, '#skF_5') | ~r2_hidden(A_55, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_206])).
% 2.73/1.45  tff(c_351, plain, (![B_148, D_149]: (r2_hidden('#skF_4'('#skF_8', B_148, k9_relat_1('#skF_8', B_148), D_149), '#skF_5') | ~r2_hidden(D_149, k9_relat_1('#skF_8', B_148)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_339, c_212])).
% 2.73/1.45  tff(c_393, plain, (![B_157, D_158]: (r2_hidden('#skF_4'('#skF_8', B_157, k9_relat_1('#skF_8', B_157), D_158), '#skF_5') | ~r2_hidden(D_158, k9_relat_1('#skF_8', B_157)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_351])).
% 2.73/1.45  tff(c_255, plain, (![A_136, B_137, D_138]: (r2_hidden('#skF_4'(A_136, B_137, k9_relat_1(A_136, B_137), D_138), B_137) | ~r2_hidden(D_138, k9_relat_1(A_136, B_137)) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.45  tff(c_48, plain, (![F_69]: (k1_funct_1('#skF_8', F_69)!='#skF_9' | ~r2_hidden(F_69, '#skF_7') | ~r2_hidden(F_69, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.73/1.45  tff(c_275, plain, (![A_136, D_138]: (k1_funct_1('#skF_8', '#skF_4'(A_136, '#skF_7', k9_relat_1(A_136, '#skF_7'), D_138))!='#skF_9' | ~r2_hidden('#skF_4'(A_136, '#skF_7', k9_relat_1(A_136, '#skF_7'), D_138), '#skF_5') | ~r2_hidden(D_138, k9_relat_1(A_136, '#skF_7')) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(resolution, [status(thm)], [c_255, c_48])).
% 2.73/1.45  tff(c_397, plain, (![D_158]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_158))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_158, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_393, c_275])).
% 2.73/1.45  tff(c_405, plain, (![D_159]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_159))!='#skF_9' | ~r2_hidden(D_159, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_397])).
% 2.73/1.45  tff(c_409, plain, (![D_51]: (D_51!='#skF_9' | ~r2_hidden(D_51, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_51, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_405])).
% 2.73/1.45  tff(c_412, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_409])).
% 2.73/1.45  tff(c_127, plain, (![A_103, B_104, C_105, D_106]: (k7_relset_1(A_103, B_104, C_105, D_106)=k9_relat_1(C_105, D_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.73/1.45  tff(c_130, plain, (![D_106]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_106)=k9_relat_1('#skF_8', D_106))), inference(resolution, [status(thm)], [c_52, c_127])).
% 2.73/1.45  tff(c_50, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.73/1.45  tff(c_131, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_50])).
% 2.73/1.45  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_412, c_131])).
% 2.73/1.45  tff(c_415, plain, (![A_77]: (~r2_hidden(A_77, '#skF_8'))), inference(splitRight, [status(thm)], [c_66])).
% 2.73/1.45  tff(c_509, plain, (![A_190]: (~r2_hidden(A_190, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_487, c_415])).
% 2.73/1.45  tff(c_522, plain, (![A_190]: (~r2_hidden(A_190, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_509])).
% 2.73/1.45  tff(c_725, plain, (![D_241, B_240]: (~r2_hidden(D_241, k9_relat_1('#skF_8', B_240)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_713, c_522])).
% 2.73/1.45  tff(c_730, plain, (![D_241, B_240]: (~r2_hidden(D_241, k9_relat_1('#skF_8', B_240)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_725])).
% 2.73/1.45  tff(c_483, plain, (![A_186, B_187, C_188, D_189]: (k7_relset_1(A_186, B_187, C_188, D_189)=k9_relat_1(C_188, D_189) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.73/1.45  tff(c_486, plain, (![D_189]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_189)=k9_relat_1('#skF_8', D_189))), inference(resolution, [status(thm)], [c_52, c_483])).
% 2.73/1.45  tff(c_537, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_50])).
% 2.73/1.45  tff(c_732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_730, c_537])).
% 2.73/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.45  
% 2.73/1.45  Inference rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Ref     : 0
% 2.73/1.45  #Sup     : 120
% 2.73/1.45  #Fact    : 0
% 2.73/1.45  #Define  : 0
% 2.73/1.45  #Split   : 14
% 2.73/1.45  #Chain   : 0
% 2.73/1.45  #Close   : 0
% 2.73/1.45  
% 2.73/1.45  Ordering : KBO
% 2.73/1.45  
% 2.73/1.45  Simplification rules
% 2.73/1.45  ----------------------
% 2.73/1.45  #Subsume      : 9
% 2.73/1.45  #Demod        : 28
% 2.73/1.45  #Tautology    : 18
% 2.73/1.45  #SimpNegUnit  : 6
% 2.73/1.45  #BackRed      : 4
% 2.73/1.45  
% 2.73/1.45  #Partial instantiations: 0
% 2.73/1.45  #Strategies tried      : 1
% 2.73/1.45  
% 2.73/1.45  Timing (in seconds)
% 2.73/1.45  ----------------------
% 2.73/1.45  Preprocessing        : 0.33
% 2.73/1.45  Parsing              : 0.17
% 2.73/1.45  CNF conversion       : 0.03
% 2.73/1.45  Main loop            : 0.35
% 2.73/1.45  Inferencing          : 0.14
% 2.73/1.45  Reduction            : 0.09
% 2.73/1.45  Demodulation         : 0.06
% 2.73/1.45  BG Simplification    : 0.02
% 2.73/1.45  Subsumption          : 0.07
% 2.73/1.45  Abstraction          : 0.02
% 2.73/1.45  MUC search           : 0.00
% 2.73/1.45  Cooper               : 0.00
% 2.73/1.45  Total                : 0.72
% 2.73/1.45  Index Insertion      : 0.00
% 2.73/1.45  Index Deletion       : 0.00
% 2.73/1.45  Index Matching       : 0.00
% 2.73/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
