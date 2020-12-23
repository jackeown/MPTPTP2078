%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:27 EST 2020

% Result     : Theorem 11.38s
% Output     : CNFRefutation 11.38s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 142 expanded)
%              Number of leaves         :   42 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 339 expanded)
%              Number of equality atoms :   30 (  71 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_142,negated_conjecture,(
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
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
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

tff(f_88,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_80,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_176,plain,(
    ! [B_110,A_111] :
      ( v1_relat_1(B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_111))
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_182,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_80,c_176])).

tff(c_186,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_182])).

tff(c_84,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_82,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_517,plain,(
    ! [A_152,B_153,C_154] :
      ( k1_relset_1(A_152,B_153,C_154) = k1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_531,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_80,c_517])).

tff(c_1166,plain,(
    ! [B_193,A_194,C_195] :
      ( k1_xboole_0 = B_193
      | k1_relset_1(A_194,B_193,C_195) = A_194
      | ~ v1_funct_2(C_195,A_194,B_193)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1181,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_1166])).

tff(c_1187,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_531,c_1181])).

tff(c_1188,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1187])).

tff(c_34,plain,(
    ! [A_25,B_48,D_63] :
      ( k1_funct_1(A_25,'#skF_6'(A_25,B_48,k9_relat_1(A_25,B_48),D_63)) = D_63
      | ~ r2_hidden(D_63,k9_relat_1(A_25,B_48))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    ! [A_25,B_48,D_63] :
      ( r2_hidden('#skF_6'(A_25,B_48,k9_relat_1(A_25,B_48),D_63),B_48)
      | ~ r2_hidden(D_63,k9_relat_1(A_25,B_48))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1662,plain,(
    ! [A_228,B_229,D_230] :
      ( r2_hidden('#skF_6'(A_228,B_229,k9_relat_1(A_228,B_229),D_230),k1_relat_1(A_228))
      | ~ r2_hidden(D_230,k9_relat_1(A_228,B_229))
      | ~ v1_funct_1(A_228)
      | ~ v1_relat_1(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14886,plain,(
    ! [A_1013,B_1014,D_1015,B_1016] :
      ( r2_hidden('#skF_6'(A_1013,B_1014,k9_relat_1(A_1013,B_1014),D_1015),B_1016)
      | ~ r1_tarski(k1_relat_1(A_1013),B_1016)
      | ~ r2_hidden(D_1015,k9_relat_1(A_1013,B_1014))
      | ~ v1_funct_1(A_1013)
      | ~ v1_relat_1(A_1013) ) ),
    inference(resolution,[status(thm)],[c_1662,c_6])).

tff(c_76,plain,(
    ! [F_87] :
      ( k1_funct_1('#skF_10',F_87) != '#skF_11'
      | ~ r2_hidden(F_87,'#skF_9')
      | ~ r2_hidden(F_87,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_15349,plain,(
    ! [A_1027,B_1028,D_1029] :
      ( k1_funct_1('#skF_10','#skF_6'(A_1027,B_1028,k9_relat_1(A_1027,B_1028),D_1029)) != '#skF_11'
      | ~ r2_hidden('#skF_6'(A_1027,B_1028,k9_relat_1(A_1027,B_1028),D_1029),'#skF_9')
      | ~ r1_tarski(k1_relat_1(A_1027),'#skF_7')
      | ~ r2_hidden(D_1029,k9_relat_1(A_1027,B_1028))
      | ~ v1_funct_1(A_1027)
      | ~ v1_relat_1(A_1027) ) ),
    inference(resolution,[status(thm)],[c_14886,c_76])).

tff(c_19070,plain,(
    ! [A_1107,D_1108] :
      ( k1_funct_1('#skF_10','#skF_6'(A_1107,'#skF_9',k9_relat_1(A_1107,'#skF_9'),D_1108)) != '#skF_11'
      | ~ r1_tarski(k1_relat_1(A_1107),'#skF_7')
      | ~ r2_hidden(D_1108,k9_relat_1(A_1107,'#skF_9'))
      | ~ v1_funct_1(A_1107)
      | ~ v1_relat_1(A_1107) ) ),
    inference(resolution,[status(thm)],[c_36,c_15349])).

tff(c_19102,plain,(
    ! [D_63] :
      ( D_63 != '#skF_11'
      | ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_7')
      | ~ r2_hidden(D_63,k9_relat_1('#skF_10','#skF_9'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_63,k9_relat_1('#skF_10','#skF_9'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_19070])).

tff(c_19119,plain,(
    ~ r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_84,c_186,c_84,c_16,c_1188,c_19102])).

tff(c_754,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( k7_relset_1(A_169,B_170,C_171,D_172) = k9_relat_1(C_171,D_172)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_769,plain,(
    ! [D_172] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_172) = k9_relat_1('#skF_10',D_172) ),
    inference(resolution,[status(thm)],[c_80,c_754])).

tff(c_78,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_865,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_78])).

tff(c_19121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19119,c_865])).

tff(c_19122,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1187])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_866,plain,(
    ! [D_176] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_176) = k9_relat_1('#skF_10',D_176) ),
    inference(resolution,[status(thm)],[c_80,c_754])).

tff(c_58,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( m1_subset_1(k7_relset_1(A_69,B_70,C_71,D_72),k1_zfmisc_1(B_70))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_872,plain,(
    ! [D_176] :
      ( m1_subset_1(k9_relat_1('#skF_10',D_176),k1_zfmisc_1('#skF_8'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_58])).

tff(c_944,plain,(
    ! [D_181] : m1_subset_1(k9_relat_1('#skF_10',D_181),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_872])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_955,plain,(
    ! [D_181] : r1_tarski(k9_relat_1('#skF_10',D_181),'#skF_8') ),
    inference(resolution,[status(thm)],[c_944,c_22])).

tff(c_270,plain,(
    ! [C_119,B_120,A_121] :
      ( r2_hidden(C_119,B_120)
      | ~ r2_hidden(C_119,A_121)
      | ~ r1_tarski(A_121,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_281,plain,(
    ! [B_120] :
      ( r2_hidden('#skF_11',B_120)
      | ~ r1_tarski(k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9'),B_120) ) ),
    inference(resolution,[status(thm)],[c_78,c_270])).

tff(c_994,plain,(
    ! [B_185] :
      ( r2_hidden('#skF_11',B_185)
      | ~ r1_tarski(k9_relat_1('#skF_10','#skF_9'),B_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_281])).

tff(c_1011,plain,(
    r2_hidden('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_955,c_994])).

tff(c_1050,plain,(
    ! [B_187] :
      ( r2_hidden('#skF_11',B_187)
      | ~ r1_tarski('#skF_8',B_187) ) ),
    inference(resolution,[status(thm)],[c_1011,c_6])).

tff(c_56,plain,(
    ! [B_68,A_67] :
      ( ~ r1_tarski(B_68,A_67)
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1113,plain,(
    ! [B_191] :
      ( ~ r1_tarski(B_191,'#skF_11')
      | ~ r1_tarski('#skF_8',B_191) ) ),
    inference(resolution,[status(thm)],[c_1050,c_56])).

tff(c_1129,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_1113])).

tff(c_19125,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19122,c_1129])).

tff(c_19147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_19125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:05:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.38/4.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.38/4.43  
% 11.38/4.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.38/4.43  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2
% 11.38/4.43  
% 11.38/4.43  %Foreground sorts:
% 11.38/4.43  
% 11.38/4.43  
% 11.38/4.43  %Background operators:
% 11.38/4.43  
% 11.38/4.43  
% 11.38/4.43  %Foreground operators:
% 11.38/4.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.38/4.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.38/4.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.38/4.43  tff('#skF_11', type, '#skF_11': $i).
% 11.38/4.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.38/4.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.38/4.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.38/4.43  tff('#skF_7', type, '#skF_7': $i).
% 11.38/4.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.38/4.43  tff('#skF_10', type, '#skF_10': $i).
% 11.38/4.43  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 11.38/4.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.38/4.43  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.38/4.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.38/4.43  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 11.38/4.43  tff('#skF_9', type, '#skF_9': $i).
% 11.38/4.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.38/4.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.38/4.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.38/4.43  tff('#skF_8', type, '#skF_8': $i).
% 11.38/4.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.38/4.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.38/4.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.38/4.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.38/4.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.38/4.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.38/4.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.38/4.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.38/4.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.38/4.43  
% 11.38/4.44  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.38/4.44  tff(f_71, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.38/4.44  tff(f_142, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 11.38/4.44  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.38/4.44  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.38/4.44  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.38/4.44  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 11.38/4.44  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.38/4.44  tff(f_105, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 11.38/4.44  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.38/4.44  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 11.38/4.44  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.38/4.44  tff(f_93, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.38/4.44  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.38/4.44  tff(c_30, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.38/4.44  tff(c_80, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.38/4.44  tff(c_176, plain, (![B_110, A_111]: (v1_relat_1(B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_111)) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.38/4.44  tff(c_182, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_80, c_176])).
% 11.38/4.44  tff(c_186, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_182])).
% 11.38/4.44  tff(c_84, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.38/4.44  tff(c_82, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.38/4.44  tff(c_517, plain, (![A_152, B_153, C_154]: (k1_relset_1(A_152, B_153, C_154)=k1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.38/4.44  tff(c_531, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_80, c_517])).
% 11.38/4.44  tff(c_1166, plain, (![B_193, A_194, C_195]: (k1_xboole_0=B_193 | k1_relset_1(A_194, B_193, C_195)=A_194 | ~v1_funct_2(C_195, A_194, B_193) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.38/4.44  tff(c_1181, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_80, c_1166])).
% 11.38/4.44  tff(c_1187, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_531, c_1181])).
% 11.38/4.44  tff(c_1188, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_1187])).
% 11.38/4.44  tff(c_34, plain, (![A_25, B_48, D_63]: (k1_funct_1(A_25, '#skF_6'(A_25, B_48, k9_relat_1(A_25, B_48), D_63))=D_63 | ~r2_hidden(D_63, k9_relat_1(A_25, B_48)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.38/4.44  tff(c_36, plain, (![A_25, B_48, D_63]: (r2_hidden('#skF_6'(A_25, B_48, k9_relat_1(A_25, B_48), D_63), B_48) | ~r2_hidden(D_63, k9_relat_1(A_25, B_48)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.38/4.44  tff(c_1662, plain, (![A_228, B_229, D_230]: (r2_hidden('#skF_6'(A_228, B_229, k9_relat_1(A_228, B_229), D_230), k1_relat_1(A_228)) | ~r2_hidden(D_230, k9_relat_1(A_228, B_229)) | ~v1_funct_1(A_228) | ~v1_relat_1(A_228))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.38/4.44  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.38/4.44  tff(c_14886, plain, (![A_1013, B_1014, D_1015, B_1016]: (r2_hidden('#skF_6'(A_1013, B_1014, k9_relat_1(A_1013, B_1014), D_1015), B_1016) | ~r1_tarski(k1_relat_1(A_1013), B_1016) | ~r2_hidden(D_1015, k9_relat_1(A_1013, B_1014)) | ~v1_funct_1(A_1013) | ~v1_relat_1(A_1013))), inference(resolution, [status(thm)], [c_1662, c_6])).
% 11.38/4.44  tff(c_76, plain, (![F_87]: (k1_funct_1('#skF_10', F_87)!='#skF_11' | ~r2_hidden(F_87, '#skF_9') | ~r2_hidden(F_87, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.38/4.44  tff(c_15349, plain, (![A_1027, B_1028, D_1029]: (k1_funct_1('#skF_10', '#skF_6'(A_1027, B_1028, k9_relat_1(A_1027, B_1028), D_1029))!='#skF_11' | ~r2_hidden('#skF_6'(A_1027, B_1028, k9_relat_1(A_1027, B_1028), D_1029), '#skF_9') | ~r1_tarski(k1_relat_1(A_1027), '#skF_7') | ~r2_hidden(D_1029, k9_relat_1(A_1027, B_1028)) | ~v1_funct_1(A_1027) | ~v1_relat_1(A_1027))), inference(resolution, [status(thm)], [c_14886, c_76])).
% 11.38/4.44  tff(c_19070, plain, (![A_1107, D_1108]: (k1_funct_1('#skF_10', '#skF_6'(A_1107, '#skF_9', k9_relat_1(A_1107, '#skF_9'), D_1108))!='#skF_11' | ~r1_tarski(k1_relat_1(A_1107), '#skF_7') | ~r2_hidden(D_1108, k9_relat_1(A_1107, '#skF_9')) | ~v1_funct_1(A_1107) | ~v1_relat_1(A_1107))), inference(resolution, [status(thm)], [c_36, c_15349])).
% 11.38/4.44  tff(c_19102, plain, (![D_63]: (D_63!='#skF_11' | ~r1_tarski(k1_relat_1('#skF_10'), '#skF_7') | ~r2_hidden(D_63, k9_relat_1('#skF_10', '#skF_9')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_63, k9_relat_1('#skF_10', '#skF_9')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_19070])).
% 11.38/4.44  tff(c_19119, plain, (~r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_84, c_186, c_84, c_16, c_1188, c_19102])).
% 11.38/4.44  tff(c_754, plain, (![A_169, B_170, C_171, D_172]: (k7_relset_1(A_169, B_170, C_171, D_172)=k9_relat_1(C_171, D_172) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.38/4.44  tff(c_769, plain, (![D_172]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_172)=k9_relat_1('#skF_10', D_172))), inference(resolution, [status(thm)], [c_80, c_754])).
% 11.38/4.44  tff(c_78, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.38/4.44  tff(c_865, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_769, c_78])).
% 11.38/4.44  tff(c_19121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19119, c_865])).
% 11.38/4.44  tff(c_19122, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1187])).
% 11.38/4.44  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.38/4.44  tff(c_866, plain, (![D_176]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_176)=k9_relat_1('#skF_10', D_176))), inference(resolution, [status(thm)], [c_80, c_754])).
% 11.38/4.44  tff(c_58, plain, (![A_69, B_70, C_71, D_72]: (m1_subset_1(k7_relset_1(A_69, B_70, C_71, D_72), k1_zfmisc_1(B_70)) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.38/4.44  tff(c_872, plain, (![D_176]: (m1_subset_1(k9_relat_1('#skF_10', D_176), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_866, c_58])).
% 11.38/4.44  tff(c_944, plain, (![D_181]: (m1_subset_1(k9_relat_1('#skF_10', D_181), k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_872])).
% 11.38/4.44  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.38/4.44  tff(c_955, plain, (![D_181]: (r1_tarski(k9_relat_1('#skF_10', D_181), '#skF_8'))), inference(resolution, [status(thm)], [c_944, c_22])).
% 11.38/4.44  tff(c_270, plain, (![C_119, B_120, A_121]: (r2_hidden(C_119, B_120) | ~r2_hidden(C_119, A_121) | ~r1_tarski(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.38/4.44  tff(c_281, plain, (![B_120]: (r2_hidden('#skF_11', B_120) | ~r1_tarski(k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'), B_120))), inference(resolution, [status(thm)], [c_78, c_270])).
% 11.38/4.44  tff(c_994, plain, (![B_185]: (r2_hidden('#skF_11', B_185) | ~r1_tarski(k9_relat_1('#skF_10', '#skF_9'), B_185))), inference(demodulation, [status(thm), theory('equality')], [c_769, c_281])).
% 11.38/4.44  tff(c_1011, plain, (r2_hidden('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_955, c_994])).
% 11.38/4.44  tff(c_1050, plain, (![B_187]: (r2_hidden('#skF_11', B_187) | ~r1_tarski('#skF_8', B_187))), inference(resolution, [status(thm)], [c_1011, c_6])).
% 11.38/4.44  tff(c_56, plain, (![B_68, A_67]: (~r1_tarski(B_68, A_67) | ~r2_hidden(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.38/4.44  tff(c_1113, plain, (![B_191]: (~r1_tarski(B_191, '#skF_11') | ~r1_tarski('#skF_8', B_191))), inference(resolution, [status(thm)], [c_1050, c_56])).
% 11.38/4.44  tff(c_1129, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1113])).
% 11.38/4.44  tff(c_19125, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_19122, c_1129])).
% 11.38/4.44  tff(c_19147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_19125])).
% 11.38/4.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.38/4.44  
% 11.38/4.44  Inference rules
% 11.38/4.44  ----------------------
% 11.38/4.44  #Ref     : 0
% 11.38/4.44  #Sup     : 4351
% 11.38/4.44  #Fact    : 0
% 11.38/4.44  #Define  : 0
% 11.38/4.44  #Split   : 43
% 11.38/4.44  #Chain   : 0
% 11.38/4.44  #Close   : 0
% 11.38/4.44  
% 11.38/4.44  Ordering : KBO
% 11.38/4.44  
% 11.38/4.44  Simplification rules
% 11.38/4.44  ----------------------
% 11.38/4.44  #Subsume      : 1516
% 11.38/4.44  #Demod        : 2359
% 11.38/4.44  #Tautology    : 753
% 11.38/4.44  #SimpNegUnit  : 82
% 11.38/4.44  #BackRed      : 79
% 11.38/4.44  
% 11.38/4.44  #Partial instantiations: 0
% 11.38/4.44  #Strategies tried      : 1
% 11.38/4.44  
% 11.38/4.44  Timing (in seconds)
% 11.38/4.44  ----------------------
% 11.38/4.45  Preprocessing        : 0.39
% 11.38/4.45  Parsing              : 0.19
% 11.38/4.45  CNF conversion       : 0.03
% 11.38/4.45  Main loop            : 3.28
% 11.38/4.45  Inferencing          : 0.88
% 11.38/4.45  Reduction            : 0.99
% 11.38/4.45  Demodulation         : 0.65
% 11.38/4.45  BG Simplification    : 0.09
% 11.38/4.45  Subsumption          : 1.06
% 11.38/4.45  Abstraction          : 0.12
% 11.38/4.45  MUC search           : 0.00
% 11.38/4.45  Cooper               : 0.00
% 11.38/4.45  Total                : 3.71
% 11.38/4.45  Index Insertion      : 0.00
% 11.38/4.45  Index Deletion       : 0.00
% 11.38/4.45  Index Matching       : 0.00
% 11.38/4.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
