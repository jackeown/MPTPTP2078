%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:19 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 175 expanded)
%              Number of leaves         :   42 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 ( 428 expanded)
%              Number of equality atoms :   34 ( 103 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_71,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_68,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_91,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_100,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_91])).

tff(c_157,plain,(
    ! [C_104,B_105,A_106] :
      ( v5_relat_1(C_104,B_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_166,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_157])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_685,plain,(
    ! [A_191,B_192,C_193] :
      ( k2_relset_1(A_191,B_192,C_193) = k2_relat_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_694,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_685])).

tff(c_66,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_696,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_66])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_225,plain,(
    ! [C_122,B_123,A_124] :
      ( ~ v1_xboole_0(C_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(C_122))
      | ~ r2_hidden(A_124,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_247,plain,(
    ! [B_128,A_129,A_130] :
      ( ~ v1_xboole_0(B_128)
      | ~ r2_hidden(A_129,A_130)
      | ~ r1_tarski(A_130,B_128) ) ),
    inference(resolution,[status(thm)],[c_18,c_225])).

tff(c_470,plain,(
    ! [B_160,A_161,B_162] :
      ( ~ v1_xboole_0(B_160)
      | ~ r1_tarski(A_161,B_160)
      | r1_tarski(A_161,B_162) ) ),
    inference(resolution,[status(thm)],[c_6,c_247])).

tff(c_480,plain,(
    ! [B_163,B_164] :
      ( ~ v1_xboole_0(B_163)
      | r1_tarski(B_163,B_164) ) ),
    inference(resolution,[status(thm)],[c_14,c_470])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_714,plain,(
    ! [B_200,B_199] :
      ( B_200 = B_199
      | ~ r1_tarski(B_199,B_200)
      | ~ v1_xboole_0(B_200) ) ),
    inference(resolution,[status(thm)],[c_480,c_10])).

tff(c_782,plain,(
    ! [B_217,A_218] :
      ( k2_relat_1(B_217) = A_218
      | ~ v1_xboole_0(A_218)
      | ~ v5_relat_1(B_217,A_218)
      | ~ v1_relat_1(B_217) ) ),
    inference(resolution,[status(thm)],[c_24,c_714])).

tff(c_791,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_166,c_782])).

tff(c_801,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_791])).

tff(c_802,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_696,c_801])).

tff(c_70,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_233,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_242,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_233])).

tff(c_1864,plain,(
    ! [B_318,A_319,C_320] :
      ( k1_xboole_0 = B_318
      | k1_relset_1(A_319,B_318,C_320) = A_319
      | ~ v1_funct_2(C_320,A_319,B_318)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_319,B_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1871,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_1864])).

tff(c_1875,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_242,c_1871])).

tff(c_1876,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1875])).

tff(c_76,plain,(
    ! [D_73] :
      ( r2_hidden('#skF_9'(D_73),'#skF_6')
      | ~ r2_hidden(D_73,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_139,plain,(
    ! [C_96,B_97,A_98] :
      ( r2_hidden(C_96,B_97)
      | ~ r2_hidden(C_96,A_98)
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [D_73,B_97] :
      ( r2_hidden('#skF_9'(D_73),B_97)
      | ~ r1_tarski('#skF_6',B_97)
      | ~ r2_hidden(D_73,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_76,c_139])).

tff(c_72,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_74,plain,(
    ! [D_73] :
      ( k1_funct_1('#skF_8','#skF_9'(D_73)) = D_73
      | ~ r2_hidden(D_73,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_855,plain,(
    ! [A_224,D_225] :
      ( r2_hidden(k1_funct_1(A_224,D_225),k2_relat_1(A_224))
      | ~ r2_hidden(D_225,k1_relat_1(A_224))
      | ~ v1_funct_1(A_224)
      | ~ v1_relat_1(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_865,plain,(
    ! [D_73] :
      ( r2_hidden(D_73,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_73),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_73,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_855])).

tff(c_887,plain,(
    ! [D_231] :
      ( r2_hidden(D_231,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_231),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_231,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_72,c_865])).

tff(c_892,plain,(
    ! [D_73] :
      ( r2_hidden(D_73,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_73,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_145,c_887])).

tff(c_1013,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_892])).

tff(c_1877,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1876,c_1013])).

tff(c_1882,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1877])).

tff(c_1883,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1875])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1907,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_8])).

tff(c_1909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_802,c_1907])).

tff(c_1942,plain,(
    ! [D_323] :
      ( r2_hidden(D_323,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_323,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_892])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2431,plain,(
    ! [A_350] :
      ( r1_tarski(A_350,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_350,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1942,c_4])).

tff(c_2436,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_2431])).

tff(c_2447,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2436,c_10])).

tff(c_2455,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_696,c_2447])).

tff(c_2493,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_24,c_2455])).

tff(c_2498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_166,c_2493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.12/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.73  
% 4.12/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.73  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 4.12/1.73  
% 4.12/1.73  %Foreground sorts:
% 4.12/1.73  
% 4.12/1.73  
% 4.12/1.73  %Background operators:
% 4.12/1.73  
% 4.12/1.73  
% 4.12/1.73  %Foreground operators:
% 4.12/1.73  tff('#skF_9', type, '#skF_9': $i > $i).
% 4.12/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.12/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.12/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.12/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.12/1.73  tff('#skF_7', type, '#skF_7': $i).
% 4.12/1.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.12/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.12/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.12/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.12/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.12/1.73  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.12/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.12/1.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.12/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.12/1.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.12/1.73  tff('#skF_8', type, '#skF_8': $i).
% 4.12/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.12/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.12/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.12/1.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.12/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.12/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.12/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.12/1.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.12/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.73  
% 4.12/1.75  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 4.12/1.75  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.12/1.75  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.12/1.75  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.12/1.75  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.12/1.75  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.12/1.75  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.12/1.75  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.12/1.75  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.12/1.75  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.12/1.75  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.12/1.75  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 4.12/1.75  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.12/1.75  tff(c_68, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.12/1.75  tff(c_91, plain, (![C_83, A_84, B_85]: (v1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.12/1.75  tff(c_100, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_91])).
% 4.12/1.75  tff(c_157, plain, (![C_104, B_105, A_106]: (v5_relat_1(C_104, B_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.12/1.75  tff(c_166, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_157])).
% 4.12/1.75  tff(c_24, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.12/1.75  tff(c_685, plain, (![A_191, B_192, C_193]: (k2_relset_1(A_191, B_192, C_193)=k2_relat_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.12/1.75  tff(c_694, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_685])).
% 4.12/1.75  tff(c_66, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.12/1.75  tff(c_696, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_694, c_66])).
% 4.12/1.75  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.12/1.75  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.12/1.75  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.12/1.75  tff(c_225, plain, (![C_122, B_123, A_124]: (~v1_xboole_0(C_122) | ~m1_subset_1(B_123, k1_zfmisc_1(C_122)) | ~r2_hidden(A_124, B_123))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.12/1.75  tff(c_247, plain, (![B_128, A_129, A_130]: (~v1_xboole_0(B_128) | ~r2_hidden(A_129, A_130) | ~r1_tarski(A_130, B_128))), inference(resolution, [status(thm)], [c_18, c_225])).
% 4.12/1.75  tff(c_470, plain, (![B_160, A_161, B_162]: (~v1_xboole_0(B_160) | ~r1_tarski(A_161, B_160) | r1_tarski(A_161, B_162))), inference(resolution, [status(thm)], [c_6, c_247])).
% 4.12/1.75  tff(c_480, plain, (![B_163, B_164]: (~v1_xboole_0(B_163) | r1_tarski(B_163, B_164))), inference(resolution, [status(thm)], [c_14, c_470])).
% 4.12/1.75  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.12/1.75  tff(c_714, plain, (![B_200, B_199]: (B_200=B_199 | ~r1_tarski(B_199, B_200) | ~v1_xboole_0(B_200))), inference(resolution, [status(thm)], [c_480, c_10])).
% 4.12/1.75  tff(c_782, plain, (![B_217, A_218]: (k2_relat_1(B_217)=A_218 | ~v1_xboole_0(A_218) | ~v5_relat_1(B_217, A_218) | ~v1_relat_1(B_217))), inference(resolution, [status(thm)], [c_24, c_714])).
% 4.12/1.75  tff(c_791, plain, (k2_relat_1('#skF_8')='#skF_7' | ~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_166, c_782])).
% 4.12/1.75  tff(c_801, plain, (k2_relat_1('#skF_8')='#skF_7' | ~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_791])).
% 4.12/1.75  tff(c_802, plain, (~v1_xboole_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_696, c_801])).
% 4.12/1.75  tff(c_70, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.12/1.75  tff(c_233, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.12/1.75  tff(c_242, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_68, c_233])).
% 4.12/1.75  tff(c_1864, plain, (![B_318, A_319, C_320]: (k1_xboole_0=B_318 | k1_relset_1(A_319, B_318, C_320)=A_319 | ~v1_funct_2(C_320, A_319, B_318) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_319, B_318))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.12/1.75  tff(c_1871, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_1864])).
% 4.12/1.75  tff(c_1875, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_242, c_1871])).
% 4.12/1.75  tff(c_1876, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_1875])).
% 4.12/1.75  tff(c_76, plain, (![D_73]: (r2_hidden('#skF_9'(D_73), '#skF_6') | ~r2_hidden(D_73, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.12/1.75  tff(c_139, plain, (![C_96, B_97, A_98]: (r2_hidden(C_96, B_97) | ~r2_hidden(C_96, A_98) | ~r1_tarski(A_98, B_97))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.12/1.75  tff(c_145, plain, (![D_73, B_97]: (r2_hidden('#skF_9'(D_73), B_97) | ~r1_tarski('#skF_6', B_97) | ~r2_hidden(D_73, '#skF_7'))), inference(resolution, [status(thm)], [c_76, c_139])).
% 4.12/1.75  tff(c_72, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.12/1.75  tff(c_74, plain, (![D_73]: (k1_funct_1('#skF_8', '#skF_9'(D_73))=D_73 | ~r2_hidden(D_73, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.12/1.75  tff(c_855, plain, (![A_224, D_225]: (r2_hidden(k1_funct_1(A_224, D_225), k2_relat_1(A_224)) | ~r2_hidden(D_225, k1_relat_1(A_224)) | ~v1_funct_1(A_224) | ~v1_relat_1(A_224))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.12/1.75  tff(c_865, plain, (![D_73]: (r2_hidden(D_73, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_73), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_73, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_855])).
% 4.12/1.75  tff(c_887, plain, (![D_231]: (r2_hidden(D_231, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_231), k1_relat_1('#skF_8')) | ~r2_hidden(D_231, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_72, c_865])).
% 4.12/1.75  tff(c_892, plain, (![D_73]: (r2_hidden(D_73, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_73, '#skF_7'))), inference(resolution, [status(thm)], [c_145, c_887])).
% 4.12/1.75  tff(c_1013, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_892])).
% 4.12/1.75  tff(c_1877, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1876, c_1013])).
% 4.12/1.75  tff(c_1882, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1877])).
% 4.12/1.75  tff(c_1883, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1875])).
% 4.12/1.75  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.12/1.75  tff(c_1907, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_8])).
% 4.12/1.75  tff(c_1909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_802, c_1907])).
% 4.12/1.75  tff(c_1942, plain, (![D_323]: (r2_hidden(D_323, k2_relat_1('#skF_8')) | ~r2_hidden(D_323, '#skF_7'))), inference(splitRight, [status(thm)], [c_892])).
% 4.12/1.75  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.12/1.75  tff(c_2431, plain, (![A_350]: (r1_tarski(A_350, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_350, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_1942, c_4])).
% 4.12/1.75  tff(c_2436, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_2431])).
% 4.12/1.75  tff(c_2447, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_2436, c_10])).
% 4.12/1.75  tff(c_2455, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_696, c_2447])).
% 4.12/1.75  tff(c_2493, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_24, c_2455])).
% 4.12/1.75  tff(c_2498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_166, c_2493])).
% 4.12/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.75  
% 4.12/1.75  Inference rules
% 4.12/1.75  ----------------------
% 4.12/1.75  #Ref     : 0
% 4.12/1.75  #Sup     : 474
% 4.12/1.75  #Fact    : 0
% 4.12/1.75  #Define  : 0
% 4.12/1.75  #Split   : 13
% 4.12/1.75  #Chain   : 0
% 4.12/1.75  #Close   : 0
% 4.12/1.75  
% 4.12/1.75  Ordering : KBO
% 4.12/1.75  
% 4.12/1.75  Simplification rules
% 4.12/1.75  ----------------------
% 4.12/1.75  #Subsume      : 117
% 4.12/1.75  #Demod        : 452
% 4.12/1.75  #Tautology    : 164
% 4.12/1.75  #SimpNegUnit  : 8
% 4.12/1.75  #BackRed      : 71
% 4.12/1.75  
% 4.12/1.75  #Partial instantiations: 0
% 4.12/1.75  #Strategies tried      : 1
% 4.12/1.75  
% 4.12/1.75  Timing (in seconds)
% 4.12/1.75  ----------------------
% 4.38/1.75  Preprocessing        : 0.35
% 4.38/1.75  Parsing              : 0.18
% 4.38/1.75  CNF conversion       : 0.03
% 4.38/1.75  Main loop            : 0.63
% 4.38/1.75  Inferencing          : 0.21
% 4.38/1.75  Reduction            : 0.20
% 4.38/1.75  Demodulation         : 0.14
% 4.38/1.75  BG Simplification    : 0.03
% 4.38/1.75  Subsumption          : 0.12
% 4.38/1.75  Abstraction          : 0.03
% 4.38/1.75  MUC search           : 0.00
% 4.38/1.75  Cooper               : 0.00
% 4.38/1.75  Total                : 1.01
% 4.38/1.75  Index Insertion      : 0.00
% 4.38/1.75  Index Deletion       : 0.00
% 4.38/1.75  Index Matching       : 0.00
% 4.38/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
