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
% DateTime   : Thu Dec  3 10:17:58 EST 2020

% Result     : Theorem 6.40s
% Output     : CNFRefutation 6.81s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 171 expanded)
%              Number of leaves         :   42 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 386 expanded)
%              Number of equality atoms :   34 (  97 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_144,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_128,axiom,(
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

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_291,plain,(
    ! [C_91,B_92,A_93] :
      ( v5_relat_1(C_91,B_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_306,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_291])).

tff(c_176,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_189,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_176])).

tff(c_399,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_relset_1(A_114,B_115,C_116) = k2_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_414,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_399])).

tff(c_72,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_422,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_72])).

tff(c_36,plain,(
    ! [C_24,A_21,B_22] :
      ( r2_hidden(C_24,A_21)
      | ~ r2_hidden(C_24,k2_relat_1(B_22))
      | ~ v5_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_428,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_2',A_21)
      | ~ v5_relat_1('#skF_5',A_21)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_422,c_36])).

tff(c_446,plain,(
    ! [A_118] :
      ( r2_hidden('#skF_2',A_118)
      | ~ v5_relat_1('#skF_5',A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_428])).

tff(c_455,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_306,c_446])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_190,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ v1_xboole_0(C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_195,plain,(
    ! [B_8,A_67,A_7] :
      ( ~ v1_xboole_0(B_8)
      | ~ r2_hidden(A_67,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_20,c_190])).

tff(c_470,plain,(
    ! [B_121] :
      ( ~ v1_xboole_0(B_121)
      | ~ r1_tarski('#skF_4',B_121) ) ),
    inference(resolution,[status(thm)],[c_455,c_195])).

tff(c_475,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_470])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_356,plain,(
    ! [A_108,B_109,C_110] :
      ( k1_relset_1(A_108,B_109,C_110) = k1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_371,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_356])).

tff(c_1076,plain,(
    ! [B_217,A_218,C_219] :
      ( k1_xboole_0 = B_217
      | k1_relset_1(A_218,B_217,C_219) = A_218
      | ~ v1_funct_2(C_219,A_218,B_217)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_218,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1083,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1076])).

tff(c_1093,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_371,c_1083])).

tff(c_1095,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1093])).

tff(c_34,plain,(
    ! [A_20] :
      ( k9_relat_1(A_20,k1_relat_1(A_20)) = k2_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1107,plain,
    ( k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1095,c_34])).

tff(c_1115,plain,(
    k9_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_1107])).

tff(c_605,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden('#skF_1'(A_150,B_151,C_152),B_151)
      | ~ r2_hidden(A_150,k9_relat_1(C_152,B_151))
      | ~ v1_relat_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_621,plain,(
    ! [A_150,B_151,C_152] :
      ( m1_subset_1('#skF_1'(A_150,B_151,C_152),B_151)
      | ~ r2_hidden(A_150,k9_relat_1(C_152,B_151))
      | ~ v1_relat_1(C_152) ) ),
    inference(resolution,[status(thm)],[c_605,c_16])).

tff(c_1126,plain,(
    ! [A_150] :
      ( m1_subset_1('#skF_1'(A_150,'#skF_3','#skF_5'),'#skF_3')
      | ~ r2_hidden(A_150,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1115,c_621])).

tff(c_1140,plain,(
    ! [A_220] :
      ( m1_subset_1('#skF_1'(A_220,'#skF_3','#skF_5'),'#skF_3')
      | ~ r2_hidden(A_220,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_1126])).

tff(c_1159,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_422,c_1140])).

tff(c_70,plain,(
    ! [E_44] :
      ( k1_funct_1('#skF_5',E_44) != '#skF_2'
      | ~ m1_subset_1(E_44,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1182,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1159,c_70])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_902,plain,(
    ! [A_199,B_200,C_201] :
      ( r2_hidden(k4_tarski('#skF_1'(A_199,B_200,C_201),A_199),C_201)
      | ~ r2_hidden(A_199,k9_relat_1(C_201,B_200))
      | ~ v1_relat_1(C_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    ! [C_27,A_25,B_26] :
      ( k1_funct_1(C_27,A_25) = B_26
      | ~ r2_hidden(k4_tarski(A_25,B_26),C_27)
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2224,plain,(
    ! [C_328,A_329,B_330] :
      ( k1_funct_1(C_328,'#skF_1'(A_329,B_330,C_328)) = A_329
      | ~ v1_funct_1(C_328)
      | ~ r2_hidden(A_329,k9_relat_1(C_328,B_330))
      | ~ v1_relat_1(C_328) ) ),
    inference(resolution,[status(thm)],[c_902,c_44])).

tff(c_2228,plain,(
    ! [A_329] :
      ( k1_funct_1('#skF_5','#skF_1'(A_329,'#skF_3','#skF_5')) = A_329
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(A_329,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1115,c_2224])).

tff(c_2250,plain,(
    ! [A_331] :
      ( k1_funct_1('#skF_5','#skF_1'(A_331,'#skF_3','#skF_5')) = A_331
      | ~ r2_hidden(A_331,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_78,c_2228])).

tff(c_2265,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_422,c_2250])).

tff(c_2272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1182,c_2265])).

tff(c_2273,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1093])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2317,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2273,c_2])).

tff(c_2319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_2317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:54:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.40/2.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.40/2.71  
% 6.40/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.40/2.71  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 6.40/2.71  
% 6.40/2.71  %Foreground sorts:
% 6.40/2.71  
% 6.40/2.71  
% 6.40/2.71  %Background operators:
% 6.40/2.71  
% 6.40/2.71  
% 6.40/2.71  %Foreground operators:
% 6.40/2.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.40/2.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.40/2.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.40/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.40/2.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.40/2.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.40/2.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.40/2.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.40/2.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.40/2.71  tff('#skF_5', type, '#skF_5': $i).
% 6.40/2.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.40/2.71  tff('#skF_2', type, '#skF_2': $i).
% 6.40/2.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.40/2.71  tff('#skF_3', type, '#skF_3': $i).
% 6.40/2.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.40/2.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.40/2.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.40/2.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.40/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.40/2.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.40/2.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.40/2.71  tff('#skF_4', type, '#skF_4': $i).
% 6.40/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.40/2.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.40/2.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.40/2.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.40/2.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.40/2.71  
% 6.81/2.74  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.81/2.74  tff(f_144, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 6.81/2.74  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.81/2.74  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.81/2.74  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.81/2.74  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 6.81/2.74  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.81/2.74  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.81/2.74  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.81/2.74  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.81/2.74  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 6.81/2.74  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 6.81/2.74  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 6.81/2.74  tff(f_92, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 6.81/2.74  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.81/2.74  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.81/2.74  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.81/2.74  tff(c_291, plain, (![C_91, B_92, A_93]: (v5_relat_1(C_91, B_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.81/2.74  tff(c_306, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_291])).
% 6.81/2.74  tff(c_176, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.81/2.74  tff(c_189, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_176])).
% 6.81/2.74  tff(c_399, plain, (![A_114, B_115, C_116]: (k2_relset_1(A_114, B_115, C_116)=k2_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.81/2.74  tff(c_414, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_399])).
% 6.81/2.74  tff(c_72, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.81/2.74  tff(c_422, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_414, c_72])).
% 6.81/2.74  tff(c_36, plain, (![C_24, A_21, B_22]: (r2_hidden(C_24, A_21) | ~r2_hidden(C_24, k2_relat_1(B_22)) | ~v5_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.81/2.74  tff(c_428, plain, (![A_21]: (r2_hidden('#skF_2', A_21) | ~v5_relat_1('#skF_5', A_21) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_422, c_36])).
% 6.81/2.74  tff(c_446, plain, (![A_118]: (r2_hidden('#skF_2', A_118) | ~v5_relat_1('#skF_5', A_118))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_428])).
% 6.81/2.74  tff(c_455, plain, (r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_306, c_446])).
% 6.81/2.74  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.81/2.74  tff(c_190, plain, (![C_65, B_66, A_67]: (~v1_xboole_0(C_65) | ~m1_subset_1(B_66, k1_zfmisc_1(C_65)) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.81/2.74  tff(c_195, plain, (![B_8, A_67, A_7]: (~v1_xboole_0(B_8) | ~r2_hidden(A_67, A_7) | ~r1_tarski(A_7, B_8))), inference(resolution, [status(thm)], [c_20, c_190])).
% 6.81/2.74  tff(c_470, plain, (![B_121]: (~v1_xboole_0(B_121) | ~r1_tarski('#skF_4', B_121))), inference(resolution, [status(thm)], [c_455, c_195])).
% 6.81/2.74  tff(c_475, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_8, c_470])).
% 6.81/2.74  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.81/2.74  tff(c_356, plain, (![A_108, B_109, C_110]: (k1_relset_1(A_108, B_109, C_110)=k1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.81/2.74  tff(c_371, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_356])).
% 6.81/2.74  tff(c_1076, plain, (![B_217, A_218, C_219]: (k1_xboole_0=B_217 | k1_relset_1(A_218, B_217, C_219)=A_218 | ~v1_funct_2(C_219, A_218, B_217) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_218, B_217))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.81/2.74  tff(c_1083, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_1076])).
% 6.81/2.74  tff(c_1093, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_371, c_1083])).
% 6.81/2.74  tff(c_1095, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1093])).
% 6.81/2.74  tff(c_34, plain, (![A_20]: (k9_relat_1(A_20, k1_relat_1(A_20))=k2_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.81/2.74  tff(c_1107, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1095, c_34])).
% 6.81/2.74  tff(c_1115, plain, (k9_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_1107])).
% 6.81/2.74  tff(c_605, plain, (![A_150, B_151, C_152]: (r2_hidden('#skF_1'(A_150, B_151, C_152), B_151) | ~r2_hidden(A_150, k9_relat_1(C_152, B_151)) | ~v1_relat_1(C_152))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.81/2.74  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.81/2.74  tff(c_621, plain, (![A_150, B_151, C_152]: (m1_subset_1('#skF_1'(A_150, B_151, C_152), B_151) | ~r2_hidden(A_150, k9_relat_1(C_152, B_151)) | ~v1_relat_1(C_152))), inference(resolution, [status(thm)], [c_605, c_16])).
% 6.81/2.74  tff(c_1126, plain, (![A_150]: (m1_subset_1('#skF_1'(A_150, '#skF_3', '#skF_5'), '#skF_3') | ~r2_hidden(A_150, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1115, c_621])).
% 6.81/2.74  tff(c_1140, plain, (![A_220]: (m1_subset_1('#skF_1'(A_220, '#skF_3', '#skF_5'), '#skF_3') | ~r2_hidden(A_220, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_1126])).
% 6.81/2.74  tff(c_1159, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_422, c_1140])).
% 6.81/2.74  tff(c_70, plain, (![E_44]: (k1_funct_1('#skF_5', E_44)!='#skF_2' | ~m1_subset_1(E_44, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.81/2.74  tff(c_1182, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))!='#skF_2'), inference(resolution, [status(thm)], [c_1159, c_70])).
% 6.81/2.74  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.81/2.74  tff(c_902, plain, (![A_199, B_200, C_201]: (r2_hidden(k4_tarski('#skF_1'(A_199, B_200, C_201), A_199), C_201) | ~r2_hidden(A_199, k9_relat_1(C_201, B_200)) | ~v1_relat_1(C_201))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.81/2.74  tff(c_44, plain, (![C_27, A_25, B_26]: (k1_funct_1(C_27, A_25)=B_26 | ~r2_hidden(k4_tarski(A_25, B_26), C_27) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.81/2.74  tff(c_2224, plain, (![C_328, A_329, B_330]: (k1_funct_1(C_328, '#skF_1'(A_329, B_330, C_328))=A_329 | ~v1_funct_1(C_328) | ~r2_hidden(A_329, k9_relat_1(C_328, B_330)) | ~v1_relat_1(C_328))), inference(resolution, [status(thm)], [c_902, c_44])).
% 6.81/2.74  tff(c_2228, plain, (![A_329]: (k1_funct_1('#skF_5', '#skF_1'(A_329, '#skF_3', '#skF_5'))=A_329 | ~v1_funct_1('#skF_5') | ~r2_hidden(A_329, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1115, c_2224])).
% 6.81/2.74  tff(c_2250, plain, (![A_331]: (k1_funct_1('#skF_5', '#skF_1'(A_331, '#skF_3', '#skF_5'))=A_331 | ~r2_hidden(A_331, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_78, c_2228])).
% 6.81/2.74  tff(c_2265, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2'), inference(resolution, [status(thm)], [c_422, c_2250])).
% 6.81/2.74  tff(c_2272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1182, c_2265])).
% 6.81/2.74  tff(c_2273, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1093])).
% 6.81/2.74  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.81/2.74  tff(c_2317, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2273, c_2])).
% 6.81/2.74  tff(c_2319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_475, c_2317])).
% 6.81/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.81/2.74  
% 6.81/2.74  Inference rules
% 6.81/2.74  ----------------------
% 6.81/2.74  #Ref     : 0
% 6.81/2.74  #Sup     : 464
% 6.81/2.74  #Fact    : 0
% 6.81/2.74  #Define  : 0
% 6.81/2.74  #Split   : 9
% 6.81/2.74  #Chain   : 0
% 6.81/2.74  #Close   : 0
% 6.81/2.74  
% 6.81/2.74  Ordering : KBO
% 6.81/2.74  
% 6.81/2.74  Simplification rules
% 6.81/2.74  ----------------------
% 6.81/2.74  #Subsume      : 110
% 6.81/2.74  #Demod        : 349
% 6.81/2.74  #Tautology    : 89
% 6.81/2.74  #SimpNegUnit  : 4
% 6.81/2.74  #BackRed      : 51
% 6.81/2.74  
% 6.81/2.74  #Partial instantiations: 0
% 6.81/2.74  #Strategies tried      : 1
% 6.81/2.74  
% 6.81/2.74  Timing (in seconds)
% 6.81/2.74  ----------------------
% 6.81/2.74  Preprocessing        : 0.56
% 6.81/2.74  Parsing              : 0.28
% 6.81/2.74  CNF conversion       : 0.04
% 6.81/2.74  Main loop            : 1.23
% 6.81/2.74  Inferencing          : 0.41
% 6.81/2.74  Reduction            : 0.39
% 6.81/2.74  Demodulation         : 0.29
% 6.81/2.74  BG Simplification    : 0.05
% 6.81/2.74  Subsumption          : 0.27
% 6.81/2.74  Abstraction          : 0.06
% 6.81/2.74  MUC search           : 0.00
% 6.81/2.74  Cooper               : 0.00
% 6.81/2.75  Total                : 1.84
% 6.81/2.75  Index Insertion      : 0.00
% 6.81/2.75  Index Deletion       : 0.00
% 6.81/2.75  Index Matching       : 0.00
% 6.81/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
