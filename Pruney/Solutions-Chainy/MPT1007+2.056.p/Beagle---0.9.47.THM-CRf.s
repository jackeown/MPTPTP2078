%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:18 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 215 expanded)
%              Number of leaves         :   45 (  93 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 481 expanded)
%              Number of equality atoms :   31 ( 110 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_74,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_14,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_102,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_106,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_102])).

tff(c_131,plain,(
    ! [A_76] :
      ( k1_xboole_0 = A_76
      | r2_hidden(k4_tarski('#skF_2'(A_76),'#skF_3'(A_76)),A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [C_20,A_17,B_18] :
      ( r2_hidden(C_20,A_17)
      | ~ r2_hidden(C_20,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_918,plain,(
    ! [A_216,A_217] :
      ( r2_hidden(k4_tarski('#skF_2'(A_216),'#skF_3'(A_216)),A_217)
      | ~ m1_subset_1(A_216,k1_zfmisc_1(A_217))
      | k1_xboole_0 = A_216
      | ~ v1_relat_1(A_216) ) ),
    inference(resolution,[status(thm)],[c_131,c_22])).

tff(c_20,plain,(
    ! [C_15,A_13,B_14,D_16] :
      ( C_15 = A_13
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(k1_tarski(C_15),D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_963,plain,(
    ! [C_222,A_223,D_224] :
      ( C_222 = '#skF_2'(A_223)
      | ~ m1_subset_1(A_223,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_222),D_224)))
      | k1_xboole_0 = A_223
      | ~ v1_relat_1(A_223) ) ),
    inference(resolution,[status(thm)],[c_918,c_20])).

tff(c_966,plain,
    ( '#skF_2'('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_963])).

tff(c_969,plain,
    ( '#skF_2'('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_966])).

tff(c_970,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_969])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [A_53] :
      ( v1_xboole_0(A_53)
      | r2_hidden('#skF_1'(A_53),A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [B_32,A_31] :
      ( ~ r1_tarski(B_32,A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_87,plain,(
    ! [A_54] :
      ( ~ r1_tarski(A_54,'#skF_1'(A_54))
      | v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_78,c_36])).

tff(c_92,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_991,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_92])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_992,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_970,c_30])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_292,plain,(
    ! [A_108,B_109,C_110] :
      ( k2_relset_1(A_108,B_109,C_110) = k2_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_296,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_292])).

tff(c_355,plain,(
    ! [D_124,C_125,A_126,B_127] :
      ( r2_hidden(k1_funct_1(D_124,C_125),k2_relset_1(A_126,B_127,D_124))
      | k1_xboole_0 = B_127
      | ~ r2_hidden(C_125,A_126)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_2(D_124,A_126,B_127)
      | ~ v1_funct_1(D_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_366,plain,(
    ! [C_125] :
      ( r2_hidden(k1_funct_1('#skF_6',C_125),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_125,k1_tarski('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')))
      | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_355])).

tff(c_371,plain,(
    ! [C_125] :
      ( r2_hidden(k1_funct_1('#skF_6',C_125),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_125,k1_tarski('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_366])).

tff(c_373,plain,(
    ! [C_128] :
      ( r2_hidden(k1_funct_1('#skF_6',C_128),k2_relat_1('#skF_6'))
      | ~ r2_hidden(C_128,k1_tarski('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_371])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_384,plain,(
    ! [C_128] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_6'))
      | ~ r2_hidden(C_128,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_373,c_2])).

tff(c_385,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_384])).

tff(c_1016,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_992,c_385])).

tff(c_1023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_1016])).

tff(c_1025,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_969])).

tff(c_107,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_111,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_107])).

tff(c_307,plain,(
    ! [B_116,C_117,A_118] :
      ( r2_hidden(k1_funct_1(B_116,C_117),A_118)
      | ~ r2_hidden(C_117,k1_relat_1(B_116))
      | ~ v1_funct_1(B_116)
      | ~ v5_relat_1(B_116,A_118)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_48,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_315,plain,
    ( ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_307,c_48])).

tff(c_323,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_111,c_56,c_315])).

tff(c_1024,plain,(
    '#skF_2'('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_969])).

tff(c_28,plain,(
    ! [A_24] :
      ( k1_xboole_0 = A_24
      | r2_hidden(k4_tarski('#skF_2'(A_24),'#skF_3'(A_24)),A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_236,plain,(
    ! [A_97,C_98,B_99] :
      ( r2_hidden(A_97,k1_relat_1(C_98))
      | ~ r2_hidden(k4_tarski(A_97,B_99),C_98)
      | ~ v1_relat_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_244,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_2'(A_24),k1_relat_1(A_24))
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(resolution,[status(thm)],[c_28,c_236])).

tff(c_1063,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1024,c_244])).

tff(c_1079,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1063])).

tff(c_1081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1025,c_323,c_1079])).

tff(c_1148,plain,(
    ! [C_235] : ~ r2_hidden(C_235,k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_384])).

tff(c_1160,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_1148])).

tff(c_1166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_1160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:18:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.56  
% 3.66/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.56  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 3.66/1.56  
% 3.66/1.56  %Foreground sorts:
% 3.66/1.56  
% 3.66/1.56  
% 3.66/1.56  %Background operators:
% 3.66/1.56  
% 3.66/1.56  
% 3.66/1.56  %Foreground operators:
% 3.66/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.66/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.66/1.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.66/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.66/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.66/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.66/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.66/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.66/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.66/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.66/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.66/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.66/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.66/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.66/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.66/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.66/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.66/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.66/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.66/1.56  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.66/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.66/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.66/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.66/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.56  
% 3.66/1.58  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.66/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.66/1.58  tff(f_128, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 3.66/1.58  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.66/1.58  tff(f_71, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 3.66/1.58  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.66/1.58  tff(f_48, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 3.66/1.58  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.66/1.58  tff(f_90, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.66/1.58  tff(f_74, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.66/1.58  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.66/1.58  tff(f_116, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.66/1.58  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.66/1.58  tff(f_85, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 3.66/1.58  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 3.66/1.58  tff(c_14, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.66/1.58  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.66/1.58  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.66/1.58  tff(c_102, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.66/1.58  tff(c_106, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_102])).
% 3.66/1.58  tff(c_131, plain, (![A_76]: (k1_xboole_0=A_76 | r2_hidden(k4_tarski('#skF_2'(A_76), '#skF_3'(A_76)), A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.66/1.58  tff(c_22, plain, (![C_20, A_17, B_18]: (r2_hidden(C_20, A_17) | ~r2_hidden(C_20, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.66/1.58  tff(c_918, plain, (![A_216, A_217]: (r2_hidden(k4_tarski('#skF_2'(A_216), '#skF_3'(A_216)), A_217) | ~m1_subset_1(A_216, k1_zfmisc_1(A_217)) | k1_xboole_0=A_216 | ~v1_relat_1(A_216))), inference(resolution, [status(thm)], [c_131, c_22])).
% 3.66/1.58  tff(c_20, plain, (![C_15, A_13, B_14, D_16]: (C_15=A_13 | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(k1_tarski(C_15), D_16)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.66/1.58  tff(c_963, plain, (![C_222, A_223, D_224]: (C_222='#skF_2'(A_223) | ~m1_subset_1(A_223, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_222), D_224))) | k1_xboole_0=A_223 | ~v1_relat_1(A_223))), inference(resolution, [status(thm)], [c_918, c_20])).
% 3.66/1.58  tff(c_966, plain, ('#skF_2'('#skF_6')='#skF_4' | k1_xboole_0='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_963])).
% 3.66/1.58  tff(c_969, plain, ('#skF_2'('#skF_6')='#skF_4' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_966])).
% 3.66/1.58  tff(c_970, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_969])).
% 3.66/1.58  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.66/1.58  tff(c_78, plain, (![A_53]: (v1_xboole_0(A_53) | r2_hidden('#skF_1'(A_53), A_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.66/1.58  tff(c_36, plain, (![B_32, A_31]: (~r1_tarski(B_32, A_31) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.66/1.58  tff(c_87, plain, (![A_54]: (~r1_tarski(A_54, '#skF_1'(A_54)) | v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_78, c_36])).
% 3.66/1.58  tff(c_92, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_87])).
% 3.66/1.58  tff(c_991, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_970, c_92])).
% 3.66/1.58  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.66/1.58  tff(c_992, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_970, c_970, c_30])).
% 3.66/1.58  tff(c_50, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.66/1.58  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.66/1.58  tff(c_54, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.66/1.58  tff(c_292, plain, (![A_108, B_109, C_110]: (k2_relset_1(A_108, B_109, C_110)=k2_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.66/1.58  tff(c_296, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_292])).
% 3.66/1.58  tff(c_355, plain, (![D_124, C_125, A_126, B_127]: (r2_hidden(k1_funct_1(D_124, C_125), k2_relset_1(A_126, B_127, D_124)) | k1_xboole_0=B_127 | ~r2_hidden(C_125, A_126) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_2(D_124, A_126, B_127) | ~v1_funct_1(D_124))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.66/1.58  tff(c_366, plain, (![C_125]: (r2_hidden(k1_funct_1('#skF_6', C_125), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_125, k1_tarski('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))) | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_296, c_355])).
% 3.66/1.58  tff(c_371, plain, (![C_125]: (r2_hidden(k1_funct_1('#skF_6', C_125), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_125, k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_366])).
% 3.66/1.58  tff(c_373, plain, (![C_128]: (r2_hidden(k1_funct_1('#skF_6', C_128), k2_relat_1('#skF_6')) | ~r2_hidden(C_128, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_371])).
% 3.66/1.58  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.66/1.58  tff(c_384, plain, (![C_128]: (~v1_xboole_0(k2_relat_1('#skF_6')) | ~r2_hidden(C_128, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_373, c_2])).
% 3.66/1.58  tff(c_385, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_384])).
% 3.66/1.58  tff(c_1016, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_992, c_385])).
% 3.66/1.58  tff(c_1023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_991, c_1016])).
% 3.66/1.58  tff(c_1025, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_969])).
% 3.66/1.58  tff(c_107, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.66/1.58  tff(c_111, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_107])).
% 3.66/1.58  tff(c_307, plain, (![B_116, C_117, A_118]: (r2_hidden(k1_funct_1(B_116, C_117), A_118) | ~r2_hidden(C_117, k1_relat_1(B_116)) | ~v1_funct_1(B_116) | ~v5_relat_1(B_116, A_118) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.66/1.58  tff(c_48, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.66/1.58  tff(c_315, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_307, c_48])).
% 3.66/1.58  tff(c_323, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_111, c_56, c_315])).
% 3.66/1.58  tff(c_1024, plain, ('#skF_2'('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_969])).
% 3.66/1.58  tff(c_28, plain, (![A_24]: (k1_xboole_0=A_24 | r2_hidden(k4_tarski('#skF_2'(A_24), '#skF_3'(A_24)), A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.66/1.58  tff(c_236, plain, (![A_97, C_98, B_99]: (r2_hidden(A_97, k1_relat_1(C_98)) | ~r2_hidden(k4_tarski(A_97, B_99), C_98) | ~v1_relat_1(C_98))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.66/1.58  tff(c_244, plain, (![A_24]: (r2_hidden('#skF_2'(A_24), k1_relat_1(A_24)) | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(resolution, [status(thm)], [c_28, c_236])).
% 3.66/1.58  tff(c_1063, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | k1_xboole_0='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1024, c_244])).
% 3.66/1.58  tff(c_1079, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1063])).
% 3.66/1.58  tff(c_1081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1025, c_323, c_1079])).
% 3.66/1.58  tff(c_1148, plain, (![C_235]: (~r2_hidden(C_235, k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_384])).
% 3.66/1.58  tff(c_1160, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_1148])).
% 3.66/1.58  tff(c_1166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_1160])).
% 3.66/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.58  
% 3.66/1.58  Inference rules
% 3.66/1.58  ----------------------
% 3.66/1.58  #Ref     : 0
% 3.66/1.58  #Sup     : 225
% 3.66/1.58  #Fact    : 0
% 3.66/1.58  #Define  : 0
% 3.66/1.58  #Split   : 10
% 3.66/1.58  #Chain   : 0
% 3.66/1.58  #Close   : 0
% 3.66/1.58  
% 3.66/1.58  Ordering : KBO
% 3.66/1.58  
% 3.66/1.58  Simplification rules
% 3.66/1.58  ----------------------
% 3.66/1.58  #Subsume      : 10
% 3.66/1.58  #Demod        : 158
% 3.66/1.58  #Tautology    : 42
% 3.66/1.58  #SimpNegUnit  : 14
% 3.66/1.58  #BackRed      : 100
% 3.66/1.58  
% 3.66/1.58  #Partial instantiations: 0
% 3.66/1.58  #Strategies tried      : 1
% 3.66/1.58  
% 3.66/1.58  Timing (in seconds)
% 3.66/1.58  ----------------------
% 3.66/1.58  Preprocessing        : 0.34
% 3.66/1.58  Parsing              : 0.18
% 3.66/1.58  CNF conversion       : 0.02
% 3.66/1.58  Main loop            : 0.47
% 3.66/1.58  Inferencing          : 0.16
% 3.66/1.58  Reduction            : 0.14
% 3.66/1.58  Demodulation         : 0.09
% 3.66/1.58  BG Simplification    : 0.02
% 3.66/1.58  Subsumption          : 0.10
% 3.66/1.58  Abstraction          : 0.02
% 3.66/1.58  MUC search           : 0.00
% 3.66/1.58  Cooper               : 0.00
% 3.66/1.58  Total                : 0.84
% 3.66/1.58  Index Insertion      : 0.00
% 3.66/1.58  Index Deletion       : 0.00
% 3.66/1.58  Index Matching       : 0.00
% 3.66/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
