%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:24 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 167 expanded)
%              Number of leaves         :   41 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  145 ( 390 expanded)
%              Number of equality atoms :   53 ( 112 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_103,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_121,axiom,(
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

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_29,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_133,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_54,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_60,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_38,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_3'(A_40),A_40)
      | k1_xboole_0 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_139,plain,(
    ! [C_95,A_96,B_97] :
      ( r2_hidden(C_95,A_96)
      | ~ r2_hidden(C_95,B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_157,plain,(
    ! [A_104,A_105] :
      ( r2_hidden('#skF_3'(A_104),A_105)
      | ~ m1_subset_1(A_104,k1_zfmisc_1(A_105))
      | k1_xboole_0 = A_104 ) ),
    inference(resolution,[status(thm)],[c_38,c_139])).

tff(c_34,plain,(
    ! [A_37,B_38,C_39] :
      ( k1_mcart_1(A_37) = B_38
      | ~ r2_hidden(A_37,k2_zfmisc_1(k1_tarski(B_38),C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_742,plain,(
    ! [A_174,B_175,C_176] :
      ( k1_mcart_1('#skF_3'(A_174)) = B_175
      | ~ m1_subset_1(A_174,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_175),C_176)))
      | k1_xboole_0 = A_174 ) ),
    inference(resolution,[status(thm)],[c_157,c_34])).

tff(c_753,plain,
    ( k1_mcart_1('#skF_3'('#skF_6')) = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_58,c_742])).

tff(c_796,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_753])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [A_72,B_73] : k2_xboole_0(k1_tarski(A_72),B_73) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    ! [A_72] : k1_tarski(A_72) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_76])).

tff(c_822,plain,(
    ! [A_72] : k1_tarski(A_72) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_80])).

tff(c_491,plain,(
    ! [B_139,A_140,C_141] :
      ( k1_xboole_0 = B_139
      | k1_relset_1(A_140,B_139,C_141) = A_140
      | ~ v1_funct_2(C_141,A_140,B_139)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_501,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_491])).

tff(c_509,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_501])).

tff(c_510,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_509])).

tff(c_820,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_3'(A_40),A_40)
      | A_40 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_38])).

tff(c_16,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_756,plain,(
    ! [D_177,A_178,B_179,C_180] :
      ( r2_hidden(k4_tarski(D_177,'#skF_2'(A_178,B_179,C_180,D_177)),C_180)
      | ~ r2_hidden(D_177,B_179)
      | k1_relset_1(B_179,A_178,C_180) != B_179
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(B_179,A_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_114,plain,(
    ! [A_83,B_84,C_85] :
      ( r2_hidden(k1_mcart_1(A_83),B_84)
      | ~ r2_hidden(A_83,k2_zfmisc_1(B_84,C_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_250,plain,(
    ! [B_118,C_119] :
      ( r2_hidden(k1_mcart_1('#skF_3'(k2_zfmisc_1(B_118,C_119))),B_118)
      | k2_zfmisc_1(B_118,C_119) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_114])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_407,plain,(
    ! [B_134,C_135] :
      ( ~ r1_tarski(B_134,k1_mcart_1('#skF_3'(k2_zfmisc_1(B_134,C_135))))
      | k2_zfmisc_1(B_134,C_135) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_250,c_20])).

tff(c_422,plain,(
    ! [C_136] : k2_zfmisc_1(k1_xboole_0,C_136) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_407])).

tff(c_30,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden(k1_mcart_1(A_34),B_35)
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_35,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_516,plain,(
    ! [A_142] :
      ( r2_hidden(k1_mcart_1(A_142),k1_xboole_0)
      | ~ r2_hidden(A_142,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_30])).

tff(c_523,plain,(
    ! [A_142] :
      ( ~ r1_tarski(k1_xboole_0,k1_mcart_1(A_142))
      | ~ r2_hidden(A_142,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_516,c_20])).

tff(c_530,plain,(
    ! [A_142] : ~ r2_hidden(A_142,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_523])).

tff(c_769,plain,(
    ! [D_177,B_179,A_178] :
      ( ~ r2_hidden(D_177,B_179)
      | k1_relset_1(B_179,A_178,k1_xboole_0) != B_179
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(B_179,A_178))) ) ),
    inference(resolution,[status(thm)],[c_756,c_530])).

tff(c_790,plain,(
    ! [D_177,B_179,A_178] :
      ( ~ r2_hidden(D_177,B_179)
      | k1_relset_1(B_179,A_178,k1_xboole_0) != B_179 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_769])).

tff(c_996,plain,(
    ! [D_204,B_205,A_206] :
      ( ~ r2_hidden(D_204,B_205)
      | k1_relset_1(B_205,A_206,'#skF_6') != B_205 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_790])).

tff(c_1006,plain,(
    ! [A_207,A_208] :
      ( k1_relset_1(A_207,A_208,'#skF_6') != A_207
      | A_207 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_820,c_996])).

tff(c_1012,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_1006])).

tff(c_1018,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_822,c_1012])).

tff(c_1020,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_753])).

tff(c_1019,plain,(
    k1_mcart_1('#skF_3'('#skF_6')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_753])).

tff(c_1274,plain,(
    ! [A_250,B_251,C_252] :
      ( r2_hidden(k1_mcart_1('#skF_3'(A_250)),B_251)
      | ~ m1_subset_1(A_250,k1_zfmisc_1(k2_zfmisc_1(B_251,C_252)))
      | k1_xboole_0 = A_250 ) ),
    inference(resolution,[status(thm)],[c_157,c_30])).

tff(c_1280,plain,
    ( r2_hidden(k1_mcart_1('#skF_3'('#skF_6')),k1_tarski('#skF_4'))
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_58,c_1274])).

tff(c_1286,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1019,c_1280])).

tff(c_1287,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1020,c_1286])).

tff(c_52,plain,(
    ! [D_68,C_67,B_66,A_65] :
      ( r2_hidden(k1_funct_1(D_68,C_67),B_66)
      | k1_xboole_0 = B_66
      | ~ r2_hidden(C_67,A_65)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ v1_funct_2(D_68,A_65,B_66)
      | ~ v1_funct_1(D_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1527,plain,(
    ! [D_276,B_277] :
      ( r2_hidden(k1_funct_1(D_276,'#skF_4'),B_277)
      | k1_xboole_0 = B_277
      | ~ m1_subset_1(D_276,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),B_277)))
      | ~ v1_funct_2(D_276,k1_tarski('#skF_4'),B_277)
      | ~ v1_funct_1(D_276) ) ),
    inference(resolution,[status(thm)],[c_1287,c_52])).

tff(c_1538,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_1527])).

tff(c_1548,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1538])).

tff(c_1550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_1548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:03:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.94/2.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/2.31  
% 5.09/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/2.32  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 5.09/2.32  
% 5.09/2.32  %Foreground sorts:
% 5.09/2.32  
% 5.09/2.32  
% 5.09/2.32  %Background operators:
% 5.09/2.32  
% 5.09/2.32  
% 5.09/2.32  %Foreground operators:
% 5.09/2.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.09/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.09/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.09/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.09/2.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.09/2.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.09/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.09/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.09/2.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.09/2.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.09/2.32  tff('#skF_5', type, '#skF_5': $i).
% 5.09/2.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.09/2.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.09/2.32  tff('#skF_6', type, '#skF_6': $i).
% 5.09/2.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.09/2.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.09/2.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.09/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.09/2.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.09/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.09/2.32  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.09/2.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.09/2.32  tff('#skF_4', type, '#skF_4': $i).
% 5.09/2.32  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.09/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.09/2.32  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.09/2.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.09/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.09/2.32  
% 5.19/2.34  tff(f_145, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 5.19/2.34  tff(f_103, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 5.19/2.34  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.19/2.34  tff(f_82, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 5.19/2.34  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.19/2.34  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 5.19/2.34  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.19/2.34  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.19/2.34  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 5.19/2.34  tff(f_29, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.19/2.34  tff(f_76, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 5.19/2.34  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.19/2.34  tff(f_133, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 5.19/2.34  tff(c_56, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.19/2.34  tff(c_54, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.19/2.34  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.19/2.34  tff(c_60, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.19/2.34  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.19/2.34  tff(c_38, plain, (![A_40]: (r2_hidden('#skF_3'(A_40), A_40) | k1_xboole_0=A_40)), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.19/2.34  tff(c_139, plain, (![C_95, A_96, B_97]: (r2_hidden(C_95, A_96) | ~r2_hidden(C_95, B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.19/2.34  tff(c_157, plain, (![A_104, A_105]: (r2_hidden('#skF_3'(A_104), A_105) | ~m1_subset_1(A_104, k1_zfmisc_1(A_105)) | k1_xboole_0=A_104)), inference(resolution, [status(thm)], [c_38, c_139])).
% 5.19/2.34  tff(c_34, plain, (![A_37, B_38, C_39]: (k1_mcart_1(A_37)=B_38 | ~r2_hidden(A_37, k2_zfmisc_1(k1_tarski(B_38), C_39)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.19/2.34  tff(c_742, plain, (![A_174, B_175, C_176]: (k1_mcart_1('#skF_3'(A_174))=B_175 | ~m1_subset_1(A_174, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_175), C_176))) | k1_xboole_0=A_174)), inference(resolution, [status(thm)], [c_157, c_34])).
% 5.19/2.34  tff(c_753, plain, (k1_mcart_1('#skF_3'('#skF_6'))='#skF_4' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_58, c_742])).
% 5.19/2.34  tff(c_796, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_753])).
% 5.19/2.34  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.19/2.34  tff(c_76, plain, (![A_72, B_73]: (k2_xboole_0(k1_tarski(A_72), B_73)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.19/2.34  tff(c_80, plain, (![A_72]: (k1_tarski(A_72)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_76])).
% 5.19/2.34  tff(c_822, plain, (![A_72]: (k1_tarski(A_72)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_796, c_80])).
% 5.19/2.34  tff(c_491, plain, (![B_139, A_140, C_141]: (k1_xboole_0=B_139 | k1_relset_1(A_140, B_139, C_141)=A_140 | ~v1_funct_2(C_141, A_140, B_139) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.19/2.34  tff(c_501, plain, (k1_xboole_0='#skF_5' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4') | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_58, c_491])).
% 5.19/2.34  tff(c_509, plain, (k1_xboole_0='#skF_5' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_501])).
% 5.19/2.34  tff(c_510, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_509])).
% 5.19/2.34  tff(c_820, plain, (![A_40]: (r2_hidden('#skF_3'(A_40), A_40) | A_40='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_796, c_38])).
% 5.19/2.34  tff(c_16, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.19/2.34  tff(c_756, plain, (![D_177, A_178, B_179, C_180]: (r2_hidden(k4_tarski(D_177, '#skF_2'(A_178, B_179, C_180, D_177)), C_180) | ~r2_hidden(D_177, B_179) | k1_relset_1(B_179, A_178, C_180)!=B_179 | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(B_179, A_178))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.19/2.34  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.19/2.34  tff(c_114, plain, (![A_83, B_84, C_85]: (r2_hidden(k1_mcart_1(A_83), B_84) | ~r2_hidden(A_83, k2_zfmisc_1(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.19/2.34  tff(c_250, plain, (![B_118, C_119]: (r2_hidden(k1_mcart_1('#skF_3'(k2_zfmisc_1(B_118, C_119))), B_118) | k2_zfmisc_1(B_118, C_119)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_114])).
% 5.19/2.34  tff(c_20, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.19/2.34  tff(c_407, plain, (![B_134, C_135]: (~r1_tarski(B_134, k1_mcart_1('#skF_3'(k2_zfmisc_1(B_134, C_135)))) | k2_zfmisc_1(B_134, C_135)=k1_xboole_0)), inference(resolution, [status(thm)], [c_250, c_20])).
% 5.19/2.34  tff(c_422, plain, (![C_136]: (k2_zfmisc_1(k1_xboole_0, C_136)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_407])).
% 5.19/2.34  tff(c_30, plain, (![A_34, B_35, C_36]: (r2_hidden(k1_mcart_1(A_34), B_35) | ~r2_hidden(A_34, k2_zfmisc_1(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.19/2.34  tff(c_516, plain, (![A_142]: (r2_hidden(k1_mcart_1(A_142), k1_xboole_0) | ~r2_hidden(A_142, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_422, c_30])).
% 5.19/2.34  tff(c_523, plain, (![A_142]: (~r1_tarski(k1_xboole_0, k1_mcart_1(A_142)) | ~r2_hidden(A_142, k1_xboole_0))), inference(resolution, [status(thm)], [c_516, c_20])).
% 5.19/2.34  tff(c_530, plain, (![A_142]: (~r2_hidden(A_142, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_523])).
% 5.19/2.34  tff(c_769, plain, (![D_177, B_179, A_178]: (~r2_hidden(D_177, B_179) | k1_relset_1(B_179, A_178, k1_xboole_0)!=B_179 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(B_179, A_178))))), inference(resolution, [status(thm)], [c_756, c_530])).
% 5.19/2.34  tff(c_790, plain, (![D_177, B_179, A_178]: (~r2_hidden(D_177, B_179) | k1_relset_1(B_179, A_178, k1_xboole_0)!=B_179)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_769])).
% 5.19/2.34  tff(c_996, plain, (![D_204, B_205, A_206]: (~r2_hidden(D_204, B_205) | k1_relset_1(B_205, A_206, '#skF_6')!=B_205)), inference(demodulation, [status(thm), theory('equality')], [c_796, c_790])).
% 5.19/2.34  tff(c_1006, plain, (![A_207, A_208]: (k1_relset_1(A_207, A_208, '#skF_6')!=A_207 | A_207='#skF_6')), inference(resolution, [status(thm)], [c_820, c_996])).
% 5.19/2.34  tff(c_1012, plain, (k1_tarski('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_510, c_1006])).
% 5.19/2.34  tff(c_1018, plain, $false, inference(negUnitSimplification, [status(thm)], [c_822, c_1012])).
% 5.19/2.34  tff(c_1020, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_753])).
% 5.19/2.34  tff(c_1019, plain, (k1_mcart_1('#skF_3'('#skF_6'))='#skF_4'), inference(splitRight, [status(thm)], [c_753])).
% 5.19/2.34  tff(c_1274, plain, (![A_250, B_251, C_252]: (r2_hidden(k1_mcart_1('#skF_3'(A_250)), B_251) | ~m1_subset_1(A_250, k1_zfmisc_1(k2_zfmisc_1(B_251, C_252))) | k1_xboole_0=A_250)), inference(resolution, [status(thm)], [c_157, c_30])).
% 5.19/2.34  tff(c_1280, plain, (r2_hidden(k1_mcart_1('#skF_3'('#skF_6')), k1_tarski('#skF_4')) | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_58, c_1274])).
% 5.19/2.34  tff(c_1286, plain, (r2_hidden('#skF_4', k1_tarski('#skF_4')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1019, c_1280])).
% 5.19/2.34  tff(c_1287, plain, (r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1020, c_1286])).
% 5.19/2.34  tff(c_52, plain, (![D_68, C_67, B_66, A_65]: (r2_hidden(k1_funct_1(D_68, C_67), B_66) | k1_xboole_0=B_66 | ~r2_hidden(C_67, A_65) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~v1_funct_2(D_68, A_65, B_66) | ~v1_funct_1(D_68))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.19/2.34  tff(c_1527, plain, (![D_276, B_277]: (r2_hidden(k1_funct_1(D_276, '#skF_4'), B_277) | k1_xboole_0=B_277 | ~m1_subset_1(D_276, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), B_277))) | ~v1_funct_2(D_276, k1_tarski('#skF_4'), B_277) | ~v1_funct_1(D_276))), inference(resolution, [status(thm)], [c_1287, c_52])).
% 5.19/2.34  tff(c_1538, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_1527])).
% 5.19/2.34  tff(c_1548, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1538])).
% 5.19/2.34  tff(c_1550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_1548])).
% 5.19/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.34  
% 5.19/2.34  Inference rules
% 5.19/2.34  ----------------------
% 5.19/2.34  #Ref     : 0
% 5.19/2.34  #Sup     : 325
% 5.19/2.34  #Fact    : 2
% 5.19/2.34  #Define  : 0
% 5.19/2.34  #Split   : 2
% 5.19/2.34  #Chain   : 0
% 5.19/2.34  #Close   : 0
% 5.19/2.34  
% 5.19/2.34  Ordering : KBO
% 5.19/2.34  
% 5.19/2.34  Simplification rules
% 5.19/2.34  ----------------------
% 5.19/2.34  #Subsume      : 66
% 5.19/2.34  #Demod        : 121
% 5.19/2.34  #Tautology    : 100
% 5.19/2.34  #SimpNegUnit  : 19
% 5.19/2.34  #BackRed      : 35
% 5.19/2.34  
% 5.19/2.34  #Partial instantiations: 0
% 5.19/2.34  #Strategies tried      : 1
% 5.19/2.34  
% 5.19/2.34  Timing (in seconds)
% 5.19/2.34  ----------------------
% 5.19/2.35  Preprocessing        : 0.54
% 5.19/2.35  Parsing              : 0.28
% 5.19/2.35  CNF conversion       : 0.04
% 5.19/2.35  Main loop            : 0.88
% 5.19/2.35  Inferencing          : 0.31
% 5.19/2.35  Reduction            : 0.26
% 5.19/2.35  Demodulation         : 0.17
% 5.19/2.35  BG Simplification    : 0.05
% 5.19/2.35  Subsumption          : 0.18
% 5.19/2.35  Abstraction          : 0.04
% 5.19/2.35  MUC search           : 0.00
% 5.19/2.35  Cooper               : 0.00
% 5.19/2.35  Total                : 1.48
% 5.19/2.35  Index Insertion      : 0.00
% 5.19/2.35  Index Deletion       : 0.00
% 5.19/2.35  Index Matching       : 0.00
% 5.19/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
