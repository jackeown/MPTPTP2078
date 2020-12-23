%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:17 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 132 expanded)
%              Number of leaves         :   44 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  124 ( 265 expanded)
%              Number of equality atoms :   42 ( 100 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_72,axiom,(
    ! [A,B] :
      ( A != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
        & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    ! [A_21] : k2_zfmisc_1(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_84,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_88,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_346,plain,(
    ! [C_101,B_102,A_103] :
      ( v5_relat_1(C_101,B_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_356,plain,(
    v5_relat_1('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_88,c_346])).

tff(c_86,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_60,plain,(
    ! [A_30,B_31] : v1_relat_1(k2_zfmisc_1(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_258,plain,(
    ! [B_80,A_81] :
      ( v1_relat_1(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_261,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_88,c_258])).

tff(c_264,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_261])).

tff(c_92,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_90,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_453,plain,(
    ! [A_117,B_118,C_119] :
      ( k1_relset_1(A_117,B_118,C_119) = k1_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_463,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_88,c_453])).

tff(c_593,plain,(
    ! [B_163,A_164,C_165] :
      ( k1_xboole_0 = B_163
      | k1_relset_1(A_164,B_163,C_165) = A_164
      | ~ v1_funct_2(C_165,A_164,B_163)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_164,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_596,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_88,c_593])).

tff(c_605,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_463,c_596])).

tff(c_607,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_605])).

tff(c_62,plain,(
    ! [C_34,B_33,A_32] :
      ( m1_subset_1(k1_funct_1(C_34,B_33),A_32)
      | ~ r2_hidden(B_33,k1_relat_1(C_34))
      | ~ v1_funct_1(C_34)
      | ~ v5_relat_1(C_34,A_32)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_611,plain,(
    ! [B_33,A_32] :
      ( m1_subset_1(k1_funct_1('#skF_9',B_33),A_32)
      | ~ r2_hidden(B_33,'#skF_6')
      | ~ v1_funct_1('#skF_9')
      | ~ v5_relat_1('#skF_9',A_32)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_62])).

tff(c_621,plain,(
    ! [B_166,A_167] :
      ( m1_subset_1(k1_funct_1('#skF_9',B_166),A_167)
      | ~ r2_hidden(B_166,'#skF_6')
      | ~ v5_relat_1('#skF_9',A_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_92,c_611])).

tff(c_14,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_128,plain,(
    ! [B_52,A_53] :
      ( ~ r2_hidden(B_52,A_53)
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [C_11] : ~ v1_xboole_0(k1_tarski(C_11)) ),
    inference(resolution,[status(thm)],[c_14,c_128])).

tff(c_276,plain,(
    ! [A_84,B_85] :
      ( r2_hidden(A_84,B_85)
      | v1_xboole_0(B_85)
      | ~ m1_subset_1(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_283,plain,(
    ! [A_84,A_7] :
      ( A_84 = A_7
      | v1_xboole_0(k1_tarski(A_7))
      | ~ m1_subset_1(A_84,k1_tarski(A_7)) ) ),
    inference(resolution,[status(thm)],[c_276,c_12])).

tff(c_290,plain,(
    ! [A_84,A_7] :
      ( A_84 = A_7
      | ~ m1_subset_1(A_84,k1_tarski(A_7)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_283])).

tff(c_687,plain,(
    ! [B_168,A_169] :
      ( k1_funct_1('#skF_9',B_168) = A_169
      | ~ r2_hidden(B_168,'#skF_6')
      | ~ v5_relat_1('#skF_9',k1_tarski(A_169)) ) ),
    inference(resolution,[status(thm)],[c_621,c_290])).

tff(c_711,plain,(
    ! [A_170] :
      ( k1_funct_1('#skF_9','#skF_8') = A_170
      | ~ v5_relat_1('#skF_9',k1_tarski(A_170)) ) ),
    inference(resolution,[status(thm)],[c_86,c_687])).

tff(c_714,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_356,c_711])).

tff(c_718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_714])).

tff(c_719,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_605])).

tff(c_52,plain,(
    ! [A_23,B_24] :
      ( k2_zfmisc_1(A_23,k1_tarski(B_24)) != k1_xboole_0
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_746,plain,(
    ! [A_23] :
      ( k2_zfmisc_1(A_23,k1_xboole_0) != k1_xboole_0
      | k1_xboole_0 = A_23 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_52])).

tff(c_779,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_746])).

tff(c_771,plain,(
    ! [A_23] : k1_xboole_0 = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_746])).

tff(c_1539,plain,(
    ! [A_3554] : A_3554 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_779,c_771])).

tff(c_200,plain,(
    ! [B_66,A_67] :
      ( ~ r1_tarski(B_66,A_67)
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_220,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_86,c_200])).

tff(c_1662,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1539,c_220])).

tff(c_1700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.73  
% 3.62/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.73  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2
% 3.62/1.73  
% 3.62/1.73  %Foreground sorts:
% 3.62/1.73  
% 3.62/1.73  
% 3.62/1.73  %Background operators:
% 3.62/1.73  
% 3.62/1.73  
% 3.62/1.73  %Foreground operators:
% 3.62/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.62/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.62/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.62/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.73  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.62/1.73  tff('#skF_7', type, '#skF_7': $i).
% 3.62/1.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.62/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.62/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.62/1.73  tff('#skF_6', type, '#skF_6': $i).
% 3.62/1.73  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.62/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.62/1.73  tff('#skF_9', type, '#skF_9': $i).
% 3.62/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.62/1.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.62/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.62/1.73  tff('#skF_8', type, '#skF_8': $i).
% 3.62/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.62/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.62/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.62/1.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.62/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.62/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.62/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.73  
% 3.62/1.75  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.62/1.75  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.62/1.75  tff(f_141, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.62/1.75  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.62/1.75  tff(f_87, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.62/1.75  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.62/1.75  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.62/1.75  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.62/1.75  tff(f_97, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 3.62/1.75  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.62/1.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.62/1.75  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.62/1.75  tff(f_72, axiom, (![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 3.62/1.75  tff(f_102, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.62/1.75  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.62/1.75  tff(c_48, plain, (![A_21]: (k2_zfmisc_1(A_21, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.62/1.75  tff(c_84, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.62/1.75  tff(c_88, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.62/1.75  tff(c_346, plain, (![C_101, B_102, A_103]: (v5_relat_1(C_101, B_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.62/1.75  tff(c_356, plain, (v5_relat_1('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_88, c_346])).
% 3.62/1.75  tff(c_86, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.62/1.75  tff(c_60, plain, (![A_30, B_31]: (v1_relat_1(k2_zfmisc_1(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.62/1.75  tff(c_258, plain, (![B_80, A_81]: (v1_relat_1(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.62/1.75  tff(c_261, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_88, c_258])).
% 3.62/1.75  tff(c_264, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_261])).
% 3.62/1.75  tff(c_92, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.62/1.75  tff(c_90, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.62/1.75  tff(c_453, plain, (![A_117, B_118, C_119]: (k1_relset_1(A_117, B_118, C_119)=k1_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.62/1.75  tff(c_463, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_88, c_453])).
% 3.62/1.75  tff(c_593, plain, (![B_163, A_164, C_165]: (k1_xboole_0=B_163 | k1_relset_1(A_164, B_163, C_165)=A_164 | ~v1_funct_2(C_165, A_164, B_163) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_164, B_163))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.62/1.75  tff(c_596, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_88, c_593])).
% 3.62/1.75  tff(c_605, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_463, c_596])).
% 3.62/1.75  tff(c_607, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_605])).
% 3.62/1.75  tff(c_62, plain, (![C_34, B_33, A_32]: (m1_subset_1(k1_funct_1(C_34, B_33), A_32) | ~r2_hidden(B_33, k1_relat_1(C_34)) | ~v1_funct_1(C_34) | ~v5_relat_1(C_34, A_32) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.62/1.75  tff(c_611, plain, (![B_33, A_32]: (m1_subset_1(k1_funct_1('#skF_9', B_33), A_32) | ~r2_hidden(B_33, '#skF_6') | ~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', A_32) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_62])).
% 3.62/1.75  tff(c_621, plain, (![B_166, A_167]: (m1_subset_1(k1_funct_1('#skF_9', B_166), A_167) | ~r2_hidden(B_166, '#skF_6') | ~v5_relat_1('#skF_9', A_167))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_92, c_611])).
% 3.62/1.75  tff(c_14, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.62/1.75  tff(c_128, plain, (![B_52, A_53]: (~r2_hidden(B_52, A_53) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.62/1.75  tff(c_135, plain, (![C_11]: (~v1_xboole_0(k1_tarski(C_11)))), inference(resolution, [status(thm)], [c_14, c_128])).
% 3.62/1.75  tff(c_276, plain, (![A_84, B_85]: (r2_hidden(A_84, B_85) | v1_xboole_0(B_85) | ~m1_subset_1(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.62/1.75  tff(c_12, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.62/1.75  tff(c_283, plain, (![A_84, A_7]: (A_84=A_7 | v1_xboole_0(k1_tarski(A_7)) | ~m1_subset_1(A_84, k1_tarski(A_7)))), inference(resolution, [status(thm)], [c_276, c_12])).
% 3.62/1.75  tff(c_290, plain, (![A_84, A_7]: (A_84=A_7 | ~m1_subset_1(A_84, k1_tarski(A_7)))), inference(negUnitSimplification, [status(thm)], [c_135, c_283])).
% 3.62/1.75  tff(c_687, plain, (![B_168, A_169]: (k1_funct_1('#skF_9', B_168)=A_169 | ~r2_hidden(B_168, '#skF_6') | ~v5_relat_1('#skF_9', k1_tarski(A_169)))), inference(resolution, [status(thm)], [c_621, c_290])).
% 3.62/1.75  tff(c_711, plain, (![A_170]: (k1_funct_1('#skF_9', '#skF_8')=A_170 | ~v5_relat_1('#skF_9', k1_tarski(A_170)))), inference(resolution, [status(thm)], [c_86, c_687])).
% 3.62/1.75  tff(c_714, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_356, c_711])).
% 3.62/1.75  tff(c_718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_714])).
% 3.62/1.75  tff(c_719, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_605])).
% 3.62/1.75  tff(c_52, plain, (![A_23, B_24]: (k2_zfmisc_1(A_23, k1_tarski(B_24))!=k1_xboole_0 | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.62/1.75  tff(c_746, plain, (![A_23]: (k2_zfmisc_1(A_23, k1_xboole_0)!=k1_xboole_0 | k1_xboole_0=A_23)), inference(superposition, [status(thm), theory('equality')], [c_719, c_52])).
% 3.62/1.75  tff(c_779, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_746])).
% 3.62/1.75  tff(c_771, plain, (![A_23]: (k1_xboole_0=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_746])).
% 3.62/1.75  tff(c_1539, plain, (![A_3554]: (A_3554='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_779, c_771])).
% 3.62/1.75  tff(c_200, plain, (![B_66, A_67]: (~r1_tarski(B_66, A_67) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.62/1.75  tff(c_220, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_86, c_200])).
% 3.62/1.75  tff(c_1662, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1539, c_220])).
% 3.62/1.75  tff(c_1700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_1662])).
% 3.62/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.75  
% 3.62/1.75  Inference rules
% 3.62/1.75  ----------------------
% 3.62/1.75  #Ref     : 0
% 3.62/1.75  #Sup     : 360
% 3.62/1.75  #Fact    : 4
% 3.62/1.75  #Define  : 0
% 3.62/1.75  #Split   : 2
% 3.62/1.75  #Chain   : 0
% 3.62/1.75  #Close   : 0
% 3.62/1.75  
% 3.62/1.75  Ordering : KBO
% 3.62/1.75  
% 3.62/1.75  Simplification rules
% 3.62/1.75  ----------------------
% 3.62/1.75  #Subsume      : 57
% 3.62/1.75  #Demod        : 58
% 3.62/1.75  #Tautology    : 59
% 3.62/1.75  #SimpNegUnit  : 15
% 3.62/1.75  #BackRed      : 5
% 3.62/1.75  
% 3.62/1.75  #Partial instantiations: 1430
% 3.62/1.75  #Strategies tried      : 1
% 3.62/1.75  
% 3.62/1.75  Timing (in seconds)
% 3.62/1.75  ----------------------
% 3.62/1.75  Preprocessing        : 0.39
% 3.62/1.75  Parsing              : 0.20
% 3.62/1.75  CNF conversion       : 0.03
% 3.62/1.75  Main loop            : 0.50
% 3.62/1.75  Inferencing          : 0.22
% 3.62/1.75  Reduction            : 0.13
% 3.62/1.75  Demodulation         : 0.09
% 3.62/1.75  BG Simplification    : 0.03
% 3.62/1.75  Subsumption          : 0.08
% 3.62/1.75  Abstraction          : 0.03
% 3.62/1.75  MUC search           : 0.00
% 3.62/1.75  Cooper               : 0.00
% 3.62/1.75  Total                : 0.92
% 3.62/1.75  Index Insertion      : 0.00
% 3.62/1.75  Index Deletion       : 0.00
% 3.62/1.75  Index Matching       : 0.00
% 3.62/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
