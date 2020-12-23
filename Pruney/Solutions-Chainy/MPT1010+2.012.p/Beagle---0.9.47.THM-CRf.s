%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:06 EST 2020

% Result     : Theorem 49.84s
% Output     : CNFRefutation 49.84s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 164 expanded)
%              Number of leaves         :   43 (  78 expanded)
%              Depth                    :   16
%              Number of atoms          :  153 ( 367 expanded)
%              Number of equality atoms :   42 ( 100 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_2 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i ) > $i )).

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
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_94,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_12,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_160,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_1'(A_79,B_80),A_79)
      | r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_172,plain,(
    ! [A_79] : r1_tarski(A_79,A_79) ),
    inference(resolution,[status(thm)],[c_160,c_4])).

tff(c_96,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_214,plain,(
    ! [C_125,B_126,A_127] :
      ( r2_hidden(C_125,B_126)
      | ~ r2_hidden(C_125,A_127)
      | ~ r1_tarski(A_127,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_238,plain,(
    ! [B_126] :
      ( r2_hidden('#skF_8',B_126)
      | ~ r1_tarski('#skF_6',B_126) ) ),
    inference(resolution,[status(thm)],[c_96,c_214])).

tff(c_98,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_155,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_159,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_98,c_155])).

tff(c_102,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_100,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_565,plain,(
    ! [A_218,B_219,C_220] :
      ( k1_relset_1(A_218,B_219,C_220) = k1_relat_1(C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_569,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_98,c_565])).

tff(c_1152,plain,(
    ! [B_332,A_333,C_334] :
      ( k1_xboole_0 = B_332
      | k1_relset_1(A_333,B_332,C_334) = A_333
      | ~ v1_funct_2(C_334,A_333,B_332)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(A_333,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1155,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_98,c_1152])).

tff(c_1158,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_569,c_1155])).

tff(c_1159,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1158])).

tff(c_298,plain,(
    ! [C_140,B_141,A_142] :
      ( v5_relat_1(C_140,B_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_302,plain,(
    v5_relat_1('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_98,c_298])).

tff(c_68,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k2_relat_1(B_32),A_31)
      | ~ v5_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_744,plain,(
    ! [A_297,B_298,B_299] :
      ( r2_hidden('#skF_1'(A_297,B_298),B_299)
      | ~ r1_tarski(A_297,B_299)
      | r1_tarski(A_297,B_298) ) ),
    inference(resolution,[status(thm)],[c_6,c_214])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1229,plain,(
    ! [A_341,A_342,B_343] :
      ( A_341 = '#skF_1'(A_342,B_343)
      | ~ r1_tarski(A_342,k1_tarski(A_341))
      | r1_tarski(A_342,B_343) ) ),
    inference(resolution,[status(thm)],[c_744,c_10])).

tff(c_14904,plain,(
    ! [A_21104,B_21105,B_21106] :
      ( A_21104 = '#skF_1'(k2_relat_1(B_21105),B_21106)
      | r1_tarski(k2_relat_1(B_21105),B_21106)
      | ~ v5_relat_1(B_21105,k1_tarski(A_21104))
      | ~ v1_relat_1(B_21105) ) ),
    inference(resolution,[status(thm)],[c_68,c_1229])).

tff(c_14978,plain,(
    ! [B_21106] :
      ( '#skF_1'(k2_relat_1('#skF_9'),B_21106) = '#skF_7'
      | r1_tarski(k2_relat_1('#skF_9'),B_21106)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_302,c_14904])).

tff(c_14981,plain,(
    ! [B_21106] :
      ( '#skF_1'(k2_relat_1('#skF_9'),B_21106) = '#skF_7'
      | r1_tarski(k2_relat_1('#skF_9'),B_21106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_14978])).

tff(c_705,plain,(
    ! [B_275,A_276] :
      ( r2_hidden(k1_funct_1(B_275,A_276),k2_relat_1(B_275))
      | ~ r2_hidden(A_276,k1_relat_1(B_275))
      | ~ v1_funct_1(B_275)
      | ~ v1_relat_1(B_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26033,plain,(
    ! [B_36843,A_36844,B_36845] :
      ( r2_hidden(k1_funct_1(B_36843,A_36844),B_36845)
      | ~ r1_tarski(k2_relat_1(B_36843),B_36845)
      | ~ r2_hidden(A_36844,k1_relat_1(B_36843))
      | ~ v1_funct_1(B_36843)
      | ~ v1_relat_1(B_36843) ) ),
    inference(resolution,[status(thm)],[c_705,c_2])).

tff(c_39229,plain,(
    ! [B_66690,A_66691,A_66692] :
      ( k1_funct_1(B_66690,A_66691) = A_66692
      | ~ r1_tarski(k2_relat_1(B_66690),k1_tarski(A_66692))
      | ~ r2_hidden(A_66691,k1_relat_1(B_66690))
      | ~ v1_funct_1(B_66690)
      | ~ v1_relat_1(B_66690) ) ),
    inference(resolution,[status(thm)],[c_26033,c_10])).

tff(c_39256,plain,(
    ! [A_66691,A_66692] :
      ( k1_funct_1('#skF_9',A_66691) = A_66692
      | ~ r2_hidden(A_66691,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_66692)) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_14981,c_39229])).

tff(c_42177,plain,(
    ! [A_73637,A_73638] :
      ( k1_funct_1('#skF_9',A_73637) = A_73638
      | ~ r2_hidden(A_73637,'#skF_6')
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_73638)) = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_102,c_1159,c_39256])).

tff(c_42342,plain,(
    ! [A_73854] :
      ( k1_funct_1('#skF_9','#skF_8') = A_73854
      | '#skF_1'(k2_relat_1('#skF_9'),k1_tarski(A_73854)) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_96,c_42177])).

tff(c_43239,plain,(
    ! [A_74286] :
      ( ~ r2_hidden('#skF_7',k1_tarski(A_74286))
      | r1_tarski(k2_relat_1('#skF_9'),k1_tarski(A_74286))
      | k1_funct_1('#skF_9','#skF_8') = A_74286 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42342,c_4])).

tff(c_26102,plain,(
    ! [B_36843,A_36844,A_7] :
      ( k1_funct_1(B_36843,A_36844) = A_7
      | ~ r1_tarski(k2_relat_1(B_36843),k1_tarski(A_7))
      | ~ r2_hidden(A_36844,k1_relat_1(B_36843))
      | ~ v1_funct_1(B_36843)
      | ~ v1_relat_1(B_36843) ) ),
    inference(resolution,[status(thm)],[c_26033,c_10])).

tff(c_43243,plain,(
    ! [A_36844,A_74286] :
      ( k1_funct_1('#skF_9',A_36844) = A_74286
      | ~ r2_hidden(A_36844,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden('#skF_7',k1_tarski(A_74286))
      | k1_funct_1('#skF_9','#skF_8') = A_74286 ) ),
    inference(resolution,[status(thm)],[c_43239,c_26102])).

tff(c_189657,plain,(
    ! [A_249245,A_249246] :
      ( k1_funct_1('#skF_9',A_249245) = A_249246
      | ~ r2_hidden(A_249245,'#skF_6')
      | ~ r2_hidden('#skF_7',k1_tarski(A_249246))
      | k1_funct_1('#skF_9','#skF_8') = A_249246 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_102,c_1159,c_43243])).

tff(c_189756,plain,(
    ! [A_249246] :
      ( ~ r2_hidden('#skF_7',k1_tarski(A_249246))
      | k1_funct_1('#skF_9','#skF_8') = A_249246
      | ~ r1_tarski('#skF_6','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_238,c_189657])).

tff(c_189795,plain,(
    ! [A_249591] :
      ( ~ r2_hidden('#skF_7',k1_tarski(A_249591))
      | k1_funct_1('#skF_9','#skF_8') = A_249591 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_189756])).

tff(c_189859,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_12,c_189795])).

tff(c_189867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_189859])).

tff(c_189868,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1158])).

tff(c_120,plain,(
    ! [B_54,A_55] :
      ( ~ r1_tarski(B_54,A_55)
      | ~ r2_hidden(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_127,plain,(
    ! [C_11] : ~ r1_tarski(k1_tarski(C_11),C_11) ),
    inference(resolution,[status(thm)],[c_12,c_120])).

tff(c_189906,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_189868,c_127])).

tff(c_189924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_189906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:25:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 49.84/36.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 49.84/36.72  
% 49.84/36.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 49.84/36.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 49.84/36.72  
% 49.84/36.72  %Foreground sorts:
% 49.84/36.72  
% 49.84/36.72  
% 49.84/36.72  %Background operators:
% 49.84/36.72  
% 49.84/36.72  
% 49.84/36.72  %Foreground operators:
% 49.84/36.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 49.84/36.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 49.84/36.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 49.84/36.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 49.84/36.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 49.84/36.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 49.84/36.72  tff('#skF_7', type, '#skF_7': $i).
% 49.84/36.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 49.84/36.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 49.84/36.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 49.84/36.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 49.84/36.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 49.84/36.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 49.84/36.72  tff('#skF_6', type, '#skF_6': $i).
% 49.84/36.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 49.84/36.72  tff('#skF_9', type, '#skF_9': $i).
% 49.84/36.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 49.84/36.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 49.84/36.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 49.84/36.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 49.84/36.72  tff('#skF_8', type, '#skF_8': $i).
% 49.84/36.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 49.84/36.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 49.84/36.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 49.84/36.72  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i) > $i).
% 49.84/36.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 49.84/36.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 49.84/36.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 49.84/36.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 49.84/36.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 49.84/36.72  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 49.84/36.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 49.84/36.72  
% 49.84/36.74  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 49.84/36.74  tff(f_132, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 49.84/36.74  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 49.84/36.74  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 49.84/36.74  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 49.84/36.74  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 49.84/36.74  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 49.84/36.74  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 49.84/36.74  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 49.84/36.74  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 49.84/36.74  tff(f_89, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 49.84/36.74  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 49.84/36.74  tff(c_94, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_132])).
% 49.84/36.74  tff(c_12, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 49.84/36.74  tff(c_160, plain, (![A_79, B_80]: (r2_hidden('#skF_1'(A_79, B_80), A_79) | r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.84/36.74  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.84/36.74  tff(c_172, plain, (![A_79]: (r1_tarski(A_79, A_79))), inference(resolution, [status(thm)], [c_160, c_4])).
% 49.84/36.74  tff(c_96, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 49.84/36.74  tff(c_214, plain, (![C_125, B_126, A_127]: (r2_hidden(C_125, B_126) | ~r2_hidden(C_125, A_127) | ~r1_tarski(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.84/36.74  tff(c_238, plain, (![B_126]: (r2_hidden('#skF_8', B_126) | ~r1_tarski('#skF_6', B_126))), inference(resolution, [status(thm)], [c_96, c_214])).
% 49.84/36.74  tff(c_98, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 49.84/36.74  tff(c_155, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 49.84/36.74  tff(c_159, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_98, c_155])).
% 49.84/36.74  tff(c_102, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_132])).
% 49.84/36.74  tff(c_100, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 49.84/36.74  tff(c_565, plain, (![A_218, B_219, C_220]: (k1_relset_1(A_218, B_219, C_220)=k1_relat_1(C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 49.84/36.74  tff(c_569, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_98, c_565])).
% 49.84/36.74  tff(c_1152, plain, (![B_332, A_333, C_334]: (k1_xboole_0=B_332 | k1_relset_1(A_333, B_332, C_334)=A_333 | ~v1_funct_2(C_334, A_333, B_332) | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(A_333, B_332))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 49.84/36.74  tff(c_1155, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_98, c_1152])).
% 49.84/36.74  tff(c_1158, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_569, c_1155])).
% 49.84/36.74  tff(c_1159, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_1158])).
% 49.84/36.74  tff(c_298, plain, (![C_140, B_141, A_142]: (v5_relat_1(C_140, B_141) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 49.84/36.74  tff(c_302, plain, (v5_relat_1('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_98, c_298])).
% 49.84/36.74  tff(c_68, plain, (![B_32, A_31]: (r1_tarski(k2_relat_1(B_32), A_31) | ~v5_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_76])).
% 49.84/36.74  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.84/36.74  tff(c_744, plain, (![A_297, B_298, B_299]: (r2_hidden('#skF_1'(A_297, B_298), B_299) | ~r1_tarski(A_297, B_299) | r1_tarski(A_297, B_298))), inference(resolution, [status(thm)], [c_6, c_214])).
% 49.84/36.74  tff(c_10, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 49.84/36.74  tff(c_1229, plain, (![A_341, A_342, B_343]: (A_341='#skF_1'(A_342, B_343) | ~r1_tarski(A_342, k1_tarski(A_341)) | r1_tarski(A_342, B_343))), inference(resolution, [status(thm)], [c_744, c_10])).
% 49.84/36.74  tff(c_14904, plain, (![A_21104, B_21105, B_21106]: (A_21104='#skF_1'(k2_relat_1(B_21105), B_21106) | r1_tarski(k2_relat_1(B_21105), B_21106) | ~v5_relat_1(B_21105, k1_tarski(A_21104)) | ~v1_relat_1(B_21105))), inference(resolution, [status(thm)], [c_68, c_1229])).
% 49.84/36.74  tff(c_14978, plain, (![B_21106]: ('#skF_1'(k2_relat_1('#skF_9'), B_21106)='#skF_7' | r1_tarski(k2_relat_1('#skF_9'), B_21106) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_302, c_14904])).
% 49.84/36.74  tff(c_14981, plain, (![B_21106]: ('#skF_1'(k2_relat_1('#skF_9'), B_21106)='#skF_7' | r1_tarski(k2_relat_1('#skF_9'), B_21106))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_14978])).
% 49.84/36.74  tff(c_705, plain, (![B_275, A_276]: (r2_hidden(k1_funct_1(B_275, A_276), k2_relat_1(B_275)) | ~r2_hidden(A_276, k1_relat_1(B_275)) | ~v1_funct_1(B_275) | ~v1_relat_1(B_275))), inference(cnfTransformation, [status(thm)], [f_84])).
% 49.84/36.74  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.84/36.74  tff(c_26033, plain, (![B_36843, A_36844, B_36845]: (r2_hidden(k1_funct_1(B_36843, A_36844), B_36845) | ~r1_tarski(k2_relat_1(B_36843), B_36845) | ~r2_hidden(A_36844, k1_relat_1(B_36843)) | ~v1_funct_1(B_36843) | ~v1_relat_1(B_36843))), inference(resolution, [status(thm)], [c_705, c_2])).
% 49.84/36.74  tff(c_39229, plain, (![B_66690, A_66691, A_66692]: (k1_funct_1(B_66690, A_66691)=A_66692 | ~r1_tarski(k2_relat_1(B_66690), k1_tarski(A_66692)) | ~r2_hidden(A_66691, k1_relat_1(B_66690)) | ~v1_funct_1(B_66690) | ~v1_relat_1(B_66690))), inference(resolution, [status(thm)], [c_26033, c_10])).
% 49.84/36.74  tff(c_39256, plain, (![A_66691, A_66692]: (k1_funct_1('#skF_9', A_66691)=A_66692 | ~r2_hidden(A_66691, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_66692))='#skF_7')), inference(resolution, [status(thm)], [c_14981, c_39229])).
% 49.84/36.74  tff(c_42177, plain, (![A_73637, A_73638]: (k1_funct_1('#skF_9', A_73637)=A_73638 | ~r2_hidden(A_73637, '#skF_6') | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_73638))='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_102, c_1159, c_39256])).
% 49.84/36.74  tff(c_42342, plain, (![A_73854]: (k1_funct_1('#skF_9', '#skF_8')=A_73854 | '#skF_1'(k2_relat_1('#skF_9'), k1_tarski(A_73854))='#skF_7')), inference(resolution, [status(thm)], [c_96, c_42177])).
% 49.84/36.74  tff(c_43239, plain, (![A_74286]: (~r2_hidden('#skF_7', k1_tarski(A_74286)) | r1_tarski(k2_relat_1('#skF_9'), k1_tarski(A_74286)) | k1_funct_1('#skF_9', '#skF_8')=A_74286)), inference(superposition, [status(thm), theory('equality')], [c_42342, c_4])).
% 49.84/36.74  tff(c_26102, plain, (![B_36843, A_36844, A_7]: (k1_funct_1(B_36843, A_36844)=A_7 | ~r1_tarski(k2_relat_1(B_36843), k1_tarski(A_7)) | ~r2_hidden(A_36844, k1_relat_1(B_36843)) | ~v1_funct_1(B_36843) | ~v1_relat_1(B_36843))), inference(resolution, [status(thm)], [c_26033, c_10])).
% 49.84/36.74  tff(c_43243, plain, (![A_36844, A_74286]: (k1_funct_1('#skF_9', A_36844)=A_74286 | ~r2_hidden(A_36844, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden('#skF_7', k1_tarski(A_74286)) | k1_funct_1('#skF_9', '#skF_8')=A_74286)), inference(resolution, [status(thm)], [c_43239, c_26102])).
% 49.84/36.74  tff(c_189657, plain, (![A_249245, A_249246]: (k1_funct_1('#skF_9', A_249245)=A_249246 | ~r2_hidden(A_249245, '#skF_6') | ~r2_hidden('#skF_7', k1_tarski(A_249246)) | k1_funct_1('#skF_9', '#skF_8')=A_249246)), inference(demodulation, [status(thm), theory('equality')], [c_159, c_102, c_1159, c_43243])).
% 49.84/36.74  tff(c_189756, plain, (![A_249246]: (~r2_hidden('#skF_7', k1_tarski(A_249246)) | k1_funct_1('#skF_9', '#skF_8')=A_249246 | ~r1_tarski('#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_238, c_189657])).
% 49.84/36.74  tff(c_189795, plain, (![A_249591]: (~r2_hidden('#skF_7', k1_tarski(A_249591)) | k1_funct_1('#skF_9', '#skF_8')=A_249591)), inference(demodulation, [status(thm), theory('equality')], [c_172, c_189756])).
% 49.84/36.74  tff(c_189859, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_12, c_189795])).
% 49.84/36.74  tff(c_189867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_189859])).
% 49.84/36.74  tff(c_189868, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1158])).
% 49.84/36.74  tff(c_120, plain, (![B_54, A_55]: (~r1_tarski(B_54, A_55) | ~r2_hidden(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_89])).
% 49.84/36.74  tff(c_127, plain, (![C_11]: (~r1_tarski(k1_tarski(C_11), C_11))), inference(resolution, [status(thm)], [c_12, c_120])).
% 49.84/36.74  tff(c_189906, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_189868, c_127])).
% 49.84/36.74  tff(c_189924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_189906])).
% 49.84/36.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 49.84/36.74  
% 49.84/36.74  Inference rules
% 49.84/36.74  ----------------------
% 49.84/36.74  #Ref     : 1
% 49.84/36.74  #Sup     : 37215
% 49.84/36.74  #Fact    : 554
% 49.84/36.74  #Define  : 0
% 49.84/36.74  #Split   : 81
% 49.84/36.74  #Chain   : 0
% 49.84/36.74  #Close   : 0
% 49.84/36.74  
% 49.84/36.74  Ordering : KBO
% 49.84/36.74  
% 49.84/36.74  Simplification rules
% 49.84/36.74  ----------------------
% 49.84/36.74  #Subsume      : 14827
% 49.84/36.74  #Demod        : 6800
% 49.84/36.74  #Tautology    : 5179
% 49.84/36.74  #SimpNegUnit  : 1769
% 49.84/36.74  #BackRed      : 257
% 49.84/36.74  
% 49.84/36.74  #Partial instantiations: 121254
% 49.84/36.74  #Strategies tried      : 1
% 49.84/36.74  
% 49.84/36.74  Timing (in seconds)
% 49.84/36.74  ----------------------
% 49.84/36.74  Preprocessing        : 0.45
% 49.84/36.74  Parsing              : 0.23
% 49.84/36.74  CNF conversion       : 0.03
% 49.84/36.74  Main loop            : 35.47
% 49.84/36.74  Inferencing          : 7.31
% 49.84/36.74  Reduction            : 10.38
% 49.84/36.74  Demodulation         : 7.00
% 49.84/36.74  BG Simplification    : 0.68
% 49.84/36.74  Subsumption          : 15.43
% 49.84/36.74  Abstraction          : 1.76
% 49.84/36.74  MUC search           : 0.00
% 49.84/36.74  Cooper               : 0.00
% 49.84/36.74  Total                : 35.95
% 49.84/36.74  Index Insertion      : 0.00
% 49.84/36.74  Index Deletion       : 0.00
% 49.84/36.74  Index Matching       : 0.00
% 49.84/36.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
