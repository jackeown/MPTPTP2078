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
% DateTime   : Thu Dec  3 10:16:41 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  132 (1436 expanded)
%              Number of leaves         :   35 ( 485 expanded)
%              Depth                    :   19
%              Number of atoms          :  211 (3857 expanded)
%              Number of equality atoms :   60 (1068 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_271,plain,(
    ! [A_108,B_109,D_110] :
      ( '#skF_4'(A_108,B_109,k1_funct_2(A_108,B_109),D_110) = D_110
      | ~ r2_hidden(D_110,k1_funct_2(A_108,B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_274,plain,(
    '#skF_4'('#skF_5','#skF_6',k1_funct_2('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_78,c_271])).

tff(c_305,plain,(
    ! [A_122,B_123,D_124] :
      ( v1_relat_1('#skF_4'(A_122,B_123,k1_funct_2(A_122,B_123),D_124))
      | ~ r2_hidden(D_124,k1_funct_2(A_122,B_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_308,plain,
    ( v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_305])).

tff(c_310,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_308])).

tff(c_315,plain,(
    ! [A_127,B_128,D_129] :
      ( k1_relat_1('#skF_4'(A_127,B_128,k1_funct_2(A_127,B_128),D_129)) = A_127
      | ~ r2_hidden(D_129,k1_funct_2(A_127,B_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_339,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_315])).

tff(c_343,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_339])).

tff(c_447,plain,(
    ! [A_138,B_139,D_140] :
      ( r1_tarski(k2_relat_1('#skF_4'(A_138,B_139,k1_funct_2(A_138,B_139),D_140)),B_139)
      | ~ r2_hidden(D_140,k1_funct_2(A_138,B_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_463,plain,
    ( r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_447])).

tff(c_469,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_463])).

tff(c_502,plain,(
    ! [C_152,A_153,B_154] :
      ( m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154)))
      | ~ r1_tarski(k2_relat_1(C_152),B_154)
      | ~ r1_tarski(k1_relat_1(C_152),A_153)
      | ~ v1_relat_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_76,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_149,plain,(
    ~ v1_funct_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_210,plain,(
    ! [A_79,B_80,D_81] :
      ( '#skF_4'(A_79,B_80,k1_funct_2(A_79,B_80),D_81) = D_81
      | ~ r2_hidden(D_81,k1_funct_2(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_213,plain,(
    '#skF_4'('#skF_5','#skF_6',k1_funct_2('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_78,c_210])).

tff(c_219,plain,(
    ! [A_84,B_85,D_86] :
      ( v1_funct_1('#skF_4'(A_84,B_85,k1_funct_2(A_84,B_85),D_86))
      | ~ r2_hidden(D_86,k1_funct_2(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_222,plain,
    ( v1_funct_1('#skF_7')
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_219])).

tff(c_224,plain,(
    v1_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_222])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_224])).

tff(c_227,plain,
    ( ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_248,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_508,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_7'),'#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_502,c_248])).

tff(c_525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_6,c_343,c_469,c_508])).

tff(c_526,plain,(
    ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_585,plain,(
    ! [A_172,B_173,D_174] :
      ( '#skF_4'(A_172,B_173,k1_funct_2(A_172,B_173),D_174) = D_174
      | ~ r2_hidden(D_174,k1_funct_2(A_172,B_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_588,plain,(
    '#skF_4'('#skF_5','#skF_6',k1_funct_2('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_78,c_585])).

tff(c_606,plain,(
    ! [A_183,B_184,D_185] :
      ( k1_relat_1('#skF_4'(A_183,B_184,k1_funct_2(A_183,B_184),D_185)) = A_183
      | ~ r2_hidden(D_185,k1_funct_2(A_183,B_184)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_627,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_588,c_606])).

tff(c_631,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_627])).

tff(c_527,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_550,plain,(
    ! [A_161,B_162,C_163] :
      ( k1_relset_1(A_161,B_162,C_163) = k1_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_560,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_527,c_550])).

tff(c_632,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_560])).

tff(c_1390,plain,(
    ! [B_295,C_296,A_297] :
      ( k1_xboole_0 = B_295
      | v1_funct_2(C_296,A_297,B_295)
      | k1_relset_1(A_297,B_295,C_296) != A_297
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(A_297,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1396,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2('#skF_7','#skF_5','#skF_6')
    | k1_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_527,c_1390])).

tff(c_1406,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_1396])).

tff(c_1407,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_526,c_1406])).

tff(c_50,plain,(
    ! [A_20,B_21,D_36] :
      ( v1_relat_1('#skF_4'(A_20,B_21,k1_funct_2(A_20,B_21),D_36))
      | ~ r2_hidden(D_36,k1_funct_2(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_593,plain,
    ( v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_588,c_50])).

tff(c_597,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_593])).

tff(c_939,plain,(
    ! [B_235,C_236,A_237] :
      ( k1_xboole_0 = B_235
      | v1_funct_2(C_236,A_237,B_235)
      | k1_relset_1(A_237,B_235,C_236) != A_237
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_945,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2('#skF_7','#skF_5','#skF_6')
    | k1_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_527,c_939])).

tff(c_955,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_945])).

tff(c_956,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_526,c_955])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_982,plain,(
    ! [A_3] : r1_tarski('#skF_6',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_8])).

tff(c_752,plain,(
    ! [A_199,B_200,D_201] :
      ( r1_tarski(k2_relat_1('#skF_4'(A_199,B_200,k1_funct_2(A_199,B_200),D_201)),B_200)
      | ~ r2_hidden(D_201,k1_funct_2(A_199,B_200)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_768,plain,
    ( r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_588,c_752])).

tff(c_774,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_768])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_781,plain,
    ( k2_relat_1('#skF_7') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_774,c_2])).

tff(c_782,plain,(
    ~ r1_tarski('#skF_6',k2_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_781])).

tff(c_989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_782])).

tff(c_990,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_781])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1003,plain,(
    ! [C_238,A_239,B_240] :
      ( m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240)))
      | ~ r1_tarski(k2_relat_1(C_238),B_240)
      | ~ r1_tarski(k1_relat_1(C_238),A_239)
      | ~ v1_relat_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1110,plain,(
    ! [C_257,A_258] :
      ( m1_subset_1(C_257,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_257),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_257),A_258)
      | ~ v1_relat_1(C_257) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1003])).

tff(c_1112,plain,(
    ! [A_258] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_6',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_7'),A_258)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_990,c_1110])).

tff(c_1117,plain,(
    ! [A_258] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_6',k1_xboole_0)
      | ~ r1_tarski('#skF_5',A_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_631,c_1112])).

tff(c_1119,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1117])).

tff(c_1422,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_1119])).

tff(c_1440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1422])).

tff(c_1442,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1117])).

tff(c_119,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(B_46,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_119])).

tff(c_1448,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1442,c_128])).

tff(c_1441,plain,(
    ! [A_258] :
      ( ~ r1_tarski('#skF_5',A_258)
      | m1_subset_1('#skF_7',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_1117])).

tff(c_1473,plain,(
    ! [A_258] :
      ( ~ r1_tarski('#skF_5',A_258)
      | m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1441])).

tff(c_1494,plain,(
    ! [A_300] : ~ r1_tarski('#skF_5',A_300) ),
    inference(splitLeft,[status(thm)],[c_1473])).

tff(c_1499,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_1494])).

tff(c_1500,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1473])).

tff(c_142,plain,(
    ! [C_49,A_50,B_51] :
      ( v4_relat_1(C_49,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_145,plain,(
    ! [C_49,A_4] :
      ( v4_relat_1(C_49,A_4)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_142])).

tff(c_1634,plain,(
    ! [C_315,A_316] :
      ( v4_relat_1(C_315,A_316)
      | ~ m1_subset_1(C_315,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_145])).

tff(c_1637,plain,(
    ! [A_316] : v4_relat_1('#skF_7',A_316) ),
    inference(resolution,[status(thm)],[c_1500,c_1634])).

tff(c_18,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_645,plain,(
    ! [A_6] :
      ( r1_tarski('#skF_5',A_6)
      | ~ v4_relat_1('#skF_7',A_6)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_18])).

tff(c_655,plain,(
    ! [A_6] :
      ( r1_tarski('#skF_5',A_6)
      | ~ v4_relat_1('#skF_7',A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_645])).

tff(c_1645,plain,(
    ! [A_318] : r1_tarski('#skF_5',A_318) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1637,c_655])).

tff(c_1463,plain,(
    ! [A_3] :
      ( A_3 = '#skF_6'
      | ~ r1_tarski(A_3,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1448,c_128])).

tff(c_1656,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1645,c_1463])).

tff(c_1662,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1656,c_631])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_559,plain,(
    ! [B_5,C_163] :
      ( k1_relset_1(k1_xboole_0,B_5,C_163) = k1_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_550])).

tff(c_1811,plain,(
    ! [B_330,C_331] :
      ( k1_relset_1('#skF_6',B_330,C_331) = k1_relat_1(C_331)
      | ~ m1_subset_1(C_331,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1448,c_559])).

tff(c_1813,plain,(
    ! [B_330] : k1_relset_1('#skF_6',B_330,'#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1500,c_1811])).

tff(c_1815,plain,(
    ! [B_330] : k1_relset_1('#skF_6',B_330,'#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1662,c_1813])).

tff(c_32,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_80,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_32])).

tff(c_1855,plain,(
    ! [C_343,B_344] :
      ( v1_funct_2(C_343,'#skF_6',B_344)
      | k1_relset_1('#skF_6',B_344,C_343) != '#skF_6'
      | ~ m1_subset_1(C_343,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1448,c_1448,c_1448,c_80])).

tff(c_1857,plain,(
    ! [B_344] :
      ( v1_funct_2('#skF_7','#skF_6',B_344)
      | k1_relset_1('#skF_6',B_344,'#skF_7') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_1500,c_1855])).

tff(c_1860,plain,(
    ! [B_344] : v1_funct_2('#skF_7','#skF_6',B_344) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1815,c_1857])).

tff(c_1664,plain,(
    ~ v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1656,c_526])).

tff(c_1863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1860,c_1664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.67  
% 3.95/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.68  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.95/1.68  
% 3.95/1.68  %Foreground sorts:
% 3.95/1.68  
% 3.95/1.68  
% 3.95/1.68  %Background operators:
% 3.95/1.68  
% 3.95/1.68  
% 3.95/1.68  %Foreground operators:
% 3.95/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.95/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.95/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.68  tff('#skF_7', type, '#skF_7': $i).
% 3.95/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.95/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.95/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.95/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.95/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.95/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.95/1.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.95/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.68  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.95/1.68  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 3.95/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.95/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.95/1.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.95/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.95/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.95/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.68  
% 4.11/1.70  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.11/1.70  tff(f_106, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 4.11/1.70  tff(f_97, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 4.11/1.70  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 4.11/1.70  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.11/1.70  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.11/1.70  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.11/1.70  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.11/1.70  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.11/1.70  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.11/1.70  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.11/1.70  tff(c_78, plain, (r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.11/1.70  tff(c_271, plain, (![A_108, B_109, D_110]: ('#skF_4'(A_108, B_109, k1_funct_2(A_108, B_109), D_110)=D_110 | ~r2_hidden(D_110, k1_funct_2(A_108, B_109)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.11/1.70  tff(c_274, plain, ('#skF_4'('#skF_5', '#skF_6', k1_funct_2('#skF_5', '#skF_6'), '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_78, c_271])).
% 4.11/1.70  tff(c_305, plain, (![A_122, B_123, D_124]: (v1_relat_1('#skF_4'(A_122, B_123, k1_funct_2(A_122, B_123), D_124)) | ~r2_hidden(D_124, k1_funct_2(A_122, B_123)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.11/1.70  tff(c_308, plain, (v1_relat_1('#skF_7') | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_305])).
% 4.11/1.70  tff(c_310, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_308])).
% 4.11/1.70  tff(c_315, plain, (![A_127, B_128, D_129]: (k1_relat_1('#skF_4'(A_127, B_128, k1_funct_2(A_127, B_128), D_129))=A_127 | ~r2_hidden(D_129, k1_funct_2(A_127, B_128)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.11/1.70  tff(c_339, plain, (k1_relat_1('#skF_7')='#skF_5' | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_315])).
% 4.11/1.70  tff(c_343, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_339])).
% 4.11/1.70  tff(c_447, plain, (![A_138, B_139, D_140]: (r1_tarski(k2_relat_1('#skF_4'(A_138, B_139, k1_funct_2(A_138, B_139), D_140)), B_139) | ~r2_hidden(D_140, k1_funct_2(A_138, B_139)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.11/1.70  tff(c_463, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_447])).
% 4.11/1.70  tff(c_469, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_463])).
% 4.11/1.70  tff(c_502, plain, (![C_152, A_153, B_154]: (m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))) | ~r1_tarski(k2_relat_1(C_152), B_154) | ~r1_tarski(k1_relat_1(C_152), A_153) | ~v1_relat_1(C_152))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.11/1.70  tff(c_76, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.11/1.70  tff(c_149, plain, (~v1_funct_1('#skF_7')), inference(splitLeft, [status(thm)], [c_76])).
% 4.11/1.70  tff(c_210, plain, (![A_79, B_80, D_81]: ('#skF_4'(A_79, B_80, k1_funct_2(A_79, B_80), D_81)=D_81 | ~r2_hidden(D_81, k1_funct_2(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.11/1.70  tff(c_213, plain, ('#skF_4'('#skF_5', '#skF_6', k1_funct_2('#skF_5', '#skF_6'), '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_78, c_210])).
% 4.11/1.70  tff(c_219, plain, (![A_84, B_85, D_86]: (v1_funct_1('#skF_4'(A_84, B_85, k1_funct_2(A_84, B_85), D_86)) | ~r2_hidden(D_86, k1_funct_2(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.11/1.70  tff(c_222, plain, (v1_funct_1('#skF_7') | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_219])).
% 4.11/1.70  tff(c_224, plain, (v1_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_222])).
% 4.11/1.70  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_224])).
% 4.11/1.70  tff(c_227, plain, (~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_76])).
% 4.11/1.70  tff(c_248, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_227])).
% 4.11/1.70  tff(c_508, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r1_tarski(k1_relat_1('#skF_7'), '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_502, c_248])).
% 4.11/1.70  tff(c_525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_310, c_6, c_343, c_469, c_508])).
% 4.11/1.70  tff(c_526, plain, (~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_227])).
% 4.11/1.70  tff(c_585, plain, (![A_172, B_173, D_174]: ('#skF_4'(A_172, B_173, k1_funct_2(A_172, B_173), D_174)=D_174 | ~r2_hidden(D_174, k1_funct_2(A_172, B_173)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.11/1.70  tff(c_588, plain, ('#skF_4'('#skF_5', '#skF_6', k1_funct_2('#skF_5', '#skF_6'), '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_78, c_585])).
% 4.11/1.70  tff(c_606, plain, (![A_183, B_184, D_185]: (k1_relat_1('#skF_4'(A_183, B_184, k1_funct_2(A_183, B_184), D_185))=A_183 | ~r2_hidden(D_185, k1_funct_2(A_183, B_184)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.11/1.70  tff(c_627, plain, (k1_relat_1('#skF_7')='#skF_5' | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_588, c_606])).
% 4.11/1.70  tff(c_631, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_627])).
% 4.11/1.70  tff(c_527, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_227])).
% 4.11/1.70  tff(c_550, plain, (![A_161, B_162, C_163]: (k1_relset_1(A_161, B_162, C_163)=k1_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.11/1.70  tff(c_560, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_527, c_550])).
% 4.11/1.70  tff(c_632, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_631, c_560])).
% 4.11/1.70  tff(c_1390, plain, (![B_295, C_296, A_297]: (k1_xboole_0=B_295 | v1_funct_2(C_296, A_297, B_295) | k1_relset_1(A_297, B_295, C_296)!=A_297 | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(A_297, B_295))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.11/1.70  tff(c_1396, plain, (k1_xboole_0='#skF_6' | v1_funct_2('#skF_7', '#skF_5', '#skF_6') | k1_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_5'), inference(resolution, [status(thm)], [c_527, c_1390])).
% 4.11/1.70  tff(c_1406, plain, (k1_xboole_0='#skF_6' | v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_632, c_1396])).
% 4.11/1.70  tff(c_1407, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_526, c_1406])).
% 4.11/1.70  tff(c_50, plain, (![A_20, B_21, D_36]: (v1_relat_1('#skF_4'(A_20, B_21, k1_funct_2(A_20, B_21), D_36)) | ~r2_hidden(D_36, k1_funct_2(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.11/1.70  tff(c_593, plain, (v1_relat_1('#skF_7') | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_588, c_50])).
% 4.11/1.70  tff(c_597, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_593])).
% 4.11/1.70  tff(c_939, plain, (![B_235, C_236, A_237]: (k1_xboole_0=B_235 | v1_funct_2(C_236, A_237, B_235) | k1_relset_1(A_237, B_235, C_236)!=A_237 | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_235))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.11/1.70  tff(c_945, plain, (k1_xboole_0='#skF_6' | v1_funct_2('#skF_7', '#skF_5', '#skF_6') | k1_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_5'), inference(resolution, [status(thm)], [c_527, c_939])).
% 4.11/1.70  tff(c_955, plain, (k1_xboole_0='#skF_6' | v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_632, c_945])).
% 4.11/1.70  tff(c_956, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_526, c_955])).
% 4.11/1.70  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.11/1.70  tff(c_982, plain, (![A_3]: (r1_tarski('#skF_6', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_956, c_8])).
% 4.11/1.70  tff(c_752, plain, (![A_199, B_200, D_201]: (r1_tarski(k2_relat_1('#skF_4'(A_199, B_200, k1_funct_2(A_199, B_200), D_201)), B_200) | ~r2_hidden(D_201, k1_funct_2(A_199, B_200)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.11/1.70  tff(c_768, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_588, c_752])).
% 4.11/1.70  tff(c_774, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_768])).
% 4.11/1.70  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.11/1.70  tff(c_781, plain, (k2_relat_1('#skF_7')='#skF_6' | ~r1_tarski('#skF_6', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_774, c_2])).
% 4.11/1.70  tff(c_782, plain, (~r1_tarski('#skF_6', k2_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_781])).
% 4.11/1.70  tff(c_989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_982, c_782])).
% 4.11/1.70  tff(c_990, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_781])).
% 4.11/1.70  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.11/1.70  tff(c_1003, plain, (![C_238, A_239, B_240]: (m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))) | ~r1_tarski(k2_relat_1(C_238), B_240) | ~r1_tarski(k1_relat_1(C_238), A_239) | ~v1_relat_1(C_238))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.11/1.70  tff(c_1110, plain, (![C_257, A_258]: (m1_subset_1(C_257, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_257), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_257), A_258) | ~v1_relat_1(C_257))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1003])).
% 4.11/1.70  tff(c_1112, plain, (![A_258]: (m1_subset_1('#skF_7', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_6', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_7'), A_258) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_990, c_1110])).
% 4.11/1.70  tff(c_1117, plain, (![A_258]: (m1_subset_1('#skF_7', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_6', k1_xboole_0) | ~r1_tarski('#skF_5', A_258))), inference(demodulation, [status(thm), theory('equality')], [c_597, c_631, c_1112])).
% 4.11/1.70  tff(c_1119, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1117])).
% 4.11/1.70  tff(c_1422, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1407, c_1119])).
% 4.11/1.70  tff(c_1440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1422])).
% 4.11/1.70  tff(c_1442, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1117])).
% 4.11/1.70  tff(c_119, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(B_46, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.11/1.70  tff(c_128, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_119])).
% 4.11/1.70  tff(c_1448, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1442, c_128])).
% 4.11/1.70  tff(c_1441, plain, (![A_258]: (~r1_tarski('#skF_5', A_258) | m1_subset_1('#skF_7', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_1117])).
% 4.11/1.70  tff(c_1473, plain, (![A_258]: (~r1_tarski('#skF_5', A_258) | m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1441])).
% 4.11/1.70  tff(c_1494, plain, (![A_300]: (~r1_tarski('#skF_5', A_300))), inference(splitLeft, [status(thm)], [c_1473])).
% 4.11/1.70  tff(c_1499, plain, $false, inference(resolution, [status(thm)], [c_6, c_1494])).
% 4.11/1.70  tff(c_1500, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1473])).
% 4.11/1.70  tff(c_142, plain, (![C_49, A_50, B_51]: (v4_relat_1(C_49, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.11/1.70  tff(c_145, plain, (![C_49, A_4]: (v4_relat_1(C_49, A_4) | ~m1_subset_1(C_49, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_142])).
% 4.11/1.70  tff(c_1634, plain, (![C_315, A_316]: (v4_relat_1(C_315, A_316) | ~m1_subset_1(C_315, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_145])).
% 4.11/1.70  tff(c_1637, plain, (![A_316]: (v4_relat_1('#skF_7', A_316))), inference(resolution, [status(thm)], [c_1500, c_1634])).
% 4.11/1.70  tff(c_18, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.11/1.70  tff(c_645, plain, (![A_6]: (r1_tarski('#skF_5', A_6) | ~v4_relat_1('#skF_7', A_6) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_631, c_18])).
% 4.11/1.70  tff(c_655, plain, (![A_6]: (r1_tarski('#skF_5', A_6) | ~v4_relat_1('#skF_7', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_597, c_645])).
% 4.11/1.70  tff(c_1645, plain, (![A_318]: (r1_tarski('#skF_5', A_318))), inference(demodulation, [status(thm), theory('equality')], [c_1637, c_655])).
% 4.11/1.70  tff(c_1463, plain, (![A_3]: (A_3='#skF_6' | ~r1_tarski(A_3, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1448, c_128])).
% 4.11/1.70  tff(c_1656, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1645, c_1463])).
% 4.11/1.70  tff(c_1662, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1656, c_631])).
% 4.11/1.70  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.11/1.70  tff(c_559, plain, (![B_5, C_163]: (k1_relset_1(k1_xboole_0, B_5, C_163)=k1_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_550])).
% 4.11/1.70  tff(c_1811, plain, (![B_330, C_331]: (k1_relset_1('#skF_6', B_330, C_331)=k1_relat_1(C_331) | ~m1_subset_1(C_331, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1448, c_559])).
% 4.11/1.70  tff(c_1813, plain, (![B_330]: (k1_relset_1('#skF_6', B_330, '#skF_7')=k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1500, c_1811])).
% 4.11/1.70  tff(c_1815, plain, (![B_330]: (k1_relset_1('#skF_6', B_330, '#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1662, c_1813])).
% 4.11/1.70  tff(c_32, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.11/1.70  tff(c_80, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_32])).
% 4.11/1.70  tff(c_1855, plain, (![C_343, B_344]: (v1_funct_2(C_343, '#skF_6', B_344) | k1_relset_1('#skF_6', B_344, C_343)!='#skF_6' | ~m1_subset_1(C_343, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1448, c_1448, c_1448, c_80])).
% 4.11/1.70  tff(c_1857, plain, (![B_344]: (v1_funct_2('#skF_7', '#skF_6', B_344) | k1_relset_1('#skF_6', B_344, '#skF_7')!='#skF_6')), inference(resolution, [status(thm)], [c_1500, c_1855])).
% 4.11/1.70  tff(c_1860, plain, (![B_344]: (v1_funct_2('#skF_7', '#skF_6', B_344))), inference(demodulation, [status(thm), theory('equality')], [c_1815, c_1857])).
% 4.11/1.70  tff(c_1664, plain, (~v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1656, c_526])).
% 4.11/1.70  tff(c_1863, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1860, c_1664])).
% 4.11/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.70  
% 4.11/1.70  Inference rules
% 4.11/1.70  ----------------------
% 4.11/1.70  #Ref     : 0
% 4.11/1.70  #Sup     : 369
% 4.11/1.70  #Fact    : 0
% 4.11/1.70  #Define  : 0
% 4.11/1.70  #Split   : 15
% 4.11/1.70  #Chain   : 0
% 4.11/1.70  #Close   : 0
% 4.11/1.70  
% 4.11/1.70  Ordering : KBO
% 4.11/1.70  
% 4.11/1.70  Simplification rules
% 4.11/1.70  ----------------------
% 4.11/1.70  #Subsume      : 53
% 4.11/1.70  #Demod        : 383
% 4.11/1.70  #Tautology    : 163
% 4.11/1.70  #SimpNegUnit  : 7
% 4.11/1.70  #BackRed      : 95
% 4.11/1.70  
% 4.11/1.70  #Partial instantiations: 0
% 4.11/1.70  #Strategies tried      : 1
% 4.11/1.70  
% 4.11/1.70  Timing (in seconds)
% 4.11/1.70  ----------------------
% 4.11/1.70  Preprocessing        : 0.36
% 4.11/1.70  Parsing              : 0.17
% 4.11/1.70  CNF conversion       : 0.03
% 4.11/1.70  Main loop            : 0.58
% 4.11/1.70  Inferencing          : 0.21
% 4.11/1.70  Reduction            : 0.18
% 4.11/1.70  Demodulation         : 0.12
% 4.11/1.70  BG Simplification    : 0.03
% 4.11/1.70  Subsumption          : 0.10
% 4.11/1.70  Abstraction          : 0.03
% 4.11/1.70  MUC search           : 0.00
% 4.11/1.70  Cooper               : 0.00
% 4.11/1.70  Total                : 0.98
% 4.11/1.70  Index Insertion      : 0.00
% 4.11/1.70  Index Deletion       : 0.00
% 4.11/1.70  Index Matching       : 0.00
% 4.11/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
