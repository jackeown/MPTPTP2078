%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:19 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 419 expanded)
%              Number of leaves         :   33 ( 162 expanded)
%              Depth                    :   17
%              Number of atoms          :  187 (1264 expanded)
%              Number of equality atoms :   55 ( 263 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_79,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_83,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_79])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_32,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26),A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_128,plain,(
    ! [B_88,A_89] :
      ( r2_hidden(k4_tarski(B_88,k1_funct_1(A_89,B_88)),A_89)
      | ~ r2_hidden(B_88,k1_relat_1(A_89))
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [C_17,A_14,B_15] :
      ( r2_hidden(C_17,A_14)
      | ~ r2_hidden(C_17,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_160,plain,(
    ! [B_102,A_103,A_104] :
      ( r2_hidden(k4_tarski(B_102,k1_funct_1(A_103,B_102)),A_104)
      | ~ m1_subset_1(A_103,k1_zfmisc_1(A_104))
      | ~ r2_hidden(B_102,k1_relat_1(A_103))
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_128,c_18])).

tff(c_14,plain,(
    ! [C_10,A_8,B_9,D_11] :
      ( C_10 = A_8
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(k1_tarski(C_10),D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_178,plain,(
    ! [C_105,B_106,A_107,D_108] :
      ( C_105 = B_106
      | ~ m1_subset_1(A_107,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_105),D_108)))
      | ~ r2_hidden(B_106,k1_relat_1(A_107))
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_160,c_14])).

tff(c_180,plain,(
    ! [B_106] :
      ( B_106 = '#skF_2'
      | ~ r2_hidden(B_106,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_178])).

tff(c_184,plain,(
    ! [B_109] :
      ( B_109 = '#skF_2'
      | ~ r2_hidden(B_109,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_44,c_180])).

tff(c_211,plain,
    ( '#skF_1'(k1_relat_1('#skF_4')) = '#skF_2'
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_184])).

tff(c_236,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_26,plain,(
    ! [A_18,B_21] :
      ( k1_funct_1(A_18,B_21) = k1_xboole_0
      | r2_hidden(B_21,k1_relat_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_243,plain,(
    ! [B_21] :
      ( k1_funct_1('#skF_4',B_21) = k1_xboole_0
      | r2_hidden(B_21,k1_xboole_0)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_26])).

tff(c_249,plain,(
    ! [B_21] :
      ( k1_funct_1('#skF_4',B_21) = k1_xboole_0
      | r2_hidden(B_21,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_44,c_243])).

tff(c_12,plain,(
    ! [B_9,D_11,A_8,C_10] :
      ( r2_hidden(B_9,D_11)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(k1_tarski(C_10),D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_388,plain,(
    ! [A_139,B_140,D_141,C_142] :
      ( r2_hidden(k1_funct_1(A_139,B_140),D_141)
      | ~ m1_subset_1(A_139,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_142),D_141)))
      | ~ r2_hidden(B_140,k1_relat_1(A_139))
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(resolution,[status(thm)],[c_160,c_12])).

tff(c_390,plain,(
    ! [B_140] :
      ( r2_hidden(k1_funct_1('#skF_4',B_140),'#skF_3')
      | ~ r2_hidden(B_140,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_388])).

tff(c_394,plain,(
    ! [B_143] :
      ( r2_hidden(k1_funct_1('#skF_4',B_143),'#skF_3')
      | ~ r2_hidden(B_143,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_44,c_236,c_390])).

tff(c_36,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_407,plain,(
    ~ r2_hidden('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_394,c_36])).

tff(c_443,plain,(
    k1_funct_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_249,c_407])).

tff(c_444,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_36])).

tff(c_42,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_63,plain,(
    ! [A_54,B_55] : k2_xboole_0(k1_tarski(A_54),B_55) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,(
    ! [A_54] : k1_tarski(A_54) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_63])).

tff(c_196,plain,(
    ! [B_21] :
      ( B_21 = '#skF_2'
      | k1_funct_1('#skF_4',B_21) = k1_xboole_0
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_184])).

tff(c_209,plain,(
    ! [B_21] :
      ( B_21 = '#skF_2'
      | k1_funct_1('#skF_4',B_21) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_44,c_196])).

tff(c_333,plain,(
    ! [D_124,C_125,B_126,A_127] :
      ( r2_hidden(k1_funct_1(D_124,C_125),B_126)
      | k1_xboole_0 = B_126
      | ~ r2_hidden(C_125,A_127)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126)))
      | ~ v1_funct_2(D_124,A_127,B_126)
      | ~ v1_funct_1(D_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_408,plain,(
    ! [D_144,A_145,B_146] :
      ( r2_hidden(k1_funct_1(D_144,'#skF_1'(A_145)),B_146)
      | k1_xboole_0 = B_146
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_2(D_144,A_145,B_146)
      | ~ v1_funct_1(D_144)
      | k1_xboole_0 = A_145 ) ),
    inference(resolution,[status(thm)],[c_32,c_333])).

tff(c_430,plain,(
    ! [B_146,A_145] :
      ( r2_hidden(k1_xboole_0,B_146)
      | k1_xboole_0 = B_146
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_2('#skF_4',A_145,B_146)
      | ~ v1_funct_1('#skF_4')
      | k1_xboole_0 = A_145
      | '#skF_1'(A_145) = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_408])).

tff(c_532,plain,(
    ! [B_157,A_158] :
      ( r2_hidden(k1_xboole_0,B_157)
      | k1_xboole_0 = B_157
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_158,B_157)))
      | ~ v1_funct_2('#skF_4',A_158,B_157)
      | k1_xboole_0 = A_158
      | '#skF_1'(A_158) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_430])).

tff(c_535,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
    | k1_tarski('#skF_2') = k1_xboole_0
    | '#skF_1'(k1_tarski('#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_532])).

tff(c_538,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_2') = k1_xboole_0
    | '#skF_1'(k1_tarski('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_535])).

tff(c_539,plain,(
    '#skF_1'(k1_tarski('#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_38,c_444,c_538])).

tff(c_357,plain,(
    ! [D_124,A_26,B_126] :
      ( r2_hidden(k1_funct_1(D_124,'#skF_1'(A_26)),B_126)
      | k1_xboole_0 = B_126
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_26,B_126)))
      | ~ v1_funct_2(D_124,A_26,B_126)
      | ~ v1_funct_1(D_124)
      | k1_xboole_0 = A_26 ) ),
    inference(resolution,[status(thm)],[c_32,c_333])).

tff(c_545,plain,(
    ! [D_124,B_126] :
      ( r2_hidden(k1_funct_1(D_124,'#skF_2'),B_126)
      | k1_xboole_0 = B_126
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),B_126)))
      | ~ v1_funct_2(D_124,k1_tarski('#skF_2'),B_126)
      | ~ v1_funct_1(D_124)
      | k1_tarski('#skF_2') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_357])).

tff(c_1543,plain,(
    ! [D_275,B_276] :
      ( r2_hidden(k1_funct_1(D_275,'#skF_2'),B_276)
      | k1_xboole_0 = B_276
      | ~ m1_subset_1(D_275,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),B_276)))
      | ~ v1_funct_2(D_275,k1_tarski('#skF_2'),B_276)
      | ~ v1_funct_1(D_275) ) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_545])).

tff(c_1546,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1543])).

tff(c_1549,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_443,c_1546])).

tff(c_1551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_444,c_1549])).

tff(c_1553,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_1552,plain,(
    '#skF_1'(k1_relat_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_1563,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1552,c_32])).

tff(c_1568,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1553,c_1563])).

tff(c_1878,plain,(
    ! [A_338,B_339,D_340,C_341] :
      ( r2_hidden(k1_funct_1(A_338,B_339),D_340)
      | ~ m1_subset_1(A_338,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_341),D_340)))
      | ~ r2_hidden(B_339,k1_relat_1(A_338))
      | ~ v1_funct_1(A_338)
      | ~ v1_relat_1(A_338) ) ),
    inference(resolution,[status(thm)],[c_160,c_12])).

tff(c_1880,plain,(
    ! [B_339] :
      ( r2_hidden(k1_funct_1('#skF_4',B_339),'#skF_3')
      | ~ r2_hidden(B_339,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_1878])).

tff(c_1884,plain,(
    ! [B_342] :
      ( r2_hidden(k1_funct_1('#skF_4',B_342),'#skF_3')
      | ~ r2_hidden(B_342,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_44,c_1880])).

tff(c_1889,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1884,c_36])).

tff(c_1897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1568,c_1889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:17:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.89  
% 4.76/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.89  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.76/1.89  
% 4.76/1.89  %Foreground sorts:
% 4.76/1.89  
% 4.76/1.89  
% 4.76/1.89  %Background operators:
% 4.76/1.89  
% 4.76/1.89  
% 4.76/1.89  %Foreground operators:
% 4.76/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.76/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.76/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.76/1.89  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.76/1.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.76/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.76/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.76/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.76/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.76/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.76/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.76/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.76/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.76/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.76/1.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.76/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.76/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.76/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.76/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.76/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.76/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.76/1.89  
% 4.76/1.91  tff(f_116, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 4.76/1.91  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.76/1.91  tff(f_92, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 4.76/1.91  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 4.76/1.91  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.76/1.91  tff(f_39, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 4.76/1.91  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.76/1.91  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.76/1.91  tff(f_104, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 4.76/1.91  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.76/1.91  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.76/1.91  tff(c_79, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.76/1.91  tff(c_83, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_79])).
% 4.76/1.91  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.76/1.91  tff(c_32, plain, (![A_26]: (r2_hidden('#skF_1'(A_26), A_26) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.76/1.91  tff(c_128, plain, (![B_88, A_89]: (r2_hidden(k4_tarski(B_88, k1_funct_1(A_89, B_88)), A_89) | ~r2_hidden(B_88, k1_relat_1(A_89)) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.76/1.91  tff(c_18, plain, (![C_17, A_14, B_15]: (r2_hidden(C_17, A_14) | ~r2_hidden(C_17, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.76/1.91  tff(c_160, plain, (![B_102, A_103, A_104]: (r2_hidden(k4_tarski(B_102, k1_funct_1(A_103, B_102)), A_104) | ~m1_subset_1(A_103, k1_zfmisc_1(A_104)) | ~r2_hidden(B_102, k1_relat_1(A_103)) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_128, c_18])).
% 4.76/1.91  tff(c_14, plain, (![C_10, A_8, B_9, D_11]: (C_10=A_8 | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(k1_tarski(C_10), D_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.76/1.91  tff(c_178, plain, (![C_105, B_106, A_107, D_108]: (C_105=B_106 | ~m1_subset_1(A_107, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_105), D_108))) | ~r2_hidden(B_106, k1_relat_1(A_107)) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_160, c_14])).
% 4.76/1.91  tff(c_180, plain, (![B_106]: (B_106='#skF_2' | ~r2_hidden(B_106, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_178])).
% 4.76/1.91  tff(c_184, plain, (![B_109]: (B_109='#skF_2' | ~r2_hidden(B_109, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_44, c_180])).
% 4.76/1.91  tff(c_211, plain, ('#skF_1'(k1_relat_1('#skF_4'))='#skF_2' | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_184])).
% 4.76/1.91  tff(c_236, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_211])).
% 4.76/1.91  tff(c_26, plain, (![A_18, B_21]: (k1_funct_1(A_18, B_21)=k1_xboole_0 | r2_hidden(B_21, k1_relat_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.76/1.91  tff(c_243, plain, (![B_21]: (k1_funct_1('#skF_4', B_21)=k1_xboole_0 | r2_hidden(B_21, k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_236, c_26])).
% 4.76/1.91  tff(c_249, plain, (![B_21]: (k1_funct_1('#skF_4', B_21)=k1_xboole_0 | r2_hidden(B_21, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_44, c_243])).
% 4.76/1.91  tff(c_12, plain, (![B_9, D_11, A_8, C_10]: (r2_hidden(B_9, D_11) | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(k1_tarski(C_10), D_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.76/1.91  tff(c_388, plain, (![A_139, B_140, D_141, C_142]: (r2_hidden(k1_funct_1(A_139, B_140), D_141) | ~m1_subset_1(A_139, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_142), D_141))) | ~r2_hidden(B_140, k1_relat_1(A_139)) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(resolution, [status(thm)], [c_160, c_12])).
% 4.76/1.91  tff(c_390, plain, (![B_140]: (r2_hidden(k1_funct_1('#skF_4', B_140), '#skF_3') | ~r2_hidden(B_140, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_388])).
% 4.76/1.91  tff(c_394, plain, (![B_143]: (r2_hidden(k1_funct_1('#skF_4', B_143), '#skF_3') | ~r2_hidden(B_143, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_44, c_236, c_390])).
% 4.76/1.91  tff(c_36, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.76/1.91  tff(c_407, plain, (~r2_hidden('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_394, c_36])).
% 4.76/1.91  tff(c_443, plain, (k1_funct_1('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_249, c_407])).
% 4.76/1.91  tff(c_444, plain, (~r2_hidden(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_443, c_36])).
% 4.76/1.91  tff(c_42, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.76/1.91  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.76/1.91  tff(c_63, plain, (![A_54, B_55]: (k2_xboole_0(k1_tarski(A_54), B_55)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.76/1.91  tff(c_67, plain, (![A_54]: (k1_tarski(A_54)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_63])).
% 4.76/1.91  tff(c_196, plain, (![B_21]: (B_21='#skF_2' | k1_funct_1('#skF_4', B_21)=k1_xboole_0 | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_184])).
% 4.76/1.91  tff(c_209, plain, (![B_21]: (B_21='#skF_2' | k1_funct_1('#skF_4', B_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_44, c_196])).
% 4.76/1.91  tff(c_333, plain, (![D_124, C_125, B_126, A_127]: (r2_hidden(k1_funct_1(D_124, C_125), B_126) | k1_xboole_0=B_126 | ~r2_hidden(C_125, A_127) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))) | ~v1_funct_2(D_124, A_127, B_126) | ~v1_funct_1(D_124))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.76/1.91  tff(c_408, plain, (![D_144, A_145, B_146]: (r2_hidden(k1_funct_1(D_144, '#skF_1'(A_145)), B_146) | k1_xboole_0=B_146 | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_2(D_144, A_145, B_146) | ~v1_funct_1(D_144) | k1_xboole_0=A_145)), inference(resolution, [status(thm)], [c_32, c_333])).
% 4.76/1.91  tff(c_430, plain, (![B_146, A_145]: (r2_hidden(k1_xboole_0, B_146) | k1_xboole_0=B_146 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_2('#skF_4', A_145, B_146) | ~v1_funct_1('#skF_4') | k1_xboole_0=A_145 | '#skF_1'(A_145)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_209, c_408])).
% 4.76/1.91  tff(c_532, plain, (![B_157, A_158]: (r2_hidden(k1_xboole_0, B_157) | k1_xboole_0=B_157 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_158, B_157))) | ~v1_funct_2('#skF_4', A_158, B_157) | k1_xboole_0=A_158 | '#skF_1'(A_158)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_430])).
% 4.76/1.91  tff(c_535, plain, (r2_hidden(k1_xboole_0, '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | k1_tarski('#skF_2')=k1_xboole_0 | '#skF_1'(k1_tarski('#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_40, c_532])).
% 4.76/1.91  tff(c_538, plain, (r2_hidden(k1_xboole_0, '#skF_3') | k1_xboole_0='#skF_3' | k1_tarski('#skF_2')=k1_xboole_0 | '#skF_1'(k1_tarski('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_535])).
% 4.76/1.91  tff(c_539, plain, ('#skF_1'(k1_tarski('#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_67, c_38, c_444, c_538])).
% 4.76/1.91  tff(c_357, plain, (![D_124, A_26, B_126]: (r2_hidden(k1_funct_1(D_124, '#skF_1'(A_26)), B_126) | k1_xboole_0=B_126 | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_26, B_126))) | ~v1_funct_2(D_124, A_26, B_126) | ~v1_funct_1(D_124) | k1_xboole_0=A_26)), inference(resolution, [status(thm)], [c_32, c_333])).
% 4.76/1.91  tff(c_545, plain, (![D_124, B_126]: (r2_hidden(k1_funct_1(D_124, '#skF_2'), B_126) | k1_xboole_0=B_126 | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), B_126))) | ~v1_funct_2(D_124, k1_tarski('#skF_2'), B_126) | ~v1_funct_1(D_124) | k1_tarski('#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_539, c_357])).
% 4.76/1.91  tff(c_1543, plain, (![D_275, B_276]: (r2_hidden(k1_funct_1(D_275, '#skF_2'), B_276) | k1_xboole_0=B_276 | ~m1_subset_1(D_275, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), B_276))) | ~v1_funct_2(D_275, k1_tarski('#skF_2'), B_276) | ~v1_funct_1(D_275))), inference(negUnitSimplification, [status(thm)], [c_67, c_545])).
% 4.76/1.91  tff(c_1546, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_1543])).
% 4.76/1.91  tff(c_1549, plain, (r2_hidden(k1_xboole_0, '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_443, c_1546])).
% 4.76/1.91  tff(c_1551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_444, c_1549])).
% 4.76/1.91  tff(c_1553, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_211])).
% 4.76/1.91  tff(c_1552, plain, ('#skF_1'(k1_relat_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_211])).
% 4.76/1.91  tff(c_1563, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | k1_relat_1('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1552, c_32])).
% 4.76/1.91  tff(c_1568, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1553, c_1563])).
% 4.76/1.91  tff(c_1878, plain, (![A_338, B_339, D_340, C_341]: (r2_hidden(k1_funct_1(A_338, B_339), D_340) | ~m1_subset_1(A_338, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_341), D_340))) | ~r2_hidden(B_339, k1_relat_1(A_338)) | ~v1_funct_1(A_338) | ~v1_relat_1(A_338))), inference(resolution, [status(thm)], [c_160, c_12])).
% 4.76/1.91  tff(c_1880, plain, (![B_339]: (r2_hidden(k1_funct_1('#skF_4', B_339), '#skF_3') | ~r2_hidden(B_339, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_1878])).
% 4.76/1.91  tff(c_1884, plain, (![B_342]: (r2_hidden(k1_funct_1('#skF_4', B_342), '#skF_3') | ~r2_hidden(B_342, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_44, c_1880])).
% 4.76/1.91  tff(c_1889, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1884, c_36])).
% 4.76/1.91  tff(c_1897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1568, c_1889])).
% 4.76/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.91  
% 4.76/1.91  Inference rules
% 4.76/1.91  ----------------------
% 4.76/1.91  #Ref     : 0
% 4.76/1.91  #Sup     : 416
% 4.76/1.91  #Fact    : 0
% 4.76/1.91  #Define  : 0
% 4.76/1.91  #Split   : 16
% 4.76/1.91  #Chain   : 0
% 4.76/1.91  #Close   : 0
% 4.76/1.91  
% 4.76/1.91  Ordering : KBO
% 4.76/1.91  
% 4.76/1.91  Simplification rules
% 4.76/1.91  ----------------------
% 4.76/1.91  #Subsume      : 86
% 4.76/1.91  #Demod        : 205
% 4.76/1.91  #Tautology    : 92
% 4.76/1.91  #SimpNegUnit  : 42
% 4.76/1.91  #BackRed      : 55
% 4.76/1.91  
% 4.76/1.91  #Partial instantiations: 0
% 4.76/1.91  #Strategies tried      : 1
% 4.76/1.91  
% 4.76/1.91  Timing (in seconds)
% 4.76/1.91  ----------------------
% 5.08/1.91  Preprocessing        : 0.34
% 5.08/1.91  Parsing              : 0.18
% 5.08/1.91  CNF conversion       : 0.02
% 5.08/1.91  Main loop            : 0.80
% 5.08/1.92  Inferencing          : 0.26
% 5.08/1.92  Reduction            : 0.23
% 5.08/1.92  Demodulation         : 0.15
% 5.08/1.92  BG Simplification    : 0.03
% 5.08/1.92  Subsumption          : 0.21
% 5.08/1.92  Abstraction          : 0.04
% 5.08/1.92  MUC search           : 0.00
% 5.08/1.92  Cooper               : 0.00
% 5.08/1.92  Total                : 1.17
% 5.08/1.92  Index Insertion      : 0.00
% 5.08/1.92  Index Deletion       : 0.00
% 5.08/1.92  Index Matching       : 0.00
% 5.08/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
