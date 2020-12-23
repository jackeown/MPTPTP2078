%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:27 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 221 expanded)
%              Number of leaves         :   45 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 438 expanded)
%              Number of equality atoms :   61 ( 159 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_121,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_129,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_121])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_42,plain,(
    ! [A_29] :
      ( k1_relat_1(A_29) = k1_xboole_0
      | k2_relat_1(A_29) != k1_xboole_0
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_144,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_129,c_42])).

tff(c_146,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_263,plain,(
    ! [A_93,B_94] :
      ( k9_relat_1(A_93,k1_tarski(B_94)) = k11_relat_1(A_93,B_94)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_200,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_210,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_200])).

tff(c_40,plain,(
    ! [B_28,A_27] :
      ( k7_relat_1(B_28,A_27) = B_28
      | ~ v4_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_213,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_210,c_40])).

tff(c_216,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_213])).

tff(c_222,plain,(
    ! [B_82,A_83] :
      ( k2_relat_1(k7_relat_1(B_82,A_83)) = k9_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_231,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_222])).

tff(c_235,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_231])).

tff(c_269,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_235])).

tff(c_278,plain,(
    k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_269])).

tff(c_36,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,k1_relat_1(B_26))
      | k11_relat_1(B_26,A_25) = k1_xboole_0
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_459,plain,(
    ! [B_128,A_129] :
      ( k1_tarski(k1_funct_1(B_128,A_129)) = k11_relat_1(B_128,A_129)
      | ~ r2_hidden(A_129,k1_relat_1(B_128))
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_577,plain,(
    ! [B_150,A_151] :
      ( k1_tarski(k1_funct_1(B_150,A_151)) = k11_relat_1(B_150,A_151)
      | ~ v1_funct_1(B_150)
      | k11_relat_1(B_150,A_151) = k1_xboole_0
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_36,c_459])).

tff(c_385,plain,(
    ! [A_112,B_113,C_114] :
      ( k2_relset_1(A_112,B_113,C_114) = k2_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_395,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_385])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_396,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_60])).

tff(c_586,plain,
    ( k11_relat_1('#skF_4','#skF_2') != k2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_396])).

tff(c_598,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_278,c_68,c_278,c_586])).

tff(c_600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_598])).

tff(c_601,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_602,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_999,plain,(
    ! [B_212,A_213] :
      ( k1_tarski(k1_funct_1(B_212,A_213)) = k2_relat_1(B_212)
      | k1_tarski(A_213) != k1_relat_1(B_212)
      | ~ v1_funct_1(B_212)
      | ~ v1_relat_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_981,plain,(
    ! [A_207,B_208,C_209] :
      ( k2_relset_1(A_207,B_208,C_209) = k2_relat_1(C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_984,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_981])).

tff(c_992,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_984])).

tff(c_993,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_992,c_60])).

tff(c_1005,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_993])).

tff(c_1014,plain,(
    k1_tarski('#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_68,c_601,c_602,c_1005])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_22,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_102,plain,(
    ! [A_51,B_52] : ~ r2_hidden(A_51,k2_zfmisc_1(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_105,plain,(
    ! [A_14] : ~ r2_hidden(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_102])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1142,plain,(
    ! [D_234,C_235,A_236,B_237] :
      ( r2_hidden(k1_funct_1(D_234,C_235),k2_relset_1(A_236,B_237,D_234))
      | k1_xboole_0 = B_237
      | ~ r2_hidden(C_235,A_236)
      | ~ m1_subset_1(D_234,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237)))
      | ~ v1_funct_2(D_234,A_236,B_237)
      | ~ v1_funct_1(D_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1147,plain,(
    ! [C_235] :
      ( r2_hidden(k1_funct_1('#skF_4',C_235),k1_xboole_0)
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_235,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_1142])).

tff(c_1150,plain,(
    ! [C_235] :
      ( r2_hidden(k1_funct_1('#skF_4',C_235),k1_xboole_0)
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_235,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1147])).

tff(c_1152,plain,(
    ! [C_238] : ~ r2_hidden(C_238,k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_105,c_1150])).

tff(c_1163,plain,(
    ! [B_239] : r1_tarski(k1_tarski('#skF_2'),B_239) ),
    inference(resolution,[status(thm)],[c_6,c_1152])).

tff(c_618,plain,(
    ! [A_154,B_155] :
      ( r2_hidden('#skF_1'(A_154,B_155),A_154)
      | r1_tarski(A_154,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_630,plain,(
    ! [B_156] : r1_tarski(k1_xboole_0,B_156) ),
    inference(resolution,[status(thm)],[c_618,c_105])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_633,plain,(
    ! [B_156] :
      ( k1_xboole_0 = B_156
      | ~ r1_tarski(B_156,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_630,c_8])).

tff(c_1182,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1163,c_633])).

tff(c_1194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1014,c_1182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:25:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.57  
% 3.21/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.57  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.21/1.57  
% 3.21/1.57  %Foreground sorts:
% 3.21/1.57  
% 3.21/1.57  
% 3.21/1.57  %Background operators:
% 3.21/1.57  
% 3.21/1.57  
% 3.21/1.57  %Foreground operators:
% 3.21/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.21/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.21/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.21/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.21/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.21/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.21/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.21/1.57  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.21/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.21/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.21/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.21/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.21/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.21/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.21/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.21/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.21/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.57  
% 3.21/1.59  tff(f_141, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.21/1.59  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.21/1.59  tff(f_87, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.21/1.59  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.21/1.59  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.21/1.59  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.21/1.59  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.21/1.59  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.21/1.59  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.21/1.59  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.21/1.59  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.21/1.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.21/1.59  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.21/1.59  tff(f_53, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.21/1.59  tff(f_129, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.21/1.59  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.21/1.59  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.21/1.59  tff(c_121, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.21/1.59  tff(c_129, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_121])).
% 3.21/1.59  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.21/1.59  tff(c_42, plain, (![A_29]: (k1_relat_1(A_29)=k1_xboole_0 | k2_relat_1(A_29)!=k1_xboole_0 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.21/1.59  tff(c_144, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_129, c_42])).
% 3.21/1.59  tff(c_146, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_144])).
% 3.21/1.59  tff(c_263, plain, (![A_93, B_94]: (k9_relat_1(A_93, k1_tarski(B_94))=k11_relat_1(A_93, B_94) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.59  tff(c_200, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.21/1.59  tff(c_210, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_200])).
% 3.21/1.59  tff(c_40, plain, (![B_28, A_27]: (k7_relat_1(B_28, A_27)=B_28 | ~v4_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.21/1.59  tff(c_213, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_210, c_40])).
% 3.21/1.59  tff(c_216, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_213])).
% 3.21/1.59  tff(c_222, plain, (![B_82, A_83]: (k2_relat_1(k7_relat_1(B_82, A_83))=k9_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.21/1.59  tff(c_231, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_216, c_222])).
% 3.21/1.59  tff(c_235, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_231])).
% 3.21/1.59  tff(c_269, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_263, c_235])).
% 3.21/1.59  tff(c_278, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_269])).
% 3.21/1.59  tff(c_36, plain, (![A_25, B_26]: (r2_hidden(A_25, k1_relat_1(B_26)) | k11_relat_1(B_26, A_25)=k1_xboole_0 | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.21/1.59  tff(c_459, plain, (![B_128, A_129]: (k1_tarski(k1_funct_1(B_128, A_129))=k11_relat_1(B_128, A_129) | ~r2_hidden(A_129, k1_relat_1(B_128)) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.21/1.59  tff(c_577, plain, (![B_150, A_151]: (k1_tarski(k1_funct_1(B_150, A_151))=k11_relat_1(B_150, A_151) | ~v1_funct_1(B_150) | k11_relat_1(B_150, A_151)=k1_xboole_0 | ~v1_relat_1(B_150))), inference(resolution, [status(thm)], [c_36, c_459])).
% 3.21/1.59  tff(c_385, plain, (![A_112, B_113, C_114]: (k2_relset_1(A_112, B_113, C_114)=k2_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.21/1.59  tff(c_395, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_385])).
% 3.21/1.59  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.21/1.59  tff(c_396, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_395, c_60])).
% 3.21/1.59  tff(c_586, plain, (k11_relat_1('#skF_4', '#skF_2')!=k2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | k11_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_577, c_396])).
% 3.21/1.59  tff(c_598, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_129, c_278, c_68, c_278, c_586])).
% 3.21/1.59  tff(c_600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_598])).
% 3.21/1.59  tff(c_601, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_144])).
% 3.21/1.59  tff(c_602, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_144])).
% 3.21/1.59  tff(c_999, plain, (![B_212, A_213]: (k1_tarski(k1_funct_1(B_212, A_213))=k2_relat_1(B_212) | k1_tarski(A_213)!=k1_relat_1(B_212) | ~v1_funct_1(B_212) | ~v1_relat_1(B_212))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.21/1.59  tff(c_981, plain, (![A_207, B_208, C_209]: (k2_relset_1(A_207, B_208, C_209)=k2_relat_1(C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.21/1.59  tff(c_984, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_981])).
% 3.21/1.59  tff(c_992, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_602, c_984])).
% 3.21/1.59  tff(c_993, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_992, c_60])).
% 3.21/1.59  tff(c_1005, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_999, c_993])).
% 3.21/1.59  tff(c_1014, plain, (k1_tarski('#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_129, c_68, c_601, c_602, c_1005])).
% 3.21/1.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.21/1.59  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.21/1.59  tff(c_22, plain, (![A_14]: (k2_zfmisc_1(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.21/1.59  tff(c_102, plain, (![A_51, B_52]: (~r2_hidden(A_51, k2_zfmisc_1(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.21/1.59  tff(c_105, plain, (![A_14]: (~r2_hidden(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_102])).
% 3.21/1.59  tff(c_66, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.21/1.59  tff(c_1142, plain, (![D_234, C_235, A_236, B_237]: (r2_hidden(k1_funct_1(D_234, C_235), k2_relset_1(A_236, B_237, D_234)) | k1_xboole_0=B_237 | ~r2_hidden(C_235, A_236) | ~m1_subset_1(D_234, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))) | ~v1_funct_2(D_234, A_236, B_237) | ~v1_funct_1(D_234))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.21/1.59  tff(c_1147, plain, (![C_235]: (r2_hidden(k1_funct_1('#skF_4', C_235), k1_xboole_0) | k1_xboole_0='#skF_3' | ~r2_hidden(C_235, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_992, c_1142])).
% 3.21/1.59  tff(c_1150, plain, (![C_235]: (r2_hidden(k1_funct_1('#skF_4', C_235), k1_xboole_0) | k1_xboole_0='#skF_3' | ~r2_hidden(C_235, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_1147])).
% 3.21/1.59  tff(c_1152, plain, (![C_238]: (~r2_hidden(C_238, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62, c_105, c_1150])).
% 3.21/1.59  tff(c_1163, plain, (![B_239]: (r1_tarski(k1_tarski('#skF_2'), B_239))), inference(resolution, [status(thm)], [c_6, c_1152])).
% 3.21/1.59  tff(c_618, plain, (![A_154, B_155]: (r2_hidden('#skF_1'(A_154, B_155), A_154) | r1_tarski(A_154, B_155))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.21/1.59  tff(c_630, plain, (![B_156]: (r1_tarski(k1_xboole_0, B_156))), inference(resolution, [status(thm)], [c_618, c_105])).
% 3.21/1.59  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.21/1.59  tff(c_633, plain, (![B_156]: (k1_xboole_0=B_156 | ~r1_tarski(B_156, k1_xboole_0))), inference(resolution, [status(thm)], [c_630, c_8])).
% 3.21/1.59  tff(c_1182, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1163, c_633])).
% 3.21/1.59  tff(c_1194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1014, c_1182])).
% 3.21/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.59  
% 3.21/1.59  Inference rules
% 3.21/1.59  ----------------------
% 3.21/1.59  #Ref     : 0
% 3.21/1.59  #Sup     : 241
% 3.21/1.59  #Fact    : 0
% 3.21/1.59  #Define  : 0
% 3.21/1.59  #Split   : 1
% 3.21/1.59  #Chain   : 0
% 3.21/1.59  #Close   : 0
% 3.21/1.59  
% 3.21/1.59  Ordering : KBO
% 3.21/1.59  
% 3.21/1.59  Simplification rules
% 3.21/1.59  ----------------------
% 3.21/1.59  #Subsume      : 26
% 3.21/1.59  #Demod        : 101
% 3.21/1.59  #Tautology    : 112
% 3.21/1.59  #SimpNegUnit  : 6
% 3.21/1.59  #BackRed      : 2
% 3.21/1.59  
% 3.21/1.59  #Partial instantiations: 0
% 3.21/1.59  #Strategies tried      : 1
% 3.21/1.59  
% 3.21/1.59  Timing (in seconds)
% 3.21/1.59  ----------------------
% 3.21/1.59  Preprocessing        : 0.36
% 3.21/1.59  Parsing              : 0.20
% 3.21/1.59  CNF conversion       : 0.02
% 3.21/1.59  Main loop            : 0.41
% 3.21/1.59  Inferencing          : 0.16
% 3.21/1.59  Reduction            : 0.12
% 3.21/1.59  Demodulation         : 0.08
% 3.21/1.59  BG Simplification    : 0.02
% 3.21/1.59  Subsumption          : 0.07
% 3.21/1.59  Abstraction          : 0.02
% 3.21/1.59  MUC search           : 0.00
% 3.21/1.59  Cooper               : 0.00
% 3.21/1.59  Total                : 0.81
% 3.21/1.59  Index Insertion      : 0.00
% 3.21/1.59  Index Deletion       : 0.00
% 3.21/1.59  Index Matching       : 0.00
% 3.21/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
