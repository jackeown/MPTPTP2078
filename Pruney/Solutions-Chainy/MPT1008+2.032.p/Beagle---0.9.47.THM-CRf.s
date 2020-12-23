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
% DateTime   : Thu Dec  3 10:14:30 EST 2020

% Result     : Theorem 6.96s
% Output     : CNFRefutation 7.25s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 265 expanded)
%              Number of leaves         :   51 ( 109 expanded)
%              Depth                    :   19
%              Number of atoms          :  186 ( 516 expanded)
%              Number of equality atoms :   86 ( 211 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_137,axiom,(
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

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_98,plain,(
    ! [D_60,A_61] : r2_hidden(D_60,k2_tarski(A_61,D_60)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_101,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_98])).

tff(c_80,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_142,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_150,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_142])).

tff(c_42,plain,(
    ! [A_27] :
      ( k2_relat_1(A_27) != k1_xboole_0
      | k1_xboole_0 = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_158,plain,
    ( k2_relat_1('#skF_7') != k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_150,c_42])).

tff(c_170,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_277,plain,(
    ! [A_102,B_103] :
      ( k9_relat_1(A_102,k1_tarski(B_103)) = k11_relat_1(A_102,B_103)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_172,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_180,plain,(
    v4_relat_1('#skF_7',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_80,c_172])).

tff(c_231,plain,(
    ! [B_97,A_98] :
      ( k7_relat_1(B_97,A_98) = B_97
      | ~ v4_relat_1(B_97,A_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_234,plain,
    ( k7_relat_1('#skF_7',k1_tarski('#skF_5')) = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_180,c_231])).

tff(c_240,plain,(
    k7_relat_1('#skF_7',k1_tarski('#skF_5')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_234])).

tff(c_34,plain,(
    ! [B_22,A_21] :
      ( k2_relat_1(k7_relat_1(B_22,A_21)) = k9_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_260,plain,
    ( k9_relat_1('#skF_7',k1_tarski('#skF_5')) = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_34])).

tff(c_264,plain,(
    k9_relat_1('#skF_7',k1_tarski('#skF_5')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_260])).

tff(c_287,plain,
    ( k11_relat_1('#skF_7','#skF_5') = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_264])).

tff(c_302,plain,(
    k11_relat_1('#skF_7','#skF_5') = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_287])).

tff(c_36,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,k1_relat_1(B_24))
      | k11_relat_1(B_24,A_23) = k1_xboole_0
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_341,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_349,plain,(
    k2_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_341])).

tff(c_76,plain,(
    k2_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') != k1_tarski(k1_funct_1('#skF_7','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_358,plain,(
    k1_tarski(k1_funct_1('#skF_7','#skF_5')) != k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_76])).

tff(c_84,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_420,plain,(
    ! [B_142,A_143] :
      ( k2_relat_1(k7_relat_1(B_142,k1_tarski(A_143))) = k1_tarski(k1_funct_1(B_142,A_143))
      | ~ r2_hidden(A_143,k1_relat_1(B_142))
      | ~ v1_funct_1(B_142)
      | ~ v1_relat_1(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_432,plain,
    ( k1_tarski(k1_funct_1('#skF_7','#skF_5')) = k2_relat_1('#skF_7')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_420])).

tff(c_444,plain,
    ( k1_tarski(k1_funct_1('#skF_7','#skF_5')) = k2_relat_1('#skF_7')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_84,c_432])).

tff(c_445,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_444])).

tff(c_450,plain,
    ( k11_relat_1('#skF_7','#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_445])).

tff(c_453,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_302,c_450])).

tff(c_455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_453])).

tff(c_456,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_463,plain,(
    ! [A_1] : r1_tarski('#skF_7',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_2])).

tff(c_28,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_462,plain,(
    ! [A_14] : m1_subset_1('#skF_7',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_28])).

tff(c_58,plain,(
    ! [D_52,A_41,B_42,C_43] :
      ( r2_hidden(k4_tarski(D_52,'#skF_4'(A_41,B_42,C_43,D_52)),C_43)
      | ~ r2_hidden(D_52,B_42)
      | k1_relset_1(B_42,A_41,C_43) != B_42
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(B_42,A_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2983,plain,(
    ! [A_9908,B_9909,C_9910] :
      ( '#skF_1'(A_9908,B_9909,C_9910) = B_9909
      | '#skF_1'(A_9908,B_9909,C_9910) = A_9908
      | r2_hidden('#skF_2'(A_9908,B_9909,C_9910),C_9910)
      | k2_tarski(A_9908,B_9909) = C_9910 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    ! [B_31,A_30] :
      ( ~ r1_tarski(B_31,A_30)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6416,plain,(
    ! [C_15407,A_15408,B_15409] :
      ( ~ r1_tarski(C_15407,'#skF_2'(A_15408,B_15409,C_15407))
      | '#skF_1'(A_15408,B_15409,C_15407) = B_15409
      | '#skF_1'(A_15408,B_15409,C_15407) = A_15408
      | k2_tarski(A_15408,B_15409) = C_15407 ) ),
    inference(resolution,[status(thm)],[c_2983,c_48])).

tff(c_6473,plain,(
    ! [A_15542,B_15543] :
      ( '#skF_1'(A_15542,B_15543,'#skF_7') = B_15543
      | '#skF_1'(A_15542,B_15543,'#skF_7') = A_15542
      | k2_tarski(A_15542,B_15543) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_463,c_6416])).

tff(c_6,plain,(
    ! [D_7,A_2] : r2_hidden(D_7,k2_tarski(A_2,D_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_108,plain,(
    ! [B_65,A_66] :
      ( ~ r1_tarski(B_65,A_66)
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_120,plain,(
    ! [A_2,D_7] : ~ r1_tarski(k2_tarski(A_2,D_7),D_7) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_6494,plain,(
    ! [B_15543,A_15542] :
      ( ~ r1_tarski('#skF_7',B_15543)
      | '#skF_1'(A_15542,B_15543,'#skF_7') = B_15543
      | '#skF_1'(A_15542,B_15543,'#skF_7') = A_15542 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6473,c_120])).

tff(c_6635,plain,(
    ! [A_15542,B_15543] :
      ( '#skF_1'(A_15542,B_15543,'#skF_7') = B_15543
      | '#skF_1'(A_15542,B_15543,'#skF_7') = A_15542 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_6494])).

tff(c_6755,plain,(
    ! [B_15810] : '#skF_1'(B_15810,B_15810,'#skF_7') = B_15810 ),
    inference(factorization,[status(thm),theory(equality)],[c_6635])).

tff(c_18,plain,(
    ! [A_2,B_3,C_4] :
      ( ~ r2_hidden('#skF_1'(A_2,B_3,C_4),C_4)
      | r2_hidden('#skF_2'(A_2,B_3,C_4),C_4)
      | k2_tarski(A_2,B_3) = C_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6774,plain,(
    ! [B_15810] :
      ( ~ r2_hidden(B_15810,'#skF_7')
      | r2_hidden('#skF_2'(B_15810,B_15810,'#skF_7'),'#skF_7')
      | k2_tarski(B_15810,B_15810) = '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6755,c_18])).

tff(c_6815,plain,(
    ! [B_15943] :
      ( ~ r2_hidden(B_15943,'#skF_7')
      | r2_hidden('#skF_2'(B_15943,B_15943,'#skF_7'),'#skF_7')
      | k1_tarski(B_15943) = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6774])).

tff(c_6824,plain,(
    ! [B_15943] :
      ( ~ r1_tarski('#skF_7','#skF_2'(B_15943,B_15943,'#skF_7'))
      | ~ r2_hidden(B_15943,'#skF_7')
      | k1_tarski(B_15943) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_6815,c_48])).

tff(c_6858,plain,(
    ! [B_16076] :
      ( ~ r2_hidden(B_16076,'#skF_7')
      | k1_tarski(B_16076) = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_6824])).

tff(c_6862,plain,(
    ! [D_52,A_41,B_42] :
      ( k1_tarski(k4_tarski(D_52,'#skF_4'(A_41,B_42,'#skF_7',D_52))) = '#skF_7'
      | ~ r2_hidden(D_52,B_42)
      | k1_relset_1(B_42,A_41,'#skF_7') != B_42
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(B_42,A_41))) ) ),
    inference(resolution,[status(thm)],[c_58,c_6858])).

tff(c_7260,plain,(
    ! [D_17017,A_17018,B_17019] :
      ( k1_tarski(k4_tarski(D_17017,'#skF_4'(A_17018,B_17019,'#skF_7',D_17017))) = '#skF_7'
      | ~ r2_hidden(D_17017,B_17019)
      | k1_relset_1(B_17019,A_17018,'#skF_7') != B_17019 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_6862])).

tff(c_119,plain,(
    ! [A_8] : ~ r1_tarski(k1_tarski(A_8),A_8) ),
    inference(resolution,[status(thm)],[c_101,c_108])).

tff(c_7285,plain,(
    ! [D_17017,A_17018,B_17019] :
      ( ~ r1_tarski('#skF_7',k4_tarski(D_17017,'#skF_4'(A_17018,B_17019,'#skF_7',D_17017)))
      | ~ r2_hidden(D_17017,B_17019)
      | k1_relset_1(B_17019,A_17018,'#skF_7') != B_17019 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7260,c_119])).

tff(c_7353,plain,(
    ! [D_17152,B_17153,A_17154] :
      ( ~ r2_hidden(D_17152,B_17153)
      | k1_relset_1(B_17153,A_17154,'#skF_7') != B_17153 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_7285])).

tff(c_7406,plain,(
    ! [A_8,A_17154] : k1_relset_1(k1_tarski(A_8),A_17154,'#skF_7') != k1_tarski(A_8) ),
    inference(resolution,[status(thm)],[c_101,c_7353])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_464,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_78])).

tff(c_82,plain,(
    v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_74,plain,(
    ! [B_55,A_54,C_56] :
      ( k1_xboole_0 = B_55
      | k1_relset_1(A_54,B_55,C_56) = A_54
      | ~ v1_funct_2(C_56,A_54,B_55)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_728,plain,(
    ! [B_214,A_215,C_216] :
      ( B_214 = '#skF_7'
      | k1_relset_1(A_215,B_214,C_216) = A_215
      | ~ v1_funct_2(C_216,A_215,B_214)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_215,B_214))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_74])).

tff(c_742,plain,(
    ! [B_218,A_219] :
      ( B_218 = '#skF_7'
      | k1_relset_1(A_219,B_218,'#skF_7') = A_219
      | ~ v1_funct_2('#skF_7',A_219,B_218) ) ),
    inference(resolution,[status(thm)],[c_462,c_728])).

tff(c_754,plain,
    ( '#skF_7' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_742])).

tff(c_761,plain,(
    k1_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_464,c_754])).

tff(c_7427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7406,c_761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.96/2.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/2.45  
% 6.96/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/2.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 6.96/2.46  
% 6.96/2.46  %Foreground sorts:
% 6.96/2.46  
% 6.96/2.46  
% 6.96/2.46  %Background operators:
% 6.96/2.46  
% 6.96/2.46  
% 6.96/2.46  %Foreground operators:
% 6.96/2.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.96/2.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.96/2.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.96/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.96/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.96/2.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.96/2.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.96/2.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.96/2.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.96/2.46  tff('#skF_7', type, '#skF_7': $i).
% 6.96/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.96/2.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.96/2.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.96/2.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.96/2.46  tff('#skF_5', type, '#skF_5': $i).
% 6.96/2.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.96/2.46  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 6.96/2.46  tff('#skF_6', type, '#skF_6': $i).
% 6.96/2.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.96/2.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.96/2.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.96/2.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.96/2.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.96/2.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.96/2.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.96/2.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.96/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.96/2.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.96/2.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.96/2.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.96/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.96/2.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.96/2.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.96/2.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.96/2.46  
% 7.25/2.48  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.25/2.48  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 7.25/2.48  tff(f_149, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 7.25/2.48  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.25/2.48  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.25/2.48  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 7.25/2.48  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.25/2.48  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 7.25/2.48  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 7.25/2.48  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 7.25/2.48  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.25/2.48  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_funct_1)).
% 7.25/2.48  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.25/2.48  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.25/2.48  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 7.25/2.48  tff(f_93, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.25/2.48  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.25/2.48  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.25/2.48  tff(c_98, plain, (![D_60, A_61]: (r2_hidden(D_60, k2_tarski(A_61, D_60)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.25/2.48  tff(c_101, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_98])).
% 7.25/2.48  tff(c_80, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.25/2.48  tff(c_142, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.25/2.48  tff(c_150, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_142])).
% 7.25/2.48  tff(c_42, plain, (![A_27]: (k2_relat_1(A_27)!=k1_xboole_0 | k1_xboole_0=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.25/2.48  tff(c_158, plain, (k2_relat_1('#skF_7')!=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_150, c_42])).
% 7.25/2.48  tff(c_170, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_158])).
% 7.25/2.48  tff(c_277, plain, (![A_102, B_103]: (k9_relat_1(A_102, k1_tarski(B_103))=k11_relat_1(A_102, B_103) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.25/2.48  tff(c_172, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.25/2.48  tff(c_180, plain, (v4_relat_1('#skF_7', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_80, c_172])).
% 7.25/2.48  tff(c_231, plain, (![B_97, A_98]: (k7_relat_1(B_97, A_98)=B_97 | ~v4_relat_1(B_97, A_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.25/2.48  tff(c_234, plain, (k7_relat_1('#skF_7', k1_tarski('#skF_5'))='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_180, c_231])).
% 7.25/2.48  tff(c_240, plain, (k7_relat_1('#skF_7', k1_tarski('#skF_5'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_234])).
% 7.25/2.48  tff(c_34, plain, (![B_22, A_21]: (k2_relat_1(k7_relat_1(B_22, A_21))=k9_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.25/2.48  tff(c_260, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_5'))=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_240, c_34])).
% 7.25/2.48  tff(c_264, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_5'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_260])).
% 7.25/2.48  tff(c_287, plain, (k11_relat_1('#skF_7', '#skF_5')=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_277, c_264])).
% 7.25/2.48  tff(c_302, plain, (k11_relat_1('#skF_7', '#skF_5')=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_287])).
% 7.25/2.48  tff(c_36, plain, (![A_23, B_24]: (r2_hidden(A_23, k1_relat_1(B_24)) | k11_relat_1(B_24, A_23)=k1_xboole_0 | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.25/2.48  tff(c_341, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.25/2.48  tff(c_349, plain, (k2_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_341])).
% 7.25/2.48  tff(c_76, plain, (k2_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')!=k1_tarski(k1_funct_1('#skF_7', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.25/2.48  tff(c_358, plain, (k1_tarski(k1_funct_1('#skF_7', '#skF_5'))!=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_349, c_76])).
% 7.25/2.48  tff(c_84, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.25/2.48  tff(c_420, plain, (![B_142, A_143]: (k2_relat_1(k7_relat_1(B_142, k1_tarski(A_143)))=k1_tarski(k1_funct_1(B_142, A_143)) | ~r2_hidden(A_143, k1_relat_1(B_142)) | ~v1_funct_1(B_142) | ~v1_relat_1(B_142))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.25/2.48  tff(c_432, plain, (k1_tarski(k1_funct_1('#skF_7', '#skF_5'))=k2_relat_1('#skF_7') | ~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_240, c_420])).
% 7.25/2.48  tff(c_444, plain, (k1_tarski(k1_funct_1('#skF_7', '#skF_5'))=k2_relat_1('#skF_7') | ~r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_84, c_432])).
% 7.25/2.48  tff(c_445, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_358, c_444])).
% 7.25/2.48  tff(c_450, plain, (k11_relat_1('#skF_7', '#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_36, c_445])).
% 7.25/2.48  tff(c_453, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_150, c_302, c_450])).
% 7.25/2.48  tff(c_455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_453])).
% 7.25/2.48  tff(c_456, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_158])).
% 7.25/2.48  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.25/2.48  tff(c_463, plain, (![A_1]: (r1_tarski('#skF_7', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_456, c_2])).
% 7.25/2.48  tff(c_28, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.25/2.48  tff(c_462, plain, (![A_14]: (m1_subset_1('#skF_7', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_456, c_28])).
% 7.25/2.48  tff(c_58, plain, (![D_52, A_41, B_42, C_43]: (r2_hidden(k4_tarski(D_52, '#skF_4'(A_41, B_42, C_43, D_52)), C_43) | ~r2_hidden(D_52, B_42) | k1_relset_1(B_42, A_41, C_43)!=B_42 | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(B_42, A_41))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.25/2.48  tff(c_2983, plain, (![A_9908, B_9909, C_9910]: ('#skF_1'(A_9908, B_9909, C_9910)=B_9909 | '#skF_1'(A_9908, B_9909, C_9910)=A_9908 | r2_hidden('#skF_2'(A_9908, B_9909, C_9910), C_9910) | k2_tarski(A_9908, B_9909)=C_9910)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.25/2.48  tff(c_48, plain, (![B_31, A_30]: (~r1_tarski(B_31, A_30) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.25/2.48  tff(c_6416, plain, (![C_15407, A_15408, B_15409]: (~r1_tarski(C_15407, '#skF_2'(A_15408, B_15409, C_15407)) | '#skF_1'(A_15408, B_15409, C_15407)=B_15409 | '#skF_1'(A_15408, B_15409, C_15407)=A_15408 | k2_tarski(A_15408, B_15409)=C_15407)), inference(resolution, [status(thm)], [c_2983, c_48])).
% 7.25/2.48  tff(c_6473, plain, (![A_15542, B_15543]: ('#skF_1'(A_15542, B_15543, '#skF_7')=B_15543 | '#skF_1'(A_15542, B_15543, '#skF_7')=A_15542 | k2_tarski(A_15542, B_15543)='#skF_7')), inference(resolution, [status(thm)], [c_463, c_6416])).
% 7.25/2.48  tff(c_6, plain, (![D_7, A_2]: (r2_hidden(D_7, k2_tarski(A_2, D_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.25/2.48  tff(c_108, plain, (![B_65, A_66]: (~r1_tarski(B_65, A_66) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.25/2.48  tff(c_120, plain, (![A_2, D_7]: (~r1_tarski(k2_tarski(A_2, D_7), D_7))), inference(resolution, [status(thm)], [c_6, c_108])).
% 7.25/2.48  tff(c_6494, plain, (![B_15543, A_15542]: (~r1_tarski('#skF_7', B_15543) | '#skF_1'(A_15542, B_15543, '#skF_7')=B_15543 | '#skF_1'(A_15542, B_15543, '#skF_7')=A_15542)), inference(superposition, [status(thm), theory('equality')], [c_6473, c_120])).
% 7.25/2.48  tff(c_6635, plain, (![A_15542, B_15543]: ('#skF_1'(A_15542, B_15543, '#skF_7')=B_15543 | '#skF_1'(A_15542, B_15543, '#skF_7')=A_15542)), inference(demodulation, [status(thm), theory('equality')], [c_463, c_6494])).
% 7.25/2.48  tff(c_6755, plain, (![B_15810]: ('#skF_1'(B_15810, B_15810, '#skF_7')=B_15810)), inference(factorization, [status(thm), theory('equality')], [c_6635])).
% 7.25/2.48  tff(c_18, plain, (![A_2, B_3, C_4]: (~r2_hidden('#skF_1'(A_2, B_3, C_4), C_4) | r2_hidden('#skF_2'(A_2, B_3, C_4), C_4) | k2_tarski(A_2, B_3)=C_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.25/2.48  tff(c_6774, plain, (![B_15810]: (~r2_hidden(B_15810, '#skF_7') | r2_hidden('#skF_2'(B_15810, B_15810, '#skF_7'), '#skF_7') | k2_tarski(B_15810, B_15810)='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6755, c_18])).
% 7.25/2.48  tff(c_6815, plain, (![B_15943]: (~r2_hidden(B_15943, '#skF_7') | r2_hidden('#skF_2'(B_15943, B_15943, '#skF_7'), '#skF_7') | k1_tarski(B_15943)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6774])).
% 7.25/2.48  tff(c_6824, plain, (![B_15943]: (~r1_tarski('#skF_7', '#skF_2'(B_15943, B_15943, '#skF_7')) | ~r2_hidden(B_15943, '#skF_7') | k1_tarski(B_15943)='#skF_7')), inference(resolution, [status(thm)], [c_6815, c_48])).
% 7.25/2.48  tff(c_6858, plain, (![B_16076]: (~r2_hidden(B_16076, '#skF_7') | k1_tarski(B_16076)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_463, c_6824])).
% 7.25/2.48  tff(c_6862, plain, (![D_52, A_41, B_42]: (k1_tarski(k4_tarski(D_52, '#skF_4'(A_41, B_42, '#skF_7', D_52)))='#skF_7' | ~r2_hidden(D_52, B_42) | k1_relset_1(B_42, A_41, '#skF_7')!=B_42 | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(B_42, A_41))))), inference(resolution, [status(thm)], [c_58, c_6858])).
% 7.25/2.48  tff(c_7260, plain, (![D_17017, A_17018, B_17019]: (k1_tarski(k4_tarski(D_17017, '#skF_4'(A_17018, B_17019, '#skF_7', D_17017)))='#skF_7' | ~r2_hidden(D_17017, B_17019) | k1_relset_1(B_17019, A_17018, '#skF_7')!=B_17019)), inference(demodulation, [status(thm), theory('equality')], [c_462, c_6862])).
% 7.25/2.48  tff(c_119, plain, (![A_8]: (~r1_tarski(k1_tarski(A_8), A_8))), inference(resolution, [status(thm)], [c_101, c_108])).
% 7.25/2.48  tff(c_7285, plain, (![D_17017, A_17018, B_17019]: (~r1_tarski('#skF_7', k4_tarski(D_17017, '#skF_4'(A_17018, B_17019, '#skF_7', D_17017))) | ~r2_hidden(D_17017, B_17019) | k1_relset_1(B_17019, A_17018, '#skF_7')!=B_17019)), inference(superposition, [status(thm), theory('equality')], [c_7260, c_119])).
% 7.25/2.48  tff(c_7353, plain, (![D_17152, B_17153, A_17154]: (~r2_hidden(D_17152, B_17153) | k1_relset_1(B_17153, A_17154, '#skF_7')!=B_17153)), inference(demodulation, [status(thm), theory('equality')], [c_463, c_7285])).
% 7.25/2.48  tff(c_7406, plain, (![A_8, A_17154]: (k1_relset_1(k1_tarski(A_8), A_17154, '#skF_7')!=k1_tarski(A_8))), inference(resolution, [status(thm)], [c_101, c_7353])).
% 7.25/2.48  tff(c_78, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.25/2.48  tff(c_464, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_456, c_78])).
% 7.25/2.48  tff(c_82, plain, (v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 7.25/2.48  tff(c_74, plain, (![B_55, A_54, C_56]: (k1_xboole_0=B_55 | k1_relset_1(A_54, B_55, C_56)=A_54 | ~v1_funct_2(C_56, A_54, B_55) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.25/2.48  tff(c_728, plain, (![B_214, A_215, C_216]: (B_214='#skF_7' | k1_relset_1(A_215, B_214, C_216)=A_215 | ~v1_funct_2(C_216, A_215, B_214) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_215, B_214))))), inference(demodulation, [status(thm), theory('equality')], [c_456, c_74])).
% 7.25/2.48  tff(c_742, plain, (![B_218, A_219]: (B_218='#skF_7' | k1_relset_1(A_219, B_218, '#skF_7')=A_219 | ~v1_funct_2('#skF_7', A_219, B_218))), inference(resolution, [status(thm)], [c_462, c_728])).
% 7.25/2.48  tff(c_754, plain, ('#skF_7'='#skF_6' | k1_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_82, c_742])).
% 7.25/2.48  tff(c_761, plain, (k1_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_464, c_754])).
% 7.25/2.48  tff(c_7427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7406, c_761])).
% 7.25/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.25/2.48  
% 7.25/2.48  Inference rules
% 7.25/2.48  ----------------------
% 7.25/2.48  #Ref     : 0
% 7.25/2.48  #Sup     : 1003
% 7.25/2.48  #Fact    : 30
% 7.25/2.48  #Define  : 0
% 7.25/2.48  #Split   : 4
% 7.25/2.48  #Chain   : 0
% 7.25/2.48  #Close   : 0
% 7.25/2.48  
% 7.25/2.48  Ordering : KBO
% 7.25/2.48  
% 7.25/2.48  Simplification rules
% 7.25/2.48  ----------------------
% 7.25/2.48  #Subsume      : 292
% 7.25/2.48  #Demod        : 296
% 7.25/2.48  #Tautology    : 329
% 7.25/2.48  #SimpNegUnit  : 7
% 7.25/2.48  #BackRed      : 12
% 7.25/2.48  
% 7.25/2.48  #Partial instantiations: 8878
% 7.25/2.48  #Strategies tried      : 1
% 7.25/2.48  
% 7.25/2.48  Timing (in seconds)
% 7.25/2.48  ----------------------
% 7.25/2.48  Preprocessing        : 0.40
% 7.25/2.48  Parsing              : 0.20
% 7.25/2.48  CNF conversion       : 0.03
% 7.25/2.48  Main loop            : 1.28
% 7.25/2.48  Inferencing          : 0.62
% 7.25/2.48  Reduction            : 0.31
% 7.25/2.48  Demodulation         : 0.21
% 7.25/2.48  BG Simplification    : 0.05
% 7.25/2.48  Subsumption          : 0.22
% 7.25/2.48  Abstraction          : 0.06
% 7.25/2.48  MUC search           : 0.00
% 7.25/2.48  Cooper               : 0.00
% 7.25/2.48  Total                : 1.73
% 7.25/2.48  Index Insertion      : 0.00
% 7.25/2.48  Index Deletion       : 0.00
% 7.25/2.48  Index Matching       : 0.00
% 7.25/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
