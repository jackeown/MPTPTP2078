%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:18 EST 2020

% Result     : Theorem 10.20s
% Output     : CNFRefutation 10.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 287 expanded)
%              Number of leaves         :   55 ( 117 expanded)
%              Depth                    :   16
%              Number of atoms          :  199 ( 599 expanded)
%              Number of equality atoms :   56 ( 172 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_182,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_148,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_152,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_99,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_170,axiom,(
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

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_36,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1('#skF_1'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_162,plain,(
    ! [C_105,A_106,B_107] :
      ( v1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_174,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_162])).

tff(c_34,plain,(
    ! [A_28] :
      ( k1_relat_1(A_28) != k1_xboole_0
      | k1_xboole_0 = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_183,plain,
    ( k1_relat_1('#skF_8') != k1_xboole_0
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_174,c_34])).

tff(c_212,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_256,plain,(
    ! [C_125,B_126,A_127] :
      ( v5_relat_1(C_125,B_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_268,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_256])).

tff(c_84,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_891,plain,(
    ! [B_193,C_194,A_195] :
      ( r2_hidden(k1_funct_1(B_193,C_194),A_195)
      | ~ r2_hidden(C_194,k1_relat_1(B_193))
      | ~ v1_funct_1(B_193)
      | ~ v5_relat_1(B_193,A_195)
      | ~ v1_relat_1(B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_76,plain,(
    ~ r2_hidden(k1_funct_1('#skF_8','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_918,plain,
    ( ~ r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_891,c_76])).

tff(c_928,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_268,c_84,c_918])).

tff(c_58,plain,(
    ! [A_57] :
      ( r2_hidden('#skF_5'(A_57),A_57)
      | k1_xboole_0 = A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_30,plain,(
    ! [A_27] :
      ( k10_relat_1(A_27,k2_relat_1(A_27)) = k1_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_60,plain,(
    ! [A_79,B_80] : k1_mcart_1(k4_tarski(A_79,B_80)) = A_79 ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_544,plain,(
    ! [A_165,B_166,C_167] :
      ( r2_hidden(k4_tarski(A_165,'#skF_2'(A_165,B_166,C_167)),C_167)
      | ~ r2_hidden(A_165,k10_relat_1(C_167,B_166))
      | ~ v1_relat_1(C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [C_14,A_11,B_12] :
      ( r2_hidden(C_14,A_11)
      | ~ r2_hidden(C_14,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8097,plain,(
    ! [A_568,B_569,C_570,A_571] :
      ( r2_hidden(k4_tarski(A_568,'#skF_2'(A_568,B_569,C_570)),A_571)
      | ~ m1_subset_1(C_570,k1_zfmisc_1(A_571))
      | ~ r2_hidden(A_568,k10_relat_1(C_570,B_569))
      | ~ v1_relat_1(C_570) ) ),
    inference(resolution,[status(thm)],[c_544,c_14])).

tff(c_54,plain,(
    ! [A_54,B_55,C_56] :
      ( k1_mcart_1(A_54) = B_55
      | ~ r2_hidden(A_54,k2_zfmisc_1(k1_tarski(B_55),C_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_8172,plain,(
    ! [C_56,B_569,A_568,C_570,B_55] :
      ( k1_mcart_1(k4_tarski(A_568,'#skF_2'(A_568,B_569,C_570))) = B_55
      | ~ m1_subset_1(C_570,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_55),C_56)))
      | ~ r2_hidden(A_568,k10_relat_1(C_570,B_569))
      | ~ v1_relat_1(C_570) ) ),
    inference(resolution,[status(thm)],[c_8097,c_54])).

tff(c_17568,plain,(
    ! [B_877,A_878,C_876,B_879,C_875] :
      ( B_877 = A_878
      | ~ m1_subset_1(C_876,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_877),C_875)))
      | ~ r2_hidden(A_878,k10_relat_1(C_876,B_879))
      | ~ v1_relat_1(C_876) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_8172])).

tff(c_17606,plain,(
    ! [A_878,B_879] :
      ( A_878 = '#skF_6'
      | ~ r2_hidden(A_878,k10_relat_1('#skF_8',B_879))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_80,c_17568])).

tff(c_17626,plain,(
    ! [A_880,B_881] :
      ( A_880 = '#skF_6'
      | ~ r2_hidden(A_880,k10_relat_1('#skF_8',B_881)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_17606])).

tff(c_17744,plain,(
    ! [A_880] :
      ( A_880 = '#skF_6'
      | ~ r2_hidden(A_880,k1_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_17626])).

tff(c_17794,plain,(
    ! [A_882] :
      ( A_882 = '#skF_6'
      | ~ r2_hidden(A_882,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_17744])).

tff(c_17878,plain,
    ( '#skF_5'(k1_relat_1('#skF_8')) = '#skF_6'
    | k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_17794])).

tff(c_17901,plain,(
    '#skF_5'(k1_relat_1('#skF_8')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_17878])).

tff(c_18036,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_17901,c_58])).

tff(c_18064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_928,c_18036])).

tff(c_18065,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18076,plain,(
    ! [A_1] : r1_tarski('#skF_8',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18065,c_2])).

tff(c_143,plain,(
    ! [A_102,B_103] :
      ( r2_hidden(A_102,B_103)
      | v1_xboole_0(B_103)
      | ~ m1_subset_1(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    ! [B_34,A_33] :
      ( ~ r1_tarski(B_34,A_33)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_18190,plain,(
    ! [B_915,A_916] :
      ( ~ r1_tarski(B_915,A_916)
      | v1_xboole_0(B_915)
      | ~ m1_subset_1(A_916,B_915) ) ),
    inference(resolution,[status(thm)],[c_143,c_38])).

tff(c_18194,plain,(
    ! [A_1] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_1,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18076,c_18190])).

tff(c_18196,plain,(
    ! [A_917] : ~ m1_subset_1(A_917,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_18194])).

tff(c_18201,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_18196])).

tff(c_18202,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_18194])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_18077,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18065,c_78])).

tff(c_82,plain,(
    v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_16,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18075,plain,(
    ! [A_15] : m1_subset_1('#skF_8',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18065,c_16])).

tff(c_74,plain,(
    ! [B_82,A_81,C_83] :
      ( k1_xboole_0 = B_82
      | k1_relset_1(A_81,B_82,C_83) = A_81
      | ~ v1_funct_2(C_83,A_81,B_82)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_19156,plain,(
    ! [B_994,A_995,C_996] :
      ( B_994 = '#skF_8'
      | k1_relset_1(A_995,B_994,C_996) = A_995
      | ~ v1_funct_2(C_996,A_995,B_994)
      | ~ m1_subset_1(C_996,k1_zfmisc_1(k2_zfmisc_1(A_995,B_994))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18065,c_74])).

tff(c_19189,plain,(
    ! [B_998,A_999] :
      ( B_998 = '#skF_8'
      | k1_relset_1(A_999,B_998,'#skF_8') = A_999
      | ~ v1_funct_2('#skF_8',A_999,B_998) ) ),
    inference(resolution,[status(thm)],[c_18075,c_19156])).

tff(c_19198,plain,
    ( '#skF_7' = '#skF_8'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_19189])).

tff(c_19204,plain,(
    k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_18077,c_19198])).

tff(c_18073,plain,(
    ! [A_57] :
      ( r2_hidden('#skF_5'(A_57),A_57)
      | A_57 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18065,c_58])).

tff(c_21013,plain,(
    ! [D_1112,A_1113,B_1114,C_1115] :
      ( r2_hidden(k4_tarski(D_1112,'#skF_4'(A_1113,B_1114,C_1115,D_1112)),C_1115)
      | ~ r2_hidden(D_1112,B_1114)
      | k1_relset_1(B_1114,A_1113,C_1115) != B_1114
      | ~ m1_subset_1(C_1115,k1_zfmisc_1(k2_zfmisc_1(B_1114,A_1113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_18229,plain,(
    ! [A_926,B_927,C_928] :
      ( r2_hidden('#skF_2'(A_926,B_927,C_928),B_927)
      | ~ r2_hidden(A_926,k10_relat_1(C_928,B_927))
      | ~ v1_relat_1(C_928) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18642,plain,(
    ! [B_962,A_963,C_964] :
      ( ~ r1_tarski(B_962,'#skF_2'(A_963,B_962,C_964))
      | ~ r2_hidden(A_963,k10_relat_1(C_964,B_962))
      | ~ v1_relat_1(C_964) ) ),
    inference(resolution,[status(thm)],[c_18229,c_38])).

tff(c_18647,plain,(
    ! [A_965,C_966] :
      ( ~ r2_hidden(A_965,k10_relat_1(C_966,'#skF_8'))
      | ~ v1_relat_1(C_966) ) ),
    inference(resolution,[status(thm)],[c_18076,c_18642])).

tff(c_18678,plain,(
    ! [C_967] :
      ( ~ v1_relat_1(C_967)
      | k10_relat_1(C_967,'#skF_8') = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_18073,c_18647])).

tff(c_18686,plain,(
    k10_relat_1('#skF_8','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_174,c_18678])).

tff(c_18646,plain,(
    ! [A_963,C_964] :
      ( ~ r2_hidden(A_963,k10_relat_1(C_964,'#skF_8'))
      | ~ v1_relat_1(C_964) ) ),
    inference(resolution,[status(thm)],[c_18076,c_18642])).

tff(c_18712,plain,(
    ! [A_963] :
      ( ~ r2_hidden(A_963,'#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18686,c_18646])).

tff(c_18716,plain,(
    ! [A_963] : ~ r2_hidden(A_963,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_18712])).

tff(c_21042,plain,(
    ! [D_1112,B_1114,A_1113] :
      ( ~ r2_hidden(D_1112,B_1114)
      | k1_relset_1(B_1114,A_1113,'#skF_8') != B_1114
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(B_1114,A_1113))) ) ),
    inference(resolution,[status(thm)],[c_21013,c_18716])).

tff(c_21082,plain,(
    ! [D_1116,B_1117,A_1118] :
      ( ~ r2_hidden(D_1116,B_1117)
      | k1_relset_1(B_1117,A_1118,'#skF_8') != B_1117 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18075,c_21042])).

tff(c_21119,plain,(
    ! [A_1119,A_1120] :
      ( k1_relset_1(A_1119,A_1120,'#skF_8') != A_1119
      | A_1119 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_18073,c_21082])).

tff(c_21136,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_19204,c_21119])).

tff(c_10,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_21183,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_21136,c_10])).

tff(c_21193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18202,c_21183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.20/4.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.20/4.14  
% 10.20/4.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.20/4.14  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 10.20/4.14  
% 10.20/4.14  %Foreground sorts:
% 10.20/4.14  
% 10.20/4.14  
% 10.20/4.14  %Background operators:
% 10.20/4.14  
% 10.20/4.14  
% 10.20/4.14  %Foreground operators:
% 10.20/4.14  tff('#skF_5', type, '#skF_5': $i > $i).
% 10.20/4.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.20/4.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.20/4.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.20/4.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.20/4.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.20/4.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.20/4.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.20/4.14  tff('#skF_7', type, '#skF_7': $i).
% 10.20/4.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.20/4.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.20/4.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.20/4.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.20/4.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.20/4.14  tff('#skF_6', type, '#skF_6': $i).
% 10.20/4.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.20/4.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.20/4.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.20/4.14  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.20/4.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.20/4.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.20/4.14  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.20/4.14  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 10.20/4.14  tff('#skF_8', type, '#skF_8': $i).
% 10.20/4.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.20/4.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.20/4.14  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 10.20/4.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.20/4.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.20/4.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.20/4.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.20/4.14  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 10.20/4.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.20/4.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.20/4.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.20/4.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.20/4.14  
% 10.20/4.16  tff(f_39, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 10.20/4.16  tff(f_182, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 10.20/4.16  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.20/4.16  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 10.20/4.16  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.20/4.16  tff(f_94, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 10.20/4.16  tff(f_148, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 10.20/4.16  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 10.20/4.16  tff(f_152, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 10.20/4.16  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 10.20/4.16  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 10.20/4.16  tff(f_127, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 10.20/4.16  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.20/4.16  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 10.20/4.16  tff(f_99, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 10.20/4.16  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.20/4.16  tff(f_170, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.20/4.16  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 10.20/4.16  tff(f_36, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 10.20/4.16  tff(c_12, plain, (![A_9]: (m1_subset_1('#skF_1'(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.20/4.16  tff(c_80, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 10.20/4.16  tff(c_162, plain, (![C_105, A_106, B_107]: (v1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.20/4.16  tff(c_174, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_80, c_162])).
% 10.20/4.16  tff(c_34, plain, (![A_28]: (k1_relat_1(A_28)!=k1_xboole_0 | k1_xboole_0=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.20/4.16  tff(c_183, plain, (k1_relat_1('#skF_8')!=k1_xboole_0 | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_174, c_34])).
% 10.20/4.16  tff(c_212, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_183])).
% 10.20/4.16  tff(c_256, plain, (![C_125, B_126, A_127]: (v5_relat_1(C_125, B_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.20/4.16  tff(c_268, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_80, c_256])).
% 10.20/4.16  tff(c_84, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_182])).
% 10.20/4.16  tff(c_891, plain, (![B_193, C_194, A_195]: (r2_hidden(k1_funct_1(B_193, C_194), A_195) | ~r2_hidden(C_194, k1_relat_1(B_193)) | ~v1_funct_1(B_193) | ~v5_relat_1(B_193, A_195) | ~v1_relat_1(B_193))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.20/4.16  tff(c_76, plain, (~r2_hidden(k1_funct_1('#skF_8', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_182])).
% 10.20/4.16  tff(c_918, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_891, c_76])).
% 10.20/4.16  tff(c_928, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_268, c_84, c_918])).
% 10.20/4.16  tff(c_58, plain, (![A_57]: (r2_hidden('#skF_5'(A_57), A_57) | k1_xboole_0=A_57)), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.20/4.16  tff(c_30, plain, (![A_27]: (k10_relat_1(A_27, k2_relat_1(A_27))=k1_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.20/4.16  tff(c_60, plain, (![A_79, B_80]: (k1_mcart_1(k4_tarski(A_79, B_80))=A_79)), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.20/4.16  tff(c_544, plain, (![A_165, B_166, C_167]: (r2_hidden(k4_tarski(A_165, '#skF_2'(A_165, B_166, C_167)), C_167) | ~r2_hidden(A_165, k10_relat_1(C_167, B_166)) | ~v1_relat_1(C_167))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.20/4.16  tff(c_14, plain, (![C_14, A_11, B_12]: (r2_hidden(C_14, A_11) | ~r2_hidden(C_14, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.20/4.16  tff(c_8097, plain, (![A_568, B_569, C_570, A_571]: (r2_hidden(k4_tarski(A_568, '#skF_2'(A_568, B_569, C_570)), A_571) | ~m1_subset_1(C_570, k1_zfmisc_1(A_571)) | ~r2_hidden(A_568, k10_relat_1(C_570, B_569)) | ~v1_relat_1(C_570))), inference(resolution, [status(thm)], [c_544, c_14])).
% 10.20/4.16  tff(c_54, plain, (![A_54, B_55, C_56]: (k1_mcart_1(A_54)=B_55 | ~r2_hidden(A_54, k2_zfmisc_1(k1_tarski(B_55), C_56)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.20/4.16  tff(c_8172, plain, (![C_56, B_569, A_568, C_570, B_55]: (k1_mcart_1(k4_tarski(A_568, '#skF_2'(A_568, B_569, C_570)))=B_55 | ~m1_subset_1(C_570, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_55), C_56))) | ~r2_hidden(A_568, k10_relat_1(C_570, B_569)) | ~v1_relat_1(C_570))), inference(resolution, [status(thm)], [c_8097, c_54])).
% 10.20/4.16  tff(c_17568, plain, (![B_877, A_878, C_876, B_879, C_875]: (B_877=A_878 | ~m1_subset_1(C_876, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_877), C_875))) | ~r2_hidden(A_878, k10_relat_1(C_876, B_879)) | ~v1_relat_1(C_876))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_8172])).
% 10.20/4.16  tff(c_17606, plain, (![A_878, B_879]: (A_878='#skF_6' | ~r2_hidden(A_878, k10_relat_1('#skF_8', B_879)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_80, c_17568])).
% 10.20/4.16  tff(c_17626, plain, (![A_880, B_881]: (A_880='#skF_6' | ~r2_hidden(A_880, k10_relat_1('#skF_8', B_881)))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_17606])).
% 10.20/4.16  tff(c_17744, plain, (![A_880]: (A_880='#skF_6' | ~r2_hidden(A_880, k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_17626])).
% 10.20/4.16  tff(c_17794, plain, (![A_882]: (A_882='#skF_6' | ~r2_hidden(A_882, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_17744])).
% 10.20/4.16  tff(c_17878, plain, ('#skF_5'(k1_relat_1('#skF_8'))='#skF_6' | k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_17794])).
% 10.20/4.16  tff(c_17901, plain, ('#skF_5'(k1_relat_1('#skF_8'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_212, c_17878])).
% 10.20/4.16  tff(c_18036, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | k1_relat_1('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_17901, c_58])).
% 10.20/4.16  tff(c_18064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_928, c_18036])).
% 10.20/4.16  tff(c_18065, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_183])).
% 10.20/4.16  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.20/4.16  tff(c_18076, plain, (![A_1]: (r1_tarski('#skF_8', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_18065, c_2])).
% 10.20/4.16  tff(c_143, plain, (![A_102, B_103]: (r2_hidden(A_102, B_103) | v1_xboole_0(B_103) | ~m1_subset_1(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.20/4.16  tff(c_38, plain, (![B_34, A_33]: (~r1_tarski(B_34, A_33) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.20/4.16  tff(c_18190, plain, (![B_915, A_916]: (~r1_tarski(B_915, A_916) | v1_xboole_0(B_915) | ~m1_subset_1(A_916, B_915))), inference(resolution, [status(thm)], [c_143, c_38])).
% 10.20/4.16  tff(c_18194, plain, (![A_1]: (v1_xboole_0('#skF_8') | ~m1_subset_1(A_1, '#skF_8'))), inference(resolution, [status(thm)], [c_18076, c_18190])).
% 10.20/4.16  tff(c_18196, plain, (![A_917]: (~m1_subset_1(A_917, '#skF_8'))), inference(splitLeft, [status(thm)], [c_18194])).
% 10.20/4.16  tff(c_18201, plain, $false, inference(resolution, [status(thm)], [c_12, c_18196])).
% 10.20/4.16  tff(c_18202, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_18194])).
% 10.20/4.16  tff(c_78, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_182])).
% 10.20/4.16  tff(c_18077, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_18065, c_78])).
% 10.20/4.16  tff(c_82, plain, (v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_182])).
% 10.20/4.16  tff(c_16, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.20/4.16  tff(c_18075, plain, (![A_15]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_18065, c_16])).
% 10.20/4.16  tff(c_74, plain, (![B_82, A_81, C_83]: (k1_xboole_0=B_82 | k1_relset_1(A_81, B_82, C_83)=A_81 | ~v1_funct_2(C_83, A_81, B_82) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.20/4.16  tff(c_19156, plain, (![B_994, A_995, C_996]: (B_994='#skF_8' | k1_relset_1(A_995, B_994, C_996)=A_995 | ~v1_funct_2(C_996, A_995, B_994) | ~m1_subset_1(C_996, k1_zfmisc_1(k2_zfmisc_1(A_995, B_994))))), inference(demodulation, [status(thm), theory('equality')], [c_18065, c_74])).
% 10.20/4.16  tff(c_19189, plain, (![B_998, A_999]: (B_998='#skF_8' | k1_relset_1(A_999, B_998, '#skF_8')=A_999 | ~v1_funct_2('#skF_8', A_999, B_998))), inference(resolution, [status(thm)], [c_18075, c_19156])).
% 10.20/4.16  tff(c_19198, plain, ('#skF_7'='#skF_8' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_82, c_19189])).
% 10.20/4.16  tff(c_19204, plain, (k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_18077, c_19198])).
% 10.20/4.16  tff(c_18073, plain, (![A_57]: (r2_hidden('#skF_5'(A_57), A_57) | A_57='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18065, c_58])).
% 10.20/4.16  tff(c_21013, plain, (![D_1112, A_1113, B_1114, C_1115]: (r2_hidden(k4_tarski(D_1112, '#skF_4'(A_1113, B_1114, C_1115, D_1112)), C_1115) | ~r2_hidden(D_1112, B_1114) | k1_relset_1(B_1114, A_1113, C_1115)!=B_1114 | ~m1_subset_1(C_1115, k1_zfmisc_1(k2_zfmisc_1(B_1114, A_1113))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/4.16  tff(c_18229, plain, (![A_926, B_927, C_928]: (r2_hidden('#skF_2'(A_926, B_927, C_928), B_927) | ~r2_hidden(A_926, k10_relat_1(C_928, B_927)) | ~v1_relat_1(C_928))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.20/4.16  tff(c_18642, plain, (![B_962, A_963, C_964]: (~r1_tarski(B_962, '#skF_2'(A_963, B_962, C_964)) | ~r2_hidden(A_963, k10_relat_1(C_964, B_962)) | ~v1_relat_1(C_964))), inference(resolution, [status(thm)], [c_18229, c_38])).
% 10.20/4.16  tff(c_18647, plain, (![A_965, C_966]: (~r2_hidden(A_965, k10_relat_1(C_966, '#skF_8')) | ~v1_relat_1(C_966))), inference(resolution, [status(thm)], [c_18076, c_18642])).
% 10.20/4.16  tff(c_18678, plain, (![C_967]: (~v1_relat_1(C_967) | k10_relat_1(C_967, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_18073, c_18647])).
% 10.20/4.16  tff(c_18686, plain, (k10_relat_1('#skF_8', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_174, c_18678])).
% 10.20/4.16  tff(c_18646, plain, (![A_963, C_964]: (~r2_hidden(A_963, k10_relat_1(C_964, '#skF_8')) | ~v1_relat_1(C_964))), inference(resolution, [status(thm)], [c_18076, c_18642])).
% 10.20/4.16  tff(c_18712, plain, (![A_963]: (~r2_hidden(A_963, '#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18686, c_18646])).
% 10.20/4.16  tff(c_18716, plain, (![A_963]: (~r2_hidden(A_963, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_18712])).
% 10.20/4.16  tff(c_21042, plain, (![D_1112, B_1114, A_1113]: (~r2_hidden(D_1112, B_1114) | k1_relset_1(B_1114, A_1113, '#skF_8')!=B_1114 | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(B_1114, A_1113))))), inference(resolution, [status(thm)], [c_21013, c_18716])).
% 10.20/4.16  tff(c_21082, plain, (![D_1116, B_1117, A_1118]: (~r2_hidden(D_1116, B_1117) | k1_relset_1(B_1117, A_1118, '#skF_8')!=B_1117)), inference(demodulation, [status(thm), theory('equality')], [c_18075, c_21042])).
% 10.20/4.16  tff(c_21119, plain, (![A_1119, A_1120]: (k1_relset_1(A_1119, A_1120, '#skF_8')!=A_1119 | A_1119='#skF_8')), inference(resolution, [status(thm)], [c_18073, c_21082])).
% 10.20/4.16  tff(c_21136, plain, (k1_tarski('#skF_6')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_19204, c_21119])).
% 10.20/4.16  tff(c_10, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.20/4.16  tff(c_21183, plain, (~v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_21136, c_10])).
% 10.20/4.16  tff(c_21193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18202, c_21183])).
% 10.20/4.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.20/4.16  
% 10.20/4.16  Inference rules
% 10.20/4.16  ----------------------
% 10.20/4.16  #Ref     : 0
% 10.20/4.16  #Sup     : 4812
% 10.20/4.16  #Fact    : 0
% 10.20/4.16  #Define  : 0
% 10.20/4.16  #Split   : 24
% 10.20/4.16  #Chain   : 0
% 10.20/4.16  #Close   : 0
% 10.20/4.16  
% 10.20/4.16  Ordering : KBO
% 10.20/4.16  
% 10.20/4.16  Simplification rules
% 10.20/4.16  ----------------------
% 10.20/4.16  #Subsume      : 1554
% 10.20/4.16  #Demod        : 3743
% 10.20/4.16  #Tautology    : 1444
% 10.20/4.16  #SimpNegUnit  : 46
% 10.20/4.16  #BackRed      : 100
% 10.20/4.16  
% 10.20/4.16  #Partial instantiations: 0
% 10.20/4.16  #Strategies tried      : 1
% 10.20/4.16  
% 10.20/4.16  Timing (in seconds)
% 10.20/4.16  ----------------------
% 10.20/4.16  Preprocessing        : 0.38
% 10.20/4.16  Parsing              : 0.20
% 10.20/4.16  CNF conversion       : 0.03
% 10.20/4.16  Main loop            : 3.01
% 10.20/4.16  Inferencing          : 0.81
% 10.20/4.16  Reduction            : 0.99
% 10.20/4.16  Demodulation         : 0.71
% 10.20/4.16  BG Simplification    : 0.08
% 10.20/4.16  Subsumption          : 0.92
% 10.20/4.16  Abstraction          : 0.12
% 10.20/4.16  MUC search           : 0.00
% 10.20/4.16  Cooper               : 0.00
% 10.20/4.16  Total                : 3.43
% 10.37/4.16  Index Insertion      : 0.00
% 10.37/4.16  Index Deletion       : 0.00
% 10.37/4.16  Index Matching       : 0.00
% 10.37/4.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
