%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:14 EST 2020

% Result     : Theorem 10.26s
% Output     : CNFRefutation 10.26s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 271 expanded)
%              Number of leaves         :   45 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          :  175 ( 539 expanded)
%              Number of equality atoms :   45 ( 145 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_78,plain,(
    k1_funct_1('#skF_11','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_178,plain,(
    ! [A_106,B_107] :
      ( ~ r2_hidden('#skF_1'(A_106,B_107),B_107)
      | r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_183,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_178])).

tff(c_80,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_237,plain,(
    ! [C_121,B_122,A_123] :
      ( r2_hidden(C_121,B_122)
      | ~ r2_hidden(C_121,A_123)
      | ~ r1_tarski(A_123,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_252,plain,(
    ! [B_122] :
      ( r2_hidden('#skF_10',B_122)
      | ~ r1_tarski('#skF_8',B_122) ) ),
    inference(resolution,[status(thm)],[c_80,c_237])).

tff(c_82,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_152,plain,(
    ! [C_98,A_99,B_100] :
      ( v1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_161,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_82,c_152])).

tff(c_86,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_84,plain,(
    v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_281,plain,(
    ! [A_127,B_128,C_129] :
      ( k1_relset_1(A_127,B_128,C_129) = k1_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_290,plain,(
    k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_82,c_281])).

tff(c_2304,plain,(
    ! [B_310,A_311,C_312] :
      ( k1_xboole_0 = B_310
      | k1_relset_1(A_311,B_310,C_312) = A_311
      | ~ v1_funct_2(C_312,A_311,B_310)
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_311,B_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2319,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_82,c_2304])).

tff(c_2326,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relat_1('#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_290,c_2319])).

tff(c_2327,plain,(
    k1_relat_1('#skF_11') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2326])).

tff(c_38,plain,(
    ! [A_21,D_60] :
      ( r2_hidden(k1_funct_1(A_21,D_60),k2_relat_1(A_21))
      | ~ r2_hidden(D_60,k1_relat_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_184,plain,(
    ! [D_108,B_109,A_110] :
      ( D_108 = B_109
      | D_108 = A_110
      | ~ r2_hidden(D_108,k2_tarski(A_110,B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_226,plain,(
    ! [D_119,A_120] :
      ( D_119 = A_120
      | D_119 = A_120
      | ~ r2_hidden(D_119,k1_tarski(A_120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_184])).

tff(c_234,plain,(
    ! [A_120,B_2] :
      ( '#skF_1'(k1_tarski(A_120),B_2) = A_120
      | r1_tarski(k1_tarski(A_120),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_226])).

tff(c_89,plain,(
    ! [A_81] : k2_tarski(A_81,A_81) = k1_tarski(A_81) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [D_12,B_8] : r2_hidden(D_12,k2_tarski(D_12,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    ! [A_81] : r2_hidden(A_81,k1_tarski(A_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_14])).

tff(c_107,plain,(
    ! [B_85,A_86] :
      ( ~ r1_tarski(B_85,A_86)
      | ~ r2_hidden(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_121,plain,(
    ! [A_81] : ~ r1_tarski(k1_tarski(A_81),A_81) ),
    inference(resolution,[status(thm)],[c_95,c_107])).

tff(c_336,plain,(
    ! [A_142,B_143] :
      ( '#skF_1'(k1_tarski(A_142),B_143) = A_142
      | r1_tarski(k1_tarski(A_142),B_143) ) ),
    inference(resolution,[status(thm)],[c_6,c_226])).

tff(c_362,plain,(
    ! [B_143] : '#skF_1'(k1_tarski(B_143),B_143) = B_143 ),
    inference(resolution,[status(thm)],[c_336,c_121])).

tff(c_497,plain,(
    ! [A_159,B_160,C_161] :
      ( k2_relset_1(A_159,B_160,C_161) = k2_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_506,plain,(
    k2_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_82,c_497])).

tff(c_637,plain,(
    ! [A_181,B_182,C_183] :
      ( m1_subset_1(k2_relset_1(A_181,B_182,C_183),k1_zfmisc_1(B_182))
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_661,plain,
    ( m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1(k1_tarski('#skF_9')))
    | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_637])).

tff(c_667,plain,(
    m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1(k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_661])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_671,plain,(
    r1_tarski(k2_relat_1('#skF_11'),k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_667,c_34])).

tff(c_520,plain,(
    ! [A_164,B_165,B_166] :
      ( r2_hidden('#skF_1'(A_164,B_165),B_166)
      | ~ r1_tarski(A_164,B_166)
      | r1_tarski(A_164,B_165) ) ),
    inference(resolution,[status(thm)],[c_6,c_237])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9856,plain,(
    ! [A_28312,B_28313,B_28314,B_28315] :
      ( r2_hidden('#skF_1'(A_28312,B_28313),B_28314)
      | ~ r1_tarski(B_28315,B_28314)
      | ~ r1_tarski(A_28312,B_28315)
      | r1_tarski(A_28312,B_28313) ) ),
    inference(resolution,[status(thm)],[c_520,c_2])).

tff(c_9911,plain,(
    ! [A_28436,B_28437] :
      ( r2_hidden('#skF_1'(A_28436,B_28437),k1_tarski('#skF_9'))
      | ~ r1_tarski(A_28436,k2_relat_1('#skF_11'))
      | r1_tarski(A_28436,B_28437) ) ),
    inference(resolution,[status(thm)],[c_671,c_9856])).

tff(c_10036,plain,(
    ! [B_143] :
      ( r2_hidden(B_143,k1_tarski('#skF_9'))
      | ~ r1_tarski(k1_tarski(B_143),k2_relat_1('#skF_11'))
      | r1_tarski(k1_tarski(B_143),B_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_9911])).

tff(c_10858,plain,(
    ! [B_29891] :
      ( r2_hidden(B_29891,k1_tarski('#skF_9'))
      | ~ r1_tarski(k1_tarski(B_29891),k2_relat_1('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_10036])).

tff(c_11373,plain,(
    ! [A_30862] :
      ( r2_hidden(A_30862,k1_tarski('#skF_9'))
      | '#skF_1'(k1_tarski(A_30862),k2_relat_1('#skF_11')) = A_30862 ) ),
    inference(resolution,[status(thm)],[c_234,c_10858])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_15632,plain,(
    ! [A_37433] :
      ( ~ r2_hidden(A_37433,k2_relat_1('#skF_11'))
      | r1_tarski(k1_tarski(A_37433),k2_relat_1('#skF_11'))
      | r2_hidden(A_37433,k1_tarski('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11373,c_4])).

tff(c_10063,plain,(
    ! [B_143] :
      ( r2_hidden(B_143,k1_tarski('#skF_9'))
      | ~ r1_tarski(k1_tarski(B_143),k2_relat_1('#skF_11')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_10036])).

tff(c_15763,plain,(
    ! [A_37554] :
      ( ~ r2_hidden(A_37554,k2_relat_1('#skF_11'))
      | r2_hidden(A_37554,k1_tarski('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_15632,c_10063])).

tff(c_15826,plain,(
    ! [D_60] :
      ( r2_hidden(k1_funct_1('#skF_11',D_60),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_60,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_38,c_15763])).

tff(c_16043,plain,(
    ! [D_37797] :
      ( r2_hidden(k1_funct_1('#skF_11',D_37797),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_37797,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_86,c_2327,c_15826])).

tff(c_194,plain,(
    ! [D_108,A_13] :
      ( D_108 = A_13
      | D_108 = A_13
      | ~ r2_hidden(D_108,k1_tarski(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_184])).

tff(c_16120,plain,(
    ! [D_37918] :
      ( k1_funct_1('#skF_11',D_37918) = '#skF_9'
      | ~ r2_hidden(D_37918,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_16043,c_194])).

tff(c_16167,plain,
    ( k1_funct_1('#skF_11','#skF_10') = '#skF_9'
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_252,c_16120])).

tff(c_16190,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_16167])).

tff(c_16192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_16190])).

tff(c_16193,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2326])).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_559,plain,(
    ! [A_169,B_170,A_171] :
      ( k2_relset_1(A_169,B_170,A_171) = k2_relat_1(A_171)
      | ~ r1_tarski(A_171,k2_zfmisc_1(A_169,B_170)) ) ),
    inference(resolution,[status(thm)],[c_36,c_497])).

tff(c_576,plain,(
    ! [A_169,B_170] : k2_relset_1(A_169,B_170,k2_zfmisc_1(A_169,B_170)) = k2_relat_1(k2_zfmisc_1(A_169,B_170)) ),
    inference(resolution,[status(thm)],[c_183,c_559])).

tff(c_1558,plain,(
    ! [A_237,B_238,C_239] :
      ( r1_tarski(k2_relset_1(A_237,B_238,C_239),B_238)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(resolution,[status(thm)],[c_637,c_34])).

tff(c_1576,plain,(
    ! [A_240,B_241,A_242] :
      ( r1_tarski(k2_relset_1(A_240,B_241,A_242),B_241)
      | ~ r1_tarski(A_242,k2_zfmisc_1(A_240,B_241)) ) ),
    inference(resolution,[status(thm)],[c_36,c_1558])).

tff(c_1609,plain,(
    ! [A_169,B_170] :
      ( r1_tarski(k2_relat_1(k2_zfmisc_1(A_169,B_170)),B_170)
      | ~ r1_tarski(k2_zfmisc_1(A_169,B_170),k2_zfmisc_1(A_169,B_170)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_1576])).

tff(c_1638,plain,(
    ! [A_245,B_246] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_245,B_246)),B_246) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_1609])).

tff(c_56,plain,(
    ! [B_62,A_61] :
      ( ~ r1_tarski(B_62,A_61)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_556,plain,(
    ! [B_166,A_164,B_165] :
      ( ~ r1_tarski(B_166,'#skF_1'(A_164,B_165))
      | ~ r1_tarski(A_164,B_166)
      | r1_tarski(A_164,B_165) ) ),
    inference(resolution,[status(thm)],[c_520,c_56])).

tff(c_1807,plain,(
    ! [A_270,A_271,B_272] :
      ( ~ r1_tarski(A_270,k2_relat_1(k2_zfmisc_1(A_271,'#skF_1'(A_270,B_272))))
      | r1_tarski(A_270,B_272) ) ),
    inference(resolution,[status(thm)],[c_1638,c_556])).

tff(c_1846,plain,(
    ! [B_143,A_271] :
      ( ~ r1_tarski(k1_tarski(B_143),k2_relat_1(k2_zfmisc_1(A_271,B_143)))
      | r1_tarski(k1_tarski(B_143),B_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_1807])).

tff(c_1861,plain,(
    ! [B_143,A_271] : ~ r1_tarski(k1_tarski(B_143),k2_relat_1(k2_zfmisc_1(A_271,B_143))) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_1846])).

tff(c_16214,plain,(
    ! [A_271] : ~ r1_tarski(k1_xboole_0,k2_relat_1(k2_zfmisc_1(A_271,'#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16193,c_1861])).

tff(c_16264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:23:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.26/3.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.26/3.43  
% 10.26/3.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.26/3.43  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 10.26/3.43  
% 10.26/3.43  %Foreground sorts:
% 10.26/3.43  
% 10.26/3.43  
% 10.26/3.43  %Background operators:
% 10.26/3.43  
% 10.26/3.43  
% 10.26/3.43  %Foreground operators:
% 10.26/3.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.26/3.43  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 10.26/3.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.26/3.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.26/3.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.26/3.43  tff('#skF_11', type, '#skF_11': $i).
% 10.26/3.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.26/3.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.26/3.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.26/3.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.26/3.43  tff('#skF_10', type, '#skF_10': $i).
% 10.26/3.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.26/3.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.26/3.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.26/3.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.26/3.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.26/3.43  tff('#skF_9', type, '#skF_9': $i).
% 10.26/3.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.26/3.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.26/3.43  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 10.26/3.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.26/3.43  tff('#skF_8', type, '#skF_8': $i).
% 10.26/3.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.26/3.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.26/3.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.26/3.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.26/3.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.26/3.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.26/3.43  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.26/3.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.26/3.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.26/3.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.26/3.43  
% 10.26/3.45  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.26/3.45  tff(f_118, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 10.26/3.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.26/3.45  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.26/3.45  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.26/3.45  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.26/3.45  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 10.26/3.45  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.26/3.45  tff(f_43, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 10.26/3.45  tff(f_73, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 10.26/3.45  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.26/3.45  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 10.26/3.45  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.26/3.45  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.26/3.45  tff(c_78, plain, (k1_funct_1('#skF_11', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.26/3.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.26/3.45  tff(c_178, plain, (![A_106, B_107]: (~r2_hidden('#skF_1'(A_106, B_107), B_107) | r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.26/3.45  tff(c_183, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_178])).
% 10.26/3.45  tff(c_80, plain, (r2_hidden('#skF_10', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.26/3.45  tff(c_237, plain, (![C_121, B_122, A_123]: (r2_hidden(C_121, B_122) | ~r2_hidden(C_121, A_123) | ~r1_tarski(A_123, B_122))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.26/3.45  tff(c_252, plain, (![B_122]: (r2_hidden('#skF_10', B_122) | ~r1_tarski('#skF_8', B_122))), inference(resolution, [status(thm)], [c_80, c_237])).
% 10.26/3.45  tff(c_82, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.26/3.45  tff(c_152, plain, (![C_98, A_99, B_100]: (v1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.26/3.45  tff(c_161, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_82, c_152])).
% 10.26/3.45  tff(c_86, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.26/3.45  tff(c_84, plain, (v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.26/3.45  tff(c_281, plain, (![A_127, B_128, C_129]: (k1_relset_1(A_127, B_128, C_129)=k1_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.26/3.45  tff(c_290, plain, (k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_82, c_281])).
% 10.26/3.45  tff(c_2304, plain, (![B_310, A_311, C_312]: (k1_xboole_0=B_310 | k1_relset_1(A_311, B_310, C_312)=A_311 | ~v1_funct_2(C_312, A_311, B_310) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_311, B_310))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.26/3.45  tff(c_2319, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')='#skF_8' | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_82, c_2304])).
% 10.26/3.45  tff(c_2326, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_290, c_2319])).
% 10.26/3.45  tff(c_2327, plain, (k1_relat_1('#skF_11')='#skF_8'), inference(splitLeft, [status(thm)], [c_2326])).
% 10.26/3.45  tff(c_38, plain, (![A_21, D_60]: (r2_hidden(k1_funct_1(A_21, D_60), k2_relat_1(A_21)) | ~r2_hidden(D_60, k1_relat_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.26/3.45  tff(c_28, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.26/3.45  tff(c_184, plain, (![D_108, B_109, A_110]: (D_108=B_109 | D_108=A_110 | ~r2_hidden(D_108, k2_tarski(A_110, B_109)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.26/3.45  tff(c_226, plain, (![D_119, A_120]: (D_119=A_120 | D_119=A_120 | ~r2_hidden(D_119, k1_tarski(A_120)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_184])).
% 10.26/3.45  tff(c_234, plain, (![A_120, B_2]: ('#skF_1'(k1_tarski(A_120), B_2)=A_120 | r1_tarski(k1_tarski(A_120), B_2))), inference(resolution, [status(thm)], [c_6, c_226])).
% 10.26/3.45  tff(c_89, plain, (![A_81]: (k2_tarski(A_81, A_81)=k1_tarski(A_81))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.26/3.45  tff(c_14, plain, (![D_12, B_8]: (r2_hidden(D_12, k2_tarski(D_12, B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.26/3.45  tff(c_95, plain, (![A_81]: (r2_hidden(A_81, k1_tarski(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_14])).
% 10.26/3.45  tff(c_107, plain, (![B_85, A_86]: (~r1_tarski(B_85, A_86) | ~r2_hidden(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.26/3.45  tff(c_121, plain, (![A_81]: (~r1_tarski(k1_tarski(A_81), A_81))), inference(resolution, [status(thm)], [c_95, c_107])).
% 10.26/3.45  tff(c_336, plain, (![A_142, B_143]: ('#skF_1'(k1_tarski(A_142), B_143)=A_142 | r1_tarski(k1_tarski(A_142), B_143))), inference(resolution, [status(thm)], [c_6, c_226])).
% 10.26/3.45  tff(c_362, plain, (![B_143]: ('#skF_1'(k1_tarski(B_143), B_143)=B_143)), inference(resolution, [status(thm)], [c_336, c_121])).
% 10.26/3.45  tff(c_497, plain, (![A_159, B_160, C_161]: (k2_relset_1(A_159, B_160, C_161)=k2_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.26/3.45  tff(c_506, plain, (k2_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_82, c_497])).
% 10.26/3.45  tff(c_637, plain, (![A_181, B_182, C_183]: (m1_subset_1(k2_relset_1(A_181, B_182, C_183), k1_zfmisc_1(B_182)) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.26/3.45  tff(c_661, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1(k1_tarski('#skF_9'))) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(superposition, [status(thm), theory('equality')], [c_506, c_637])).
% 10.26/3.45  tff(c_667, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1(k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_661])).
% 10.26/3.45  tff(c_34, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.26/3.45  tff(c_671, plain, (r1_tarski(k2_relat_1('#skF_11'), k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_667, c_34])).
% 10.26/3.45  tff(c_520, plain, (![A_164, B_165, B_166]: (r2_hidden('#skF_1'(A_164, B_165), B_166) | ~r1_tarski(A_164, B_166) | r1_tarski(A_164, B_165))), inference(resolution, [status(thm)], [c_6, c_237])).
% 10.26/3.45  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.26/3.45  tff(c_9856, plain, (![A_28312, B_28313, B_28314, B_28315]: (r2_hidden('#skF_1'(A_28312, B_28313), B_28314) | ~r1_tarski(B_28315, B_28314) | ~r1_tarski(A_28312, B_28315) | r1_tarski(A_28312, B_28313))), inference(resolution, [status(thm)], [c_520, c_2])).
% 10.26/3.45  tff(c_9911, plain, (![A_28436, B_28437]: (r2_hidden('#skF_1'(A_28436, B_28437), k1_tarski('#skF_9')) | ~r1_tarski(A_28436, k2_relat_1('#skF_11')) | r1_tarski(A_28436, B_28437))), inference(resolution, [status(thm)], [c_671, c_9856])).
% 10.26/3.45  tff(c_10036, plain, (![B_143]: (r2_hidden(B_143, k1_tarski('#skF_9')) | ~r1_tarski(k1_tarski(B_143), k2_relat_1('#skF_11')) | r1_tarski(k1_tarski(B_143), B_143))), inference(superposition, [status(thm), theory('equality')], [c_362, c_9911])).
% 10.26/3.45  tff(c_10858, plain, (![B_29891]: (r2_hidden(B_29891, k1_tarski('#skF_9')) | ~r1_tarski(k1_tarski(B_29891), k2_relat_1('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_121, c_10036])).
% 10.26/3.45  tff(c_11373, plain, (![A_30862]: (r2_hidden(A_30862, k1_tarski('#skF_9')) | '#skF_1'(k1_tarski(A_30862), k2_relat_1('#skF_11'))=A_30862)), inference(resolution, [status(thm)], [c_234, c_10858])).
% 10.26/3.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.26/3.45  tff(c_15632, plain, (![A_37433]: (~r2_hidden(A_37433, k2_relat_1('#skF_11')) | r1_tarski(k1_tarski(A_37433), k2_relat_1('#skF_11')) | r2_hidden(A_37433, k1_tarski('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_11373, c_4])).
% 10.26/3.45  tff(c_10063, plain, (![B_143]: (r2_hidden(B_143, k1_tarski('#skF_9')) | ~r1_tarski(k1_tarski(B_143), k2_relat_1('#skF_11')))), inference(negUnitSimplification, [status(thm)], [c_121, c_10036])).
% 10.26/3.45  tff(c_15763, plain, (![A_37554]: (~r2_hidden(A_37554, k2_relat_1('#skF_11')) | r2_hidden(A_37554, k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_15632, c_10063])).
% 10.26/3.45  tff(c_15826, plain, (![D_60]: (r2_hidden(k1_funct_1('#skF_11', D_60), k1_tarski('#skF_9')) | ~r2_hidden(D_60, k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_38, c_15763])).
% 10.26/3.45  tff(c_16043, plain, (![D_37797]: (r2_hidden(k1_funct_1('#skF_11', D_37797), k1_tarski('#skF_9')) | ~r2_hidden(D_37797, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_86, c_2327, c_15826])).
% 10.26/3.45  tff(c_194, plain, (![D_108, A_13]: (D_108=A_13 | D_108=A_13 | ~r2_hidden(D_108, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_184])).
% 10.26/3.45  tff(c_16120, plain, (![D_37918]: (k1_funct_1('#skF_11', D_37918)='#skF_9' | ~r2_hidden(D_37918, '#skF_8'))), inference(resolution, [status(thm)], [c_16043, c_194])).
% 10.26/3.45  tff(c_16167, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9' | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_252, c_16120])).
% 10.26/3.45  tff(c_16190, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_183, c_16167])).
% 10.26/3.45  tff(c_16192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_16190])).
% 10.26/3.45  tff(c_16193, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2326])).
% 10.26/3.45  tff(c_36, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.26/3.45  tff(c_559, plain, (![A_169, B_170, A_171]: (k2_relset_1(A_169, B_170, A_171)=k2_relat_1(A_171) | ~r1_tarski(A_171, k2_zfmisc_1(A_169, B_170)))), inference(resolution, [status(thm)], [c_36, c_497])).
% 10.26/3.45  tff(c_576, plain, (![A_169, B_170]: (k2_relset_1(A_169, B_170, k2_zfmisc_1(A_169, B_170))=k2_relat_1(k2_zfmisc_1(A_169, B_170)))), inference(resolution, [status(thm)], [c_183, c_559])).
% 10.26/3.45  tff(c_1558, plain, (![A_237, B_238, C_239]: (r1_tarski(k2_relset_1(A_237, B_238, C_239), B_238) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(resolution, [status(thm)], [c_637, c_34])).
% 10.26/3.45  tff(c_1576, plain, (![A_240, B_241, A_242]: (r1_tarski(k2_relset_1(A_240, B_241, A_242), B_241) | ~r1_tarski(A_242, k2_zfmisc_1(A_240, B_241)))), inference(resolution, [status(thm)], [c_36, c_1558])).
% 10.26/3.45  tff(c_1609, plain, (![A_169, B_170]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_169, B_170)), B_170) | ~r1_tarski(k2_zfmisc_1(A_169, B_170), k2_zfmisc_1(A_169, B_170)))), inference(superposition, [status(thm), theory('equality')], [c_576, c_1576])).
% 10.26/3.45  tff(c_1638, plain, (![A_245, B_246]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_245, B_246)), B_246))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_1609])).
% 10.26/3.45  tff(c_56, plain, (![B_62, A_61]: (~r1_tarski(B_62, A_61) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.26/3.45  tff(c_556, plain, (![B_166, A_164, B_165]: (~r1_tarski(B_166, '#skF_1'(A_164, B_165)) | ~r1_tarski(A_164, B_166) | r1_tarski(A_164, B_165))), inference(resolution, [status(thm)], [c_520, c_56])).
% 10.26/3.45  tff(c_1807, plain, (![A_270, A_271, B_272]: (~r1_tarski(A_270, k2_relat_1(k2_zfmisc_1(A_271, '#skF_1'(A_270, B_272)))) | r1_tarski(A_270, B_272))), inference(resolution, [status(thm)], [c_1638, c_556])).
% 10.26/3.45  tff(c_1846, plain, (![B_143, A_271]: (~r1_tarski(k1_tarski(B_143), k2_relat_1(k2_zfmisc_1(A_271, B_143))) | r1_tarski(k1_tarski(B_143), B_143))), inference(superposition, [status(thm), theory('equality')], [c_362, c_1807])).
% 10.26/3.45  tff(c_1861, plain, (![B_143, A_271]: (~r1_tarski(k1_tarski(B_143), k2_relat_1(k2_zfmisc_1(A_271, B_143))))), inference(negUnitSimplification, [status(thm)], [c_121, c_1846])).
% 10.26/3.45  tff(c_16214, plain, (![A_271]: (~r1_tarski(k1_xboole_0, k2_relat_1(k2_zfmisc_1(A_271, '#skF_9'))))), inference(superposition, [status(thm), theory('equality')], [c_16193, c_1861])).
% 10.26/3.45  tff(c_16264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_16214])).
% 10.26/3.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.26/3.45  
% 10.26/3.45  Inference rules
% 10.26/3.45  ----------------------
% 10.26/3.45  #Ref     : 0
% 10.26/3.45  #Sup     : 2374
% 10.26/3.45  #Fact    : 18
% 10.26/3.45  #Define  : 0
% 10.26/3.45  #Split   : 24
% 10.26/3.45  #Chain   : 0
% 10.26/3.45  #Close   : 0
% 10.26/3.45  
% 10.26/3.45  Ordering : KBO
% 10.26/3.45  
% 10.26/3.45  Simplification rules
% 10.26/3.45  ----------------------
% 10.26/3.45  #Subsume      : 646
% 10.26/3.45  #Demod        : 668
% 10.26/3.45  #Tautology    : 641
% 10.26/3.45  #SimpNegUnit  : 152
% 10.26/3.45  #BackRed      : 43
% 10.26/3.45  
% 10.26/3.45  #Partial instantiations: 21482
% 10.26/3.45  #Strategies tried      : 1
% 10.26/3.45  
% 10.26/3.45  Timing (in seconds)
% 10.26/3.45  ----------------------
% 10.26/3.45  Preprocessing        : 0.35
% 10.26/3.45  Parsing              : 0.17
% 10.26/3.45  CNF conversion       : 0.03
% 10.26/3.45  Main loop            : 2.27
% 10.26/3.45  Inferencing          : 0.92
% 10.26/3.45  Reduction            : 0.70
% 10.26/3.45  Demodulation         : 0.48
% 10.26/3.45  BG Simplification    : 0.07
% 10.26/3.45  Subsumption          : 0.44
% 10.26/3.45  Abstraction          : 0.08
% 10.26/3.45  MUC search           : 0.00
% 10.26/3.45  Cooper               : 0.00
% 10.26/3.45  Total                : 2.66
% 10.26/3.45  Index Insertion      : 0.00
% 10.26/3.45  Index Deletion       : 0.00
% 10.26/3.45  Index Matching       : 0.00
% 10.26/3.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
