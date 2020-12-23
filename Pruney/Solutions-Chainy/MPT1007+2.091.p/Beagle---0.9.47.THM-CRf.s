%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:23 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 5.23s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 257 expanded)
%              Number of leaves         :   42 ( 104 expanded)
%              Depth                    :   14
%              Number of atoms          :  203 ( 615 expanded)
%              Number of equality atoms :   61 ( 139 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_123,axiom,(
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

tff(f_105,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_36,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_58,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_66,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_64,plain,(
    v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_166,plain,(
    ! [C_88,A_89,B_90] :
      ( r2_hidden(C_88,A_89)
      | ~ r2_hidden(C_88,B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_940,plain,(
    ! [A_195,A_196,B_197] :
      ( r2_hidden(A_195,A_196)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(A_196))
      | v1_xboole_0(B_197)
      | ~ m1_subset_1(A_195,B_197) ) ),
    inference(resolution,[status(thm)],[c_18,c_166])).

tff(c_952,plain,(
    ! [A_195] :
      ( r2_hidden(A_195,k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_195,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_62,c_940])).

tff(c_956,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_952])).

tff(c_628,plain,(
    ! [B_140,A_141,C_142] :
      ( k1_xboole_0 = B_140
      | k1_relset_1(A_141,B_140,C_142) = A_141
      | ~ v1_funct_2(C_142,A_141,B_140)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_641,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k1_tarski('#skF_5')
    | ~ v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_628])).

tff(c_654,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_641])).

tff(c_655,plain,(
    k1_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_654])).

tff(c_38,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_4'(A_42),A_42)
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_235,plain,(
    ! [A_111,A_112] :
      ( r2_hidden('#skF_4'(A_111),A_112)
      | ~ m1_subset_1(A_111,k1_zfmisc_1(A_112))
      | k1_xboole_0 = A_111 ) ),
    inference(resolution,[status(thm)],[c_38,c_166])).

tff(c_32,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden(k1_mcart_1(A_36),B_37)
      | ~ r2_hidden(A_36,k2_zfmisc_1(B_37,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1340,plain,(
    ! [A_232,B_233,C_234] :
      ( r2_hidden(k1_mcart_1('#skF_4'(A_232)),B_233)
      | ~ m1_subset_1(A_232,k1_zfmisc_1(k2_zfmisc_1(B_233,C_234)))
      | k1_xboole_0 = A_232 ) ),
    inference(resolution,[status(thm)],[c_235,c_32])).

tff(c_1362,plain,
    ( r2_hidden(k1_mcart_1('#skF_4'('#skF_7')),k1_tarski('#skF_5'))
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_62,c_1340])).

tff(c_1366,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1362])).

tff(c_16,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_840,plain,(
    ! [D_168,A_169,B_170,C_171] :
      ( r2_hidden(k4_tarski(D_168,'#skF_3'(A_169,B_170,C_171,D_168)),C_171)
      | ~ r2_hidden(D_168,B_170)
      | k1_relset_1(B_170,A_169,C_171) != B_170
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(B_170,A_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_157,plain,(
    ! [A_85,C_86,B_87] :
      ( r2_hidden(k2_mcart_1(A_85),C_86)
      | ~ r2_hidden(A_85,k2_zfmisc_1(B_87,C_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_357,plain,(
    ! [B_122,C_123] :
      ( r2_hidden(k2_mcart_1('#skF_4'(k2_zfmisc_1(B_122,C_123))),C_123)
      | k2_zfmisc_1(B_122,C_123) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_157])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_450,plain,(
    ! [C_129,B_130] :
      ( ~ r1_tarski(C_129,k2_mcart_1('#skF_4'(k2_zfmisc_1(B_130,C_129))))
      | k2_zfmisc_1(B_130,C_129) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_357,c_22])).

tff(c_473,plain,(
    ! [B_134] : k2_zfmisc_1(B_134,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_450])).

tff(c_30,plain,(
    ! [A_36,C_38,B_37] :
      ( r2_hidden(k2_mcart_1(A_36),C_38)
      | ~ r2_hidden(A_36,k2_zfmisc_1(B_37,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_534,plain,(
    ! [A_137] :
      ( r2_hidden(k2_mcart_1(A_137),k1_xboole_0)
      | ~ r2_hidden(A_137,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_30])).

tff(c_547,plain,(
    ! [A_137] :
      ( ~ r1_tarski(k1_xboole_0,k2_mcart_1(A_137))
      | ~ r2_hidden(A_137,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_534,c_22])).

tff(c_559,plain,(
    ! [A_137] : ~ r2_hidden(A_137,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_547])).

tff(c_850,plain,(
    ! [D_168,B_170,A_169] :
      ( ~ r2_hidden(D_168,B_170)
      | k1_relset_1(B_170,A_169,k1_xboole_0) != B_170
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(B_170,A_169))) ) ),
    inference(resolution,[status(thm)],[c_840,c_559])).

tff(c_887,plain,(
    ! [D_172,B_173,A_174] :
      ( ~ r2_hidden(D_172,B_173)
      | k1_relset_1(B_173,A_174,k1_xboole_0) != B_173 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_850])).

tff(c_908,plain,(
    ! [A_42,A_174] :
      ( k1_relset_1(A_42,A_174,k1_xboole_0) != A_42
      | k1_xboole_0 = A_42 ) ),
    inference(resolution,[status(thm)],[c_38,c_887])).

tff(c_1734,plain,(
    ! [A_250,A_251] :
      ( k1_relset_1(A_250,A_251,'#skF_7') != A_250
      | A_250 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_1366,c_908])).

tff(c_1743,plain,(
    k1_tarski('#skF_5') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_1734])).

tff(c_10,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1758,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1743,c_10])).

tff(c_1765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_1758])).

tff(c_1767,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1362])).

tff(c_36,plain,(
    ! [A_39,B_40,C_41] :
      ( k1_mcart_1(A_39) = B_40
      | ~ r2_hidden(A_39,k2_zfmisc_1(k1_tarski(B_40),C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1926,plain,(
    ! [A_267,B_268,C_269] :
      ( k1_mcart_1('#skF_4'(A_267)) = B_268
      | ~ m1_subset_1(A_267,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_268),C_269)))
      | k1_xboole_0 = A_267 ) ),
    inference(resolution,[status(thm)],[c_235,c_36])).

tff(c_1940,plain,
    ( k1_mcart_1('#skF_4'('#skF_7')) = '#skF_5'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_62,c_1926])).

tff(c_1953,plain,(
    k1_mcart_1('#skF_4'('#skF_7')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1767,c_1940])).

tff(c_1766,plain,(
    r2_hidden(k1_mcart_1('#skF_4'('#skF_7')),k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1362])).

tff(c_56,plain,(
    ! [D_58,C_57,B_56,A_55] :
      ( r2_hidden(k1_funct_1(D_58,C_57),B_56)
      | k1_xboole_0 = B_56
      | ~ r2_hidden(C_57,A_55)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ v1_funct_2(D_58,A_55,B_56)
      | ~ v1_funct_1(D_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1782,plain,(
    ! [D_58,B_56] :
      ( r2_hidden(k1_funct_1(D_58,k1_mcart_1('#skF_4'('#skF_7'))),B_56)
      | k1_xboole_0 = B_56
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'),B_56)))
      | ~ v1_funct_2(D_58,k1_tarski('#skF_5'),B_56)
      | ~ v1_funct_1(D_58) ) ),
    inference(resolution,[status(thm)],[c_1766,c_56])).

tff(c_1989,plain,(
    ! [D_270,B_271] :
      ( r2_hidden(k1_funct_1(D_270,'#skF_5'),B_271)
      | k1_xboole_0 = B_271
      | ~ m1_subset_1(D_270,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'),B_271)))
      | ~ v1_funct_2(D_270,k1_tarski('#skF_5'),B_271)
      | ~ v1_funct_1(D_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1953,c_1782])).

tff(c_2004,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6')
    | k1_xboole_0 = '#skF_6'
    | ~ v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_1989])).

tff(c_2019,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2004])).

tff(c_2021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_2019])).

tff(c_2023,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_952])).

tff(c_2784,plain,(
    ! [A_343,B_344,C_345] :
      ( r2_hidden(k1_mcart_1('#skF_4'(A_343)),B_344)
      | ~ m1_subset_1(A_343,k1_zfmisc_1(k2_zfmisc_1(B_344,C_345)))
      | k1_xboole_0 = A_343 ) ),
    inference(resolution,[status(thm)],[c_235,c_32])).

tff(c_2806,plain,
    ( r2_hidden(k1_mcart_1('#skF_4'('#skF_7')),k1_tarski('#skF_5'))
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_62,c_2784])).

tff(c_2810,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_2806])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1('#skF_1'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [A_71,B_72] :
      ( r2_hidden(A_71,B_72)
      | v1_xboole_0(B_72)
      | ~ m1_subset_1(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_115,plain,(
    ! [B_73,A_74] :
      ( ~ r1_tarski(B_73,A_74)
      | v1_xboole_0(B_73)
      | ~ m1_subset_1(A_74,B_73) ) ),
    inference(resolution,[status(thm)],[c_105,c_22])).

tff(c_119,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_1,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_115])).

tff(c_130,plain,(
    ! [A_78] : ~ m1_subset_1(A_78,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_135,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_130])).

tff(c_136,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_2859,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2810,c_136])).

tff(c_2867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2023,c_2859])).

tff(c_2869,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2806])).

tff(c_3009,plain,(
    ! [A_358,B_359,C_360] :
      ( k1_mcart_1('#skF_4'(A_358)) = B_359
      | ~ m1_subset_1(A_358,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_359),C_360)))
      | k1_xboole_0 = A_358 ) ),
    inference(resolution,[status(thm)],[c_235,c_36])).

tff(c_3023,plain,
    ( k1_mcart_1('#skF_4'('#skF_7')) = '#skF_5'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_62,c_3009])).

tff(c_3036,plain,(
    k1_mcart_1('#skF_4'('#skF_7')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_2869,c_3023])).

tff(c_2868,plain,(
    r2_hidden(k1_mcart_1('#skF_4'('#skF_7')),k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2806])).

tff(c_2884,plain,(
    ! [D_58,B_56] :
      ( r2_hidden(k1_funct_1(D_58,k1_mcart_1('#skF_4'('#skF_7'))),B_56)
      | k1_xboole_0 = B_56
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'),B_56)))
      | ~ v1_funct_2(D_58,k1_tarski('#skF_5'),B_56)
      | ~ v1_funct_1(D_58) ) ),
    inference(resolution,[status(thm)],[c_2868,c_56])).

tff(c_3460,plain,(
    ! [D_409,B_410] :
      ( r2_hidden(k1_funct_1(D_409,'#skF_5'),B_410)
      | k1_xboole_0 = B_410
      | ~ m1_subset_1(D_409,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'),B_410)))
      | ~ v1_funct_2(D_409,k1_tarski('#skF_5'),B_410)
      | ~ v1_funct_1(D_409) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3036,c_2884])).

tff(c_3475,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6')
    | k1_xboole_0 = '#skF_6'
    | ~ v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_3460])).

tff(c_3490,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3475])).

tff(c_3492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_3490])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:56:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.94/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.94/2.01  
% 4.94/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/2.01  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 5.23/2.01  
% 5.23/2.01  %Foreground sorts:
% 5.23/2.01  
% 5.23/2.01  
% 5.23/2.01  %Background operators:
% 5.23/2.01  
% 5.23/2.01  
% 5.23/2.01  %Foreground operators:
% 5.23/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.23/2.01  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.23/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.23/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.23/2.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.23/2.01  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.23/2.01  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.23/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.23/2.01  tff('#skF_7', type, '#skF_7': $i).
% 5.23/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.23/2.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.23/2.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.23/2.01  tff('#skF_5', type, '#skF_5': $i).
% 5.23/2.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.23/2.01  tff('#skF_6', type, '#skF_6': $i).
% 5.23/2.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.23/2.01  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.23/2.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.23/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.23/2.01  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.23/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.23/2.01  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.23/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.23/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.23/2.01  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.23/2.01  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.23/2.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.23/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.23/2.01  
% 5.23/2.03  tff(f_147, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 5.23/2.03  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.23/2.03  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.23/2.03  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.23/2.03  tff(f_105, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 5.23/2.03  tff(f_83, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 5.23/2.03  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.23/2.03  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 5.23/2.03  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.23/2.03  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.23/2.03  tff(f_36, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 5.23/2.03  tff(f_89, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 5.23/2.03  tff(f_135, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 5.23/2.03  tff(f_39, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 5.23/2.03  tff(c_60, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.23/2.03  tff(c_58, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.23/2.03  tff(c_66, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.23/2.03  tff(c_64, plain, (v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.23/2.03  tff(c_62, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.23/2.03  tff(c_18, plain, (![A_16, B_17]: (r2_hidden(A_16, B_17) | v1_xboole_0(B_17) | ~m1_subset_1(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.23/2.03  tff(c_166, plain, (![C_88, A_89, B_90]: (r2_hidden(C_88, A_89) | ~r2_hidden(C_88, B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.23/2.03  tff(c_940, plain, (![A_195, A_196, B_197]: (r2_hidden(A_195, A_196) | ~m1_subset_1(B_197, k1_zfmisc_1(A_196)) | v1_xboole_0(B_197) | ~m1_subset_1(A_195, B_197))), inference(resolution, [status(thm)], [c_18, c_166])).
% 5.23/2.03  tff(c_952, plain, (![A_195]: (r2_hidden(A_195, k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | v1_xboole_0('#skF_7') | ~m1_subset_1(A_195, '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_940])).
% 5.23/2.03  tff(c_956, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_952])).
% 5.23/2.03  tff(c_628, plain, (![B_140, A_141, C_142]: (k1_xboole_0=B_140 | k1_relset_1(A_141, B_140, C_142)=A_141 | ~v1_funct_2(C_142, A_141, B_140) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.23/2.03  tff(c_641, plain, (k1_xboole_0='#skF_6' | k1_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k1_tarski('#skF_5') | ~v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_62, c_628])).
% 5.23/2.03  tff(c_654, plain, (k1_xboole_0='#skF_6' | k1_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_641])).
% 5.23/2.03  tff(c_655, plain, (k1_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_654])).
% 5.23/2.03  tff(c_38, plain, (![A_42]: (r2_hidden('#skF_4'(A_42), A_42) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.23/2.03  tff(c_235, plain, (![A_111, A_112]: (r2_hidden('#skF_4'(A_111), A_112) | ~m1_subset_1(A_111, k1_zfmisc_1(A_112)) | k1_xboole_0=A_111)), inference(resolution, [status(thm)], [c_38, c_166])).
% 5.23/2.03  tff(c_32, plain, (![A_36, B_37, C_38]: (r2_hidden(k1_mcart_1(A_36), B_37) | ~r2_hidden(A_36, k2_zfmisc_1(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.23/2.03  tff(c_1340, plain, (![A_232, B_233, C_234]: (r2_hidden(k1_mcart_1('#skF_4'(A_232)), B_233) | ~m1_subset_1(A_232, k1_zfmisc_1(k2_zfmisc_1(B_233, C_234))) | k1_xboole_0=A_232)), inference(resolution, [status(thm)], [c_235, c_32])).
% 5.23/2.03  tff(c_1362, plain, (r2_hidden(k1_mcart_1('#skF_4'('#skF_7')), k1_tarski('#skF_5')) | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_62, c_1340])).
% 5.23/2.03  tff(c_1366, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_1362])).
% 5.23/2.03  tff(c_16, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.23/2.03  tff(c_840, plain, (![D_168, A_169, B_170, C_171]: (r2_hidden(k4_tarski(D_168, '#skF_3'(A_169, B_170, C_171, D_168)), C_171) | ~r2_hidden(D_168, B_170) | k1_relset_1(B_170, A_169, C_171)!=B_170 | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(B_170, A_169))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.23/2.03  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.23/2.03  tff(c_157, plain, (![A_85, C_86, B_87]: (r2_hidden(k2_mcart_1(A_85), C_86) | ~r2_hidden(A_85, k2_zfmisc_1(B_87, C_86)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.23/2.03  tff(c_357, plain, (![B_122, C_123]: (r2_hidden(k2_mcart_1('#skF_4'(k2_zfmisc_1(B_122, C_123))), C_123) | k2_zfmisc_1(B_122, C_123)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_157])).
% 5.23/2.03  tff(c_22, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.23/2.03  tff(c_450, plain, (![C_129, B_130]: (~r1_tarski(C_129, k2_mcart_1('#skF_4'(k2_zfmisc_1(B_130, C_129)))) | k2_zfmisc_1(B_130, C_129)=k1_xboole_0)), inference(resolution, [status(thm)], [c_357, c_22])).
% 5.23/2.03  tff(c_473, plain, (![B_134]: (k2_zfmisc_1(B_134, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_450])).
% 5.23/2.03  tff(c_30, plain, (![A_36, C_38, B_37]: (r2_hidden(k2_mcart_1(A_36), C_38) | ~r2_hidden(A_36, k2_zfmisc_1(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.23/2.03  tff(c_534, plain, (![A_137]: (r2_hidden(k2_mcart_1(A_137), k1_xboole_0) | ~r2_hidden(A_137, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_473, c_30])).
% 5.23/2.03  tff(c_547, plain, (![A_137]: (~r1_tarski(k1_xboole_0, k2_mcart_1(A_137)) | ~r2_hidden(A_137, k1_xboole_0))), inference(resolution, [status(thm)], [c_534, c_22])).
% 5.23/2.03  tff(c_559, plain, (![A_137]: (~r2_hidden(A_137, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_547])).
% 5.23/2.03  tff(c_850, plain, (![D_168, B_170, A_169]: (~r2_hidden(D_168, B_170) | k1_relset_1(B_170, A_169, k1_xboole_0)!=B_170 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(B_170, A_169))))), inference(resolution, [status(thm)], [c_840, c_559])).
% 5.23/2.03  tff(c_887, plain, (![D_172, B_173, A_174]: (~r2_hidden(D_172, B_173) | k1_relset_1(B_173, A_174, k1_xboole_0)!=B_173)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_850])).
% 5.23/2.03  tff(c_908, plain, (![A_42, A_174]: (k1_relset_1(A_42, A_174, k1_xboole_0)!=A_42 | k1_xboole_0=A_42)), inference(resolution, [status(thm)], [c_38, c_887])).
% 5.23/2.03  tff(c_1734, plain, (![A_250, A_251]: (k1_relset_1(A_250, A_251, '#skF_7')!=A_250 | A_250='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_1366, c_908])).
% 5.23/2.03  tff(c_1743, plain, (k1_tarski('#skF_5')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_655, c_1734])).
% 5.23/2.03  tff(c_10, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.23/2.03  tff(c_1758, plain, (~v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1743, c_10])).
% 5.23/2.03  tff(c_1765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_956, c_1758])).
% 5.23/2.03  tff(c_1767, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_1362])).
% 5.23/2.03  tff(c_36, plain, (![A_39, B_40, C_41]: (k1_mcart_1(A_39)=B_40 | ~r2_hidden(A_39, k2_zfmisc_1(k1_tarski(B_40), C_41)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.23/2.03  tff(c_1926, plain, (![A_267, B_268, C_269]: (k1_mcart_1('#skF_4'(A_267))=B_268 | ~m1_subset_1(A_267, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_268), C_269))) | k1_xboole_0=A_267)), inference(resolution, [status(thm)], [c_235, c_36])).
% 5.23/2.03  tff(c_1940, plain, (k1_mcart_1('#skF_4'('#skF_7'))='#skF_5' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_62, c_1926])).
% 5.23/2.03  tff(c_1953, plain, (k1_mcart_1('#skF_4'('#skF_7'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1767, c_1940])).
% 5.23/2.03  tff(c_1766, plain, (r2_hidden(k1_mcart_1('#skF_4'('#skF_7')), k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_1362])).
% 5.23/2.03  tff(c_56, plain, (![D_58, C_57, B_56, A_55]: (r2_hidden(k1_funct_1(D_58, C_57), B_56) | k1_xboole_0=B_56 | ~r2_hidden(C_57, A_55) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~v1_funct_2(D_58, A_55, B_56) | ~v1_funct_1(D_58))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.23/2.03  tff(c_1782, plain, (![D_58, B_56]: (r2_hidden(k1_funct_1(D_58, k1_mcart_1('#skF_4'('#skF_7'))), B_56) | k1_xboole_0=B_56 | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'), B_56))) | ~v1_funct_2(D_58, k1_tarski('#skF_5'), B_56) | ~v1_funct_1(D_58))), inference(resolution, [status(thm)], [c_1766, c_56])).
% 5.23/2.03  tff(c_1989, plain, (![D_270, B_271]: (r2_hidden(k1_funct_1(D_270, '#skF_5'), B_271) | k1_xboole_0=B_271 | ~m1_subset_1(D_270, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'), B_271))) | ~v1_funct_2(D_270, k1_tarski('#skF_5'), B_271) | ~v1_funct_1(D_270))), inference(demodulation, [status(thm), theory('equality')], [c_1953, c_1782])).
% 5.23/2.03  tff(c_2004, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6') | k1_xboole_0='#skF_6' | ~v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_62, c_1989])).
% 5.23/2.03  tff(c_2019, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2004])).
% 5.23/2.03  tff(c_2021, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_2019])).
% 5.23/2.03  tff(c_2023, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_952])).
% 5.23/2.03  tff(c_2784, plain, (![A_343, B_344, C_345]: (r2_hidden(k1_mcart_1('#skF_4'(A_343)), B_344) | ~m1_subset_1(A_343, k1_zfmisc_1(k2_zfmisc_1(B_344, C_345))) | k1_xboole_0=A_343)), inference(resolution, [status(thm)], [c_235, c_32])).
% 5.23/2.03  tff(c_2806, plain, (r2_hidden(k1_mcart_1('#skF_4'('#skF_7')), k1_tarski('#skF_5')) | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_62, c_2784])).
% 5.23/2.03  tff(c_2810, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_2806])).
% 5.23/2.03  tff(c_12, plain, (![A_9]: (m1_subset_1('#skF_1'(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.23/2.03  tff(c_105, plain, (![A_71, B_72]: (r2_hidden(A_71, B_72) | v1_xboole_0(B_72) | ~m1_subset_1(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.23/2.03  tff(c_115, plain, (![B_73, A_74]: (~r1_tarski(B_73, A_74) | v1_xboole_0(B_73) | ~m1_subset_1(A_74, B_73))), inference(resolution, [status(thm)], [c_105, c_22])).
% 5.23/2.03  tff(c_119, plain, (![A_1]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_115])).
% 5.23/2.03  tff(c_130, plain, (![A_78]: (~m1_subset_1(A_78, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_119])).
% 5.23/2.03  tff(c_135, plain, $false, inference(resolution, [status(thm)], [c_12, c_130])).
% 5.23/2.03  tff(c_136, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_119])).
% 5.23/2.03  tff(c_2859, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2810, c_136])).
% 5.23/2.03  tff(c_2867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2023, c_2859])).
% 5.23/2.03  tff(c_2869, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_2806])).
% 5.23/2.03  tff(c_3009, plain, (![A_358, B_359, C_360]: (k1_mcart_1('#skF_4'(A_358))=B_359 | ~m1_subset_1(A_358, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_359), C_360))) | k1_xboole_0=A_358)), inference(resolution, [status(thm)], [c_235, c_36])).
% 5.23/2.03  tff(c_3023, plain, (k1_mcart_1('#skF_4'('#skF_7'))='#skF_5' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_62, c_3009])).
% 5.23/2.03  tff(c_3036, plain, (k1_mcart_1('#skF_4'('#skF_7'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_2869, c_3023])).
% 5.23/2.03  tff(c_2868, plain, (r2_hidden(k1_mcart_1('#skF_4'('#skF_7')), k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_2806])).
% 5.23/2.03  tff(c_2884, plain, (![D_58, B_56]: (r2_hidden(k1_funct_1(D_58, k1_mcart_1('#skF_4'('#skF_7'))), B_56) | k1_xboole_0=B_56 | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'), B_56))) | ~v1_funct_2(D_58, k1_tarski('#skF_5'), B_56) | ~v1_funct_1(D_58))), inference(resolution, [status(thm)], [c_2868, c_56])).
% 5.23/2.03  tff(c_3460, plain, (![D_409, B_410]: (r2_hidden(k1_funct_1(D_409, '#skF_5'), B_410) | k1_xboole_0=B_410 | ~m1_subset_1(D_409, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'), B_410))) | ~v1_funct_2(D_409, k1_tarski('#skF_5'), B_410) | ~v1_funct_1(D_409))), inference(demodulation, [status(thm), theory('equality')], [c_3036, c_2884])).
% 5.23/2.03  tff(c_3475, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6') | k1_xboole_0='#skF_6' | ~v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_62, c_3460])).
% 5.23/2.03  tff(c_3490, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3475])).
% 5.23/2.03  tff(c_3492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_3490])).
% 5.23/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/2.03  
% 5.23/2.03  Inference rules
% 5.23/2.03  ----------------------
% 5.23/2.03  #Ref     : 0
% 5.23/2.03  #Sup     : 756
% 5.23/2.03  #Fact    : 0
% 5.23/2.03  #Define  : 0
% 5.23/2.03  #Split   : 24
% 5.23/2.03  #Chain   : 0
% 5.23/2.03  #Close   : 0
% 5.23/2.03  
% 5.23/2.03  Ordering : KBO
% 5.23/2.03  
% 5.23/2.03  Simplification rules
% 5.23/2.03  ----------------------
% 5.23/2.03  #Subsume      : 132
% 5.23/2.03  #Demod        : 584
% 5.23/2.03  #Tautology    : 268
% 5.23/2.03  #SimpNegUnit  : 48
% 5.23/2.03  #BackRed      : 125
% 5.23/2.03  
% 5.23/2.03  #Partial instantiations: 0
% 5.23/2.03  #Strategies tried      : 1
% 5.23/2.03  
% 5.23/2.03  Timing (in seconds)
% 5.23/2.03  ----------------------
% 5.23/2.03  Preprocessing        : 0.35
% 5.23/2.03  Parsing              : 0.20
% 5.23/2.03  CNF conversion       : 0.02
% 5.23/2.03  Main loop            : 0.82
% 5.23/2.03  Inferencing          : 0.26
% 5.23/2.03  Reduction            : 0.28
% 5.23/2.03  Demodulation         : 0.19
% 5.23/2.03  BG Simplification    : 0.04
% 5.23/2.03  Subsumption          : 0.16
% 5.23/2.03  Abstraction          : 0.04
% 5.23/2.03  MUC search           : 0.00
% 5.23/2.03  Cooper               : 0.00
% 5.23/2.03  Total                : 1.22
% 5.23/2.03  Index Insertion      : 0.00
% 5.23/2.03  Index Deletion       : 0.00
% 5.23/2.03  Index Matching       : 0.00
% 5.23/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
