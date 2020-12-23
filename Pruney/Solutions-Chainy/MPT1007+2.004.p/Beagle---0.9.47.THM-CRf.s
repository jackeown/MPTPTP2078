%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:11 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.49s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 229 expanded)
%              Number of leaves         :   46 (  97 expanded)
%              Depth                    :   11
%              Number of atoms          :  169 ( 553 expanded)
%              Number of equality atoms :   42 ( 145 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_40,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_30,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_120,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_82,axiom,(
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

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_52,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1('#skF_1'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,(
    ! [A_65] : k2_tarski(A_65,A_65) = k1_tarski(A_65) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12,plain,(
    ! [A_8,B_9] : ~ v1_xboole_0(k2_tarski(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_87,plain,(
    ! [A_65] : ~ v1_xboole_0(k1_tarski(A_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_48,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_2'(A_33),A_33)
      | k1_xboole_0 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_170,plain,(
    ! [C_89,A_90,B_91] :
      ( r2_hidden(C_89,A_90)
      | ~ r2_hidden(C_89,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_177,plain,(
    ! [A_92,A_93] :
      ( r2_hidden('#skF_2'(A_92),A_93)
      | ~ m1_subset_1(A_92,k1_zfmisc_1(A_93))
      | k1_xboole_0 = A_92 ) ),
    inference(resolution,[status(thm)],[c_48,c_170])).

tff(c_44,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_mcart_1(A_30) = B_31
      | ~ r2_hidden(A_30,k2_zfmisc_1(k1_tarski(B_31),C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_801,plain,(
    ! [A_158,B_159,C_160] :
      ( k1_mcart_1('#skF_2'(A_158)) = B_159
      | ~ m1_subset_1(A_158,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_159),C_160)))
      | k1_xboole_0 = A_158 ) ),
    inference(resolution,[status(thm)],[c_177,c_44])).

tff(c_812,plain,
    ( k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56,c_801])).

tff(c_814,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_812])).

tff(c_842,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_54])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_72,plain,(
    ! [A_63] :
      ( v1_relat_1(A_63)
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_77,plain,(
    ! [A_64] :
      ( v1_funct_1(A_64)
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_81,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_77])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_222,plain,(
    ! [A_97,B_98] :
      ( k1_funct_1(A_97,B_98) = k1_xboole_0
      | r2_hidden(B_98,k1_relat_1(A_97))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_230,plain,(
    ! [B_98] :
      ( k1_funct_1(k1_xboole_0,B_98) = k1_xboole_0
      | r2_hidden(B_98,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_222])).

tff(c_235,plain,(
    ! [B_99] :
      ( k1_funct_1(k1_xboole_0,B_99) = k1_xboole_0
      | r2_hidden(B_99,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_81,c_230])).

tff(c_36,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_240,plain,(
    ! [B_99] :
      ( ~ r1_tarski(k1_xboole_0,B_99)
      | k1_funct_1(k1_xboole_0,B_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_235,c_36])).

tff(c_244,plain,(
    ! [B_99] : k1_funct_1(k1_xboole_0,B_99) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_240])).

tff(c_827,plain,(
    ! [B_99] : k1_funct_1('#skF_5',B_99) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_814,c_244])).

tff(c_944,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_52])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_523,plain,(
    ! [D_129,C_130,B_131,A_132] :
      ( r2_hidden(k1_funct_1(D_129,C_130),B_131)
      | k1_xboole_0 = B_131
      | ~ r2_hidden(C_130,A_132)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131)))
      | ~ v1_funct_2(D_129,A_132,B_131)
      | ~ v1_funct_1(D_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_543,plain,(
    ! [D_129,A_16,B_131,B_17] :
      ( r2_hidden(k1_funct_1(D_129,A_16),B_131)
      | k1_xboole_0 = B_131
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(B_17,B_131)))
      | ~ v1_funct_2(D_129,B_17,B_131)
      | ~ v1_funct_1(D_129)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_523])).

tff(c_2140,plain,(
    ! [D_274,A_275,B_276,B_277] :
      ( r2_hidden(k1_funct_1(D_274,A_275),B_276)
      | B_276 = '#skF_5'
      | ~ m1_subset_1(D_274,k1_zfmisc_1(k2_zfmisc_1(B_277,B_276)))
      | ~ v1_funct_2(D_274,B_277,B_276)
      | ~ v1_funct_1(D_274)
      | v1_xboole_0(B_277)
      | ~ m1_subset_1(A_275,B_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_543])).

tff(c_2148,plain,(
    ! [A_275] :
      ( r2_hidden(k1_funct_1('#skF_5',A_275),'#skF_4')
      | '#skF_5' = '#skF_4'
      | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(k1_tarski('#skF_3'))
      | ~ m1_subset_1(A_275,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_56,c_2140])).

tff(c_2158,plain,(
    ! [A_275] :
      ( r2_hidden('#skF_5','#skF_4')
      | '#skF_5' = '#skF_4'
      | v1_xboole_0(k1_tarski('#skF_3'))
      | ~ m1_subset_1(A_275,k1_tarski('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_827,c_2148])).

tff(c_2161,plain,(
    ! [A_278] : ~ m1_subset_1(A_278,k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_842,c_944,c_2158])).

tff(c_2166,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_2161])).

tff(c_2168,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_812])).

tff(c_2167,plain,(
    k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_812])).

tff(c_40,plain,(
    ! [A_27,B_28,C_29] :
      ( r2_hidden(k1_mcart_1(A_27),B_28)
      | ~ r2_hidden(A_27,k2_zfmisc_1(B_28,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2307,plain,(
    ! [A_294,B_295,C_296] :
      ( r2_hidden(k1_mcart_1('#skF_2'(A_294)),B_295)
      | ~ m1_subset_1(A_294,k1_zfmisc_1(k2_zfmisc_1(B_295,C_296)))
      | k1_xboole_0 = A_294 ) ),
    inference(resolution,[status(thm)],[c_177,c_40])).

tff(c_2313,plain,
    ( r2_hidden(k1_mcart_1('#skF_2'('#skF_5')),k1_tarski('#skF_3'))
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56,c_2307])).

tff(c_2319,plain,
    ( r2_hidden('#skF_3',k1_tarski('#skF_3'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2167,c_2313])).

tff(c_2320,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_2168,c_2319])).

tff(c_50,plain,(
    ! [D_58,C_57,B_56,A_55] :
      ( r2_hidden(k1_funct_1(D_58,C_57),B_56)
      | k1_xboole_0 = B_56
      | ~ r2_hidden(C_57,A_55)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ v1_funct_2(D_58,A_55,B_56)
      | ~ v1_funct_1(D_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2356,plain,(
    ! [D_304,B_305] :
      ( r2_hidden(k1_funct_1(D_304,'#skF_3'),B_305)
      | k1_xboole_0 = B_305
      | ~ m1_subset_1(D_304,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),B_305)))
      | ~ v1_funct_2(D_304,k1_tarski('#skF_3'),B_305)
      | ~ v1_funct_1(D_304) ) ),
    inference(resolution,[status(thm)],[c_2320,c_50])).

tff(c_2363,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2356])).

tff(c_2372,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2363])).

tff(c_2374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_2372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.76  
% 4.10/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.76  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 4.10/1.76  
% 4.10/1.76  %Foreground sorts:
% 4.10/1.76  
% 4.10/1.76  
% 4.10/1.76  %Background operators:
% 4.10/1.76  
% 4.10/1.76  
% 4.10/1.76  %Foreground operators:
% 4.10/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.10/1.76  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.10/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.10/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.10/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.10/1.76  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.10/1.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.10/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.10/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.10/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.10/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.10/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.10/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.10/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.10/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.10/1.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.10/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.10/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.10/1.76  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.10/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.76  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.10/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.10/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.10/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.10/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.76  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.10/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.10/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.10/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.10/1.76  
% 4.49/1.78  tff(f_144, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 4.49/1.78  tff(f_40, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 4.49/1.78  tff(f_30, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.49/1.78  tff(f_37, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 4.49/1.78  tff(f_120, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 4.49/1.78  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.49/1.78  tff(f_99, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 4.49/1.78  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.49/1.78  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.49/1.78  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 4.49/1.78  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 4.49/1.78  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.49/1.78  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 4.49/1.78  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.49/1.78  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.49/1.78  tff(f_132, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 4.49/1.78  tff(f_93, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.49/1.78  tff(c_54, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.49/1.78  tff(c_52, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.49/1.78  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.49/1.78  tff(c_58, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.49/1.78  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.49/1.78  tff(c_14, plain, (![A_10]: (m1_subset_1('#skF_1'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.49/1.78  tff(c_82, plain, (![A_65]: (k2_tarski(A_65, A_65)=k1_tarski(A_65))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.49/1.78  tff(c_12, plain, (![A_8, B_9]: (~v1_xboole_0(k2_tarski(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.49/1.78  tff(c_87, plain, (![A_65]: (~v1_xboole_0(k1_tarski(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_12])).
% 4.49/1.78  tff(c_48, plain, (![A_33]: (r2_hidden('#skF_2'(A_33), A_33) | k1_xboole_0=A_33)), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.49/1.78  tff(c_170, plain, (![C_89, A_90, B_91]: (r2_hidden(C_89, A_90) | ~r2_hidden(C_89, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.49/1.78  tff(c_177, plain, (![A_92, A_93]: (r2_hidden('#skF_2'(A_92), A_93) | ~m1_subset_1(A_92, k1_zfmisc_1(A_93)) | k1_xboole_0=A_92)), inference(resolution, [status(thm)], [c_48, c_170])).
% 4.49/1.78  tff(c_44, plain, (![A_30, B_31, C_32]: (k1_mcart_1(A_30)=B_31 | ~r2_hidden(A_30, k2_zfmisc_1(k1_tarski(B_31), C_32)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.49/1.78  tff(c_801, plain, (![A_158, B_159, C_160]: (k1_mcart_1('#skF_2'(A_158))=B_159 | ~m1_subset_1(A_158, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_159), C_160))) | k1_xboole_0=A_158)), inference(resolution, [status(thm)], [c_177, c_44])).
% 4.49/1.78  tff(c_812, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_56, c_801])).
% 4.49/1.78  tff(c_814, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_812])).
% 4.49/1.78  tff(c_842, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_814, c_54])).
% 4.49/1.78  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.49/1.78  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.49/1.78  tff(c_72, plain, (![A_63]: (v1_relat_1(A_63) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.49/1.78  tff(c_76, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_72])).
% 4.49/1.78  tff(c_77, plain, (![A_64]: (v1_funct_1(A_64) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.49/1.78  tff(c_81, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_77])).
% 4.49/1.78  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.49/1.78  tff(c_222, plain, (![A_97, B_98]: (k1_funct_1(A_97, B_98)=k1_xboole_0 | r2_hidden(B_98, k1_relat_1(A_97)) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.49/1.78  tff(c_230, plain, (![B_98]: (k1_funct_1(k1_xboole_0, B_98)=k1_xboole_0 | r2_hidden(B_98, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_222])).
% 4.49/1.78  tff(c_235, plain, (![B_99]: (k1_funct_1(k1_xboole_0, B_99)=k1_xboole_0 | r2_hidden(B_99, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_81, c_230])).
% 4.49/1.78  tff(c_36, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.49/1.78  tff(c_240, plain, (![B_99]: (~r1_tarski(k1_xboole_0, B_99) | k1_funct_1(k1_xboole_0, B_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_235, c_36])).
% 4.49/1.78  tff(c_244, plain, (![B_99]: (k1_funct_1(k1_xboole_0, B_99)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_240])).
% 4.49/1.78  tff(c_827, plain, (![B_99]: (k1_funct_1('#skF_5', B_99)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_814, c_814, c_244])).
% 4.49/1.78  tff(c_944, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_827, c_52])).
% 4.49/1.78  tff(c_18, plain, (![A_16, B_17]: (r2_hidden(A_16, B_17) | v1_xboole_0(B_17) | ~m1_subset_1(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.49/1.78  tff(c_523, plain, (![D_129, C_130, B_131, A_132]: (r2_hidden(k1_funct_1(D_129, C_130), B_131) | k1_xboole_0=B_131 | ~r2_hidden(C_130, A_132) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))) | ~v1_funct_2(D_129, A_132, B_131) | ~v1_funct_1(D_129))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.49/1.78  tff(c_543, plain, (![D_129, A_16, B_131, B_17]: (r2_hidden(k1_funct_1(D_129, A_16), B_131) | k1_xboole_0=B_131 | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(B_17, B_131))) | ~v1_funct_2(D_129, B_17, B_131) | ~v1_funct_1(D_129) | v1_xboole_0(B_17) | ~m1_subset_1(A_16, B_17))), inference(resolution, [status(thm)], [c_18, c_523])).
% 4.49/1.78  tff(c_2140, plain, (![D_274, A_275, B_276, B_277]: (r2_hidden(k1_funct_1(D_274, A_275), B_276) | B_276='#skF_5' | ~m1_subset_1(D_274, k1_zfmisc_1(k2_zfmisc_1(B_277, B_276))) | ~v1_funct_2(D_274, B_277, B_276) | ~v1_funct_1(D_274) | v1_xboole_0(B_277) | ~m1_subset_1(A_275, B_277))), inference(demodulation, [status(thm), theory('equality')], [c_814, c_543])).
% 4.49/1.78  tff(c_2148, plain, (![A_275]: (r2_hidden(k1_funct_1('#skF_5', A_275), '#skF_4') | '#skF_5'='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0(k1_tarski('#skF_3')) | ~m1_subset_1(A_275, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_56, c_2140])).
% 4.49/1.78  tff(c_2158, plain, (![A_275]: (r2_hidden('#skF_5', '#skF_4') | '#skF_5'='#skF_4' | v1_xboole_0(k1_tarski('#skF_3')) | ~m1_subset_1(A_275, k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_827, c_2148])).
% 4.49/1.78  tff(c_2161, plain, (![A_278]: (~m1_subset_1(A_278, k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_87, c_842, c_944, c_2158])).
% 4.49/1.78  tff(c_2166, plain, $false, inference(resolution, [status(thm)], [c_14, c_2161])).
% 4.49/1.78  tff(c_2168, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_812])).
% 4.49/1.78  tff(c_2167, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3'), inference(splitRight, [status(thm)], [c_812])).
% 4.49/1.78  tff(c_40, plain, (![A_27, B_28, C_29]: (r2_hidden(k1_mcart_1(A_27), B_28) | ~r2_hidden(A_27, k2_zfmisc_1(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.49/1.78  tff(c_2307, plain, (![A_294, B_295, C_296]: (r2_hidden(k1_mcart_1('#skF_2'(A_294)), B_295) | ~m1_subset_1(A_294, k1_zfmisc_1(k2_zfmisc_1(B_295, C_296))) | k1_xboole_0=A_294)), inference(resolution, [status(thm)], [c_177, c_40])).
% 4.49/1.78  tff(c_2313, plain, (r2_hidden(k1_mcart_1('#skF_2'('#skF_5')), k1_tarski('#skF_3')) | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_56, c_2307])).
% 4.49/1.78  tff(c_2319, plain, (r2_hidden('#skF_3', k1_tarski('#skF_3')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2167, c_2313])).
% 4.49/1.78  tff(c_2320, plain, (r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2168, c_2319])).
% 4.49/1.78  tff(c_50, plain, (![D_58, C_57, B_56, A_55]: (r2_hidden(k1_funct_1(D_58, C_57), B_56) | k1_xboole_0=B_56 | ~r2_hidden(C_57, A_55) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~v1_funct_2(D_58, A_55, B_56) | ~v1_funct_1(D_58))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.49/1.78  tff(c_2356, plain, (![D_304, B_305]: (r2_hidden(k1_funct_1(D_304, '#skF_3'), B_305) | k1_xboole_0=B_305 | ~m1_subset_1(D_304, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), B_305))) | ~v1_funct_2(D_304, k1_tarski('#skF_3'), B_305) | ~v1_funct_1(D_304))), inference(resolution, [status(thm)], [c_2320, c_50])).
% 4.49/1.78  tff(c_2363, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_2356])).
% 4.49/1.78  tff(c_2372, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2363])).
% 4.49/1.78  tff(c_2374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_2372])).
% 4.49/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.78  
% 4.49/1.78  Inference rules
% 4.49/1.78  ----------------------
% 4.49/1.78  #Ref     : 0
% 4.49/1.78  #Sup     : 507
% 4.49/1.78  #Fact    : 2
% 4.49/1.78  #Define  : 0
% 4.49/1.78  #Split   : 4
% 4.49/1.78  #Chain   : 0
% 4.49/1.78  #Close   : 0
% 4.49/1.78  
% 4.49/1.78  Ordering : KBO
% 4.49/1.78  
% 4.49/1.78  Simplification rules
% 4.49/1.78  ----------------------
% 4.49/1.78  #Subsume      : 80
% 4.49/1.78  #Demod        : 388
% 4.49/1.78  #Tautology    : 187
% 4.49/1.78  #SimpNegUnit  : 43
% 4.49/1.78  #BackRed      : 34
% 4.49/1.78  
% 4.49/1.78  #Partial instantiations: 0
% 4.49/1.78  #Strategies tried      : 1
% 4.49/1.78  
% 4.49/1.78  Timing (in seconds)
% 4.49/1.78  ----------------------
% 4.49/1.78  Preprocessing        : 0.33
% 4.49/1.78  Parsing              : 0.18
% 4.49/1.78  CNF conversion       : 0.02
% 4.49/1.78  Main loop            : 0.67
% 4.49/1.78  Inferencing          : 0.23
% 4.49/1.78  Reduction            : 0.21
% 4.49/1.78  Demodulation         : 0.14
% 4.49/1.78  BG Simplification    : 0.03
% 4.49/1.78  Subsumption          : 0.14
% 4.49/1.78  Abstraction          : 0.03
% 4.49/1.78  MUC search           : 0.00
% 4.49/1.78  Cooper               : 0.00
% 4.49/1.78  Total                : 1.04
% 4.49/1.78  Index Insertion      : 0.00
% 4.49/1.78  Index Deletion       : 0.00
% 4.49/1.78  Index Matching       : 0.00
% 4.49/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
