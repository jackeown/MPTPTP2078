%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:11 EST 2020

% Result     : Theorem 4.35s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 238 expanded)
%              Number of leaves         :   45 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  173 ( 586 expanded)
%              Number of equality atoms :   42 ( 122 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_40,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_37,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

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
    ! [A_9] : m1_subset_1('#skF_1'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_2'(A_32),A_32)
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_167,plain,(
    ! [C_86,A_87,B_88] :
      ( r2_hidden(C_86,A_87)
      | ~ r2_hidden(C_86,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_205,plain,(
    ! [A_93,A_94] :
      ( r2_hidden('#skF_2'(A_93),A_94)
      | ~ m1_subset_1(A_93,k1_zfmisc_1(A_94))
      | k1_xboole_0 = A_93 ) ),
    inference(resolution,[status(thm)],[c_48,c_167])).

tff(c_38,plain,(
    ! [A_26,C_28,B_27] :
      ( r2_hidden(k2_mcart_1(A_26),C_28)
      | ~ r2_hidden(A_26,k2_zfmisc_1(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_804,plain,(
    ! [A_155,C_156,B_157] :
      ( r2_hidden(k2_mcart_1('#skF_2'(A_155)),C_156)
      | ~ m1_subset_1(A_155,k1_zfmisc_1(k2_zfmisc_1(B_157,C_156)))
      | k1_xboole_0 = A_155 ) ),
    inference(resolution,[status(thm)],[c_205,c_38])).

tff(c_815,plain,
    ( r2_hidden(k2_mcart_1('#skF_2'('#skF_5')),'#skF_4')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56,c_804])).

tff(c_817,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_815])).

tff(c_845,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_54])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_72,plain,(
    ! [A_61] :
      ( v1_relat_1(A_61)
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_77,plain,(
    ! [A_62] :
      ( v1_funct_1(A_62)
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_81,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_77])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_174,plain,(
    ! [A_89,B_90] :
      ( k1_funct_1(A_89,B_90) = k1_xboole_0
      | r2_hidden(B_90,k1_relat_1(A_89))
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_182,plain,(
    ! [B_90] :
      ( k1_funct_1(k1_xboole_0,B_90) = k1_xboole_0
      | r2_hidden(B_90,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_174])).

tff(c_187,plain,(
    ! [B_91] :
      ( k1_funct_1(k1_xboole_0,B_91) = k1_xboole_0
      | r2_hidden(B_91,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_81,c_182])).

tff(c_36,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_192,plain,(
    ! [B_91] :
      ( ~ r1_tarski(k1_xboole_0,B_91)
      | k1_funct_1(k1_xboole_0,B_91) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_187,c_36])).

tff(c_196,plain,(
    ! [B_91] : k1_funct_1(k1_xboole_0,B_91) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_192])).

tff(c_835,plain,(
    ! [B_91] : k1_funct_1('#skF_5',B_91) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_817,c_196])).

tff(c_920,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_52])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_497,plain,(
    ! [D_121,C_122,B_123,A_124] :
      ( r2_hidden(k1_funct_1(D_121,C_122),B_123)
      | k1_xboole_0 = B_123
      | ~ r2_hidden(C_122,A_124)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123)))
      | ~ v1_funct_2(D_121,A_124,B_123)
      | ~ v1_funct_1(D_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_517,plain,(
    ! [D_121,A_15,B_123,B_16] :
      ( r2_hidden(k1_funct_1(D_121,A_15),B_123)
      | k1_xboole_0 = B_123
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(B_16,B_123)))
      | ~ v1_funct_2(D_121,B_16,B_123)
      | ~ v1_funct_1(D_121)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_18,c_497])).

tff(c_2354,plain,(
    ! [D_285,A_286,B_287,B_288] :
      ( r2_hidden(k1_funct_1(D_285,A_286),B_287)
      | B_287 = '#skF_5'
      | ~ m1_subset_1(D_285,k1_zfmisc_1(k2_zfmisc_1(B_288,B_287)))
      | ~ v1_funct_2(D_285,B_288,B_287)
      | ~ v1_funct_1(D_285)
      | v1_xboole_0(B_288)
      | ~ m1_subset_1(A_286,B_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_517])).

tff(c_2362,plain,(
    ! [A_286] :
      ( r2_hidden(k1_funct_1('#skF_5',A_286),'#skF_4')
      | '#skF_5' = '#skF_4'
      | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(k1_tarski('#skF_3'))
      | ~ m1_subset_1(A_286,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_56,c_2354])).

tff(c_2372,plain,(
    ! [A_286] :
      ( r2_hidden('#skF_5','#skF_4')
      | '#skF_5' = '#skF_4'
      | v1_xboole_0(k1_tarski('#skF_3'))
      | ~ m1_subset_1(A_286,k1_tarski('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_835,c_2362])).

tff(c_2375,plain,(
    ! [A_289] : ~ m1_subset_1(A_289,k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_845,c_920,c_2372])).

tff(c_2380,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_2375])).

tff(c_2382,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_815])).

tff(c_44,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_mcart_1(A_29) = B_30
      | ~ r2_hidden(A_29,k2_zfmisc_1(k1_tarski(B_30),C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2461,plain,(
    ! [A_300,B_301,C_302] :
      ( k1_mcart_1('#skF_2'(A_300)) = B_301
      | ~ m1_subset_1(A_300,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_301),C_302)))
      | k1_xboole_0 = A_300 ) ),
    inference(resolution,[status(thm)],[c_205,c_44])).

tff(c_2467,plain,
    ( k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56,c_2461])).

tff(c_2474,plain,(
    k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2382,c_2467])).

tff(c_40,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_hidden(k1_mcart_1(A_26),B_27)
      | ~ r2_hidden(A_26,k2_zfmisc_1(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2521,plain,(
    ! [A_305,B_306,C_307] :
      ( r2_hidden(k1_mcart_1('#skF_2'(A_305)),B_306)
      | ~ m1_subset_1(A_305,k1_zfmisc_1(k2_zfmisc_1(B_306,C_307)))
      | k1_xboole_0 = A_305 ) ),
    inference(resolution,[status(thm)],[c_205,c_40])).

tff(c_2527,plain,
    ( r2_hidden(k1_mcart_1('#skF_2'('#skF_5')),k1_tarski('#skF_3'))
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56,c_2521])).

tff(c_2533,plain,
    ( r2_hidden('#skF_3',k1_tarski('#skF_3'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2474,c_2527])).

tff(c_2534,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_2382,c_2533])).

tff(c_50,plain,(
    ! [D_57,C_56,B_55,A_54] :
      ( r2_hidden(k1_funct_1(D_57,C_56),B_55)
      | k1_xboole_0 = B_55
      | ~ r2_hidden(C_56,A_54)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(D_57,A_54,B_55)
      | ~ v1_funct_1(D_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2570,plain,(
    ! [D_315,B_316] :
      ( r2_hidden(k1_funct_1(D_315,'#skF_3'),B_316)
      | k1_xboole_0 = B_316
      | ~ m1_subset_1(D_315,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),B_316)))
      | ~ v1_funct_2(D_315,k1_tarski('#skF_3'),B_316)
      | ~ v1_funct_1(D_315) ) ),
    inference(resolution,[status(thm)],[c_2534,c_50])).

tff(c_2577,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2570])).

tff(c_2586,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2577])).

tff(c_2588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_2586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.35/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.81  
% 4.54/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.82  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 4.54/1.82  
% 4.54/1.82  %Foreground sorts:
% 4.54/1.82  
% 4.54/1.82  
% 4.54/1.82  %Background operators:
% 4.54/1.82  
% 4.54/1.82  
% 4.54/1.82  %Foreground operators:
% 4.54/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.54/1.82  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.54/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.54/1.82  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.54/1.82  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.54/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.54/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.54/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.54/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.54/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.54/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.54/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.54/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.54/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.54/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.54/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.54/1.82  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.82  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.54/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.54/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.54/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.82  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.54/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.54/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.54/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.54/1.82  
% 4.54/1.83  tff(f_144, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 4.54/1.83  tff(f_40, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 4.54/1.83  tff(f_37, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 4.54/1.83  tff(f_120, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 4.54/1.83  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.54/1.83  tff(f_93, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.54/1.83  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.54/1.83  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.54/1.83  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 4.54/1.83  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 4.54/1.83  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.54/1.83  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 4.54/1.83  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.54/1.83  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.54/1.83  tff(f_132, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 4.54/1.83  tff(f_99, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 4.54/1.83  tff(c_54, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.54/1.83  tff(c_52, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.54/1.83  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.54/1.83  tff(c_58, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.54/1.83  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.54/1.83  tff(c_14, plain, (![A_9]: (m1_subset_1('#skF_1'(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.54/1.83  tff(c_12, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.54/1.83  tff(c_48, plain, (![A_32]: (r2_hidden('#skF_2'(A_32), A_32) | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.54/1.83  tff(c_167, plain, (![C_86, A_87, B_88]: (r2_hidden(C_86, A_87) | ~r2_hidden(C_86, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.54/1.83  tff(c_205, plain, (![A_93, A_94]: (r2_hidden('#skF_2'(A_93), A_94) | ~m1_subset_1(A_93, k1_zfmisc_1(A_94)) | k1_xboole_0=A_93)), inference(resolution, [status(thm)], [c_48, c_167])).
% 4.54/1.83  tff(c_38, plain, (![A_26, C_28, B_27]: (r2_hidden(k2_mcart_1(A_26), C_28) | ~r2_hidden(A_26, k2_zfmisc_1(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.54/1.83  tff(c_804, plain, (![A_155, C_156, B_157]: (r2_hidden(k2_mcart_1('#skF_2'(A_155)), C_156) | ~m1_subset_1(A_155, k1_zfmisc_1(k2_zfmisc_1(B_157, C_156))) | k1_xboole_0=A_155)), inference(resolution, [status(thm)], [c_205, c_38])).
% 4.54/1.83  tff(c_815, plain, (r2_hidden(k2_mcart_1('#skF_2'('#skF_5')), '#skF_4') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_56, c_804])).
% 4.54/1.83  tff(c_817, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_815])).
% 4.54/1.83  tff(c_845, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_817, c_54])).
% 4.54/1.83  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.54/1.83  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.54/1.83  tff(c_72, plain, (![A_61]: (v1_relat_1(A_61) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.54/1.83  tff(c_76, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_72])).
% 4.54/1.83  tff(c_77, plain, (![A_62]: (v1_funct_1(A_62) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.54/1.83  tff(c_81, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_77])).
% 4.54/1.83  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.54/1.83  tff(c_174, plain, (![A_89, B_90]: (k1_funct_1(A_89, B_90)=k1_xboole_0 | r2_hidden(B_90, k1_relat_1(A_89)) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.54/1.83  tff(c_182, plain, (![B_90]: (k1_funct_1(k1_xboole_0, B_90)=k1_xboole_0 | r2_hidden(B_90, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_174])).
% 4.54/1.83  tff(c_187, plain, (![B_91]: (k1_funct_1(k1_xboole_0, B_91)=k1_xboole_0 | r2_hidden(B_91, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_81, c_182])).
% 4.54/1.83  tff(c_36, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.54/1.83  tff(c_192, plain, (![B_91]: (~r1_tarski(k1_xboole_0, B_91) | k1_funct_1(k1_xboole_0, B_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_187, c_36])).
% 4.54/1.83  tff(c_196, plain, (![B_91]: (k1_funct_1(k1_xboole_0, B_91)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_192])).
% 4.54/1.83  tff(c_835, plain, (![B_91]: (k1_funct_1('#skF_5', B_91)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_817, c_817, c_196])).
% 4.54/1.83  tff(c_920, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_835, c_52])).
% 4.54/1.83  tff(c_18, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.54/1.83  tff(c_497, plain, (![D_121, C_122, B_123, A_124]: (r2_hidden(k1_funct_1(D_121, C_122), B_123) | k1_xboole_0=B_123 | ~r2_hidden(C_122, A_124) | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))) | ~v1_funct_2(D_121, A_124, B_123) | ~v1_funct_1(D_121))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.54/1.83  tff(c_517, plain, (![D_121, A_15, B_123, B_16]: (r2_hidden(k1_funct_1(D_121, A_15), B_123) | k1_xboole_0=B_123 | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(B_16, B_123))) | ~v1_funct_2(D_121, B_16, B_123) | ~v1_funct_1(D_121) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(resolution, [status(thm)], [c_18, c_497])).
% 4.54/1.83  tff(c_2354, plain, (![D_285, A_286, B_287, B_288]: (r2_hidden(k1_funct_1(D_285, A_286), B_287) | B_287='#skF_5' | ~m1_subset_1(D_285, k1_zfmisc_1(k2_zfmisc_1(B_288, B_287))) | ~v1_funct_2(D_285, B_288, B_287) | ~v1_funct_1(D_285) | v1_xboole_0(B_288) | ~m1_subset_1(A_286, B_288))), inference(demodulation, [status(thm), theory('equality')], [c_817, c_517])).
% 4.54/1.83  tff(c_2362, plain, (![A_286]: (r2_hidden(k1_funct_1('#skF_5', A_286), '#skF_4') | '#skF_5'='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0(k1_tarski('#skF_3')) | ~m1_subset_1(A_286, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_56, c_2354])).
% 4.54/1.83  tff(c_2372, plain, (![A_286]: (r2_hidden('#skF_5', '#skF_4') | '#skF_5'='#skF_4' | v1_xboole_0(k1_tarski('#skF_3')) | ~m1_subset_1(A_286, k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_835, c_2362])).
% 4.54/1.83  tff(c_2375, plain, (![A_289]: (~m1_subset_1(A_289, k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_12, c_845, c_920, c_2372])).
% 4.54/1.83  tff(c_2380, plain, $false, inference(resolution, [status(thm)], [c_14, c_2375])).
% 4.54/1.83  tff(c_2382, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_815])).
% 4.54/1.83  tff(c_44, plain, (![A_29, B_30, C_31]: (k1_mcart_1(A_29)=B_30 | ~r2_hidden(A_29, k2_zfmisc_1(k1_tarski(B_30), C_31)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.54/1.83  tff(c_2461, plain, (![A_300, B_301, C_302]: (k1_mcart_1('#skF_2'(A_300))=B_301 | ~m1_subset_1(A_300, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_301), C_302))) | k1_xboole_0=A_300)), inference(resolution, [status(thm)], [c_205, c_44])).
% 4.54/1.83  tff(c_2467, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_56, c_2461])).
% 4.54/1.83  tff(c_2474, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2382, c_2467])).
% 4.54/1.83  tff(c_40, plain, (![A_26, B_27, C_28]: (r2_hidden(k1_mcart_1(A_26), B_27) | ~r2_hidden(A_26, k2_zfmisc_1(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.54/1.83  tff(c_2521, plain, (![A_305, B_306, C_307]: (r2_hidden(k1_mcart_1('#skF_2'(A_305)), B_306) | ~m1_subset_1(A_305, k1_zfmisc_1(k2_zfmisc_1(B_306, C_307))) | k1_xboole_0=A_305)), inference(resolution, [status(thm)], [c_205, c_40])).
% 4.54/1.83  tff(c_2527, plain, (r2_hidden(k1_mcart_1('#skF_2'('#skF_5')), k1_tarski('#skF_3')) | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_56, c_2521])).
% 4.54/1.83  tff(c_2533, plain, (r2_hidden('#skF_3', k1_tarski('#skF_3')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2474, c_2527])).
% 4.54/1.83  tff(c_2534, plain, (r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2382, c_2533])).
% 4.54/1.83  tff(c_50, plain, (![D_57, C_56, B_55, A_54]: (r2_hidden(k1_funct_1(D_57, C_56), B_55) | k1_xboole_0=B_55 | ~r2_hidden(C_56, A_54) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(D_57, A_54, B_55) | ~v1_funct_1(D_57))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.54/1.83  tff(c_2570, plain, (![D_315, B_316]: (r2_hidden(k1_funct_1(D_315, '#skF_3'), B_316) | k1_xboole_0=B_316 | ~m1_subset_1(D_315, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), B_316))) | ~v1_funct_2(D_315, k1_tarski('#skF_3'), B_316) | ~v1_funct_1(D_315))), inference(resolution, [status(thm)], [c_2534, c_50])).
% 4.54/1.83  tff(c_2577, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_2570])).
% 4.54/1.83  tff(c_2586, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2577])).
% 4.54/1.83  tff(c_2588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_2586])).
% 4.54/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.83  
% 4.54/1.83  Inference rules
% 4.54/1.83  ----------------------
% 4.54/1.83  #Ref     : 0
% 4.54/1.83  #Sup     : 552
% 4.54/1.83  #Fact    : 4
% 4.54/1.83  #Define  : 0
% 4.54/1.83  #Split   : 4
% 4.54/1.83  #Chain   : 0
% 4.54/1.83  #Close   : 0
% 4.54/1.83  
% 4.54/1.83  Ordering : KBO
% 4.54/1.83  
% 4.54/1.83  Simplification rules
% 4.54/1.83  ----------------------
% 4.54/1.83  #Subsume      : 85
% 4.54/1.83  #Demod        : 430
% 4.54/1.83  #Tautology    : 198
% 4.54/1.83  #SimpNegUnit  : 44
% 4.54/1.83  #BackRed      : 32
% 4.54/1.83  
% 4.54/1.83  #Partial instantiations: 0
% 4.54/1.83  #Strategies tried      : 1
% 4.54/1.83  
% 4.54/1.83  Timing (in seconds)
% 4.54/1.83  ----------------------
% 4.54/1.84  Preprocessing        : 0.32
% 4.54/1.84  Parsing              : 0.16
% 4.54/1.84  CNF conversion       : 0.02
% 4.54/1.84  Main loop            : 0.70
% 4.54/1.84  Inferencing          : 0.24
% 4.54/1.84  Reduction            : 0.22
% 4.54/1.84  Demodulation         : 0.15
% 4.54/1.84  BG Simplification    : 0.03
% 4.54/1.84  Subsumption          : 0.15
% 4.54/1.84  Abstraction          : 0.03
% 4.54/1.84  MUC search           : 0.00
% 4.54/1.84  Cooper               : 0.00
% 4.54/1.84  Total                : 1.05
% 4.54/1.84  Index Insertion      : 0.00
% 4.54/1.84  Index Deletion       : 0.00
% 4.54/1.84  Index Matching       : 0.00
% 4.54/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
