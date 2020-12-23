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
% DateTime   : Thu Dec  3 10:16:41 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 338 expanded)
%              Number of leaves         :   33 ( 133 expanded)
%              Depth                    :   12
%              Number of atoms          :  179 ( 920 expanded)
%              Number of equality atoms :   18 ( 212 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_9 > #skF_3 > #skF_13 > #skF_5 > #skF_7 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_63,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_47,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_76,plain,(
    r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_159,plain,(
    ! [A_98,B_99,D_100] :
      ( '#skF_9'(A_98,B_99,k1_funct_2(A_98,B_99),D_100) = D_100
      | ~ r2_hidden(D_100,k1_funct_2(A_98,B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_170,plain,(
    '#skF_9'('#skF_11','#skF_12',k1_funct_2('#skF_11','#skF_12'),'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_76,c_159])).

tff(c_36,plain,(
    ! [A_46,B_47,D_62] :
      ( v1_relat_1('#skF_9'(A_46,B_47,k1_funct_2(A_46,B_47),D_62))
      | ~ r2_hidden(D_62,k1_funct_2(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_174,plain,
    ( v1_relat_1('#skF_13')
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_36])).

tff(c_178,plain,(
    v1_relat_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_174])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12')))
    | ~ v1_funct_2('#skF_13','#skF_11','#skF_12')
    | ~ v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_92,plain,(
    ~ v1_funct_1('#skF_13') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_109,plain,(
    ! [A_82,B_83,D_84] :
      ( '#skF_9'(A_82,B_83,k1_funct_2(A_82,B_83),D_84) = D_84
      | ~ r2_hidden(D_84,k1_funct_2(A_82,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_120,plain,(
    '#skF_9'('#skF_11','#skF_12',k1_funct_2('#skF_11','#skF_12'),'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_76,c_109])).

tff(c_131,plain,(
    ! [A_88,B_89,D_90] :
      ( v1_funct_1('#skF_9'(A_88,B_89,k1_funct_2(A_88,B_89),D_90))
      | ~ r2_hidden(D_90,k1_funct_2(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_134,plain,
    ( v1_funct_1('#skF_13')
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_131])).

tff(c_136,plain,(
    v1_funct_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_134])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_136])).

tff(c_140,plain,(
    v1_funct_1('#skF_13') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_197,plain,(
    ! [A_108,B_109,D_110] :
      ( k1_relat_1('#skF_9'(A_108,B_109,k1_funct_2(A_108,B_109),D_110)) = A_108
      | ~ r2_hidden(D_110,k1_funct_2(A_108,B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_209,plain,
    ( k1_relat_1('#skF_13') = '#skF_11'
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_197])).

tff(c_213,plain,(
    k1_relat_1('#skF_13') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_209])).

tff(c_628,plain,(
    ! [C_190,B_191] :
      ( r2_hidden('#skF_10'(k1_relat_1(C_190),B_191,C_190),k1_relat_1(C_190))
      | m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_190),B_191)))
      | ~ v1_funct_1(C_190)
      | ~ v1_relat_1(C_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_633,plain,(
    ! [B_191] :
      ( r2_hidden('#skF_10'('#skF_11',B_191,'#skF_13'),k1_relat_1('#skF_13'))
      | m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_13'),B_191)))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_628])).

tff(c_648,plain,(
    ! [B_192] :
      ( r2_hidden('#skF_10'('#skF_11',B_192,'#skF_13'),'#skF_11')
      | m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11',B_192))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_140,c_213,c_213,c_633])).

tff(c_139,plain,
    ( ~ v1_funct_2('#skF_13','#skF_11','#skF_12')
    | ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_141,plain,(
    ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12'))) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_652,plain,(
    r2_hidden('#skF_10'('#skF_11','#skF_12','#skF_13'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_648,c_141])).

tff(c_277,plain,(
    ! [A_125,B_126,D_127] :
      ( r1_tarski(k2_relat_1('#skF_9'(A_125,B_126,k1_funct_2(A_125,B_126),D_127)),B_126)
      | ~ r2_hidden(D_127,k1_funct_2(A_125,B_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_285,plain,
    ( r1_tarski(k2_relat_1('#skF_13'),'#skF_12')
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_277])).

tff(c_289,plain,(
    r1_tarski(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_285])).

tff(c_186,plain,(
    ! [A_104,D_105] :
      ( r2_hidden(k1_funct_1(A_104,D_105),k2_relat_1(A_104))
      | ~ r2_hidden(D_105,k1_relat_1(A_104))
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_189,plain,(
    ! [A_104,D_105,B_2] :
      ( r2_hidden(k1_funct_1(A_104,D_105),B_2)
      | ~ r1_tarski(k2_relat_1(A_104),B_2)
      | ~ r2_hidden(D_105,k1_relat_1(A_104))
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_186,c_2])).

tff(c_873,plain,(
    ! [C_221,B_222] :
      ( ~ r2_hidden(k1_funct_1(C_221,'#skF_10'(k1_relat_1(C_221),B_222,C_221)),B_222)
      | m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_221),B_222)))
      | ~ v1_funct_1(C_221)
      | ~ v1_relat_1(C_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_880,plain,(
    ! [B_222] :
      ( ~ r2_hidden(k1_funct_1('#skF_13','#skF_10'('#skF_11',B_222,'#skF_13')),B_222)
      | m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_13'),B_222)))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_873])).

tff(c_892,plain,(
    ! [B_223] :
      ( ~ r2_hidden(k1_funct_1('#skF_13','#skF_10'('#skF_11',B_223,'#skF_13')),B_223)
      | m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11',B_223))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_140,c_213,c_880])).

tff(c_896,plain,(
    ! [B_2] :
      ( m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11',B_2)))
      | ~ r1_tarski(k2_relat_1('#skF_13'),B_2)
      | ~ r2_hidden('#skF_10'('#skF_11',B_2,'#skF_13'),k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_189,c_892])).

tff(c_907,plain,(
    ! [B_224] :
      ( m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11',B_224)))
      | ~ r1_tarski(k2_relat_1('#skF_13'),B_224)
      | ~ r2_hidden('#skF_10'('#skF_11',B_224,'#skF_13'),'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_140,c_213,c_896])).

tff(c_910,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_13'),'#skF_12')
    | ~ r2_hidden('#skF_10'('#skF_11','#skF_12','#skF_13'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_907,c_141])).

tff(c_914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_289,c_910])).

tff(c_915,plain,(
    ~ v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_933,plain,(
    ! [A_229,B_230,D_231] :
      ( '#skF_9'(A_229,B_230,k1_funct_2(A_229,B_230),D_231) = D_231
      | ~ r2_hidden(D_231,k1_funct_2(A_229,B_230)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_944,plain,(
    '#skF_9'('#skF_11','#skF_12',k1_funct_2('#skF_11','#skF_12'),'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_76,c_933])).

tff(c_1044,plain,(
    ! [A_256,B_257,D_258] :
      ( r1_tarski(k2_relat_1('#skF_9'(A_256,B_257,k1_funct_2(A_256,B_257),D_258)),B_257)
      | ~ r2_hidden(D_258,k1_funct_2(A_256,B_257)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1052,plain,
    ( r1_tarski(k2_relat_1('#skF_13'),'#skF_12')
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_944,c_1044])).

tff(c_1056,plain,(
    r1_tarski(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1052])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [A_72,B_73] :
      ( ~ r2_hidden('#skF_1'(A_72,B_73),B_73)
      | r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_955,plain,(
    ! [A_235,B_236,D_237] :
      ( v1_relat_1('#skF_9'(A_235,B_236,k1_funct_2(A_235,B_236),D_237))
      | ~ r2_hidden(D_237,k1_funct_2(A_235,B_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_958,plain,
    ( v1_relat_1('#skF_13')
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_944,c_955])).

tff(c_960,plain,(
    v1_relat_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_958])).

tff(c_961,plain,(
    ! [A_238,B_239,D_240] :
      ( k1_relat_1('#skF_9'(A_238,B_239,k1_funct_2(A_238,B_239),D_240)) = A_238
      | ~ r2_hidden(D_240,k1_funct_2(A_238,B_239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_970,plain,
    ( k1_relat_1('#skF_13') = '#skF_11'
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_944,c_961])).

tff(c_974,plain,(
    k1_relat_1('#skF_13') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_970])).

tff(c_1165,plain,(
    ! [C_287,B_288] :
      ( r2_hidden('#skF_10'(k1_relat_1(C_287),B_288,C_287),k1_relat_1(C_287))
      | v1_funct_2(C_287,k1_relat_1(C_287),B_288)
      | ~ v1_funct_1(C_287)
      | ~ v1_relat_1(C_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1170,plain,(
    ! [B_288] :
      ( r2_hidden('#skF_10'('#skF_11',B_288,'#skF_13'),k1_relat_1('#skF_13'))
      | v1_funct_2('#skF_13',k1_relat_1('#skF_13'),B_288)
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_1165])).

tff(c_1185,plain,(
    ! [B_289] :
      ( r2_hidden('#skF_10'('#skF_11',B_289,'#skF_13'),'#skF_11')
      | v1_funct_2('#skF_13','#skF_11',B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_960,c_140,c_974,c_974,c_1170])).

tff(c_1188,plain,(
    ! [B_289,B_2] :
      ( r2_hidden('#skF_10'('#skF_11',B_289,'#skF_13'),B_2)
      | ~ r1_tarski('#skF_11',B_2)
      | v1_funct_2('#skF_13','#skF_11',B_289) ) ),
    inference(resolution,[status(thm)],[c_1185,c_2])).

tff(c_1028,plain,(
    ! [A_247,D_248] :
      ( r2_hidden(k1_funct_1(A_247,D_248),k2_relat_1(A_247))
      | ~ r2_hidden(D_248,k1_relat_1(A_247))
      | ~ v1_funct_1(A_247)
      | ~ v1_relat_1(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1031,plain,(
    ! [A_247,D_248,B_2] :
      ( r2_hidden(k1_funct_1(A_247,D_248),B_2)
      | ~ r1_tarski(k2_relat_1(A_247),B_2)
      | ~ r2_hidden(D_248,k1_relat_1(A_247))
      | ~ v1_funct_1(A_247)
      | ~ v1_relat_1(A_247) ) ),
    inference(resolution,[status(thm)],[c_1028,c_2])).

tff(c_1301,plain,(
    ! [C_310,B_311] :
      ( ~ r2_hidden(k1_funct_1(C_310,'#skF_10'(k1_relat_1(C_310),B_311,C_310)),B_311)
      | v1_funct_2(C_310,k1_relat_1(C_310),B_311)
      | ~ v1_funct_1(C_310)
      | ~ v1_relat_1(C_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1312,plain,(
    ! [B_311] :
      ( ~ r2_hidden(k1_funct_1('#skF_13','#skF_10'('#skF_11',B_311,'#skF_13')),B_311)
      | v1_funct_2('#skF_13',k1_relat_1('#skF_13'),B_311)
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_1301])).

tff(c_1320,plain,(
    ! [B_312] :
      ( ~ r2_hidden(k1_funct_1('#skF_13','#skF_10'('#skF_11',B_312,'#skF_13')),B_312)
      | v1_funct_2('#skF_13','#skF_11',B_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_960,c_140,c_974,c_1312])).

tff(c_1324,plain,(
    ! [B_2] :
      ( v1_funct_2('#skF_13','#skF_11',B_2)
      | ~ r1_tarski(k2_relat_1('#skF_13'),B_2)
      | ~ r2_hidden('#skF_10'('#skF_11',B_2,'#skF_13'),k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_1031,c_1320])).

tff(c_1347,plain,(
    ! [B_313] :
      ( v1_funct_2('#skF_13','#skF_11',B_313)
      | ~ r1_tarski(k2_relat_1('#skF_13'),B_313)
      | ~ r2_hidden('#skF_10'('#skF_11',B_313,'#skF_13'),'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_960,c_140,c_974,c_1324])).

tff(c_1351,plain,(
    ! [B_289] :
      ( ~ r1_tarski(k2_relat_1('#skF_13'),B_289)
      | ~ r1_tarski('#skF_11','#skF_11')
      | v1_funct_2('#skF_13','#skF_11',B_289) ) ),
    inference(resolution,[status(thm)],[c_1188,c_1347])).

tff(c_1359,plain,(
    ! [B_314] :
      ( ~ r1_tarski(k2_relat_1('#skF_13'),B_314)
      | v1_funct_2('#skF_13','#skF_11',B_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1351])).

tff(c_1362,plain,(
    v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_1056,c_1359])).

tff(c_1370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_915,c_1362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n021.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 13:12:04 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.56  
% 3.72/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.57  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_9 > #skF_3 > #skF_13 > #skF_5 > #skF_7 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4 > #skF_10
% 3.72/1.57  
% 3.72/1.57  %Foreground sorts:
% 3.72/1.57  
% 3.72/1.57  
% 3.72/1.57  %Background operators:
% 3.72/1.57  
% 3.72/1.57  
% 3.72/1.57  %Foreground operators:
% 3.72/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.72/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.72/1.57  tff('#skF_11', type, '#skF_11': $i).
% 3.72/1.57  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.72/1.57  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 3.72/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.72/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.72/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.72/1.57  tff('#skF_13', type, '#skF_13': $i).
% 3.72/1.57  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.72/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.72/1.57  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.72/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.72/1.57  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 3.72/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.72/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.72/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.72/1.57  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.72/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.72/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.72/1.57  tff('#skF_12', type, '#skF_12': $i).
% 3.72/1.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.72/1.57  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 3.72/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.72/1.57  
% 3.89/1.58  tff(f_89, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 3.89/1.58  tff(f_63, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 3.89/1.58  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 3.89/1.58  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.89/1.58  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.89/1.58  tff(c_76, plain, (r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.89/1.58  tff(c_159, plain, (![A_98, B_99, D_100]: ('#skF_9'(A_98, B_99, k1_funct_2(A_98, B_99), D_100)=D_100 | ~r2_hidden(D_100, k1_funct_2(A_98, B_99)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.58  tff(c_170, plain, ('#skF_9'('#skF_11', '#skF_12', k1_funct_2('#skF_11', '#skF_12'), '#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_76, c_159])).
% 3.89/1.58  tff(c_36, plain, (![A_46, B_47, D_62]: (v1_relat_1('#skF_9'(A_46, B_47, k1_funct_2(A_46, B_47), D_62)) | ~r2_hidden(D_62, k1_funct_2(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.58  tff(c_174, plain, (v1_relat_1('#skF_13') | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_36])).
% 3.89/1.58  tff(c_178, plain, (v1_relat_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_174])).
% 3.89/1.58  tff(c_74, plain, (~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12'))) | ~v1_funct_2('#skF_13', '#skF_11', '#skF_12') | ~v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.89/1.58  tff(c_92, plain, (~v1_funct_1('#skF_13')), inference(splitLeft, [status(thm)], [c_74])).
% 3.89/1.58  tff(c_109, plain, (![A_82, B_83, D_84]: ('#skF_9'(A_82, B_83, k1_funct_2(A_82, B_83), D_84)=D_84 | ~r2_hidden(D_84, k1_funct_2(A_82, B_83)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.58  tff(c_120, plain, ('#skF_9'('#skF_11', '#skF_12', k1_funct_2('#skF_11', '#skF_12'), '#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_76, c_109])).
% 3.89/1.58  tff(c_131, plain, (![A_88, B_89, D_90]: (v1_funct_1('#skF_9'(A_88, B_89, k1_funct_2(A_88, B_89), D_90)) | ~r2_hidden(D_90, k1_funct_2(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.58  tff(c_134, plain, (v1_funct_1('#skF_13') | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_131])).
% 3.89/1.58  tff(c_136, plain, (v1_funct_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_134])).
% 3.89/1.58  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_136])).
% 3.89/1.58  tff(c_140, plain, (v1_funct_1('#skF_13')), inference(splitRight, [status(thm)], [c_74])).
% 3.89/1.58  tff(c_197, plain, (![A_108, B_109, D_110]: (k1_relat_1('#skF_9'(A_108, B_109, k1_funct_2(A_108, B_109), D_110))=A_108 | ~r2_hidden(D_110, k1_funct_2(A_108, B_109)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.58  tff(c_209, plain, (k1_relat_1('#skF_13')='#skF_11' | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_197])).
% 3.89/1.58  tff(c_213, plain, (k1_relat_1('#skF_13')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_209])).
% 3.89/1.58  tff(c_628, plain, (![C_190, B_191]: (r2_hidden('#skF_10'(k1_relat_1(C_190), B_191, C_190), k1_relat_1(C_190)) | m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_190), B_191))) | ~v1_funct_1(C_190) | ~v1_relat_1(C_190))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.89/1.58  tff(c_633, plain, (![B_191]: (r2_hidden('#skF_10'('#skF_11', B_191, '#skF_13'), k1_relat_1('#skF_13')) | m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_13'), B_191))) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_628])).
% 3.89/1.58  tff(c_648, plain, (![B_192]: (r2_hidden('#skF_10'('#skF_11', B_192, '#skF_13'), '#skF_11') | m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', B_192))))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_140, c_213, c_213, c_633])).
% 3.89/1.58  tff(c_139, plain, (~v1_funct_2('#skF_13', '#skF_11', '#skF_12') | ~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12')))), inference(splitRight, [status(thm)], [c_74])).
% 3.89/1.58  tff(c_141, plain, (~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12')))), inference(splitLeft, [status(thm)], [c_139])).
% 3.89/1.58  tff(c_652, plain, (r2_hidden('#skF_10'('#skF_11', '#skF_12', '#skF_13'), '#skF_11')), inference(resolution, [status(thm)], [c_648, c_141])).
% 3.89/1.58  tff(c_277, plain, (![A_125, B_126, D_127]: (r1_tarski(k2_relat_1('#skF_9'(A_125, B_126, k1_funct_2(A_125, B_126), D_127)), B_126) | ~r2_hidden(D_127, k1_funct_2(A_125, B_126)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.58  tff(c_285, plain, (r1_tarski(k2_relat_1('#skF_13'), '#skF_12') | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_277])).
% 3.89/1.58  tff(c_289, plain, (r1_tarski(k2_relat_1('#skF_13'), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_285])).
% 3.89/1.58  tff(c_186, plain, (![A_104, D_105]: (r2_hidden(k1_funct_1(A_104, D_105), k2_relat_1(A_104)) | ~r2_hidden(D_105, k1_relat_1(A_104)) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.89/1.58  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.89/1.58  tff(c_189, plain, (![A_104, D_105, B_2]: (r2_hidden(k1_funct_1(A_104, D_105), B_2) | ~r1_tarski(k2_relat_1(A_104), B_2) | ~r2_hidden(D_105, k1_relat_1(A_104)) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_186, c_2])).
% 3.89/1.58  tff(c_873, plain, (![C_221, B_222]: (~r2_hidden(k1_funct_1(C_221, '#skF_10'(k1_relat_1(C_221), B_222, C_221)), B_222) | m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_221), B_222))) | ~v1_funct_1(C_221) | ~v1_relat_1(C_221))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.89/1.58  tff(c_880, plain, (![B_222]: (~r2_hidden(k1_funct_1('#skF_13', '#skF_10'('#skF_11', B_222, '#skF_13')), B_222) | m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_13'), B_222))) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_873])).
% 3.89/1.58  tff(c_892, plain, (![B_223]: (~r2_hidden(k1_funct_1('#skF_13', '#skF_10'('#skF_11', B_223, '#skF_13')), B_223) | m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', B_223))))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_140, c_213, c_880])).
% 3.89/1.58  tff(c_896, plain, (![B_2]: (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', B_2))) | ~r1_tarski(k2_relat_1('#skF_13'), B_2) | ~r2_hidden('#skF_10'('#skF_11', B_2, '#skF_13'), k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_189, c_892])).
% 3.89/1.58  tff(c_907, plain, (![B_224]: (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', B_224))) | ~r1_tarski(k2_relat_1('#skF_13'), B_224) | ~r2_hidden('#skF_10'('#skF_11', B_224, '#skF_13'), '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_140, c_213, c_896])).
% 3.89/1.58  tff(c_910, plain, (~r1_tarski(k2_relat_1('#skF_13'), '#skF_12') | ~r2_hidden('#skF_10'('#skF_11', '#skF_12', '#skF_13'), '#skF_11')), inference(resolution, [status(thm)], [c_907, c_141])).
% 3.89/1.58  tff(c_914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_652, c_289, c_910])).
% 3.89/1.58  tff(c_915, plain, (~v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(splitRight, [status(thm)], [c_139])).
% 3.89/1.58  tff(c_933, plain, (![A_229, B_230, D_231]: ('#skF_9'(A_229, B_230, k1_funct_2(A_229, B_230), D_231)=D_231 | ~r2_hidden(D_231, k1_funct_2(A_229, B_230)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.58  tff(c_944, plain, ('#skF_9'('#skF_11', '#skF_12', k1_funct_2('#skF_11', '#skF_12'), '#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_76, c_933])).
% 3.89/1.58  tff(c_1044, plain, (![A_256, B_257, D_258]: (r1_tarski(k2_relat_1('#skF_9'(A_256, B_257, k1_funct_2(A_256, B_257), D_258)), B_257) | ~r2_hidden(D_258, k1_funct_2(A_256, B_257)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.58  tff(c_1052, plain, (r1_tarski(k2_relat_1('#skF_13'), '#skF_12') | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_944, c_1044])).
% 3.89/1.58  tff(c_1056, plain, (r1_tarski(k2_relat_1('#skF_13'), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1052])).
% 3.89/1.58  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.89/1.58  tff(c_78, plain, (![A_72, B_73]: (~r2_hidden('#skF_1'(A_72, B_73), B_73) | r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.89/1.58  tff(c_83, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_78])).
% 3.89/1.58  tff(c_955, plain, (![A_235, B_236, D_237]: (v1_relat_1('#skF_9'(A_235, B_236, k1_funct_2(A_235, B_236), D_237)) | ~r2_hidden(D_237, k1_funct_2(A_235, B_236)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.58  tff(c_958, plain, (v1_relat_1('#skF_13') | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_944, c_955])).
% 3.89/1.58  tff(c_960, plain, (v1_relat_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_958])).
% 3.89/1.58  tff(c_961, plain, (![A_238, B_239, D_240]: (k1_relat_1('#skF_9'(A_238, B_239, k1_funct_2(A_238, B_239), D_240))=A_238 | ~r2_hidden(D_240, k1_funct_2(A_238, B_239)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.58  tff(c_970, plain, (k1_relat_1('#skF_13')='#skF_11' | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_944, c_961])).
% 3.89/1.58  tff(c_974, plain, (k1_relat_1('#skF_13')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_970])).
% 3.89/1.58  tff(c_1165, plain, (![C_287, B_288]: (r2_hidden('#skF_10'(k1_relat_1(C_287), B_288, C_287), k1_relat_1(C_287)) | v1_funct_2(C_287, k1_relat_1(C_287), B_288) | ~v1_funct_1(C_287) | ~v1_relat_1(C_287))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.89/1.58  tff(c_1170, plain, (![B_288]: (r2_hidden('#skF_10'('#skF_11', B_288, '#skF_13'), k1_relat_1('#skF_13')) | v1_funct_2('#skF_13', k1_relat_1('#skF_13'), B_288) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_974, c_1165])).
% 3.89/1.58  tff(c_1185, plain, (![B_289]: (r2_hidden('#skF_10'('#skF_11', B_289, '#skF_13'), '#skF_11') | v1_funct_2('#skF_13', '#skF_11', B_289))), inference(demodulation, [status(thm), theory('equality')], [c_960, c_140, c_974, c_974, c_1170])).
% 3.89/1.58  tff(c_1188, plain, (![B_289, B_2]: (r2_hidden('#skF_10'('#skF_11', B_289, '#skF_13'), B_2) | ~r1_tarski('#skF_11', B_2) | v1_funct_2('#skF_13', '#skF_11', B_289))), inference(resolution, [status(thm)], [c_1185, c_2])).
% 3.89/1.58  tff(c_1028, plain, (![A_247, D_248]: (r2_hidden(k1_funct_1(A_247, D_248), k2_relat_1(A_247)) | ~r2_hidden(D_248, k1_relat_1(A_247)) | ~v1_funct_1(A_247) | ~v1_relat_1(A_247))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.89/1.58  tff(c_1031, plain, (![A_247, D_248, B_2]: (r2_hidden(k1_funct_1(A_247, D_248), B_2) | ~r1_tarski(k2_relat_1(A_247), B_2) | ~r2_hidden(D_248, k1_relat_1(A_247)) | ~v1_funct_1(A_247) | ~v1_relat_1(A_247))), inference(resolution, [status(thm)], [c_1028, c_2])).
% 3.89/1.58  tff(c_1301, plain, (![C_310, B_311]: (~r2_hidden(k1_funct_1(C_310, '#skF_10'(k1_relat_1(C_310), B_311, C_310)), B_311) | v1_funct_2(C_310, k1_relat_1(C_310), B_311) | ~v1_funct_1(C_310) | ~v1_relat_1(C_310))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.89/1.58  tff(c_1312, plain, (![B_311]: (~r2_hidden(k1_funct_1('#skF_13', '#skF_10'('#skF_11', B_311, '#skF_13')), B_311) | v1_funct_2('#skF_13', k1_relat_1('#skF_13'), B_311) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_974, c_1301])).
% 3.89/1.58  tff(c_1320, plain, (![B_312]: (~r2_hidden(k1_funct_1('#skF_13', '#skF_10'('#skF_11', B_312, '#skF_13')), B_312) | v1_funct_2('#skF_13', '#skF_11', B_312))), inference(demodulation, [status(thm), theory('equality')], [c_960, c_140, c_974, c_1312])).
% 3.89/1.58  tff(c_1324, plain, (![B_2]: (v1_funct_2('#skF_13', '#skF_11', B_2) | ~r1_tarski(k2_relat_1('#skF_13'), B_2) | ~r2_hidden('#skF_10'('#skF_11', B_2, '#skF_13'), k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_1031, c_1320])).
% 3.89/1.58  tff(c_1347, plain, (![B_313]: (v1_funct_2('#skF_13', '#skF_11', B_313) | ~r1_tarski(k2_relat_1('#skF_13'), B_313) | ~r2_hidden('#skF_10'('#skF_11', B_313, '#skF_13'), '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_960, c_140, c_974, c_1324])).
% 3.89/1.58  tff(c_1351, plain, (![B_289]: (~r1_tarski(k2_relat_1('#skF_13'), B_289) | ~r1_tarski('#skF_11', '#skF_11') | v1_funct_2('#skF_13', '#skF_11', B_289))), inference(resolution, [status(thm)], [c_1188, c_1347])).
% 3.89/1.58  tff(c_1359, plain, (![B_314]: (~r1_tarski(k2_relat_1('#skF_13'), B_314) | v1_funct_2('#skF_13', '#skF_11', B_314))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1351])).
% 3.89/1.58  tff(c_1362, plain, (v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(resolution, [status(thm)], [c_1056, c_1359])).
% 3.89/1.58  tff(c_1370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_915, c_1362])).
% 3.89/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.58  
% 3.89/1.58  Inference rules
% 3.89/1.58  ----------------------
% 3.89/1.58  #Ref     : 0
% 3.89/1.58  #Sup     : 307
% 3.89/1.58  #Fact    : 0
% 3.89/1.58  #Define  : 0
% 3.89/1.58  #Split   : 7
% 3.89/1.58  #Chain   : 0
% 3.89/1.58  #Close   : 0
% 3.89/1.58  
% 3.89/1.58  Ordering : KBO
% 3.89/1.58  
% 3.89/1.58  Simplification rules
% 3.89/1.58  ----------------------
% 3.89/1.58  #Subsume      : 40
% 3.89/1.58  #Demod        : 125
% 3.89/1.58  #Tautology    : 65
% 3.89/1.58  #SimpNegUnit  : 2
% 3.89/1.58  #BackRed      : 0
% 3.89/1.58  
% 3.89/1.58  #Partial instantiations: 0
% 3.89/1.58  #Strategies tried      : 1
% 3.89/1.58  
% 3.89/1.58  Timing (in seconds)
% 3.89/1.58  ----------------------
% 3.89/1.59  Preprocessing        : 0.34
% 3.89/1.59  Parsing              : 0.17
% 3.89/1.59  CNF conversion       : 0.03
% 3.89/1.59  Main loop            : 0.50
% 3.89/1.59  Inferencing          : 0.20
% 3.89/1.59  Reduction            : 0.14
% 3.89/1.59  Demodulation         : 0.10
% 3.89/1.59  BG Simplification    : 0.03
% 3.89/1.59  Subsumption          : 0.09
% 3.89/1.59  Abstraction          : 0.03
% 3.89/1.59  MUC search           : 0.00
% 3.89/1.59  Cooper               : 0.00
% 3.89/1.59  Total                : 0.88
% 3.89/1.59  Index Insertion      : 0.00
% 3.89/1.59  Index Deletion       : 0.00
% 3.89/1.59  Index Matching       : 0.00
% 3.89/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
