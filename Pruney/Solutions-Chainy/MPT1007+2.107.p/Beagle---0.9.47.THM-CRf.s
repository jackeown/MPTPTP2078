%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:25 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 230 expanded)
%              Number of leaves         :   46 (  98 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 552 expanded)
%              Number of equality atoms :   44 ( 125 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_140,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_116,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_55,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_74,axiom,(
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

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_52,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_12,plain,(
    ! [A_10] : m1_subset_1('#skF_1'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    ! [A_64] : k2_tarski(A_64,A_64) = k1_tarski(A_64) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_8,B_9] : ~ v1_xboole_0(k2_tarski(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_87,plain,(
    ! [A_64] : ~ v1_xboole_0(k1_tarski(A_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10])).

tff(c_48,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_2'(A_32),A_32)
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_177,plain,(
    ! [C_89,A_90,B_91] :
      ( r2_hidden(C_89,A_90)
      | ~ r2_hidden(C_89,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_184,plain,(
    ! [A_92,A_93] :
      ( r2_hidden('#skF_2'(A_92),A_93)
      | ~ m1_subset_1(A_92,k1_zfmisc_1(A_93))
      | k1_xboole_0 = A_92 ) ),
    inference(resolution,[status(thm)],[c_48,c_177])).

tff(c_40,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_hidden(k1_mcart_1(A_26),B_27)
      | ~ r2_hidden(A_26,k2_zfmisc_1(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_768,plain,(
    ! [A_153,B_154,C_155] :
      ( r2_hidden(k1_mcart_1('#skF_2'(A_153)),B_154)
      | ~ m1_subset_1(A_153,k1_zfmisc_1(k2_zfmisc_1(B_154,C_155)))
      | k1_xboole_0 = A_153 ) ),
    inference(resolution,[status(thm)],[c_184,c_40])).

tff(c_779,plain,
    ( r2_hidden(k1_mcart_1('#skF_2'('#skF_5')),k1_tarski('#skF_3'))
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56,c_768])).

tff(c_781,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_779])).

tff(c_810,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_54])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_77,plain,(
    ! [A_60] : v1_relat_1(k6_relat_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_79,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_77])).

tff(c_73,plain,(
    ! [A_58] : v1_funct_1(k6_relat_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_75,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_73])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_211,plain,(
    ! [A_96,B_97] :
      ( k1_funct_1(A_96,B_97) = k1_xboole_0
      | r2_hidden(B_97,k1_relat_1(A_96))
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_219,plain,(
    ! [B_97] :
      ( k1_funct_1(k1_xboole_0,B_97) = k1_xboole_0
      | r2_hidden(B_97,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_211])).

tff(c_263,plain,(
    ! [B_101] :
      ( k1_funct_1(k1_xboole_0,B_101) = k1_xboole_0
      | r2_hidden(B_101,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_75,c_219])).

tff(c_36,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_268,plain,(
    ! [B_101] :
      ( ~ r1_tarski(k1_xboole_0,B_101)
      | k1_funct_1(k1_xboole_0,B_101) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_263,c_36])).

tff(c_272,plain,(
    ! [B_101] : k1_funct_1(k1_xboole_0,B_101) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_268])).

tff(c_794,plain,(
    ! [B_101] : k1_funct_1('#skF_5',B_101) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_781,c_272])).

tff(c_919,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_794,c_52])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_528,plain,(
    ! [D_128,C_129,B_130,A_131] :
      ( r2_hidden(k1_funct_1(D_128,C_129),B_130)
      | k1_xboole_0 = B_130
      | ~ r2_hidden(C_129,A_131)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130)))
      | ~ v1_funct_2(D_128,A_131,B_130)
      | ~ v1_funct_1(D_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_548,plain,(
    ! [D_128,A_16,B_130,B_17] :
      ( r2_hidden(k1_funct_1(D_128,A_16),B_130)
      | k1_xboole_0 = B_130
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(B_17,B_130)))
      | ~ v1_funct_2(D_128,B_17,B_130)
      | ~ v1_funct_1(D_128)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_16,c_528])).

tff(c_2396,plain,(
    ! [D_290,A_291,B_292,B_293] :
      ( r2_hidden(k1_funct_1(D_290,A_291),B_292)
      | B_292 = '#skF_5'
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(B_293,B_292)))
      | ~ v1_funct_2(D_290,B_293,B_292)
      | ~ v1_funct_1(D_290)
      | v1_xboole_0(B_293)
      | ~ m1_subset_1(A_291,B_293) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_548])).

tff(c_2404,plain,(
    ! [A_291] :
      ( r2_hidden(k1_funct_1('#skF_5',A_291),'#skF_4')
      | '#skF_5' = '#skF_4'
      | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(k1_tarski('#skF_3'))
      | ~ m1_subset_1(A_291,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_56,c_2396])).

tff(c_2414,plain,(
    ! [A_291] :
      ( r2_hidden('#skF_5','#skF_4')
      | '#skF_5' = '#skF_4'
      | v1_xboole_0(k1_tarski('#skF_3'))
      | ~ m1_subset_1(A_291,k1_tarski('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_794,c_2404])).

tff(c_2417,plain,(
    ! [A_294] : ~ m1_subset_1(A_294,k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_810,c_919,c_2414])).

tff(c_2422,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_2417])).

tff(c_2424,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_44,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_mcart_1(A_29) = B_30
      | ~ r2_hidden(A_29,k2_zfmisc_1(k1_tarski(B_30),C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2474,plain,(
    ! [A_297,B_298,C_299] :
      ( k1_mcart_1('#skF_2'(A_297)) = B_298
      | ~ m1_subset_1(A_297,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_298),C_299)))
      | k1_xboole_0 = A_297 ) ),
    inference(resolution,[status(thm)],[c_184,c_44])).

tff(c_2480,plain,
    ( k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56,c_2474])).

tff(c_2487,plain,(
    k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2424,c_2480])).

tff(c_2423,plain,(
    r2_hidden(k1_mcart_1('#skF_2'('#skF_5')),k1_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_50,plain,(
    ! [D_57,C_56,B_55,A_54] :
      ( r2_hidden(k1_funct_1(D_57,C_56),B_55)
      | k1_xboole_0 = B_55
      | ~ r2_hidden(C_56,A_54)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(D_57,A_54,B_55)
      | ~ v1_funct_1(D_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2432,plain,(
    ! [D_57,B_55] :
      ( r2_hidden(k1_funct_1(D_57,k1_mcart_1('#skF_2'('#skF_5'))),B_55)
      | k1_xboole_0 = B_55
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),B_55)))
      | ~ v1_funct_2(D_57,k1_tarski('#skF_3'),B_55)
      | ~ v1_funct_1(D_57) ) ),
    inference(resolution,[status(thm)],[c_2423,c_50])).

tff(c_2519,plain,(
    ! [D_303,B_304] :
      ( r2_hidden(k1_funct_1(D_303,'#skF_3'),B_304)
      | k1_xboole_0 = B_304
      | ~ m1_subset_1(D_303,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),B_304)))
      | ~ v1_funct_2(D_303,k1_tarski('#skF_3'),B_304)
      | ~ v1_funct_1(D_303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2487,c_2432])).

tff(c_2526,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2519])).

tff(c_2535,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2526])).

tff(c_2537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_2535])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:15:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.87  
% 4.51/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.87  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 4.51/1.87  
% 4.51/1.87  %Foreground sorts:
% 4.51/1.87  
% 4.51/1.87  
% 4.51/1.87  %Background operators:
% 4.51/1.87  
% 4.51/1.87  
% 4.51/1.87  %Foreground operators:
% 4.51/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.51/1.87  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.51/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.51/1.87  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.51/1.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.51/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.51/1.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.51/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.51/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.51/1.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.51/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.51/1.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.51/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.87  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.51/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.87  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.51/1.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.51/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.51/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.51/1.87  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.51/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.87  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.51/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.51/1.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.51/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.87  
% 4.51/1.88  tff(f_140, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 4.51/1.88  tff(f_39, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 4.51/1.88  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.51/1.88  tff(f_36, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 4.51/1.88  tff(f_116, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 4.51/1.88  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.51/1.88  tff(f_89, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.51/1.88  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.51/1.88  tff(f_56, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 4.51/1.88  tff(f_78, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.51/1.88  tff(f_55, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.51/1.88  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 4.51/1.88  tff(f_83, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.51/1.88  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.51/1.88  tff(f_128, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 4.51/1.88  tff(f_95, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 4.51/1.88  tff(c_54, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.51/1.88  tff(c_52, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.51/1.88  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.51/1.88  tff(c_58, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.51/1.88  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.51/1.88  tff(c_12, plain, (![A_10]: (m1_subset_1('#skF_1'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.51/1.88  tff(c_82, plain, (![A_64]: (k2_tarski(A_64, A_64)=k1_tarski(A_64))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.51/1.88  tff(c_10, plain, (![A_8, B_9]: (~v1_xboole_0(k2_tarski(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.51/1.88  tff(c_87, plain, (![A_64]: (~v1_xboole_0(k1_tarski(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_10])).
% 4.51/1.88  tff(c_48, plain, (![A_32]: (r2_hidden('#skF_2'(A_32), A_32) | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.51/1.88  tff(c_177, plain, (![C_89, A_90, B_91]: (r2_hidden(C_89, A_90) | ~r2_hidden(C_89, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.88  tff(c_184, plain, (![A_92, A_93]: (r2_hidden('#skF_2'(A_92), A_93) | ~m1_subset_1(A_92, k1_zfmisc_1(A_93)) | k1_xboole_0=A_92)), inference(resolution, [status(thm)], [c_48, c_177])).
% 4.51/1.88  tff(c_40, plain, (![A_26, B_27, C_28]: (r2_hidden(k1_mcart_1(A_26), B_27) | ~r2_hidden(A_26, k2_zfmisc_1(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.51/1.88  tff(c_768, plain, (![A_153, B_154, C_155]: (r2_hidden(k1_mcart_1('#skF_2'(A_153)), B_154) | ~m1_subset_1(A_153, k1_zfmisc_1(k2_zfmisc_1(B_154, C_155))) | k1_xboole_0=A_153)), inference(resolution, [status(thm)], [c_184, c_40])).
% 4.51/1.88  tff(c_779, plain, (r2_hidden(k1_mcart_1('#skF_2'('#skF_5')), k1_tarski('#skF_3')) | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_56, c_768])).
% 4.51/1.88  tff(c_781, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_779])).
% 4.51/1.88  tff(c_810, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_781, c_54])).
% 4.51/1.88  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.51/1.88  tff(c_22, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.51/1.88  tff(c_77, plain, (![A_60]: (v1_relat_1(k6_relat_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.51/1.88  tff(c_79, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_77])).
% 4.51/1.88  tff(c_73, plain, (![A_58]: (v1_funct_1(k6_relat_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.51/1.88  tff(c_75, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_73])).
% 4.51/1.88  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.51/1.88  tff(c_211, plain, (![A_96, B_97]: (k1_funct_1(A_96, B_97)=k1_xboole_0 | r2_hidden(B_97, k1_relat_1(A_96)) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.51/1.88  tff(c_219, plain, (![B_97]: (k1_funct_1(k1_xboole_0, B_97)=k1_xboole_0 | r2_hidden(B_97, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_211])).
% 4.51/1.88  tff(c_263, plain, (![B_101]: (k1_funct_1(k1_xboole_0, B_101)=k1_xboole_0 | r2_hidden(B_101, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_75, c_219])).
% 4.51/1.88  tff(c_36, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.51/1.88  tff(c_268, plain, (![B_101]: (~r1_tarski(k1_xboole_0, B_101) | k1_funct_1(k1_xboole_0, B_101)=k1_xboole_0)), inference(resolution, [status(thm)], [c_263, c_36])).
% 4.51/1.88  tff(c_272, plain, (![B_101]: (k1_funct_1(k1_xboole_0, B_101)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_268])).
% 4.51/1.88  tff(c_794, plain, (![B_101]: (k1_funct_1('#skF_5', B_101)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_781, c_781, c_272])).
% 4.51/1.88  tff(c_919, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_794, c_52])).
% 4.51/1.88  tff(c_16, plain, (![A_16, B_17]: (r2_hidden(A_16, B_17) | v1_xboole_0(B_17) | ~m1_subset_1(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.51/1.88  tff(c_528, plain, (![D_128, C_129, B_130, A_131]: (r2_hidden(k1_funct_1(D_128, C_129), B_130) | k1_xboole_0=B_130 | ~r2_hidden(C_129, A_131) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))) | ~v1_funct_2(D_128, A_131, B_130) | ~v1_funct_1(D_128))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.51/1.88  tff(c_548, plain, (![D_128, A_16, B_130, B_17]: (r2_hidden(k1_funct_1(D_128, A_16), B_130) | k1_xboole_0=B_130 | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(B_17, B_130))) | ~v1_funct_2(D_128, B_17, B_130) | ~v1_funct_1(D_128) | v1_xboole_0(B_17) | ~m1_subset_1(A_16, B_17))), inference(resolution, [status(thm)], [c_16, c_528])).
% 4.51/1.88  tff(c_2396, plain, (![D_290, A_291, B_292, B_293]: (r2_hidden(k1_funct_1(D_290, A_291), B_292) | B_292='#skF_5' | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(B_293, B_292))) | ~v1_funct_2(D_290, B_293, B_292) | ~v1_funct_1(D_290) | v1_xboole_0(B_293) | ~m1_subset_1(A_291, B_293))), inference(demodulation, [status(thm), theory('equality')], [c_781, c_548])).
% 4.51/1.88  tff(c_2404, plain, (![A_291]: (r2_hidden(k1_funct_1('#skF_5', A_291), '#skF_4') | '#skF_5'='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0(k1_tarski('#skF_3')) | ~m1_subset_1(A_291, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_56, c_2396])).
% 4.51/1.88  tff(c_2414, plain, (![A_291]: (r2_hidden('#skF_5', '#skF_4') | '#skF_5'='#skF_4' | v1_xboole_0(k1_tarski('#skF_3')) | ~m1_subset_1(A_291, k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_794, c_2404])).
% 4.51/1.88  tff(c_2417, plain, (![A_294]: (~m1_subset_1(A_294, k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_87, c_810, c_919, c_2414])).
% 4.51/1.88  tff(c_2422, plain, $false, inference(resolution, [status(thm)], [c_12, c_2417])).
% 4.51/1.88  tff(c_2424, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_779])).
% 4.51/1.88  tff(c_44, plain, (![A_29, B_30, C_31]: (k1_mcart_1(A_29)=B_30 | ~r2_hidden(A_29, k2_zfmisc_1(k1_tarski(B_30), C_31)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.51/1.88  tff(c_2474, plain, (![A_297, B_298, C_299]: (k1_mcart_1('#skF_2'(A_297))=B_298 | ~m1_subset_1(A_297, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_298), C_299))) | k1_xboole_0=A_297)), inference(resolution, [status(thm)], [c_184, c_44])).
% 4.51/1.88  tff(c_2480, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_56, c_2474])).
% 4.51/1.88  tff(c_2487, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2424, c_2480])).
% 4.51/1.88  tff(c_2423, plain, (r2_hidden(k1_mcart_1('#skF_2'('#skF_5')), k1_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_779])).
% 4.51/1.88  tff(c_50, plain, (![D_57, C_56, B_55, A_54]: (r2_hidden(k1_funct_1(D_57, C_56), B_55) | k1_xboole_0=B_55 | ~r2_hidden(C_56, A_54) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(D_57, A_54, B_55) | ~v1_funct_1(D_57))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.51/1.88  tff(c_2432, plain, (![D_57, B_55]: (r2_hidden(k1_funct_1(D_57, k1_mcart_1('#skF_2'('#skF_5'))), B_55) | k1_xboole_0=B_55 | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), B_55))) | ~v1_funct_2(D_57, k1_tarski('#skF_3'), B_55) | ~v1_funct_1(D_57))), inference(resolution, [status(thm)], [c_2423, c_50])).
% 4.51/1.88  tff(c_2519, plain, (![D_303, B_304]: (r2_hidden(k1_funct_1(D_303, '#skF_3'), B_304) | k1_xboole_0=B_304 | ~m1_subset_1(D_303, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), B_304))) | ~v1_funct_2(D_303, k1_tarski('#skF_3'), B_304) | ~v1_funct_1(D_303))), inference(demodulation, [status(thm), theory('equality')], [c_2487, c_2432])).
% 4.51/1.88  tff(c_2526, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_2519])).
% 4.51/1.88  tff(c_2535, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2526])).
% 4.51/1.88  tff(c_2537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_2535])).
% 4.51/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.88  
% 4.51/1.88  Inference rules
% 4.51/1.88  ----------------------
% 4.51/1.88  #Ref     : 0
% 4.51/1.88  #Sup     : 547
% 4.51/1.88  #Fact    : 4
% 4.51/1.88  #Define  : 0
% 4.51/1.88  #Split   : 4
% 4.51/1.88  #Chain   : 0
% 4.51/1.88  #Close   : 0
% 4.51/1.88  
% 4.51/1.88  Ordering : KBO
% 4.51/1.88  
% 4.51/1.88  Simplification rules
% 4.51/1.88  ----------------------
% 4.51/1.88  #Subsume      : 93
% 4.51/1.88  #Demod        : 395
% 4.51/1.88  #Tautology    : 190
% 4.51/1.88  #SimpNegUnit  : 39
% 4.51/1.88  #BackRed      : 37
% 4.51/1.88  
% 4.51/1.88  #Partial instantiations: 0
% 4.51/1.88  #Strategies tried      : 1
% 4.51/1.88  
% 4.51/1.88  Timing (in seconds)
% 4.51/1.88  ----------------------
% 4.51/1.89  Preprocessing        : 0.36
% 4.51/1.89  Parsing              : 0.20
% 4.51/1.89  CNF conversion       : 0.02
% 4.51/1.89  Main loop            : 0.71
% 4.51/1.89  Inferencing          : 0.25
% 4.51/1.89  Reduction            : 0.22
% 4.51/1.89  Demodulation         : 0.15
% 4.51/1.89  BG Simplification    : 0.03
% 4.51/1.89  Subsumption          : 0.14
% 4.51/1.89  Abstraction          : 0.03
% 4.51/1.89  MUC search           : 0.00
% 4.51/1.89  Cooper               : 0.00
% 4.51/1.89  Total                : 1.10
% 4.51/1.89  Index Insertion      : 0.00
% 4.51/1.89  Index Deletion       : 0.00
% 4.51/1.89  Index Matching       : 0.00
% 4.51/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
