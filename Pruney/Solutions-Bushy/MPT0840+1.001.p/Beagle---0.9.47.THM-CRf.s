%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0840+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:56 EST 2020

% Result     : Theorem 12.25s
% Output     : CNFRefutation 12.34s
% Verified   : 
% Statistics : Number of formulae       :  221 (1071 expanded)
%              Number of leaves         :   40 ( 368 expanded)
%              Depth                    :   12
%              Number of atoms          :  477 (3397 expanded)
%              Number of equality atoms :   16 (  98 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_17 > #skF_11 > #skF_6 > #skF_15 > #skF_4 > #skF_10 > #skF_16 > #skF_14 > #skF_13 > #skF_5 > #skF_2 > #skF_9 > #skF_1 > #skF_8 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C)))
                       => ! [F,G] :
                            ( r2_hidden(k4_tarski(F,G),k4_relset_1(A,B,B,C,D,E))
                          <=> ? [H] :
                                ( m1_subset_1(H,B)
                                & r2_hidden(k4_tarski(F,H),D)
                                & r2_hidden(k4_tarski(H,G),E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_55,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_44,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_19311,plain,(
    ! [C_2532,A_2533,B_2534] :
      ( v1_relat_1(C_2532)
      | ~ m1_subset_1(C_2532,k1_zfmisc_1(k2_zfmisc_1(A_2533,B_2534))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_19323,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_44,c_19311])).

tff(c_42,plain,(
    m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_19322,plain,(
    v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_42,c_19311])).

tff(c_22,plain,(
    ! [A_103,B_104] :
      ( v1_relat_1(k5_relat_1(A_103,B_104))
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_81,plain,(
    ! [C_350,A_351,B_352] :
      ( v1_relat_1(C_350)
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_93,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_44,c_81])).

tff(c_92,plain,(
    v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_42,c_81])).

tff(c_12474,plain,(
    ! [A_1858,C_1853,F_1854,B_1856,D_1855,E_1857] :
      ( k4_relset_1(A_1858,B_1856,C_1853,D_1855,E_1857,F_1854) = k5_relat_1(E_1857,F_1854)
      | ~ m1_subset_1(F_1854,k1_zfmisc_1(k2_zfmisc_1(C_1853,D_1855)))
      | ~ m1_subset_1(E_1857,k1_zfmisc_1(k2_zfmisc_1(A_1858,B_1856))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12973,plain,(
    ! [A_1926,B_1927,E_1928] :
      ( k4_relset_1(A_1926,B_1927,'#skF_9','#skF_10',E_1928,'#skF_12') = k5_relat_1(E_1928,'#skF_12')
      | ~ m1_subset_1(E_1928,k1_zfmisc_1(k2_zfmisc_1(A_1926,B_1927))) ) ),
    inference(resolution,[status(thm)],[c_42,c_12474])).

tff(c_12990,plain,(
    k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12') = k5_relat_1('#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_44,c_12973])).

tff(c_66,plain,
    ( m1_subset_1('#skF_15','#skF_9')
    | r2_hidden(k4_tarski('#skF_16','#skF_17'),k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_79,plain,(
    r2_hidden(k4_tarski('#skF_16','#skF_17'),k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_13000,plain,(
    r2_hidden(k4_tarski('#skF_16','#skF_17'),k5_relat_1('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12990,c_79])).

tff(c_13046,plain,(
    ! [B_1932,A_1933,D_1934,E_1935] :
      ( r2_hidden(k4_tarski('#skF_1'(B_1932,k5_relat_1(A_1933,B_1932),D_1934,E_1935,A_1933),E_1935),B_1932)
      | ~ r2_hidden(k4_tarski(D_1934,E_1935),k5_relat_1(A_1933,B_1932))
      | ~ v1_relat_1(k5_relat_1(A_1933,B_1932))
      | ~ v1_relat_1(B_1932)
      | ~ v1_relat_1(A_1933) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_105] : m1_subset_1('#skF_7'(A_105),A_105) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    ! [A_119,B_120] :
      ( r2_hidden(A_119,B_120)
      | v1_xboole_0(B_120)
      | ~ m1_subset_1(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_101,plain,(
    ! [A_359,C_360,B_361] :
      ( m1_subset_1(A_359,C_360)
      | ~ m1_subset_1(B_361,k1_zfmisc_1(C_360))
      | ~ r2_hidden(A_359,B_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_109,plain,(
    ! [A_359] :
      ( m1_subset_1(A_359,k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(A_359,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_42,c_101])).

tff(c_121,plain,(
    ! [B_366,D_367,A_368,C_369] :
      ( r2_hidden(B_366,D_367)
      | ~ r2_hidden(k4_tarski(A_368,B_366),k2_zfmisc_1(C_369,D_367)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_176,plain,(
    ! [B_385,D_386,C_387,A_388] :
      ( r2_hidden(B_385,D_386)
      | v1_xboole_0(k2_zfmisc_1(C_387,D_386))
      | ~ m1_subset_1(k4_tarski(A_388,B_385),k2_zfmisc_1(C_387,D_386)) ) ),
    inference(resolution,[status(thm)],[c_36,c_121])).

tff(c_190,plain,(
    ! [B_385,A_388] :
      ( r2_hidden(B_385,'#skF_10')
      | v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(k4_tarski(A_388,B_385),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_109,c_176])).

tff(c_739,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_135,plain,(
    ! [A_370,B_371,C_372,D_373] :
      ( r2_hidden(k4_tarski(A_370,B_371),k2_zfmisc_1(C_372,D_373))
      | ~ r2_hidden(B_371,D_373)
      | ~ r2_hidden(A_370,C_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ! [B_125,A_124] :
      ( ~ v1_xboole_0(B_125)
      | ~ r2_hidden(A_124,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_151,plain,(
    ! [C_372,D_373,B_371,A_370] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_372,D_373))
      | ~ r2_hidden(B_371,D_373)
      | ~ r2_hidden(A_370,C_372) ) ),
    inference(resolution,[status(thm)],[c_135,c_40])).

tff(c_743,plain,(
    ! [B_371,A_370] :
      ( ~ r2_hidden(B_371,'#skF_10')
      | ~ r2_hidden(A_370,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_739,c_151])).

tff(c_747,plain,(
    ! [A_472] : ~ r2_hidden(A_472,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_743])).

tff(c_751,plain,(
    ! [A_119] :
      ( v1_xboole_0('#skF_9')
      | ~ m1_subset_1(A_119,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_747])).

tff(c_756,plain,(
    ! [A_473] : ~ m1_subset_1(A_473,'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_751])).

tff(c_766,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_24,c_756])).

tff(c_768,plain,(
    ! [B_474] : ~ r2_hidden(B_474,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_743])).

tff(c_772,plain,(
    ! [A_119] :
      ( v1_xboole_0('#skF_10')
      | ~ m1_subset_1(A_119,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_36,c_768])).

tff(c_776,plain,(
    ! [A_475] : ~ m1_subset_1(A_475,'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_772])).

tff(c_786,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_24,c_776])).

tff(c_787,plain,(
    ! [B_385,A_388] :
      ( r2_hidden(B_385,'#skF_10')
      | ~ r2_hidden(k4_tarski(A_388,B_385),'#skF_12') ) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_13067,plain,(
    ! [E_1935,D_1934,A_1933] :
      ( r2_hidden(E_1935,'#skF_10')
      | ~ r2_hidden(k4_tarski(D_1934,E_1935),k5_relat_1(A_1933,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1933,'#skF_12'))
      | ~ v1_relat_1('#skF_12')
      | ~ v1_relat_1(A_1933) ) ),
    inference(resolution,[status(thm)],[c_13046,c_787])).

tff(c_13132,plain,(
    ! [E_1939,D_1940,A_1941] :
      ( r2_hidden(E_1939,'#skF_10')
      | ~ r2_hidden(k4_tarski(D_1940,E_1939),k5_relat_1(A_1941,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1941,'#skF_12'))
      | ~ v1_relat_1(A_1941) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_13067])).

tff(c_13142,plain,
    ( r2_hidden('#skF_17','#skF_10')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_13000,c_13132])).

tff(c_13152,plain,
    ( r2_hidden('#skF_17','#skF_10')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_13142])).

tff(c_13154,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_13152])).

tff(c_13157,plain,
    ( ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_22,c_13154])).

tff(c_13161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_92,c_13157])).

tff(c_13163,plain,(
    v1_relat_1(k5_relat_1('#skF_11','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_13152])).

tff(c_13172,plain,(
    ! [D_1942,B_1943,A_1944,E_1945] :
      ( r2_hidden(k4_tarski(D_1942,'#skF_1'(B_1943,k5_relat_1(A_1944,B_1943),D_1942,E_1945,A_1944)),A_1944)
      | ~ r2_hidden(k4_tarski(D_1942,E_1945),k5_relat_1(A_1944,B_1943))
      | ~ v1_relat_1(k5_relat_1(A_1944,B_1943))
      | ~ v1_relat_1(B_1943)
      | ~ v1_relat_1(A_1944) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_110,plain,(
    ! [A_359] :
      ( m1_subset_1(A_359,k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(A_359,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_44,c_101])).

tff(c_189,plain,(
    ! [B_385,A_388] :
      ( r2_hidden(B_385,'#skF_9')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(k4_tarski(A_388,B_385),'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_110,c_176])).

tff(c_191,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_194,plain,(
    ! [B_371,A_370] :
      ( ~ r2_hidden(B_371,'#skF_9')
      | ~ r2_hidden(A_370,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_191,c_151])).

tff(c_197,plain,(
    ! [A_389] : ~ r2_hidden(A_389,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_201,plain,(
    ! [A_119] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_119,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_197])).

tff(c_205,plain,(
    ! [A_390] : ~ m1_subset_1(A_390,'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_201])).

tff(c_215,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_24,c_205])).

tff(c_218,plain,(
    ! [B_391] : ~ r2_hidden(B_391,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_222,plain,(
    ! [A_119] :
      ( v1_xboole_0('#skF_9')
      | ~ m1_subset_1(A_119,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_218])).

tff(c_226,plain,(
    ! [A_392] : ~ m1_subset_1(A_392,'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_222])).

tff(c_236,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_24,c_226])).

tff(c_237,plain,(
    ! [B_385,A_388] :
      ( r2_hidden(B_385,'#skF_9')
      | ~ r2_hidden(k4_tarski(A_388,B_385),'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_13206,plain,(
    ! [B_1943,D_1942,E_1945] :
      ( r2_hidden('#skF_1'(B_1943,k5_relat_1('#skF_11',B_1943),D_1942,E_1945,'#skF_11'),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_1942,E_1945),k5_relat_1('#skF_11',B_1943))
      | ~ v1_relat_1(k5_relat_1('#skF_11',B_1943))
      | ~ v1_relat_1(B_1943)
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_13172,c_237])).

tff(c_15553,plain,(
    ! [B_2211,D_2212,E_2213] :
      ( r2_hidden('#skF_1'(B_2211,k5_relat_1('#skF_11',B_2211),D_2212,E_2213,'#skF_11'),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_2212,E_2213),k5_relat_1('#skF_11',B_2211))
      | ~ v1_relat_1(k5_relat_1('#skF_11',B_2211))
      | ~ v1_relat_1(B_2211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_13206])).

tff(c_34,plain,(
    ! [A_117,B_118] :
      ( m1_subset_1(A_117,B_118)
      | ~ r2_hidden(A_117,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_15598,plain,(
    ! [B_2226,D_2227,E_2228] :
      ( m1_subset_1('#skF_1'(B_2226,k5_relat_1('#skF_11',B_2226),D_2227,E_2228,'#skF_11'),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_2227,E_2228),k5_relat_1('#skF_11',B_2226))
      | ~ v1_relat_1(k5_relat_1('#skF_11',B_2226))
      | ~ v1_relat_1(B_2226) ) ),
    inference(resolution,[status(thm)],[c_15553,c_34])).

tff(c_15647,plain,
    ( m1_subset_1('#skF_1'('#skF_12',k5_relat_1('#skF_11','#skF_12'),'#skF_16','#skF_17','#skF_11'),'#skF_9')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_13000,c_15598])).

tff(c_15679,plain,(
    m1_subset_1('#skF_1'('#skF_12',k5_relat_1('#skF_11','#skF_12'),'#skF_16','#skF_17','#skF_11'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_13163,c_15647])).

tff(c_20,plain,(
    ! [D_95,B_56,A_4,E_96] :
      ( r2_hidden(k4_tarski(D_95,'#skF_1'(B_56,k5_relat_1(A_4,B_56),D_95,E_96,A_4)),A_4)
      | ~ r2_hidden(k4_tarski(D_95,E_96),k5_relat_1(A_4,B_56))
      | ~ v1_relat_1(k5_relat_1(A_4,B_56))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12613,plain,(
    ! [A_1883,B_1884,E_1885] :
      ( k4_relset_1(A_1883,B_1884,'#skF_9','#skF_10',E_1885,'#skF_12') = k5_relat_1(E_1885,'#skF_12')
      | ~ m1_subset_1(E_1885,k1_zfmisc_1(k2_zfmisc_1(A_1883,B_1884))) ) ),
    inference(resolution,[status(thm)],[c_42,c_12474])).

tff(c_12630,plain,(
    k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12') = k5_relat_1('#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_44,c_12613])).

tff(c_12640,plain,(
    r2_hidden(k4_tarski('#skF_16','#skF_17'),k5_relat_1('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12630,c_79])).

tff(c_12645,plain,(
    ! [D_1886,B_1887,A_1888,E_1889] :
      ( r2_hidden(k4_tarski(D_1886,'#skF_1'(B_1887,k5_relat_1(A_1888,B_1887),D_1886,E_1889,A_1888)),A_1888)
      | ~ r2_hidden(k4_tarski(D_1886,E_1889),k5_relat_1(A_1888,B_1887))
      | ~ v1_relat_1(k5_relat_1(A_1888,B_1887))
      | ~ v1_relat_1(B_1887)
      | ~ v1_relat_1(A_1888) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_238,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_96,plain,(
    ! [A_355,C_356,B_357,D_358] :
      ( r2_hidden(A_355,C_356)
      | ~ r2_hidden(k4_tarski(A_355,B_357),k2_zfmisc_1(C_356,D_358)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12489,plain,(
    ! [A_1859,C_1860,D_1861,B_1862] :
      ( r2_hidden(A_1859,C_1860)
      | v1_xboole_0(k2_zfmisc_1(C_1860,D_1861))
      | ~ m1_subset_1(k4_tarski(A_1859,B_1862),k2_zfmisc_1(C_1860,D_1861)) ) ),
    inference(resolution,[status(thm)],[c_36,c_96])).

tff(c_12496,plain,(
    ! [A_1859,B_1862] :
      ( r2_hidden(A_1859,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(k4_tarski(A_1859,B_1862),'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_110,c_12489])).

tff(c_12504,plain,(
    ! [A_1859,B_1862] :
      ( r2_hidden(A_1859,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_1859,B_1862),'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_12496])).

tff(c_12659,plain,(
    ! [D_1886,E_1889,B_1887] :
      ( r2_hidden(D_1886,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1886,E_1889),k5_relat_1('#skF_11',B_1887))
      | ~ v1_relat_1(k5_relat_1('#skF_11',B_1887))
      | ~ v1_relat_1(B_1887)
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_12645,c_12504])).

tff(c_12723,plain,(
    ! [D_1890,E_1891,B_1892] :
      ( r2_hidden(D_1890,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_1890,E_1891),k5_relat_1('#skF_11',B_1892))
      | ~ v1_relat_1(k5_relat_1('#skF_11',B_1892))
      | ~ v1_relat_1(B_1892) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_12659])).

tff(c_12726,plain,
    ( r2_hidden('#skF_16','#skF_8')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_12640,c_12723])).

tff(c_12736,plain,
    ( r2_hidden('#skF_16','#skF_8')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_12726])).

tff(c_12739,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_12736])).

tff(c_12807,plain,
    ( ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_22,c_12739])).

tff(c_12811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_92,c_12807])).

tff(c_12813,plain,(
    v1_relat_1(k5_relat_1('#skF_11','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_12736])).

tff(c_6499,plain,(
    ! [A_1234,D_1231,B_1232,C_1229,F_1230,E_1233] :
      ( k4_relset_1(A_1234,B_1232,C_1229,D_1231,E_1233,F_1230) = k5_relat_1(E_1233,F_1230)
      | ~ m1_subset_1(F_1230,k1_zfmisc_1(k2_zfmisc_1(C_1229,D_1231)))
      | ~ m1_subset_1(E_1233,k1_zfmisc_1(k2_zfmisc_1(A_1234,B_1232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6617,plain,(
    ! [A_1259,B_1260,E_1261] :
      ( k4_relset_1(A_1259,B_1260,'#skF_9','#skF_10',E_1261,'#skF_12') = k5_relat_1(E_1261,'#skF_12')
      | ~ m1_subset_1(E_1261,k1_zfmisc_1(k2_zfmisc_1(A_1259,B_1260))) ) ),
    inference(resolution,[status(thm)],[c_42,c_6499])).

tff(c_6634,plain,(
    k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12') = k5_relat_1('#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_44,c_6617])).

tff(c_6642,plain,(
    r2_hidden(k4_tarski('#skF_16','#skF_17'),k5_relat_1('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6634,c_79])).

tff(c_6659,plain,(
    ! [B_1262,A_1263,D_1264,E_1265] :
      ( r2_hidden(k4_tarski('#skF_1'(B_1262,k5_relat_1(A_1263,B_1262),D_1264,E_1265,A_1263),E_1265),B_1262)
      | ~ r2_hidden(k4_tarski(D_1264,E_1265),k5_relat_1(A_1263,B_1262))
      | ~ v1_relat_1(k5_relat_1(A_1263,B_1262))
      | ~ v1_relat_1(B_1262)
      | ~ v1_relat_1(A_1263) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6680,plain,(
    ! [E_1265,D_1264,A_1263] :
      ( r2_hidden(E_1265,'#skF_10')
      | ~ r2_hidden(k4_tarski(D_1264,E_1265),k5_relat_1(A_1263,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1263,'#skF_12'))
      | ~ v1_relat_1('#skF_12')
      | ~ v1_relat_1(A_1263) ) ),
    inference(resolution,[status(thm)],[c_6659,c_787])).

tff(c_6725,plain,(
    ! [E_1266,D_1267,A_1268] :
      ( r2_hidden(E_1266,'#skF_10')
      | ~ r2_hidden(k4_tarski(D_1267,E_1266),k5_relat_1(A_1268,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1268,'#skF_12'))
      | ~ v1_relat_1(A_1268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_6680])).

tff(c_6732,plain,
    ( r2_hidden('#skF_17','#skF_10')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_6642,c_6725])).

tff(c_6739,plain,
    ( r2_hidden('#skF_17','#skF_10')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_6732])).

tff(c_6741,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_6739])).

tff(c_6744,plain,
    ( ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_22,c_6741])).

tff(c_6748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_92,c_6744])).

tff(c_6750,plain,(
    v1_relat_1(k5_relat_1('#skF_11','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_6739])).

tff(c_788,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_6514,plain,(
    ! [A_1235,C_1236,D_1237,B_1238] :
      ( r2_hidden(A_1235,C_1236)
      | v1_xboole_0(k2_zfmisc_1(C_1236,D_1237))
      | ~ m1_subset_1(k4_tarski(A_1235,B_1238),k2_zfmisc_1(C_1236,D_1237)) ) ),
    inference(resolution,[status(thm)],[c_36,c_96])).

tff(c_6525,plain,(
    ! [A_1235,B_1238] :
      ( r2_hidden(A_1235,'#skF_9')
      | v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(k4_tarski(A_1235,B_1238),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_109,c_6514])).

tff(c_6532,plain,(
    ! [A_1235,B_1238] :
      ( r2_hidden(A_1235,'#skF_9')
      | ~ r2_hidden(k4_tarski(A_1235,B_1238),'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_788,c_6525])).

tff(c_6669,plain,(
    ! [A_1263,D_1264,E_1265] :
      ( r2_hidden('#skF_1'('#skF_12',k5_relat_1(A_1263,'#skF_12'),D_1264,E_1265,A_1263),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_1264,E_1265),k5_relat_1(A_1263,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1263,'#skF_12'))
      | ~ v1_relat_1('#skF_12')
      | ~ v1_relat_1(A_1263) ) ),
    inference(resolution,[status(thm)],[c_6659,c_6532])).

tff(c_8829,plain,(
    ! [A_1520,D_1521,E_1522] :
      ( r2_hidden('#skF_1'('#skF_12',k5_relat_1(A_1520,'#skF_12'),D_1521,E_1522,A_1520),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_1521,E_1522),k5_relat_1(A_1520,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1520,'#skF_12'))
      | ~ v1_relat_1(A_1520) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_6669])).

tff(c_8966,plain,(
    ! [A_1537,D_1538,E_1539] :
      ( m1_subset_1('#skF_1'('#skF_12',k5_relat_1(A_1537,'#skF_12'),D_1538,E_1539,A_1537),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_1538,E_1539),k5_relat_1(A_1537,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1537,'#skF_12'))
      | ~ v1_relat_1(A_1537) ) ),
    inference(resolution,[status(thm)],[c_8829,c_34])).

tff(c_9003,plain,
    ( m1_subset_1('#skF_1'('#skF_12',k5_relat_1('#skF_11','#skF_12'),'#skF_16','#skF_17','#skF_11'),'#skF_9')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_6642,c_8966])).

tff(c_9021,plain,(
    m1_subset_1('#skF_1'('#skF_12',k5_relat_1('#skF_11','#skF_12'),'#skF_16','#skF_17','#skF_11'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_6750,c_9003])).

tff(c_56,plain,(
    ! [H_340] :
      ( r2_hidden(k4_tarski('#skF_13','#skF_15'),'#skF_11')
      | ~ r2_hidden(k4_tarski(H_340,'#skF_17'),'#skF_12')
      | ~ r2_hidden(k4_tarski('#skF_16',H_340),'#skF_11')
      | ~ m1_subset_1(H_340,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_6467,plain,(
    ! [H_340] :
      ( ~ r2_hidden(k4_tarski(H_340,'#skF_17'),'#skF_12')
      | ~ r2_hidden(k4_tarski('#skF_16',H_340),'#skF_11')
      | ~ m1_subset_1(H_340,'#skF_9') ) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_6676,plain,(
    ! [A_1263,D_1264] :
      ( ~ r2_hidden(k4_tarski('#skF_16','#skF_1'('#skF_12',k5_relat_1(A_1263,'#skF_12'),D_1264,'#skF_17',A_1263)),'#skF_11')
      | ~ m1_subset_1('#skF_1'('#skF_12',k5_relat_1(A_1263,'#skF_12'),D_1264,'#skF_17',A_1263),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_1264,'#skF_17'),k5_relat_1(A_1263,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1263,'#skF_12'))
      | ~ v1_relat_1('#skF_12')
      | ~ v1_relat_1(A_1263) ) ),
    inference(resolution,[status(thm)],[c_6659,c_6467])).

tff(c_12419,plain,(
    ! [A_1849,D_1850] :
      ( ~ r2_hidden(k4_tarski('#skF_16','#skF_1'('#skF_12',k5_relat_1(A_1849,'#skF_12'),D_1850,'#skF_17',A_1849)),'#skF_11')
      | ~ m1_subset_1('#skF_1'('#skF_12',k5_relat_1(A_1849,'#skF_12'),D_1850,'#skF_17',A_1849),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_1850,'#skF_17'),k5_relat_1(A_1849,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1849,'#skF_12'))
      | ~ v1_relat_1(A_1849) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_6676])).

tff(c_12423,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_12',k5_relat_1('#skF_11','#skF_12'),'#skF_16','#skF_17','#skF_11'),'#skF_9')
    | ~ r2_hidden(k4_tarski('#skF_16','#skF_17'),k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_20,c_12419])).

tff(c_12430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_92,c_6750,c_6642,c_9021,c_12423])).

tff(c_12431,plain,(
    r2_hidden(k4_tarski('#skF_13','#skF_15'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4098,plain,(
    ! [E_942,C_938,A_943,B_941,F_939,D_940] :
      ( k4_relset_1(A_943,B_941,C_938,D_940,E_942,F_939) = k5_relat_1(E_942,F_939)
      | ~ m1_subset_1(F_939,k1_zfmisc_1(k2_zfmisc_1(C_938,D_940)))
      | ~ m1_subset_1(E_942,k1_zfmisc_1(k2_zfmisc_1(A_943,B_941))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4141,plain,(
    ! [A_949,B_950,E_951] :
      ( k4_relset_1(A_949,B_950,'#skF_9','#skF_10',E_951,'#skF_12') = k5_relat_1(E_951,'#skF_12')
      | ~ m1_subset_1(E_951,k1_zfmisc_1(k2_zfmisc_1(A_949,B_950))) ) ),
    inference(resolution,[status(thm)],[c_42,c_4098])).

tff(c_4158,plain,(
    k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12') = k5_relat_1('#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_44,c_4141])).

tff(c_4166,plain,(
    r2_hidden(k4_tarski('#skF_16','#skF_17'),k5_relat_1('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4158,c_79])).

tff(c_4303,plain,(
    ! [D_972,B_973,A_974,E_975] :
      ( r2_hidden(k4_tarski(D_972,'#skF_1'(B_973,k5_relat_1(A_974,B_973),D_972,E_975,A_974)),A_974)
      | ~ r2_hidden(k4_tarski(D_972,E_975),k5_relat_1(A_974,B_973))
      | ~ v1_relat_1(k5_relat_1(A_974,B_973))
      | ~ v1_relat_1(B_973)
      | ~ v1_relat_1(A_974) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4056,plain,(
    ! [A_924,C_925,D_926,B_927] :
      ( r2_hidden(A_924,C_925)
      | v1_xboole_0(k2_zfmisc_1(C_925,D_926))
      | ~ m1_subset_1(k4_tarski(A_924,B_927),k2_zfmisc_1(C_925,D_926)) ) ),
    inference(resolution,[status(thm)],[c_36,c_96])).

tff(c_4063,plain,(
    ! [A_924,B_927] :
      ( r2_hidden(A_924,'#skF_8')
      | v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(k4_tarski(A_924,B_927),'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_110,c_4056])).

tff(c_4071,plain,(
    ! [A_924,B_927] :
      ( r2_hidden(A_924,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_924,B_927),'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_4063])).

tff(c_4321,plain,(
    ! [D_972,E_975,B_973] :
      ( r2_hidden(D_972,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_972,E_975),k5_relat_1('#skF_11',B_973))
      | ~ v1_relat_1(k5_relat_1('#skF_11',B_973))
      | ~ v1_relat_1(B_973)
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_4303,c_4071])).

tff(c_4385,plain,(
    ! [D_979,E_980,B_981] :
      ( r2_hidden(D_979,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_979,E_980),k5_relat_1('#skF_11',B_981))
      | ~ v1_relat_1(k5_relat_1('#skF_11',B_981))
      | ~ v1_relat_1(B_981) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_4321])).

tff(c_4392,plain,
    ( r2_hidden('#skF_16','#skF_8')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_4166,c_4385])).

tff(c_4399,plain,
    ( r2_hidden('#skF_16','#skF_8')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_4392])).

tff(c_4401,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_4399])).

tff(c_4413,plain,
    ( ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_22,c_4401])).

tff(c_4417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_92,c_4413])).

tff(c_4419,plain,(
    v1_relat_1(k5_relat_1('#skF_11','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_4399])).

tff(c_4444,plain,(
    ! [B_988,A_989,D_990,E_991] :
      ( r2_hidden(k4_tarski('#skF_1'(B_988,k5_relat_1(A_989,B_988),D_990,E_991,A_989),E_991),B_988)
      | ~ r2_hidden(k4_tarski(D_990,E_991),k5_relat_1(A_989,B_988))
      | ~ v1_relat_1(k5_relat_1(A_989,B_988))
      | ~ v1_relat_1(B_988)
      | ~ v1_relat_1(A_989) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_54,plain,(
    ! [H_340] :
      ( r2_hidden(k4_tarski('#skF_15','#skF_14'),'#skF_12')
      | ~ r2_hidden(k4_tarski(H_340,'#skF_17'),'#skF_12')
      | ~ r2_hidden(k4_tarski('#skF_16',H_340),'#skF_11')
      | ~ m1_subset_1(H_340,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3516,plain,(
    ! [H_340] :
      ( ~ r2_hidden(k4_tarski(H_340,'#skF_17'),'#skF_12')
      | ~ r2_hidden(k4_tarski('#skF_16',H_340),'#skF_11')
      | ~ m1_subset_1(H_340,'#skF_9') ) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_4477,plain,(
    ! [A_989,D_990] :
      ( ~ r2_hidden(k4_tarski('#skF_16','#skF_1'('#skF_12',k5_relat_1(A_989,'#skF_12'),D_990,'#skF_17',A_989)),'#skF_11')
      | ~ m1_subset_1('#skF_1'('#skF_12',k5_relat_1(A_989,'#skF_12'),D_990,'#skF_17',A_989),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_990,'#skF_17'),k5_relat_1(A_989,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_989,'#skF_12'))
      | ~ v1_relat_1('#skF_12')
      | ~ v1_relat_1(A_989) ) ),
    inference(resolution,[status(thm)],[c_4444,c_3516])).

tff(c_5844,plain,(
    ! [A_1180,D_1181] :
      ( ~ r2_hidden(k4_tarski('#skF_16','#skF_1'('#skF_12',k5_relat_1(A_1180,'#skF_12'),D_1181,'#skF_17',A_1180)),'#skF_11')
      | ~ m1_subset_1('#skF_1'('#skF_12',k5_relat_1(A_1180,'#skF_12'),D_1181,'#skF_17',A_1180),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_1181,'#skF_17'),k5_relat_1(A_1180,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1180,'#skF_12'))
      | ~ v1_relat_1(A_1180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_4477])).

tff(c_5848,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_12',k5_relat_1('#skF_11','#skF_12'),'#skF_16','#skF_17','#skF_11'),'#skF_9')
    | ~ r2_hidden(k4_tarski('#skF_16','#skF_17'),k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_20,c_5844])).

tff(c_5854,plain,(
    ~ m1_subset_1('#skF_1'('#skF_12',k5_relat_1('#skF_11','#skF_12'),'#skF_16','#skF_17','#skF_11'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_92,c_4419,c_4166,c_5848])).

tff(c_4067,plain,(
    ! [A_924,B_927] :
      ( r2_hidden(A_924,'#skF_9')
      | v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(k4_tarski(A_924,B_927),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_109,c_4056])).

tff(c_4074,plain,(
    ! [A_924,B_927] :
      ( r2_hidden(A_924,'#skF_9')
      | ~ r2_hidden(k4_tarski(A_924,B_927),'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_788,c_4067])).

tff(c_4470,plain,(
    ! [A_989,D_990,E_991] :
      ( r2_hidden('#skF_1'('#skF_12',k5_relat_1(A_989,'#skF_12'),D_990,E_991,A_989),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_990,E_991),k5_relat_1(A_989,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_989,'#skF_12'))
      | ~ v1_relat_1('#skF_12')
      | ~ v1_relat_1(A_989) ) ),
    inference(resolution,[status(thm)],[c_4444,c_4074])).

tff(c_6354,plain,(
    ! [A_1205,D_1206,E_1207] :
      ( r2_hidden('#skF_1'('#skF_12',k5_relat_1(A_1205,'#skF_12'),D_1206,E_1207,A_1205),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_1206,E_1207),k5_relat_1(A_1205,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1205,'#skF_12'))
      | ~ v1_relat_1(A_1205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_4470])).

tff(c_6399,plain,(
    ! [A_1221,D_1222,E_1223] :
      ( m1_subset_1('#skF_1'('#skF_12',k5_relat_1(A_1221,'#skF_12'),D_1222,E_1223,A_1221),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_1222,E_1223),k5_relat_1(A_1221,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1221,'#skF_12'))
      | ~ v1_relat_1(A_1221) ) ),
    inference(resolution,[status(thm)],[c_6354,c_34])).

tff(c_6434,plain,
    ( m1_subset_1('#skF_1'('#skF_12',k5_relat_1('#skF_11','#skF_12'),'#skF_16','#skF_17','#skF_11'),'#skF_9')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_4166,c_6399])).

tff(c_6451,plain,(
    m1_subset_1('#skF_1'('#skF_12',k5_relat_1('#skF_11','#skF_12'),'#skF_16','#skF_17','#skF_11'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_4419,c_6434])).

tff(c_6453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5854,c_6451])).

tff(c_6454,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_14'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_12558,plain,(
    ! [E_1874,D_1873,B_1871,A_1875,F_1872] :
      ( r2_hidden(k4_tarski(D_1873,E_1874),k5_relat_1(A_1875,B_1871))
      | ~ r2_hidden(k4_tarski(F_1872,E_1874),B_1871)
      | ~ r2_hidden(k4_tarski(D_1873,F_1872),A_1875)
      | ~ v1_relat_1(k5_relat_1(A_1875,B_1871))
      | ~ v1_relat_1(B_1871)
      | ~ v1_relat_1(A_1875) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12562,plain,(
    ! [D_1873,A_1875] :
      ( r2_hidden(k4_tarski(D_1873,'#skF_14'),k5_relat_1(A_1875,'#skF_12'))
      | ~ r2_hidden(k4_tarski(D_1873,'#skF_15'),A_1875)
      | ~ v1_relat_1(k5_relat_1(A_1875,'#skF_12'))
      | ~ v1_relat_1('#skF_12')
      | ~ v1_relat_1(A_1875) ) ),
    inference(resolution,[status(thm)],[c_6454,c_12558])).

tff(c_12857,plain,(
    ! [D_1906,A_1907] :
      ( r2_hidden(k4_tarski(D_1906,'#skF_14'),k5_relat_1(A_1907,'#skF_12'))
      | ~ r2_hidden(k4_tarski(D_1906,'#skF_15'),A_1907)
      | ~ v1_relat_1(k5_relat_1(A_1907,'#skF_12'))
      | ~ v1_relat_1(A_1907) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_12562])).

tff(c_52,plain,(
    ! [H_340] :
      ( ~ r2_hidden(k4_tarski('#skF_13','#skF_14'),k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12'))
      | ~ r2_hidden(k4_tarski(H_340,'#skF_17'),'#skF_12')
      | ~ r2_hidden(k4_tarski('#skF_16',H_340),'#skF_11')
      | ~ m1_subset_1(H_340,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_12527,plain,(
    ~ r2_hidden(k4_tarski('#skF_13','#skF_14'),k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_12637,plain,(
    ~ r2_hidden(k4_tarski('#skF_13','#skF_14'),k5_relat_1('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12630,c_12527])).

tff(c_12871,plain,
    ( ~ r2_hidden(k4_tarski('#skF_13','#skF_15'),'#skF_11')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_12857,c_12637])).

tff(c_12892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_12813,c_12431,c_12871])).

tff(c_12893,plain,(
    ! [H_340] :
      ( ~ r2_hidden(k4_tarski(H_340,'#skF_17'),'#skF_12')
      | ~ r2_hidden(k4_tarski('#skF_16',H_340),'#skF_11')
      | ~ m1_subset_1(H_340,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_13055,plain,(
    ! [A_1933,D_1934] :
      ( ~ r2_hidden(k4_tarski('#skF_16','#skF_1'('#skF_12',k5_relat_1(A_1933,'#skF_12'),D_1934,'#skF_17',A_1933)),'#skF_11')
      | ~ m1_subset_1('#skF_1'('#skF_12',k5_relat_1(A_1933,'#skF_12'),D_1934,'#skF_17',A_1933),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_1934,'#skF_17'),k5_relat_1(A_1933,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_1933,'#skF_12'))
      | ~ v1_relat_1('#skF_12')
      | ~ v1_relat_1(A_1933) ) ),
    inference(resolution,[status(thm)],[c_13046,c_12893])).

tff(c_19297,plain,(
    ! [A_2530,D_2531] :
      ( ~ r2_hidden(k4_tarski('#skF_16','#skF_1'('#skF_12',k5_relat_1(A_2530,'#skF_12'),D_2531,'#skF_17',A_2530)),'#skF_11')
      | ~ m1_subset_1('#skF_1'('#skF_12',k5_relat_1(A_2530,'#skF_12'),D_2531,'#skF_17',A_2530),'#skF_9')
      | ~ r2_hidden(k4_tarski(D_2531,'#skF_17'),k5_relat_1(A_2530,'#skF_12'))
      | ~ v1_relat_1(k5_relat_1(A_2530,'#skF_12'))
      | ~ v1_relat_1(A_2530) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_13055])).

tff(c_19301,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_12',k5_relat_1('#skF_11','#skF_12'),'#skF_16','#skF_17','#skF_11'),'#skF_9')
    | ~ r2_hidden(k4_tarski('#skF_16','#skF_17'),k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_20,c_19297])).

tff(c_19308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_92,c_13163,c_13000,c_15679,c_19301])).

tff(c_19310,plain,(
    ~ r2_hidden(k4_tarski('#skF_16','#skF_17'),k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,
    ( r2_hidden(k4_tarski('#skF_13','#skF_15'),'#skF_11')
    | r2_hidden(k4_tarski('#skF_16','#skF_17'),k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_19325,plain,(
    r2_hidden(k4_tarski('#skF_16','#skF_17'),k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_19362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19310,c_19325])).

tff(c_19363,plain,(
    r2_hidden(k4_tarski('#skF_13','#skF_15'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_19364,plain,(
    ~ r2_hidden(k4_tarski('#skF_16','#skF_17'),k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,
    ( r2_hidden(k4_tarski('#skF_15','#skF_14'),'#skF_12')
    | r2_hidden(k4_tarski('#skF_16','#skF_17'),k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_19430,plain,(
    r2_hidden(k4_tarski('#skF_15','#skF_14'),'#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_19364,c_62])).

tff(c_19704,plain,(
    ! [A_2636,D_2634,B_2632,F_2633,E_2635] :
      ( r2_hidden(k4_tarski(D_2634,E_2635),k5_relat_1(A_2636,B_2632))
      | ~ r2_hidden(k4_tarski(F_2633,E_2635),B_2632)
      | ~ r2_hidden(k4_tarski(D_2634,F_2633),A_2636)
      | ~ v1_relat_1(k5_relat_1(A_2636,B_2632))
      | ~ v1_relat_1(B_2632)
      | ~ v1_relat_1(A_2636) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19708,plain,(
    ! [D_2634,A_2636] :
      ( r2_hidden(k4_tarski(D_2634,'#skF_14'),k5_relat_1(A_2636,'#skF_12'))
      | ~ r2_hidden(k4_tarski(D_2634,'#skF_15'),A_2636)
      | ~ v1_relat_1(k5_relat_1(A_2636,'#skF_12'))
      | ~ v1_relat_1('#skF_12')
      | ~ v1_relat_1(A_2636) ) ),
    inference(resolution,[status(thm)],[c_19430,c_19704])).

tff(c_20096,plain,(
    ! [D_2683,A_2684] :
      ( r2_hidden(k4_tarski(D_2683,'#skF_14'),k5_relat_1(A_2684,'#skF_12'))
      | ~ r2_hidden(k4_tarski(D_2683,'#skF_15'),A_2684)
      | ~ v1_relat_1(k5_relat_1(A_2684,'#skF_12'))
      | ~ v1_relat_1(A_2684) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19322,c_19708])).

tff(c_19621,plain,(
    ! [E_2616,A_2617,F_2613,B_2615,C_2612,D_2614] :
      ( k4_relset_1(A_2617,B_2615,C_2612,D_2614,E_2616,F_2613) = k5_relat_1(E_2616,F_2613)
      | ~ m1_subset_1(F_2613,k1_zfmisc_1(k2_zfmisc_1(C_2612,D_2614)))
      | ~ m1_subset_1(E_2616,k1_zfmisc_1(k2_zfmisc_1(A_2617,B_2615))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_19750,plain,(
    ! [A_2642,B_2643,E_2644] :
      ( k4_relset_1(A_2642,B_2643,'#skF_9','#skF_10',E_2644,'#skF_12') = k5_relat_1(E_2644,'#skF_12')
      | ~ m1_subset_1(E_2644,k1_zfmisc_1(k2_zfmisc_1(A_2642,B_2643))) ) ),
    inference(resolution,[status(thm)],[c_42,c_19621])).

tff(c_19767,plain,(
    k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12') = k5_relat_1('#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_44,c_19750])).

tff(c_60,plain,
    ( ~ r2_hidden(k4_tarski('#skF_13','#skF_14'),k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12'))
    | r2_hidden(k4_tarski('#skF_16','#skF_17'),k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_19532,plain,(
    ~ r2_hidden(k4_tarski('#skF_13','#skF_14'),k4_relset_1('#skF_8','#skF_9','#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_19364,c_60])).

tff(c_19773,plain,(
    ~ r2_hidden(k4_tarski('#skF_13','#skF_14'),k5_relat_1('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19767,c_19532])).

tff(c_20116,plain,
    ( ~ r2_hidden(k4_tarski('#skF_13','#skF_15'),'#skF_11')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_20096,c_19773])).

tff(c_20141,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_11','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19323,c_19363,c_20116])).

tff(c_20147,plain,
    ( ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_22,c_20141])).

tff(c_20151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19323,c_19322,c_20147])).

%------------------------------------------------------------------------------
