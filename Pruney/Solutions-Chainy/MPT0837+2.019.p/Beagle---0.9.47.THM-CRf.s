%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:07 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 246 expanded)
%              Number of leaves         :   37 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  164 ( 541 expanded)
%              Number of equality atoms :   11 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1092,plain,(
    ! [A_232,B_233,C_234] :
      ( k2_relset_1(A_232,B_233,C_234) = k2_relat_1(C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1096,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_1092])).

tff(c_54,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_73,plain,(
    r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_1103,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_73])).

tff(c_20,plain,(
    ! [A_29,B_30] : v1_relat_1(k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    ! [B_94,A_95] :
      ( v1_relat_1(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_95))
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_69,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_38,c_66])).

tff(c_72,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_69])).

tff(c_30,plain,(
    ! [A_37] :
      ( k9_relat_1(A_37,k1_relat_1(A_37)) = k2_relat_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1087,plain,(
    ! [A_229,B_230,C_231] :
      ( k1_relset_1(A_229,B_230,C_231) = k1_relat_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1091,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_1087])).

tff(c_2090,plain,(
    ! [A_357,B_358,C_359] :
      ( m1_subset_1(k1_relset_1(A_357,B_358,C_359),k1_zfmisc_1(A_357))
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(A_357,B_358))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2106,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_2090])).

tff(c_2112,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2106])).

tff(c_2201,plain,(
    ! [A_370,B_371,C_372] :
      ( r2_hidden('#skF_5'(A_370,B_371,C_372),k1_relat_1(C_372))
      | ~ r2_hidden(A_370,k9_relat_1(C_372,B_371))
      | ~ v1_relat_1(C_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3164,plain,(
    ! [A_469,B_470,C_471,A_472] :
      ( r2_hidden('#skF_5'(A_469,B_470,C_471),A_472)
      | ~ m1_subset_1(k1_relat_1(C_471),k1_zfmisc_1(A_472))
      | ~ r2_hidden(A_469,k9_relat_1(C_471,B_470))
      | ~ v1_relat_1(C_471) ) ),
    inference(resolution,[status(thm)],[c_2201,c_2])).

tff(c_3166,plain,(
    ! [A_469,B_470] :
      ( r2_hidden('#skF_5'(A_469,B_470,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_469,k9_relat_1('#skF_8',B_470))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2112,c_3164])).

tff(c_3170,plain,(
    ! [A_473,B_474] :
      ( r2_hidden('#skF_5'(A_473,B_474,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_473,k9_relat_1('#skF_8',B_474)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3166])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3181,plain,(
    ! [A_475,B_476] :
      ( m1_subset_1('#skF_5'(A_475,B_476,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_475,k9_relat_1('#skF_8',B_476)) ) ),
    inference(resolution,[status(thm)],[c_3170,c_4])).

tff(c_3229,plain,(
    ! [A_475] :
      ( m1_subset_1('#skF_5'(A_475,k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_475,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3181])).

tff(c_3246,plain,(
    ! [A_478] :
      ( m1_subset_1('#skF_5'(A_478,k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_478,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3229])).

tff(c_2211,plain,(
    ! [A_378,B_379,C_380] :
      ( r2_hidden(k4_tarski('#skF_5'(A_378,B_379,C_380),A_378),C_380)
      | ~ r2_hidden(A_378,k9_relat_1(C_380,B_379))
      | ~ v1_relat_1(C_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ! [E_88] :
      ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(E_88,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_88,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1970,plain,(
    ! [E_88] :
      ( ~ r2_hidden('#skF_9',k2_relat_1('#skF_8'))
      | ~ r2_hidden(k4_tarski(E_88,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_88,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1096,c_44])).

tff(c_1971,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1970])).

tff(c_1154,plain,(
    ! [A_244,B_245,C_246] :
      ( m1_subset_1(k1_relset_1(A_244,B_245,C_246),k1_zfmisc_1(A_244))
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1168,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_1154])).

tff(c_1173,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1168])).

tff(c_1192,plain,(
    ! [A_252,B_253,C_254] :
      ( r2_hidden('#skF_5'(A_252,B_253,C_254),k1_relat_1(C_254))
      | ~ r2_hidden(A_252,k9_relat_1(C_254,B_253))
      | ~ v1_relat_1(C_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1887,plain,(
    ! [A_331,B_332,C_333,A_334] :
      ( r2_hidden('#skF_5'(A_331,B_332,C_333),A_334)
      | ~ m1_subset_1(k1_relat_1(C_333),k1_zfmisc_1(A_334))
      | ~ r2_hidden(A_331,k9_relat_1(C_333,B_332))
      | ~ v1_relat_1(C_333) ) ),
    inference(resolution,[status(thm)],[c_1192,c_2])).

tff(c_1889,plain,(
    ! [A_331,B_332] :
      ( r2_hidden('#skF_5'(A_331,B_332,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_331,k9_relat_1('#skF_8',B_332))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1173,c_1887])).

tff(c_1893,plain,(
    ! [A_335,B_336] :
      ( r2_hidden('#skF_5'(A_335,B_336,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_335,k9_relat_1('#skF_8',B_336)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1889])).

tff(c_1904,plain,(
    ! [A_337,B_338] :
      ( m1_subset_1('#skF_5'(A_337,B_338,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_337,k9_relat_1('#skF_8',B_338)) ) ),
    inference(resolution,[status(thm)],[c_1893,c_4])).

tff(c_1948,plain,(
    ! [A_337] :
      ( m1_subset_1('#skF_5'(A_337,k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_337,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1904])).

tff(c_1961,plain,(
    ! [A_339] :
      ( m1_subset_1('#skF_5'(A_339,k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_339,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1948])).

tff(c_1238,plain,(
    ! [A_266,B_267,C_268] :
      ( r2_hidden(k4_tarski('#skF_5'(A_266,B_267,C_268),A_266),C_268)
      | ~ r2_hidden(A_266,k9_relat_1(C_268,B_267))
      | ~ v1_relat_1(C_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    ! [E_88] :
      ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
      | ~ r2_hidden(k4_tarski(E_88,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_88,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1108,plain,(
    ! [E_88] :
      ( ~ r2_hidden(k4_tarski(E_88,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_88,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1245,plain,(
    ! [B_267] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_267,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_267))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1238,c_1108])).

tff(c_1285,plain,(
    ! [B_272] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_272,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_272)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1245])).

tff(c_1289,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11',k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1285])).

tff(c_1291,plain,(
    ~ m1_subset_1('#skF_5'('#skF_11',k1_relat_1('#skF_8'),'#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1103,c_1289])).

tff(c_1964,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1961,c_1291])).

tff(c_1968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1103,c_1964])).

tff(c_1969,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_10,plain,(
    ! [C_25,A_10,D_28] :
      ( r2_hidden(C_25,k2_relat_1(A_10))
      | ~ r2_hidden(k4_tarski(D_28,C_25),A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1984,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1969,c_10])).

tff(c_1992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1971,c_1984])).

tff(c_1993,plain,(
    ! [E_88] :
      ( ~ r2_hidden(k4_tarski(E_88,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_88,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_1970])).

tff(c_2218,plain,(
    ! [B_379] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_379,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_379))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2211,c_1993])).

tff(c_2288,plain,(
    ! [B_386] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_386,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_386)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2218])).

tff(c_2292,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11',k1_relat_1('#skF_8'),'#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2288])).

tff(c_2294,plain,(
    ~ m1_subset_1('#skF_5'('#skF_11',k1_relat_1('#skF_8'),'#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1103,c_2292])).

tff(c_3249,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_3246,c_2294])).

tff(c_3253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1103,c_3249])).

tff(c_3255,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3258,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_3255,c_52])).

tff(c_3268,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_3258,c_10])).

tff(c_3309,plain,(
    ! [A_491,B_492,C_493] :
      ( k2_relset_1(A_491,B_492,C_493) = k2_relat_1(C_493)
      | ~ m1_subset_1(C_493,k1_zfmisc_1(k2_zfmisc_1(A_491,B_492))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3318,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_3309])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3306,plain,(
    ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_3255,c_50])).

tff(c_3320,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3318,c_3306])).

tff(c_3324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3268,c_3320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:47:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/1.99  
% 5.35/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/1.99  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 5.35/1.99  
% 5.35/1.99  %Foreground sorts:
% 5.35/1.99  
% 5.35/1.99  
% 5.35/1.99  %Background operators:
% 5.35/1.99  
% 5.35/1.99  
% 5.35/1.99  %Foreground operators:
% 5.35/1.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.35/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/1.99  tff('#skF_11', type, '#skF_11': $i).
% 5.35/1.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.35/1.99  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.35/1.99  tff('#skF_7', type, '#skF_7': $i).
% 5.35/1.99  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.35/1.99  tff('#skF_10', type, '#skF_10': $i).
% 5.35/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.35/1.99  tff('#skF_6', type, '#skF_6': $i).
% 5.35/1.99  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.35/1.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.35/1.99  tff('#skF_9', type, '#skF_9': $i).
% 5.35/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.35/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.35/1.99  tff('#skF_8', type, '#skF_8': $i).
% 5.35/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.35/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.35/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/1.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.35/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.35/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.35/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.35/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.35/1.99  
% 5.35/2.01  tff(f_99, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 5.35/2.01  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.35/2.01  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.35/2.01  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.35/2.01  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 5.35/2.01  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.35/2.01  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 5.35/2.01  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 5.35/2.01  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.35/2.01  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.35/2.01  tff(f_51, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 5.35/2.01  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.35/2.01  tff(c_1092, plain, (![A_232, B_233, C_234]: (k2_relset_1(A_232, B_233, C_234)=k2_relat_1(C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.35/2.01  tff(c_1096, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_1092])).
% 5.35/2.01  tff(c_54, plain, (m1_subset_1('#skF_10', '#skF_7') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.35/2.01  tff(c_73, plain, (r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_54])).
% 5.35/2.01  tff(c_1103, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1096, c_73])).
% 5.35/2.01  tff(c_20, plain, (![A_29, B_30]: (v1_relat_1(k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.35/2.01  tff(c_66, plain, (![B_94, A_95]: (v1_relat_1(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_95)) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.35/2.01  tff(c_69, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_66])).
% 5.35/2.01  tff(c_72, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_69])).
% 5.35/2.01  tff(c_30, plain, (![A_37]: (k9_relat_1(A_37, k1_relat_1(A_37))=k2_relat_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.35/2.01  tff(c_1087, plain, (![A_229, B_230, C_231]: (k1_relset_1(A_229, B_230, C_231)=k1_relat_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.35/2.01  tff(c_1091, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_1087])).
% 5.35/2.01  tff(c_2090, plain, (![A_357, B_358, C_359]: (m1_subset_1(k1_relset_1(A_357, B_358, C_359), k1_zfmisc_1(A_357)) | ~m1_subset_1(C_359, k1_zfmisc_1(k2_zfmisc_1(A_357, B_358))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.35/2.01  tff(c_2106, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1091, c_2090])).
% 5.35/2.01  tff(c_2112, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2106])).
% 5.35/2.01  tff(c_2201, plain, (![A_370, B_371, C_372]: (r2_hidden('#skF_5'(A_370, B_371, C_372), k1_relat_1(C_372)) | ~r2_hidden(A_370, k9_relat_1(C_372, B_371)) | ~v1_relat_1(C_372))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.35/2.01  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.01  tff(c_3164, plain, (![A_469, B_470, C_471, A_472]: (r2_hidden('#skF_5'(A_469, B_470, C_471), A_472) | ~m1_subset_1(k1_relat_1(C_471), k1_zfmisc_1(A_472)) | ~r2_hidden(A_469, k9_relat_1(C_471, B_470)) | ~v1_relat_1(C_471))), inference(resolution, [status(thm)], [c_2201, c_2])).
% 5.35/2.01  tff(c_3166, plain, (![A_469, B_470]: (r2_hidden('#skF_5'(A_469, B_470, '#skF_8'), '#skF_7') | ~r2_hidden(A_469, k9_relat_1('#skF_8', B_470)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_2112, c_3164])).
% 5.35/2.01  tff(c_3170, plain, (![A_473, B_474]: (r2_hidden('#skF_5'(A_473, B_474, '#skF_8'), '#skF_7') | ~r2_hidden(A_473, k9_relat_1('#skF_8', B_474)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3166])).
% 5.35/2.01  tff(c_4, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.35/2.01  tff(c_3181, plain, (![A_475, B_476]: (m1_subset_1('#skF_5'(A_475, B_476, '#skF_8'), '#skF_7') | ~r2_hidden(A_475, k9_relat_1('#skF_8', B_476)))), inference(resolution, [status(thm)], [c_3170, c_4])).
% 5.35/2.01  tff(c_3229, plain, (![A_475]: (m1_subset_1('#skF_5'(A_475, k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden(A_475, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_3181])).
% 5.35/2.01  tff(c_3246, plain, (![A_478]: (m1_subset_1('#skF_5'(A_478, k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden(A_478, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3229])).
% 5.35/2.01  tff(c_2211, plain, (![A_378, B_379, C_380]: (r2_hidden(k4_tarski('#skF_5'(A_378, B_379, C_380), A_378), C_380) | ~r2_hidden(A_378, k9_relat_1(C_380, B_379)) | ~v1_relat_1(C_380))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.35/2.01  tff(c_44, plain, (![E_88]: (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(E_88, '#skF_11'), '#skF_8') | ~m1_subset_1(E_88, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.35/2.01  tff(c_1970, plain, (![E_88]: (~r2_hidden('#skF_9', k2_relat_1('#skF_8')) | ~r2_hidden(k4_tarski(E_88, '#skF_11'), '#skF_8') | ~m1_subset_1(E_88, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1096, c_44])).
% 5.35/2.01  tff(c_1971, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_1970])).
% 5.35/2.01  tff(c_1154, plain, (![A_244, B_245, C_246]: (m1_subset_1(k1_relset_1(A_244, B_245, C_246), k1_zfmisc_1(A_244)) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.35/2.01  tff(c_1168, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1091, c_1154])).
% 5.35/2.01  tff(c_1173, plain, (m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1168])).
% 5.35/2.01  tff(c_1192, plain, (![A_252, B_253, C_254]: (r2_hidden('#skF_5'(A_252, B_253, C_254), k1_relat_1(C_254)) | ~r2_hidden(A_252, k9_relat_1(C_254, B_253)) | ~v1_relat_1(C_254))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.35/2.01  tff(c_1887, plain, (![A_331, B_332, C_333, A_334]: (r2_hidden('#skF_5'(A_331, B_332, C_333), A_334) | ~m1_subset_1(k1_relat_1(C_333), k1_zfmisc_1(A_334)) | ~r2_hidden(A_331, k9_relat_1(C_333, B_332)) | ~v1_relat_1(C_333))), inference(resolution, [status(thm)], [c_1192, c_2])).
% 5.35/2.01  tff(c_1889, plain, (![A_331, B_332]: (r2_hidden('#skF_5'(A_331, B_332, '#skF_8'), '#skF_7') | ~r2_hidden(A_331, k9_relat_1('#skF_8', B_332)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1173, c_1887])).
% 5.35/2.01  tff(c_1893, plain, (![A_335, B_336]: (r2_hidden('#skF_5'(A_335, B_336, '#skF_8'), '#skF_7') | ~r2_hidden(A_335, k9_relat_1('#skF_8', B_336)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1889])).
% 5.35/2.01  tff(c_1904, plain, (![A_337, B_338]: (m1_subset_1('#skF_5'(A_337, B_338, '#skF_8'), '#skF_7') | ~r2_hidden(A_337, k9_relat_1('#skF_8', B_338)))), inference(resolution, [status(thm)], [c_1893, c_4])).
% 5.35/2.01  tff(c_1948, plain, (![A_337]: (m1_subset_1('#skF_5'(A_337, k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden(A_337, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1904])).
% 5.35/2.01  tff(c_1961, plain, (![A_339]: (m1_subset_1('#skF_5'(A_339, k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden(A_339, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1948])).
% 5.35/2.01  tff(c_1238, plain, (![A_266, B_267, C_268]: (r2_hidden(k4_tarski('#skF_5'(A_266, B_267, C_268), A_266), C_268) | ~r2_hidden(A_266, k9_relat_1(C_268, B_267)) | ~v1_relat_1(C_268))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.35/2.01  tff(c_46, plain, (![E_88]: (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden(k4_tarski(E_88, '#skF_11'), '#skF_8') | ~m1_subset_1(E_88, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.35/2.01  tff(c_1108, plain, (![E_88]: (~r2_hidden(k4_tarski(E_88, '#skF_11'), '#skF_8') | ~m1_subset_1(E_88, '#skF_7'))), inference(splitLeft, [status(thm)], [c_46])).
% 5.35/2.01  tff(c_1245, plain, (![B_267]: (~m1_subset_1('#skF_5'('#skF_11', B_267, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_267)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1238, c_1108])).
% 5.35/2.01  tff(c_1285, plain, (![B_272]: (~m1_subset_1('#skF_5'('#skF_11', B_272, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_272)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1245])).
% 5.35/2.01  tff(c_1289, plain, (~m1_subset_1('#skF_5'('#skF_11', k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1285])).
% 5.35/2.01  tff(c_1291, plain, (~m1_subset_1('#skF_5'('#skF_11', k1_relat_1('#skF_8'), '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1103, c_1289])).
% 5.35/2.01  tff(c_1964, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1961, c_1291])).
% 5.35/2.01  tff(c_1968, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1103, c_1964])).
% 5.35/2.01  tff(c_1969, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_46])).
% 5.35/2.01  tff(c_10, plain, (![C_25, A_10, D_28]: (r2_hidden(C_25, k2_relat_1(A_10)) | ~r2_hidden(k4_tarski(D_28, C_25), A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.35/2.01  tff(c_1984, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1969, c_10])).
% 5.35/2.01  tff(c_1992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1971, c_1984])).
% 5.35/2.01  tff(c_1993, plain, (![E_88]: (~r2_hidden(k4_tarski(E_88, '#skF_11'), '#skF_8') | ~m1_subset_1(E_88, '#skF_7'))), inference(splitRight, [status(thm)], [c_1970])).
% 5.35/2.01  tff(c_2218, plain, (![B_379]: (~m1_subset_1('#skF_5'('#skF_11', B_379, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_379)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_2211, c_1993])).
% 5.35/2.01  tff(c_2288, plain, (![B_386]: (~m1_subset_1('#skF_5'('#skF_11', B_386, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_386)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2218])).
% 5.35/2.01  tff(c_2292, plain, (~m1_subset_1('#skF_5'('#skF_11', k1_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_30, c_2288])).
% 5.35/2.01  tff(c_2294, plain, (~m1_subset_1('#skF_5'('#skF_11', k1_relat_1('#skF_8'), '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1103, c_2292])).
% 5.35/2.01  tff(c_3249, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_3246, c_2294])).
% 5.35/2.01  tff(c_3253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1103, c_3249])).
% 5.35/2.01  tff(c_3255, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_54])).
% 5.35/2.01  tff(c_52, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.35/2.01  tff(c_3258, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_3255, c_52])).
% 5.35/2.01  tff(c_3268, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_3258, c_10])).
% 5.35/2.01  tff(c_3309, plain, (![A_491, B_492, C_493]: (k2_relset_1(A_491, B_492, C_493)=k2_relat_1(C_493) | ~m1_subset_1(C_493, k1_zfmisc_1(k2_zfmisc_1(A_491, B_492))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.35/2.01  tff(c_3318, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_3309])).
% 5.35/2.01  tff(c_50, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.35/2.01  tff(c_3306, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_3255, c_50])).
% 5.35/2.01  tff(c_3320, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3318, c_3306])).
% 5.35/2.01  tff(c_3324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3268, c_3320])).
% 5.35/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.01  
% 5.35/2.01  Inference rules
% 5.35/2.01  ----------------------
% 5.35/2.01  #Ref     : 0
% 5.35/2.01  #Sup     : 722
% 5.35/2.01  #Fact    : 0
% 5.35/2.01  #Define  : 0
% 5.35/2.01  #Split   : 22
% 5.35/2.01  #Chain   : 0
% 5.35/2.01  #Close   : 0
% 5.35/2.01  
% 5.35/2.01  Ordering : KBO
% 5.35/2.01  
% 5.35/2.01  Simplification rules
% 5.35/2.01  ----------------------
% 5.35/2.01  #Subsume      : 19
% 5.35/2.01  #Demod        : 55
% 5.35/2.01  #Tautology    : 38
% 5.35/2.01  #SimpNegUnit  : 3
% 5.35/2.01  #BackRed      : 8
% 5.35/2.01  
% 5.35/2.01  #Partial instantiations: 0
% 5.35/2.01  #Strategies tried      : 1
% 5.35/2.01  
% 5.35/2.01  Timing (in seconds)
% 5.35/2.01  ----------------------
% 5.35/2.01  Preprocessing        : 0.33
% 5.35/2.01  Parsing              : 0.17
% 5.35/2.01  CNF conversion       : 0.03
% 5.35/2.01  Main loop            : 0.90
% 5.35/2.01  Inferencing          : 0.35
% 5.35/2.01  Reduction            : 0.24
% 5.35/2.01  Demodulation         : 0.16
% 5.35/2.01  BG Simplification    : 0.04
% 5.35/2.01  Subsumption          : 0.18
% 5.35/2.01  Abstraction          : 0.05
% 5.35/2.01  MUC search           : 0.00
% 5.35/2.01  Cooper               : 0.00
% 5.35/2.01  Total                : 1.27
% 5.35/2.01  Index Insertion      : 0.00
% 5.35/2.01  Index Deletion       : 0.00
% 5.35/2.01  Index Matching       : 0.00
% 5.35/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
