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
% DateTime   : Thu Dec  3 10:08:34 EST 2020

% Result     : Theorem 18.63s
% Output     : CNFRefutation 18.63s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 436 expanded)
%              Number of leaves         :   42 ( 163 expanded)
%              Depth                    :   10
%              Number of atoms          :  345 (1202 expanded)
%              Number of equality atoms :   48 ( 108 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(F,E),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_26,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_41153,plain,(
    ! [B_37113,A_37114] :
      ( v1_relat_1(B_37113)
      | ~ m1_subset_1(B_37113,k1_zfmisc_1(A_37114))
      | ~ v1_relat_1(A_37114) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_41163,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_41153])).

tff(c_41168,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_41163])).

tff(c_41752,plain,(
    ! [A_37198,B_37199,C_37200,D_37201] :
      ( k7_relset_1(A_37198,B_37199,C_37200,D_37201) = k9_relat_1(C_37200,D_37201)
      | ~ m1_subset_1(C_37200,k1_zfmisc_1(k2_zfmisc_1(A_37198,B_37199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_41775,plain,(
    ! [D_37201] : k7_relset_1('#skF_6','#skF_4','#skF_7',D_37201) = k9_relat_1('#skF_7',D_37201) ),
    inference(resolution,[status(thm)],[c_52,c_41752])).

tff(c_158,plain,(
    ! [B_153,A_154] :
      ( v1_relat_1(B_153)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_154))
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_168,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_158])).

tff(c_173,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_168])).

tff(c_19930,plain,(
    ! [A_1403,B_1404,C_1405,D_1406] :
      ( k7_relset_1(A_1403,B_1404,C_1405,D_1406) = k9_relat_1(C_1405,D_1406)
      | ~ m1_subset_1(C_1405,k1_zfmisc_1(k2_zfmisc_1(A_1403,B_1404))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_19953,plain,(
    ! [D_1406] : k7_relset_1('#skF_6','#skF_4','#skF_7',D_1406) = k9_relat_1('#skF_7',D_1406) ),
    inference(resolution,[status(thm)],[c_52,c_19930])).

tff(c_2356,plain,(
    ! [A_377,B_378,C_379,D_380] :
      ( k7_relset_1(A_377,B_378,C_379,D_380) = k9_relat_1(C_379,D_380)
      | ~ m1_subset_1(C_379,k1_zfmisc_1(k2_zfmisc_1(A_377,B_378))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2379,plain,(
    ! [D_380] : k7_relset_1('#skF_6','#skF_4','#skF_7',D_380) = k9_relat_1('#skF_7',D_380) ),
    inference(resolution,[status(thm)],[c_52,c_2356])).

tff(c_181,plain,(
    ! [A_157,B_158] :
      ( r2_hidden('#skF_2'(A_157,B_158),A_157)
      | r1_tarski(A_157,B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_196,plain,(
    ! [A_157] : r1_tarski(A_157,A_157) ),
    inference(resolution,[status(thm)],[c_181,c_8])).

tff(c_74,plain,
    ( r2_hidden('#skF_8',k7_relset_1('#skF_6','#skF_4','#skF_7','#skF_5'))
    | m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_199,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_66,plain,
    ( r2_hidden('#skF_8',k7_relset_1('#skF_6','#skF_4','#skF_7','#skF_5'))
    | r2_hidden('#skF_9','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_145,plain,(
    r2_hidden('#skF_9','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_70,plain,
    ( r2_hidden('#skF_8',k7_relset_1('#skF_6','#skF_4','#skF_7','#skF_5'))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_242,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_300,plain,(
    ! [C_175,B_176,A_177] :
      ( r2_hidden(C_175,B_176)
      | ~ r2_hidden(C_175,A_177)
      | ~ r1_tarski(A_177,B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_309,plain,(
    ! [B_176] :
      ( r2_hidden(k4_tarski('#skF_9','#skF_8'),B_176)
      | ~ r1_tarski('#skF_7',B_176) ) ),
    inference(resolution,[status(thm)],[c_242,c_300])).

tff(c_948,plain,(
    ! [A_237,B_238,C_239,D_240] :
      ( k7_relset_1(A_237,B_238,C_239,D_240) = k9_relat_1(C_239,D_240)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_971,plain,(
    ! [D_240] : k7_relset_1('#skF_6','#skF_4','#skF_7',D_240) = k9_relat_1('#skF_7',D_240) ),
    inference(resolution,[status(thm)],[c_52,c_948])).

tff(c_60,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_5')
      | ~ r2_hidden(k4_tarski(F_130,'#skF_8'),'#skF_7')
      | ~ m1_subset_1(F_130,'#skF_6')
      | ~ r2_hidden('#skF_8',k7_relset_1('#skF_6','#skF_4','#skF_7','#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_612,plain,(
    ~ r2_hidden('#skF_8',k7_relset_1('#skF_6','#skF_4','#skF_7','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_972,plain,(
    ~ r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_971,c_612])).

tff(c_464,plain,(
    ! [A_188,C_189,B_190] :
      ( r2_hidden(A_188,k1_relat_1(C_189))
      | ~ r2_hidden(k4_tarski(A_188,B_190),C_189)
      | ~ v1_relat_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_470,plain,
    ( r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_242,c_464])).

tff(c_474,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_470])).

tff(c_1363,plain,(
    ! [A_266,C_267,B_268,D_269] :
      ( r2_hidden(A_266,k9_relat_1(C_267,B_268))
      | ~ r2_hidden(D_269,B_268)
      | ~ r2_hidden(k4_tarski(D_269,A_266),C_267)
      | ~ r2_hidden(D_269,k1_relat_1(C_267))
      | ~ v1_relat_1(C_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1477,plain,(
    ! [A_273,C_274] :
      ( r2_hidden(A_273,k9_relat_1(C_274,'#skF_5'))
      | ~ r2_hidden(k4_tarski('#skF_9',A_273),C_274)
      | ~ r2_hidden('#skF_9',k1_relat_1(C_274))
      | ~ v1_relat_1(C_274) ) ),
    inference(resolution,[status(thm)],[c_145,c_1363])).

tff(c_1486,plain,
    ( r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_5'))
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_242,c_1477])).

tff(c_1493,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_474,c_1486])).

tff(c_1495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_972,c_1493])).

tff(c_1517,plain,(
    ! [F_275] :
      ( ~ r2_hidden(F_275,'#skF_5')
      | ~ r2_hidden(k4_tarski(F_275,'#skF_8'),'#skF_7')
      | ~ m1_subset_1(F_275,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1521,plain,
    ( ~ r2_hidden('#skF_9','#skF_5')
    | ~ m1_subset_1('#skF_9','#skF_6')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_309,c_1517])).

tff(c_1528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_199,c_145,c_1521])).

tff(c_1529,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_6','#skF_4','#skF_7','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2384,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2379,c_1529])).

tff(c_30,plain,(
    ! [A_24,B_25,C_26] :
      ( r2_hidden('#skF_3'(A_24,B_25,C_26),B_25)
      | ~ r2_hidden(A_24,k9_relat_1(C_26,B_25))
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2615,plain,(
    ! [A_402,B_403,C_404] :
      ( r2_hidden(k4_tarski('#skF_3'(A_402,B_403,C_404),A_402),C_404)
      | ~ r2_hidden(A_402,k9_relat_1(C_404,B_403))
      | ~ v1_relat_1(C_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1530,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_68,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_5')
      | ~ r2_hidden(k4_tarski(F_130,'#skF_8'),'#skF_7')
      | ~ m1_subset_1(F_130,'#skF_6')
      | r2_hidden(k4_tarski('#skF_9','#skF_8'),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1708,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_5')
      | ~ r2_hidden(k4_tarski(F_130,'#skF_8'),'#skF_7')
      | ~ m1_subset_1(F_130,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1530,c_68])).

tff(c_2634,plain,(
    ! [B_403] :
      ( ~ r2_hidden('#skF_3'('#skF_8',B_403,'#skF_7'),'#skF_5')
      | ~ m1_subset_1('#skF_3'('#skF_8',B_403,'#skF_7'),'#skF_6')
      | ~ r2_hidden('#skF_8',k9_relat_1('#skF_7',B_403))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2615,c_1708])).

tff(c_3634,plain,(
    ! [B_487] :
      ( ~ r2_hidden('#skF_3'('#skF_8',B_487,'#skF_7'),'#skF_5')
      | ~ m1_subset_1('#skF_3'('#skF_8',B_487,'#skF_7'),'#skF_6')
      | ~ r2_hidden('#skF_8',k9_relat_1('#skF_7',B_487)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_2634])).

tff(c_3638,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_8','#skF_5','#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_5'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_3634])).

tff(c_3641,plain,(
    ~ m1_subset_1('#skF_3'('#skF_8','#skF_5','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_2384,c_3638])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [A_148,B_149] :
      ( k2_xboole_0(k1_tarski(A_148),B_149) = B_149
      | ~ r2_hidden(A_148,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),B_14) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_126,plain,(
    ! [B_150,A_151] :
      ( k1_xboole_0 != B_150
      | ~ r2_hidden(A_151,B_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_16])).

tff(c_132,plain,(
    ! [A_152] :
      ( k1_xboole_0 != A_152
      | v1_xboole_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_142,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_132,c_54])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_144,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_132,c_58])).

tff(c_99,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(A_144,B_145)
      | ~ m1_subset_1(A_144,k1_zfmisc_1(B_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_112,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_99])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( k1_relat_1(k2_zfmisc_1(A_30,B_31)) = A_30
      | k1_xboole_0 = B_31
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1790,plain,(
    ! [A_312,B_313] :
      ( r1_tarski(k1_relat_1(A_312),k1_relat_1(B_313))
      | ~ r1_tarski(A_312,B_313)
      | ~ v1_relat_1(B_313)
      | ~ v1_relat_1(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1807,plain,(
    ! [A_312,A_30,B_31] :
      ( r1_tarski(k1_relat_1(A_312),A_30)
      | ~ r1_tarski(A_312,k2_zfmisc_1(A_30,B_31))
      | ~ v1_relat_1(k2_zfmisc_1(A_30,B_31))
      | ~ v1_relat_1(A_312)
      | k1_xboole_0 = B_31
      | k1_xboole_0 = A_30 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1790])).

tff(c_3878,plain,(
    ! [A_510,A_511,B_512] :
      ( r1_tarski(k1_relat_1(A_510),A_511)
      | ~ r1_tarski(A_510,k2_zfmisc_1(A_511,B_512))
      | ~ v1_relat_1(A_510)
      | k1_xboole_0 = B_512
      | k1_xboole_0 = A_511 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1807])).

tff(c_3922,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),'#skF_6')
    | ~ v1_relat_1('#skF_7')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_112,c_3878])).

tff(c_3941,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),'#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_3922])).

tff(c_3942,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_144,c_3941])).

tff(c_2469,plain,(
    ! [A_383,B_384,C_385] :
      ( r2_hidden('#skF_3'(A_383,B_384,C_385),k1_relat_1(C_385))
      | ~ r2_hidden(A_383,k9_relat_1(C_385,B_384))
      | ~ v1_relat_1(C_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4875,plain,(
    ! [A_562,B_563,C_564,B_565] :
      ( r2_hidden('#skF_3'(A_562,B_563,C_564),B_565)
      | ~ r1_tarski(k1_relat_1(C_564),B_565)
      | ~ r2_hidden(A_562,k9_relat_1(C_564,B_563))
      | ~ v1_relat_1(C_564) ) ),
    inference(resolution,[status(thm)],[c_2469,c_6])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18128,plain,(
    ! [A_1214,B_1215,C_1216,B_1217] :
      ( m1_subset_1('#skF_3'(A_1214,B_1215,C_1216),B_1217)
      | ~ r1_tarski(k1_relat_1(C_1216),B_1217)
      | ~ r2_hidden(A_1214,k9_relat_1(C_1216,B_1215))
      | ~ v1_relat_1(C_1216) ) ),
    inference(resolution,[status(thm)],[c_4875,c_18])).

tff(c_18150,plain,(
    ! [A_1214,B_1215] :
      ( m1_subset_1('#skF_3'(A_1214,B_1215,'#skF_7'),'#skF_6')
      | ~ r2_hidden(A_1214,k9_relat_1('#skF_7',B_1215))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3942,c_18128])).

tff(c_18194,plain,(
    ! [A_1218,B_1219] :
      ( m1_subset_1('#skF_3'(A_1218,B_1219,'#skF_7'),'#skF_6')
      | ~ r2_hidden(A_1218,k9_relat_1('#skF_7',B_1219)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_18150])).

tff(c_18237,plain,(
    m1_subset_1('#skF_3'('#skF_8','#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2384,c_18194])).

tff(c_18277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3641,c_18237])).

tff(c_18278,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_6','#skF_4','#skF_7','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_19958,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19953,c_18278])).

tff(c_20039,plain,(
    ! [A_1408,B_1409,C_1410] :
      ( r2_hidden(k4_tarski('#skF_3'(A_1408,B_1409,C_1410),A_1408),C_1410)
      | ~ r2_hidden(A_1408,k9_relat_1(C_1410,B_1409))
      | ~ v1_relat_1(C_1410) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18279,plain,(
    ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_5')
      | ~ r2_hidden(k4_tarski(F_130,'#skF_8'),'#skF_7')
      | ~ m1_subset_1(F_130,'#skF_6')
      | m1_subset_1('#skF_9','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_19101,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_5')
      | ~ r2_hidden(k4_tarski(F_130,'#skF_8'),'#skF_7')
      | ~ m1_subset_1(F_130,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_18279,c_72])).

tff(c_20067,plain,(
    ! [B_1409] :
      ( ~ r2_hidden('#skF_3'('#skF_8',B_1409,'#skF_7'),'#skF_5')
      | ~ m1_subset_1('#skF_3'('#skF_8',B_1409,'#skF_7'),'#skF_6')
      | ~ r2_hidden('#skF_8',k9_relat_1('#skF_7',B_1409))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_20039,c_19101])).

tff(c_21185,plain,(
    ! [B_1501] :
      ( ~ r2_hidden('#skF_3'('#skF_8',B_1501,'#skF_7'),'#skF_5')
      | ~ m1_subset_1('#skF_3'('#skF_8',B_1501,'#skF_7'),'#skF_6')
      | ~ r2_hidden('#skF_8',k9_relat_1('#skF_7',B_1501)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_20067])).

tff(c_21189,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_8','#skF_5','#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_5'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_21185])).

tff(c_21192,plain,(
    ~ m1_subset_1('#skF_3'('#skF_8','#skF_5','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_19958,c_21189])).

tff(c_19429,plain,(
    ! [A_1332,B_1333] :
      ( r1_tarski(k1_relat_1(A_1332),k1_relat_1(B_1333))
      | ~ r1_tarski(A_1332,B_1333)
      | ~ v1_relat_1(B_1333)
      | ~ v1_relat_1(A_1332) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_19446,plain,(
    ! [A_1332,A_30,B_31] :
      ( r1_tarski(k1_relat_1(A_1332),A_30)
      | ~ r1_tarski(A_1332,k2_zfmisc_1(A_30,B_31))
      | ~ v1_relat_1(k2_zfmisc_1(A_30,B_31))
      | ~ v1_relat_1(A_1332)
      | k1_xboole_0 = B_31
      | k1_xboole_0 = A_30 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_19429])).

tff(c_21448,plain,(
    ! [A_1522,A_1523,B_1524] :
      ( r1_tarski(k1_relat_1(A_1522),A_1523)
      | ~ r1_tarski(A_1522,k2_zfmisc_1(A_1523,B_1524))
      | ~ v1_relat_1(A_1522)
      | k1_xboole_0 = B_1524
      | k1_xboole_0 = A_1523 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_19446])).

tff(c_21492,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),'#skF_6')
    | ~ v1_relat_1('#skF_7')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_112,c_21448])).

tff(c_21511,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),'#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_21492])).

tff(c_21512,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_144,c_21511])).

tff(c_19781,plain,(
    ! [A_1379,B_1380,C_1381] :
      ( r2_hidden('#skF_3'(A_1379,B_1380,C_1381),k1_relat_1(C_1381))
      | ~ r2_hidden(A_1379,k9_relat_1(C_1381,B_1380))
      | ~ v1_relat_1(C_1381) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22468,plain,(
    ! [A_1571,B_1572,C_1573,B_1574] :
      ( r2_hidden('#skF_3'(A_1571,B_1572,C_1573),B_1574)
      | ~ r1_tarski(k1_relat_1(C_1573),B_1574)
      | ~ r2_hidden(A_1571,k9_relat_1(C_1573,B_1572))
      | ~ v1_relat_1(C_1573) ) ),
    inference(resolution,[status(thm)],[c_19781,c_6])).

tff(c_40954,plain,(
    ! [A_37100,B_37101,C_37102,B_37103] :
      ( m1_subset_1('#skF_3'(A_37100,B_37101,C_37102),B_37103)
      | ~ r1_tarski(k1_relat_1(C_37102),B_37103)
      | ~ r2_hidden(A_37100,k9_relat_1(C_37102,B_37101))
      | ~ v1_relat_1(C_37102) ) ),
    inference(resolution,[status(thm)],[c_22468,c_18])).

tff(c_40976,plain,(
    ! [A_37100,B_37101] :
      ( m1_subset_1('#skF_3'(A_37100,B_37101,'#skF_7'),'#skF_6')
      | ~ r2_hidden(A_37100,k9_relat_1('#skF_7',B_37101))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_21512,c_40954])).

tff(c_41020,plain,(
    ! [A_37104,B_37105] :
      ( m1_subset_1('#skF_3'(A_37104,B_37105,'#skF_7'),'#skF_6')
      | ~ r2_hidden(A_37104,k9_relat_1('#skF_7',B_37105)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_40976])).

tff(c_41067,plain,(
    m1_subset_1('#skF_3'('#skF_8','#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_19958,c_41020])).

tff(c_41110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21192,c_41067])).

tff(c_41111,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_6','#skF_4','#skF_7','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_41780,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41775,c_41111])).

tff(c_41860,plain,(
    ! [A_37207,B_37208,C_37209] :
      ( r2_hidden(k4_tarski('#skF_3'(A_37207,B_37208,C_37209),A_37207),C_37209)
      | ~ r2_hidden(A_37207,k9_relat_1(C_37209,B_37208))
      | ~ v1_relat_1(C_37209) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_41112,plain,(
    ~ r2_hidden('#skF_9','#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_5')
      | ~ r2_hidden(k4_tarski(F_130,'#skF_8'),'#skF_7')
      | ~ m1_subset_1(F_130,'#skF_6')
      | r2_hidden('#skF_9','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_41205,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_5')
      | ~ r2_hidden(k4_tarski(F_130,'#skF_8'),'#skF_7')
      | ~ m1_subset_1(F_130,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_41112,c_64])).

tff(c_41874,plain,(
    ! [B_37208] :
      ( ~ r2_hidden('#skF_3'('#skF_8',B_37208,'#skF_7'),'#skF_5')
      | ~ m1_subset_1('#skF_3'('#skF_8',B_37208,'#skF_7'),'#skF_6')
      | ~ r2_hidden('#skF_8',k9_relat_1('#skF_7',B_37208))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_41860,c_41205])).

tff(c_42026,plain,(
    ! [B_37228] :
      ( ~ r2_hidden('#skF_3'('#skF_8',B_37228,'#skF_7'),'#skF_5')
      | ~ m1_subset_1('#skF_3'('#skF_8',B_37228,'#skF_7'),'#skF_6')
      | ~ r2_hidden('#skF_8',k9_relat_1('#skF_7',B_37228)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41168,c_41874])).

tff(c_42030,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_8','#skF_5','#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_5'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_42026])).

tff(c_42033,plain,(
    ~ m1_subset_1('#skF_3'('#skF_8','#skF_5','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41168,c_41780,c_42030])).

tff(c_41499,plain,(
    ! [A_37169,B_37170] :
      ( r1_tarski(k1_relat_1(A_37169),k1_relat_1(B_37170))
      | ~ r1_tarski(A_37169,B_37170)
      | ~ v1_relat_1(B_37170)
      | ~ v1_relat_1(A_37169) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_41518,plain,(
    ! [A_37169,A_30,B_31] :
      ( r1_tarski(k1_relat_1(A_37169),A_30)
      | ~ r1_tarski(A_37169,k2_zfmisc_1(A_30,B_31))
      | ~ v1_relat_1(k2_zfmisc_1(A_30,B_31))
      | ~ v1_relat_1(A_37169)
      | k1_xboole_0 = B_31
      | k1_xboole_0 = A_30 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_41499])).

tff(c_43495,plain,(
    ! [A_37340,A_37341,B_37342] :
      ( r1_tarski(k1_relat_1(A_37340),A_37341)
      | ~ r1_tarski(A_37340,k2_zfmisc_1(A_37341,B_37342))
      | ~ v1_relat_1(A_37340)
      | k1_xboole_0 = B_37342
      | k1_xboole_0 = A_37341 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_41518])).

tff(c_43542,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),'#skF_6')
    | ~ v1_relat_1('#skF_7')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_112,c_43495])).

tff(c_43562,plain,
    ( r1_tarski(k1_relat_1('#skF_7'),'#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41168,c_43542])).

tff(c_43563,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_144,c_43562])).

tff(c_41800,plain,(
    ! [A_37203,B_37204,C_37205] :
      ( r2_hidden('#skF_3'(A_37203,B_37204,C_37205),k1_relat_1(C_37205))
      | ~ r2_hidden(A_37203,k9_relat_1(C_37205,B_37204))
      | ~ v1_relat_1(C_37205) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44858,plain,(
    ! [A_37411,B_37412,C_37413,B_37414] :
      ( r2_hidden('#skF_3'(A_37411,B_37412,C_37413),B_37414)
      | ~ r1_tarski(k1_relat_1(C_37413),B_37414)
      | ~ r2_hidden(A_37411,k9_relat_1(C_37413,B_37412))
      | ~ v1_relat_1(C_37413) ) ),
    inference(resolution,[status(thm)],[c_41800,c_6])).

tff(c_63407,plain,(
    ! [A_70409,B_70410,C_70411,B_70412] :
      ( m1_subset_1('#skF_3'(A_70409,B_70410,C_70411),B_70412)
      | ~ r1_tarski(k1_relat_1(C_70411),B_70412)
      | ~ r2_hidden(A_70409,k9_relat_1(C_70411,B_70410))
      | ~ v1_relat_1(C_70411) ) ),
    inference(resolution,[status(thm)],[c_44858,c_18])).

tff(c_63438,plain,(
    ! [A_70409,B_70410] :
      ( m1_subset_1('#skF_3'(A_70409,B_70410,'#skF_7'),'#skF_6')
      | ~ r2_hidden(A_70409,k9_relat_1('#skF_7',B_70410))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_43563,c_63407])).

tff(c_63530,plain,(
    ! [A_70414,B_70415] :
      ( m1_subset_1('#skF_3'(A_70414,B_70415,'#skF_7'),'#skF_6')
      | ~ r2_hidden(A_70414,k9_relat_1('#skF_7',B_70415)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41168,c_63438])).

tff(c_63585,plain,(
    m1_subset_1('#skF_3'('#skF_8','#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_41780,c_63530])).

tff(c_63626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42033,c_63585])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.63/9.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.63/9.53  
% 18.63/9.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.63/9.53  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_2
% 18.63/9.53  
% 18.63/9.53  %Foreground sorts:
% 18.63/9.53  
% 18.63/9.53  
% 18.63/9.53  %Background operators:
% 18.63/9.53  
% 18.63/9.53  
% 18.63/9.53  %Foreground operators:
% 18.63/9.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.63/9.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.63/9.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.63/9.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 18.63/9.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 18.63/9.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.63/9.53  tff('#skF_7', type, '#skF_7': $i).
% 18.63/9.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.63/9.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.63/9.53  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 18.63/9.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.63/9.53  tff('#skF_5', type, '#skF_5': $i).
% 18.63/9.53  tff('#skF_6', type, '#skF_6': $i).
% 18.63/9.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.63/9.53  tff('#skF_9', type, '#skF_9': $i).
% 18.63/9.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.63/9.53  tff('#skF_8', type, '#skF_8': $i).
% 18.63/9.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.63/9.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.63/9.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 18.63/9.53  tff('#skF_4', type, '#skF_4': $i).
% 18.63/9.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 18.63/9.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.63/9.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 18.63/9.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.63/9.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 18.63/9.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.63/9.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.63/9.53  
% 18.63/9.55  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 18.63/9.55  tff(f_137, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 18.63/9.55  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 18.63/9.55  tff(f_110, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 18.63/9.55  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 18.63/9.55  tff(f_95, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 18.63/9.55  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 18.63/9.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 18.63/9.55  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 18.63/9.55  tff(f_47, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 18.63/9.55  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 18.63/9.55  tff(f_87, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 18.63/9.55  tff(f_106, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 18.63/9.55  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 18.63/9.55  tff(c_26, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 18.63/9.55  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.63/9.55  tff(c_41153, plain, (![B_37113, A_37114]: (v1_relat_1(B_37113) | ~m1_subset_1(B_37113, k1_zfmisc_1(A_37114)) | ~v1_relat_1(A_37114))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.63/9.55  tff(c_41163, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_41153])).
% 18.63/9.55  tff(c_41168, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_41163])).
% 18.63/9.55  tff(c_41752, plain, (![A_37198, B_37199, C_37200, D_37201]: (k7_relset_1(A_37198, B_37199, C_37200, D_37201)=k9_relat_1(C_37200, D_37201) | ~m1_subset_1(C_37200, k1_zfmisc_1(k2_zfmisc_1(A_37198, B_37199))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.63/9.55  tff(c_41775, plain, (![D_37201]: (k7_relset_1('#skF_6', '#skF_4', '#skF_7', D_37201)=k9_relat_1('#skF_7', D_37201))), inference(resolution, [status(thm)], [c_52, c_41752])).
% 18.63/9.55  tff(c_158, plain, (![B_153, A_154]: (v1_relat_1(B_153) | ~m1_subset_1(B_153, k1_zfmisc_1(A_154)) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.63/9.55  tff(c_168, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_158])).
% 18.63/9.55  tff(c_173, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_168])).
% 18.63/9.55  tff(c_19930, plain, (![A_1403, B_1404, C_1405, D_1406]: (k7_relset_1(A_1403, B_1404, C_1405, D_1406)=k9_relat_1(C_1405, D_1406) | ~m1_subset_1(C_1405, k1_zfmisc_1(k2_zfmisc_1(A_1403, B_1404))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.63/9.55  tff(c_19953, plain, (![D_1406]: (k7_relset_1('#skF_6', '#skF_4', '#skF_7', D_1406)=k9_relat_1('#skF_7', D_1406))), inference(resolution, [status(thm)], [c_52, c_19930])).
% 18.63/9.55  tff(c_2356, plain, (![A_377, B_378, C_379, D_380]: (k7_relset_1(A_377, B_378, C_379, D_380)=k9_relat_1(C_379, D_380) | ~m1_subset_1(C_379, k1_zfmisc_1(k2_zfmisc_1(A_377, B_378))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.63/9.55  tff(c_2379, plain, (![D_380]: (k7_relset_1('#skF_6', '#skF_4', '#skF_7', D_380)=k9_relat_1('#skF_7', D_380))), inference(resolution, [status(thm)], [c_52, c_2356])).
% 18.63/9.55  tff(c_181, plain, (![A_157, B_158]: (r2_hidden('#skF_2'(A_157, B_158), A_157) | r1_tarski(A_157, B_158))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.63/9.55  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.63/9.55  tff(c_196, plain, (![A_157]: (r1_tarski(A_157, A_157))), inference(resolution, [status(thm)], [c_181, c_8])).
% 18.63/9.55  tff(c_74, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_6', '#skF_4', '#skF_7', '#skF_5')) | m1_subset_1('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.63/9.55  tff(c_199, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_74])).
% 18.63/9.55  tff(c_66, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_6', '#skF_4', '#skF_7', '#skF_5')) | r2_hidden('#skF_9', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.63/9.55  tff(c_145, plain, (r2_hidden('#skF_9', '#skF_5')), inference(splitLeft, [status(thm)], [c_66])).
% 18.63/9.55  tff(c_70, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_6', '#skF_4', '#skF_7', '#skF_5')) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.63/9.55  tff(c_242, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_70])).
% 18.63/9.55  tff(c_300, plain, (![C_175, B_176, A_177]: (r2_hidden(C_175, B_176) | ~r2_hidden(C_175, A_177) | ~r1_tarski(A_177, B_176))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.63/9.55  tff(c_309, plain, (![B_176]: (r2_hidden(k4_tarski('#skF_9', '#skF_8'), B_176) | ~r1_tarski('#skF_7', B_176))), inference(resolution, [status(thm)], [c_242, c_300])).
% 18.63/9.55  tff(c_948, plain, (![A_237, B_238, C_239, D_240]: (k7_relset_1(A_237, B_238, C_239, D_240)=k9_relat_1(C_239, D_240) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.63/9.55  tff(c_971, plain, (![D_240]: (k7_relset_1('#skF_6', '#skF_4', '#skF_7', D_240)=k9_relat_1('#skF_7', D_240))), inference(resolution, [status(thm)], [c_52, c_948])).
% 18.63/9.55  tff(c_60, plain, (![F_130]: (~r2_hidden(F_130, '#skF_5') | ~r2_hidden(k4_tarski(F_130, '#skF_8'), '#skF_7') | ~m1_subset_1(F_130, '#skF_6') | ~r2_hidden('#skF_8', k7_relset_1('#skF_6', '#skF_4', '#skF_7', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.63/9.55  tff(c_612, plain, (~r2_hidden('#skF_8', k7_relset_1('#skF_6', '#skF_4', '#skF_7', '#skF_5'))), inference(splitLeft, [status(thm)], [c_60])).
% 18.63/9.55  tff(c_972, plain, (~r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_971, c_612])).
% 18.63/9.55  tff(c_464, plain, (![A_188, C_189, B_190]: (r2_hidden(A_188, k1_relat_1(C_189)) | ~r2_hidden(k4_tarski(A_188, B_190), C_189) | ~v1_relat_1(C_189))), inference(cnfTransformation, [status(thm)], [f_95])).
% 18.63/9.55  tff(c_470, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_242, c_464])).
% 18.63/9.55  tff(c_474, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_470])).
% 18.63/9.55  tff(c_1363, plain, (![A_266, C_267, B_268, D_269]: (r2_hidden(A_266, k9_relat_1(C_267, B_268)) | ~r2_hidden(D_269, B_268) | ~r2_hidden(k4_tarski(D_269, A_266), C_267) | ~r2_hidden(D_269, k1_relat_1(C_267)) | ~v1_relat_1(C_267))), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.63/9.55  tff(c_1477, plain, (![A_273, C_274]: (r2_hidden(A_273, k9_relat_1(C_274, '#skF_5')) | ~r2_hidden(k4_tarski('#skF_9', A_273), C_274) | ~r2_hidden('#skF_9', k1_relat_1(C_274)) | ~v1_relat_1(C_274))), inference(resolution, [status(thm)], [c_145, c_1363])).
% 18.63/9.55  tff(c_1486, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_5')) | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_242, c_1477])).
% 18.63/9.55  tff(c_1493, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_474, c_1486])).
% 18.63/9.55  tff(c_1495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_972, c_1493])).
% 18.63/9.55  tff(c_1517, plain, (![F_275]: (~r2_hidden(F_275, '#skF_5') | ~r2_hidden(k4_tarski(F_275, '#skF_8'), '#skF_7') | ~m1_subset_1(F_275, '#skF_6'))), inference(splitRight, [status(thm)], [c_60])).
% 18.63/9.55  tff(c_1521, plain, (~r2_hidden('#skF_9', '#skF_5') | ~m1_subset_1('#skF_9', '#skF_6') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_309, c_1517])).
% 18.63/9.55  tff(c_1528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_196, c_199, c_145, c_1521])).
% 18.63/9.55  tff(c_1529, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_6', '#skF_4', '#skF_7', '#skF_5'))), inference(splitRight, [status(thm)], [c_70])).
% 18.63/9.55  tff(c_2384, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2379, c_1529])).
% 18.63/9.55  tff(c_30, plain, (![A_24, B_25, C_26]: (r2_hidden('#skF_3'(A_24, B_25, C_26), B_25) | ~r2_hidden(A_24, k9_relat_1(C_26, B_25)) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.63/9.55  tff(c_2615, plain, (![A_402, B_403, C_404]: (r2_hidden(k4_tarski('#skF_3'(A_402, B_403, C_404), A_402), C_404) | ~r2_hidden(A_402, k9_relat_1(C_404, B_403)) | ~v1_relat_1(C_404))), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.63/9.55  tff(c_1530, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 18.63/9.55  tff(c_68, plain, (![F_130]: (~r2_hidden(F_130, '#skF_5') | ~r2_hidden(k4_tarski(F_130, '#skF_8'), '#skF_7') | ~m1_subset_1(F_130, '#skF_6') | r2_hidden(k4_tarski('#skF_9', '#skF_8'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.63/9.55  tff(c_1708, plain, (![F_130]: (~r2_hidden(F_130, '#skF_5') | ~r2_hidden(k4_tarski(F_130, '#skF_8'), '#skF_7') | ~m1_subset_1(F_130, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1530, c_68])).
% 18.63/9.55  tff(c_2634, plain, (![B_403]: (~r2_hidden('#skF_3'('#skF_8', B_403, '#skF_7'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_8', B_403, '#skF_7'), '#skF_6') | ~r2_hidden('#skF_8', k9_relat_1('#skF_7', B_403)) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_2615, c_1708])).
% 18.63/9.55  tff(c_3634, plain, (![B_487]: (~r2_hidden('#skF_3'('#skF_8', B_487, '#skF_7'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_8', B_487, '#skF_7'), '#skF_6') | ~r2_hidden('#skF_8', k9_relat_1('#skF_7', B_487)))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_2634])).
% 18.63/9.55  tff(c_3638, plain, (~m1_subset_1('#skF_3'('#skF_8', '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_5')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_3634])).
% 18.63/9.55  tff(c_3641, plain, (~m1_subset_1('#skF_3'('#skF_8', '#skF_5', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_2384, c_3638])).
% 18.63/9.55  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.63/9.55  tff(c_114, plain, (![A_148, B_149]: (k2_xboole_0(k1_tarski(A_148), B_149)=B_149 | ~r2_hidden(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_44])).
% 18.63/9.55  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.63/9.55  tff(c_126, plain, (![B_150, A_151]: (k1_xboole_0!=B_150 | ~r2_hidden(A_151, B_150))), inference(superposition, [status(thm), theory('equality')], [c_114, c_16])).
% 18.63/9.55  tff(c_132, plain, (![A_152]: (k1_xboole_0!=A_152 | v1_xboole_0(A_152))), inference(resolution, [status(thm)], [c_4, c_126])).
% 18.63/9.55  tff(c_54, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.63/9.55  tff(c_142, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_132, c_54])).
% 18.63/9.55  tff(c_58, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.63/9.55  tff(c_144, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_132, c_58])).
% 18.63/9.55  tff(c_99, plain, (![A_144, B_145]: (r1_tarski(A_144, B_145) | ~m1_subset_1(A_144, k1_zfmisc_1(B_145)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 18.63/9.55  tff(c_112, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_99])).
% 18.63/9.55  tff(c_38, plain, (![A_30, B_31]: (k1_relat_1(k2_zfmisc_1(A_30, B_31))=A_30 | k1_xboole_0=B_31 | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.63/9.55  tff(c_1790, plain, (![A_312, B_313]: (r1_tarski(k1_relat_1(A_312), k1_relat_1(B_313)) | ~r1_tarski(A_312, B_313) | ~v1_relat_1(B_313) | ~v1_relat_1(A_312))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.63/9.55  tff(c_1807, plain, (![A_312, A_30, B_31]: (r1_tarski(k1_relat_1(A_312), A_30) | ~r1_tarski(A_312, k2_zfmisc_1(A_30, B_31)) | ~v1_relat_1(k2_zfmisc_1(A_30, B_31)) | ~v1_relat_1(A_312) | k1_xboole_0=B_31 | k1_xboole_0=A_30)), inference(superposition, [status(thm), theory('equality')], [c_38, c_1790])).
% 18.63/9.55  tff(c_3878, plain, (![A_510, A_511, B_512]: (r1_tarski(k1_relat_1(A_510), A_511) | ~r1_tarski(A_510, k2_zfmisc_1(A_511, B_512)) | ~v1_relat_1(A_510) | k1_xboole_0=B_512 | k1_xboole_0=A_511)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1807])).
% 18.63/9.55  tff(c_3922, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_6') | ~v1_relat_1('#skF_7') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_112, c_3878])).
% 18.63/9.55  tff(c_3941, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_3922])).
% 18.63/9.55  tff(c_3942, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_142, c_144, c_3941])).
% 18.63/9.55  tff(c_2469, plain, (![A_383, B_384, C_385]: (r2_hidden('#skF_3'(A_383, B_384, C_385), k1_relat_1(C_385)) | ~r2_hidden(A_383, k9_relat_1(C_385, B_384)) | ~v1_relat_1(C_385))), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.63/9.55  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.63/9.55  tff(c_4875, plain, (![A_562, B_563, C_564, B_565]: (r2_hidden('#skF_3'(A_562, B_563, C_564), B_565) | ~r1_tarski(k1_relat_1(C_564), B_565) | ~r2_hidden(A_562, k9_relat_1(C_564, B_563)) | ~v1_relat_1(C_564))), inference(resolution, [status(thm)], [c_2469, c_6])).
% 18.63/9.55  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(A_15, B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.63/9.55  tff(c_18128, plain, (![A_1214, B_1215, C_1216, B_1217]: (m1_subset_1('#skF_3'(A_1214, B_1215, C_1216), B_1217) | ~r1_tarski(k1_relat_1(C_1216), B_1217) | ~r2_hidden(A_1214, k9_relat_1(C_1216, B_1215)) | ~v1_relat_1(C_1216))), inference(resolution, [status(thm)], [c_4875, c_18])).
% 18.63/9.55  tff(c_18150, plain, (![A_1214, B_1215]: (m1_subset_1('#skF_3'(A_1214, B_1215, '#skF_7'), '#skF_6') | ~r2_hidden(A_1214, k9_relat_1('#skF_7', B_1215)) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_3942, c_18128])).
% 18.63/9.55  tff(c_18194, plain, (![A_1218, B_1219]: (m1_subset_1('#skF_3'(A_1218, B_1219, '#skF_7'), '#skF_6') | ~r2_hidden(A_1218, k9_relat_1('#skF_7', B_1219)))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_18150])).
% 18.63/9.55  tff(c_18237, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_2384, c_18194])).
% 18.63/9.55  tff(c_18277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3641, c_18237])).
% 18.63/9.55  tff(c_18278, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_6', '#skF_4', '#skF_7', '#skF_5'))), inference(splitRight, [status(thm)], [c_74])).
% 18.63/9.55  tff(c_19958, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_19953, c_18278])).
% 18.63/9.55  tff(c_20039, plain, (![A_1408, B_1409, C_1410]: (r2_hidden(k4_tarski('#skF_3'(A_1408, B_1409, C_1410), A_1408), C_1410) | ~r2_hidden(A_1408, k9_relat_1(C_1410, B_1409)) | ~v1_relat_1(C_1410))), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.63/9.55  tff(c_18279, plain, (~m1_subset_1('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_74])).
% 18.63/9.55  tff(c_72, plain, (![F_130]: (~r2_hidden(F_130, '#skF_5') | ~r2_hidden(k4_tarski(F_130, '#skF_8'), '#skF_7') | ~m1_subset_1(F_130, '#skF_6') | m1_subset_1('#skF_9', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.63/9.55  tff(c_19101, plain, (![F_130]: (~r2_hidden(F_130, '#skF_5') | ~r2_hidden(k4_tarski(F_130, '#skF_8'), '#skF_7') | ~m1_subset_1(F_130, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_18279, c_72])).
% 18.63/9.55  tff(c_20067, plain, (![B_1409]: (~r2_hidden('#skF_3'('#skF_8', B_1409, '#skF_7'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_8', B_1409, '#skF_7'), '#skF_6') | ~r2_hidden('#skF_8', k9_relat_1('#skF_7', B_1409)) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_20039, c_19101])).
% 18.63/9.55  tff(c_21185, plain, (![B_1501]: (~r2_hidden('#skF_3'('#skF_8', B_1501, '#skF_7'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_8', B_1501, '#skF_7'), '#skF_6') | ~r2_hidden('#skF_8', k9_relat_1('#skF_7', B_1501)))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_20067])).
% 18.63/9.55  tff(c_21189, plain, (~m1_subset_1('#skF_3'('#skF_8', '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_5')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_21185])).
% 18.63/9.55  tff(c_21192, plain, (~m1_subset_1('#skF_3'('#skF_8', '#skF_5', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_19958, c_21189])).
% 18.63/9.55  tff(c_19429, plain, (![A_1332, B_1333]: (r1_tarski(k1_relat_1(A_1332), k1_relat_1(B_1333)) | ~r1_tarski(A_1332, B_1333) | ~v1_relat_1(B_1333) | ~v1_relat_1(A_1332))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.63/9.55  tff(c_19446, plain, (![A_1332, A_30, B_31]: (r1_tarski(k1_relat_1(A_1332), A_30) | ~r1_tarski(A_1332, k2_zfmisc_1(A_30, B_31)) | ~v1_relat_1(k2_zfmisc_1(A_30, B_31)) | ~v1_relat_1(A_1332) | k1_xboole_0=B_31 | k1_xboole_0=A_30)), inference(superposition, [status(thm), theory('equality')], [c_38, c_19429])).
% 18.63/9.55  tff(c_21448, plain, (![A_1522, A_1523, B_1524]: (r1_tarski(k1_relat_1(A_1522), A_1523) | ~r1_tarski(A_1522, k2_zfmisc_1(A_1523, B_1524)) | ~v1_relat_1(A_1522) | k1_xboole_0=B_1524 | k1_xboole_0=A_1523)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_19446])).
% 18.63/9.55  tff(c_21492, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_6') | ~v1_relat_1('#skF_7') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_112, c_21448])).
% 18.63/9.55  tff(c_21511, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_21492])).
% 18.63/9.55  tff(c_21512, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_142, c_144, c_21511])).
% 18.63/9.55  tff(c_19781, plain, (![A_1379, B_1380, C_1381]: (r2_hidden('#skF_3'(A_1379, B_1380, C_1381), k1_relat_1(C_1381)) | ~r2_hidden(A_1379, k9_relat_1(C_1381, B_1380)) | ~v1_relat_1(C_1381))), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.63/9.55  tff(c_22468, plain, (![A_1571, B_1572, C_1573, B_1574]: (r2_hidden('#skF_3'(A_1571, B_1572, C_1573), B_1574) | ~r1_tarski(k1_relat_1(C_1573), B_1574) | ~r2_hidden(A_1571, k9_relat_1(C_1573, B_1572)) | ~v1_relat_1(C_1573))), inference(resolution, [status(thm)], [c_19781, c_6])).
% 18.63/9.55  tff(c_40954, plain, (![A_37100, B_37101, C_37102, B_37103]: (m1_subset_1('#skF_3'(A_37100, B_37101, C_37102), B_37103) | ~r1_tarski(k1_relat_1(C_37102), B_37103) | ~r2_hidden(A_37100, k9_relat_1(C_37102, B_37101)) | ~v1_relat_1(C_37102))), inference(resolution, [status(thm)], [c_22468, c_18])).
% 18.63/9.55  tff(c_40976, plain, (![A_37100, B_37101]: (m1_subset_1('#skF_3'(A_37100, B_37101, '#skF_7'), '#skF_6') | ~r2_hidden(A_37100, k9_relat_1('#skF_7', B_37101)) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_21512, c_40954])).
% 18.63/9.55  tff(c_41020, plain, (![A_37104, B_37105]: (m1_subset_1('#skF_3'(A_37104, B_37105, '#skF_7'), '#skF_6') | ~r2_hidden(A_37104, k9_relat_1('#skF_7', B_37105)))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_40976])).
% 18.63/9.55  tff(c_41067, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_19958, c_41020])).
% 18.63/9.55  tff(c_41110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21192, c_41067])).
% 18.63/9.55  tff(c_41111, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_6', '#skF_4', '#skF_7', '#skF_5'))), inference(splitRight, [status(thm)], [c_66])).
% 18.63/9.55  tff(c_41780, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_41775, c_41111])).
% 18.63/9.55  tff(c_41860, plain, (![A_37207, B_37208, C_37209]: (r2_hidden(k4_tarski('#skF_3'(A_37207, B_37208, C_37209), A_37207), C_37209) | ~r2_hidden(A_37207, k9_relat_1(C_37209, B_37208)) | ~v1_relat_1(C_37209))), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.63/9.55  tff(c_41112, plain, (~r2_hidden('#skF_9', '#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 18.63/9.55  tff(c_64, plain, (![F_130]: (~r2_hidden(F_130, '#skF_5') | ~r2_hidden(k4_tarski(F_130, '#skF_8'), '#skF_7') | ~m1_subset_1(F_130, '#skF_6') | r2_hidden('#skF_9', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 18.63/9.55  tff(c_41205, plain, (![F_130]: (~r2_hidden(F_130, '#skF_5') | ~r2_hidden(k4_tarski(F_130, '#skF_8'), '#skF_7') | ~m1_subset_1(F_130, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_41112, c_64])).
% 18.63/9.55  tff(c_41874, plain, (![B_37208]: (~r2_hidden('#skF_3'('#skF_8', B_37208, '#skF_7'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_8', B_37208, '#skF_7'), '#skF_6') | ~r2_hidden('#skF_8', k9_relat_1('#skF_7', B_37208)) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_41860, c_41205])).
% 18.63/9.55  tff(c_42026, plain, (![B_37228]: (~r2_hidden('#skF_3'('#skF_8', B_37228, '#skF_7'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_8', B_37228, '#skF_7'), '#skF_6') | ~r2_hidden('#skF_8', k9_relat_1('#skF_7', B_37228)))), inference(demodulation, [status(thm), theory('equality')], [c_41168, c_41874])).
% 18.63/9.55  tff(c_42030, plain, (~m1_subset_1('#skF_3'('#skF_8', '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_5')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_42026])).
% 18.63/9.55  tff(c_42033, plain, (~m1_subset_1('#skF_3'('#skF_8', '#skF_5', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_41168, c_41780, c_42030])).
% 18.63/9.55  tff(c_41499, plain, (![A_37169, B_37170]: (r1_tarski(k1_relat_1(A_37169), k1_relat_1(B_37170)) | ~r1_tarski(A_37169, B_37170) | ~v1_relat_1(B_37170) | ~v1_relat_1(A_37169))), inference(cnfTransformation, [status(thm)], [f_106])).
% 18.63/9.55  tff(c_41518, plain, (![A_37169, A_30, B_31]: (r1_tarski(k1_relat_1(A_37169), A_30) | ~r1_tarski(A_37169, k2_zfmisc_1(A_30, B_31)) | ~v1_relat_1(k2_zfmisc_1(A_30, B_31)) | ~v1_relat_1(A_37169) | k1_xboole_0=B_31 | k1_xboole_0=A_30)), inference(superposition, [status(thm), theory('equality')], [c_38, c_41499])).
% 18.63/9.55  tff(c_43495, plain, (![A_37340, A_37341, B_37342]: (r1_tarski(k1_relat_1(A_37340), A_37341) | ~r1_tarski(A_37340, k2_zfmisc_1(A_37341, B_37342)) | ~v1_relat_1(A_37340) | k1_xboole_0=B_37342 | k1_xboole_0=A_37341)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_41518])).
% 18.63/9.55  tff(c_43542, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_6') | ~v1_relat_1('#skF_7') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_112, c_43495])).
% 18.63/9.55  tff(c_43562, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_41168, c_43542])).
% 18.63/9.55  tff(c_43563, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_142, c_144, c_43562])).
% 18.63/9.55  tff(c_41800, plain, (![A_37203, B_37204, C_37205]: (r2_hidden('#skF_3'(A_37203, B_37204, C_37205), k1_relat_1(C_37205)) | ~r2_hidden(A_37203, k9_relat_1(C_37205, B_37204)) | ~v1_relat_1(C_37205))), inference(cnfTransformation, [status(thm)], [f_75])).
% 18.63/9.55  tff(c_44858, plain, (![A_37411, B_37412, C_37413, B_37414]: (r2_hidden('#skF_3'(A_37411, B_37412, C_37413), B_37414) | ~r1_tarski(k1_relat_1(C_37413), B_37414) | ~r2_hidden(A_37411, k9_relat_1(C_37413, B_37412)) | ~v1_relat_1(C_37413))), inference(resolution, [status(thm)], [c_41800, c_6])).
% 18.63/9.55  tff(c_63407, plain, (![A_70409, B_70410, C_70411, B_70412]: (m1_subset_1('#skF_3'(A_70409, B_70410, C_70411), B_70412) | ~r1_tarski(k1_relat_1(C_70411), B_70412) | ~r2_hidden(A_70409, k9_relat_1(C_70411, B_70410)) | ~v1_relat_1(C_70411))), inference(resolution, [status(thm)], [c_44858, c_18])).
% 18.63/9.55  tff(c_63438, plain, (![A_70409, B_70410]: (m1_subset_1('#skF_3'(A_70409, B_70410, '#skF_7'), '#skF_6') | ~r2_hidden(A_70409, k9_relat_1('#skF_7', B_70410)) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_43563, c_63407])).
% 18.63/9.55  tff(c_63530, plain, (![A_70414, B_70415]: (m1_subset_1('#skF_3'(A_70414, B_70415, '#skF_7'), '#skF_6') | ~r2_hidden(A_70414, k9_relat_1('#skF_7', B_70415)))), inference(demodulation, [status(thm), theory('equality')], [c_41168, c_63438])).
% 18.63/9.55  tff(c_63585, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_41780, c_63530])).
% 18.63/9.55  tff(c_63626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42033, c_63585])).
% 18.63/9.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.63/9.55  
% 18.63/9.55  Inference rules
% 18.63/9.55  ----------------------
% 18.63/9.55  #Ref     : 0
% 18.63/9.55  #Sup     : 12739
% 18.63/9.55  #Fact    : 8
% 18.63/9.55  #Define  : 0
% 18.63/9.55  #Split   : 177
% 18.63/9.55  #Chain   : 0
% 18.63/9.55  #Close   : 0
% 18.63/9.55  
% 18.63/9.55  Ordering : KBO
% 18.63/9.55  
% 18.63/9.55  Simplification rules
% 18.63/9.55  ----------------------
% 18.63/9.55  #Subsume      : 5684
% 18.63/9.55  #Demod        : 1329
% 18.63/9.55  #Tautology    : 598
% 18.63/9.55  #SimpNegUnit  : 801
% 18.63/9.55  #BackRed      : 24
% 18.63/9.55  
% 18.63/9.55  #Partial instantiations: 16812
% 18.63/9.55  #Strategies tried      : 1
% 18.63/9.55  
% 18.63/9.55  Timing (in seconds)
% 18.63/9.55  ----------------------
% 18.63/9.56  Preprocessing        : 0.37
% 18.63/9.56  Parsing              : 0.19
% 18.63/9.56  CNF conversion       : 0.04
% 18.63/9.56  Main loop            : 8.34
% 18.63/9.56  Inferencing          : 2.24
% 18.63/9.56  Reduction            : 2.15
% 18.63/9.56  Demodulation         : 1.33
% 18.63/9.56  BG Simplification    : 0.13
% 18.63/9.56  Subsumption          : 3.19
% 18.63/9.56  Abstraction          : 0.21
% 18.63/9.56  MUC search           : 0.00
% 18.63/9.56  Cooper               : 0.00
% 18.63/9.56  Total                : 8.76
% 18.63/9.56  Index Insertion      : 0.00
% 18.63/9.56  Index Deletion       : 0.00
% 18.63/9.56  Index Matching       : 0.00
% 18.63/9.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
