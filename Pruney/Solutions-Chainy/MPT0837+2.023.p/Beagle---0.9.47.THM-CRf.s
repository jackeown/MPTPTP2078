%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:08 EST 2020

% Result     : Theorem 16.51s
% Output     : CNFRefutation 16.51s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 231 expanded)
%              Number of leaves         :   32 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  189 ( 576 expanded)
%              Number of equality atoms :   12 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_12 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_44,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34385,plain,(
    ! [A_1304,B_1305,C_1306] :
      ( k2_relset_1(A_1304,B_1305,C_1306) = k2_relat_1(C_1306)
      | ~ m1_subset_1(C_1306,k1_zfmisc_1(k2_zfmisc_1(A_1304,B_1305))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34409,plain,(
    k2_relset_1('#skF_8','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_34385])).

tff(c_60,plain,
    ( m1_subset_1('#skF_11','#skF_8')
    | r2_hidden('#skF_12',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_96,plain,(
    r2_hidden('#skF_12',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_34415,plain,(
    r2_hidden('#skF_12',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34409,c_96])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_21484,plain,(
    ! [A_763,B_764,C_765] :
      ( k2_relset_1(A_763,B_764,C_765) = k2_relat_1(C_765)
      | ~ m1_subset_1(C_765,k1_zfmisc_1(k2_zfmisc_1(A_763,B_764))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_21508,plain,(
    k2_relset_1('#skF_8','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_21484])).

tff(c_21512,plain,(
    r2_hidden('#skF_12',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21508,c_96])).

tff(c_21353,plain,(
    ! [A_729,B_730] :
      ( r2_hidden('#skF_2'(A_729,B_730),A_729)
      | r1_tarski(A_729,B_730) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_21365,plain,(
    ! [A_729] : r1_tarski(A_729,A_729) ),
    inference(resolution,[status(thm)],[c_21353,c_8])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( m1_subset_1(B_15,A_14)
      | ~ v1_xboole_0(B_15)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( r2_hidden(B_15,A_14)
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    ! [E_81] :
      ( r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9')
      | ~ r2_hidden(k4_tarski(E_81,'#skF_12'),'#skF_9')
      | ~ m1_subset_1(E_81,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_21472,plain,(
    ! [E_761] :
      ( ~ r2_hidden(k4_tarski(E_761,'#skF_12'),'#skF_9')
      | ~ m1_subset_1(E_761,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_21476,plain,(
    ! [E_761] :
      ( ~ m1_subset_1(E_761,'#skF_8')
      | ~ m1_subset_1(k4_tarski(E_761,'#skF_12'),'#skF_9')
      | v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_20,c_21472])).

tff(c_21478,plain,(
    ! [E_762] :
      ( ~ m1_subset_1(E_762,'#skF_8')
      | ~ m1_subset_1(k4_tarski(E_762,'#skF_12'),'#skF_9') ) ),
    inference(splitLeft,[status(thm)],[c_21476])).

tff(c_21482,plain,(
    ! [E_762] :
      ( ~ m1_subset_1(E_762,'#skF_8')
      | ~ v1_xboole_0(k4_tarski(E_762,'#skF_12'))
      | ~ v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_22,c_21478])).

tff(c_21483,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_21482])).

tff(c_21721,plain,(
    ! [A_800,C_801] :
      ( r2_hidden(k4_tarski('#skF_6'(A_800,k2_relat_1(A_800),C_801),C_801),A_800)
      | ~ r2_hidden(C_801,k2_relat_1(A_800)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( m1_subset_1(B_15,A_14)
      | ~ r2_hidden(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24189,plain,(
    ! [A_950,C_951] :
      ( m1_subset_1(k4_tarski('#skF_6'(A_950,k2_relat_1(A_950),C_951),C_951),A_950)
      | v1_xboole_0(A_950)
      | ~ r2_hidden(C_951,k2_relat_1(A_950)) ) ),
    inference(resolution,[status(thm)],[c_21721,c_18])).

tff(c_82,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(A_91,B_92)
      | ~ m1_subset_1(A_91,k1_zfmisc_1(B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_95,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_44,c_82])).

tff(c_21370,plain,(
    ! [C_736,B_737,A_738] :
      ( r2_hidden(C_736,B_737)
      | ~ r2_hidden(C_736,A_738)
      | ~ r1_tarski(A_738,B_737) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_21664,plain,(
    ! [B_796,B_797,A_798] :
      ( r2_hidden(B_796,B_797)
      | ~ r1_tarski(A_798,B_797)
      | ~ m1_subset_1(B_796,A_798)
      | v1_xboole_0(A_798) ) ),
    inference(resolution,[status(thm)],[c_20,c_21370])).

tff(c_21674,plain,(
    ! [B_796] :
      ( r2_hidden(B_796,k2_zfmisc_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(B_796,'#skF_9')
      | v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_95,c_21664])).

tff(c_21682,plain,(
    ! [B_799] :
      ( r2_hidden(B_799,k2_zfmisc_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(B_799,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_21483,c_21674])).

tff(c_16,plain,(
    ! [A_10,C_12,B_11,D_13] :
      ( r2_hidden(A_10,C_12)
      | ~ r2_hidden(k4_tarski(A_10,B_11),k2_zfmisc_1(C_12,D_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_21713,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,'#skF_8')
      | ~ m1_subset_1(k4_tarski(A_10,B_11),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_21682,c_16])).

tff(c_24208,plain,(
    ! [C_951] :
      ( r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_951),'#skF_8')
      | v1_xboole_0('#skF_9')
      | ~ r2_hidden(C_951,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_24189,c_21713])).

tff(c_32929,plain,(
    ! [C_1229] :
      ( r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_1229),'#skF_8')
      | ~ r2_hidden(C_1229,k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_21483,c_24208])).

tff(c_32940,plain,(
    ! [C_1229] :
      ( m1_subset_1('#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_1229),'#skF_8')
      | v1_xboole_0('#skF_8')
      | ~ r2_hidden(C_1229,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_32929,c_18])).

tff(c_33883,plain,(
    ! [C_1247] :
      ( m1_subset_1('#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_1247),'#skF_8')
      | ~ r2_hidden(C_1247,k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_32940])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24723,plain,(
    ! [A_969,C_970,B_971] :
      ( r2_hidden(k4_tarski('#skF_6'(A_969,k2_relat_1(A_969),C_970),C_970),B_971)
      | ~ r1_tarski(A_969,B_971)
      | ~ r2_hidden(C_970,k2_relat_1(A_969)) ) ),
    inference(resolution,[status(thm)],[c_21721,c_6])).

tff(c_21471,plain,(
    ! [E_81] :
      ( ~ r2_hidden(k4_tarski(E_81,'#skF_12'),'#skF_9')
      | ~ m1_subset_1(E_81,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_24804,plain,(
    ! [A_969] :
      ( ~ m1_subset_1('#skF_6'(A_969,k2_relat_1(A_969),'#skF_12'),'#skF_8')
      | ~ r1_tarski(A_969,'#skF_9')
      | ~ r2_hidden('#skF_12',k2_relat_1(A_969)) ) ),
    inference(resolution,[status(thm)],[c_24723,c_21471])).

tff(c_33887,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | ~ r2_hidden('#skF_12',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_33883,c_24804])).

tff(c_33897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21512,c_21365,c_33887])).

tff(c_33899,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_21482])).

tff(c_33940,plain,(
    ! [A_1258,B_1259,C_1260] :
      ( k2_relset_1(A_1258,B_1259,C_1260) = k2_relat_1(C_1260)
      | ~ m1_subset_1(C_1260,k1_zfmisc_1(k2_zfmisc_1(A_1258,B_1259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_33964,plain,(
    k2_relset_1('#skF_8','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_33940])).

tff(c_33968,plain,(
    r2_hidden('#skF_12',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33964,c_96])).

tff(c_34176,plain,(
    ! [A_1295,C_1296] :
      ( r2_hidden(k4_tarski('#skF_6'(A_1295,k2_relat_1(A_1295),C_1296),C_1296),A_1295)
      | ~ r2_hidden(C_1296,k2_relat_1(A_1295)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34212,plain,(
    ! [A_1297,C_1298] :
      ( ~ v1_xboole_0(A_1297)
      | ~ r2_hidden(C_1298,k2_relat_1(A_1297)) ) ),
    inference(resolution,[status(thm)],[c_34176,c_2])).

tff(c_34222,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_33968,c_34212])).

tff(c_34248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33899,c_34222])).

tff(c_34249,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_34264,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_34249,c_2])).

tff(c_34693,plain,(
    ! [A_1333,C_1334] :
      ( r2_hidden(k4_tarski('#skF_6'(A_1333,k2_relat_1(A_1333),C_1334),C_1334),A_1333)
      | ~ r2_hidden(C_1334,k2_relat_1(A_1333)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38073,plain,(
    ! [A_1558,C_1559] :
      ( m1_subset_1(k4_tarski('#skF_6'(A_1558,k2_relat_1(A_1558),C_1559),C_1559),A_1558)
      | v1_xboole_0(A_1558)
      | ~ r2_hidden(C_1559,k2_relat_1(A_1558)) ) ),
    inference(resolution,[status(thm)],[c_34693,c_18])).

tff(c_36529,plain,(
    ! [B_1452,B_1453,A_1454] :
      ( r2_hidden(B_1452,B_1453)
      | ~ r1_tarski(A_1454,B_1453)
      | ~ m1_subset_1(B_1452,A_1454)
      | v1_xboole_0(A_1454) ) ),
    inference(resolution,[status(thm)],[c_20,c_21370])).

tff(c_36549,plain,(
    ! [B_1452] :
      ( r2_hidden(B_1452,k2_zfmisc_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(B_1452,'#skF_9')
      | v1_xboole_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_95,c_36529])).

tff(c_36562,plain,(
    ! [B_1455] :
      ( r2_hidden(B_1455,k2_zfmisc_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(B_1455,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34264,c_36549])).

tff(c_36601,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,'#skF_8')
      | ~ m1_subset_1(k4_tarski(A_10,B_11),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36562,c_16])).

tff(c_38085,plain,(
    ! [C_1559] :
      ( r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_1559),'#skF_8')
      | v1_xboole_0('#skF_9')
      | ~ r2_hidden(C_1559,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_38073,c_36601])).

tff(c_38448,plain,(
    ! [C_1569] :
      ( r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_1569),'#skF_8')
      | ~ r2_hidden(C_1569,k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34264,c_38085])).

tff(c_38455,plain,(
    ! [C_1569] :
      ( m1_subset_1('#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_1569),'#skF_8')
      | v1_xboole_0('#skF_8')
      | ~ r2_hidden(C_1569,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_38448,c_18])).

tff(c_39004,plain,(
    ! [C_1602] :
      ( m1_subset_1('#skF_6'('#skF_9',k2_relat_1('#skF_9'),C_1602),'#skF_8')
      | ~ r2_hidden(C_1602,k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38455])).

tff(c_32,plain,(
    ! [C_33,A_18,D_36] :
      ( r2_hidden(C_33,k2_relat_1(A_18))
      | ~ r2_hidden(k4_tarski(D_36,C_33),A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34261,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_34249,c_32])).

tff(c_34292,plain,(
    ! [A_1299,B_1300,C_1301] :
      ( k2_relset_1(A_1299,B_1300,C_1301) = k2_relat_1(C_1301)
      | ~ m1_subset_1(C_1301,k1_zfmisc_1(k2_zfmisc_1(A_1299,B_1300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34316,plain,(
    k2_relset_1('#skF_8','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_34292])).

tff(c_50,plain,(
    ! [E_81] :
      ( ~ r2_hidden('#skF_10',k2_relset_1('#skF_8','#skF_7','#skF_9'))
      | ~ r2_hidden(k4_tarski(E_81,'#skF_12'),'#skF_9')
      | ~ m1_subset_1(E_81,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34265,plain,(
    ~ r2_hidden('#skF_10',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_34318,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34316,c_34265])).

tff(c_34325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34261,c_34318])).

tff(c_34326,plain,(
    ! [E_81] :
      ( ~ r2_hidden(k4_tarski(E_81,'#skF_12'),'#skF_9')
      | ~ m1_subset_1(E_81,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_34697,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_9',k2_relat_1('#skF_9'),'#skF_12'),'#skF_8')
    | ~ r2_hidden('#skF_12',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_34693,c_34326])).

tff(c_34719,plain,(
    ~ m1_subset_1('#skF_6'('#skF_9',k2_relat_1('#skF_9'),'#skF_12'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34415,c_34697])).

tff(c_39007,plain,(
    ~ r2_hidden('#skF_12',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_39004,c_34719])).

tff(c_39014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34415,c_39007])).

tff(c_39016,plain,(
    ~ r2_hidden('#skF_12',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9')
    | r2_hidden('#skF_12',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_39103,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_39016,c_58])).

tff(c_39116,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_39103,c_32])).

tff(c_39339,plain,(
    ! [A_1649,B_1650,C_1651] :
      ( k2_relset_1(A_1649,B_1650,C_1651) = k2_relat_1(C_1651)
      | ~ m1_subset_1(C_1651,k1_zfmisc_1(k2_zfmisc_1(A_1649,B_1650))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_39358,plain,(
    k2_relset_1('#skF_8','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_39339])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_10',k2_relset_1('#skF_8','#skF_7','#skF_9'))
    | r2_hidden('#skF_12',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_39176,plain,(
    ~ r2_hidden('#skF_10',k2_relset_1('#skF_8','#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_39016,c_56])).

tff(c_39359,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39358,c_39176])).

tff(c_39363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39116,c_39359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:45:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.51/7.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.51/7.95  
% 16.51/7.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.51/7.95  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_12 > #skF_4
% 16.51/7.95  
% 16.51/7.95  %Foreground sorts:
% 16.51/7.95  
% 16.51/7.95  
% 16.51/7.95  %Background operators:
% 16.51/7.95  
% 16.51/7.95  
% 16.51/7.95  %Foreground operators:
% 16.51/7.95  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 16.51/7.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.51/7.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.51/7.95  tff('#skF_11', type, '#skF_11': $i).
% 16.51/7.95  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 16.51/7.95  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.51/7.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 16.51/7.95  tff('#skF_7', type, '#skF_7': $i).
% 16.51/7.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.51/7.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.51/7.95  tff('#skF_10', type, '#skF_10': $i).
% 16.51/7.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.51/7.95  tff('#skF_9', type, '#skF_9': $i).
% 16.51/7.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.51/7.95  tff('#skF_8', type, '#skF_8': $i).
% 16.51/7.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.51/7.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.51/7.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.51/7.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.51/7.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.51/7.95  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 16.51/7.95  tff('#skF_12', type, '#skF_12': $i).
% 16.51/7.95  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 16.51/7.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.51/7.95  
% 16.51/7.97  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 16.51/7.97  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 16.51/7.97  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 16.51/7.97  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 16.51/7.97  tff(f_69, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 16.51/7.97  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.51/7.97  tff(f_44, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 16.51/7.97  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 16.51/7.97  tff(c_44, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.51/7.97  tff(c_34385, plain, (![A_1304, B_1305, C_1306]: (k2_relset_1(A_1304, B_1305, C_1306)=k2_relat_1(C_1306) | ~m1_subset_1(C_1306, k1_zfmisc_1(k2_zfmisc_1(A_1304, B_1305))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.51/7.97  tff(c_34409, plain, (k2_relset_1('#skF_8', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_44, c_34385])).
% 16.51/7.97  tff(c_60, plain, (m1_subset_1('#skF_11', '#skF_8') | r2_hidden('#skF_12', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.51/7.97  tff(c_96, plain, (r2_hidden('#skF_12', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_60])).
% 16.51/7.97  tff(c_34415, plain, (r2_hidden('#skF_12', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_34409, c_96])).
% 16.51/7.97  tff(c_46, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.51/7.97  tff(c_21484, plain, (![A_763, B_764, C_765]: (k2_relset_1(A_763, B_764, C_765)=k2_relat_1(C_765) | ~m1_subset_1(C_765, k1_zfmisc_1(k2_zfmisc_1(A_763, B_764))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.51/7.97  tff(c_21508, plain, (k2_relset_1('#skF_8', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_44, c_21484])).
% 16.51/7.97  tff(c_21512, plain, (r2_hidden('#skF_12', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_21508, c_96])).
% 16.51/7.97  tff(c_21353, plain, (![A_729, B_730]: (r2_hidden('#skF_2'(A_729, B_730), A_729) | r1_tarski(A_729, B_730))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.51/7.97  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.51/7.97  tff(c_21365, plain, (![A_729]: (r1_tarski(A_729, A_729))), inference(resolution, [status(thm)], [c_21353, c_8])).
% 16.51/7.97  tff(c_22, plain, (![B_15, A_14]: (m1_subset_1(B_15, A_14) | ~v1_xboole_0(B_15) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.51/7.97  tff(c_20, plain, (![B_15, A_14]: (r2_hidden(B_15, A_14) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.51/7.97  tff(c_52, plain, (![E_81]: (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9') | ~r2_hidden(k4_tarski(E_81, '#skF_12'), '#skF_9') | ~m1_subset_1(E_81, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.51/7.97  tff(c_21472, plain, (![E_761]: (~r2_hidden(k4_tarski(E_761, '#skF_12'), '#skF_9') | ~m1_subset_1(E_761, '#skF_8'))), inference(splitLeft, [status(thm)], [c_52])).
% 16.51/7.97  tff(c_21476, plain, (![E_761]: (~m1_subset_1(E_761, '#skF_8') | ~m1_subset_1(k4_tarski(E_761, '#skF_12'), '#skF_9') | v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_20, c_21472])).
% 16.51/7.97  tff(c_21478, plain, (![E_762]: (~m1_subset_1(E_762, '#skF_8') | ~m1_subset_1(k4_tarski(E_762, '#skF_12'), '#skF_9'))), inference(splitLeft, [status(thm)], [c_21476])).
% 16.51/7.97  tff(c_21482, plain, (![E_762]: (~m1_subset_1(E_762, '#skF_8') | ~v1_xboole_0(k4_tarski(E_762, '#skF_12')) | ~v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_22, c_21478])).
% 16.51/7.97  tff(c_21483, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_21482])).
% 16.51/7.97  tff(c_21721, plain, (![A_800, C_801]: (r2_hidden(k4_tarski('#skF_6'(A_800, k2_relat_1(A_800), C_801), C_801), A_800) | ~r2_hidden(C_801, k2_relat_1(A_800)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.51/7.97  tff(c_18, plain, (![B_15, A_14]: (m1_subset_1(B_15, A_14) | ~r2_hidden(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.51/7.97  tff(c_24189, plain, (![A_950, C_951]: (m1_subset_1(k4_tarski('#skF_6'(A_950, k2_relat_1(A_950), C_951), C_951), A_950) | v1_xboole_0(A_950) | ~r2_hidden(C_951, k2_relat_1(A_950)))), inference(resolution, [status(thm)], [c_21721, c_18])).
% 16.51/7.97  tff(c_82, plain, (![A_91, B_92]: (r1_tarski(A_91, B_92) | ~m1_subset_1(A_91, k1_zfmisc_1(B_92)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.51/7.97  tff(c_95, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_44, c_82])).
% 16.51/7.97  tff(c_21370, plain, (![C_736, B_737, A_738]: (r2_hidden(C_736, B_737) | ~r2_hidden(C_736, A_738) | ~r1_tarski(A_738, B_737))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.51/7.97  tff(c_21664, plain, (![B_796, B_797, A_798]: (r2_hidden(B_796, B_797) | ~r1_tarski(A_798, B_797) | ~m1_subset_1(B_796, A_798) | v1_xboole_0(A_798))), inference(resolution, [status(thm)], [c_20, c_21370])).
% 16.51/7.97  tff(c_21674, plain, (![B_796]: (r2_hidden(B_796, k2_zfmisc_1('#skF_8', '#skF_7')) | ~m1_subset_1(B_796, '#skF_9') | v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_95, c_21664])).
% 16.51/7.97  tff(c_21682, plain, (![B_799]: (r2_hidden(B_799, k2_zfmisc_1('#skF_8', '#skF_7')) | ~m1_subset_1(B_799, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_21483, c_21674])).
% 16.51/7.97  tff(c_16, plain, (![A_10, C_12, B_11, D_13]: (r2_hidden(A_10, C_12) | ~r2_hidden(k4_tarski(A_10, B_11), k2_zfmisc_1(C_12, D_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.51/7.97  tff(c_21713, plain, (![A_10, B_11]: (r2_hidden(A_10, '#skF_8') | ~m1_subset_1(k4_tarski(A_10, B_11), '#skF_9'))), inference(resolution, [status(thm)], [c_21682, c_16])).
% 16.51/7.97  tff(c_24208, plain, (![C_951]: (r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_951), '#skF_8') | v1_xboole_0('#skF_9') | ~r2_hidden(C_951, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_24189, c_21713])).
% 16.51/7.97  tff(c_32929, plain, (![C_1229]: (r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_1229), '#skF_8') | ~r2_hidden(C_1229, k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_21483, c_24208])).
% 16.51/7.97  tff(c_32940, plain, (![C_1229]: (m1_subset_1('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_1229), '#skF_8') | v1_xboole_0('#skF_8') | ~r2_hidden(C_1229, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_32929, c_18])).
% 16.51/7.97  tff(c_33883, plain, (![C_1247]: (m1_subset_1('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_1247), '#skF_8') | ~r2_hidden(C_1247, k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_46, c_32940])).
% 16.51/7.97  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.51/7.97  tff(c_24723, plain, (![A_969, C_970, B_971]: (r2_hidden(k4_tarski('#skF_6'(A_969, k2_relat_1(A_969), C_970), C_970), B_971) | ~r1_tarski(A_969, B_971) | ~r2_hidden(C_970, k2_relat_1(A_969)))), inference(resolution, [status(thm)], [c_21721, c_6])).
% 16.51/7.97  tff(c_21471, plain, (![E_81]: (~r2_hidden(k4_tarski(E_81, '#skF_12'), '#skF_9') | ~m1_subset_1(E_81, '#skF_8'))), inference(splitLeft, [status(thm)], [c_52])).
% 16.51/7.97  tff(c_24804, plain, (![A_969]: (~m1_subset_1('#skF_6'(A_969, k2_relat_1(A_969), '#skF_12'), '#skF_8') | ~r1_tarski(A_969, '#skF_9') | ~r2_hidden('#skF_12', k2_relat_1(A_969)))), inference(resolution, [status(thm)], [c_24723, c_21471])).
% 16.51/7.97  tff(c_33887, plain, (~r1_tarski('#skF_9', '#skF_9') | ~r2_hidden('#skF_12', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_33883, c_24804])).
% 16.51/7.97  tff(c_33897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21512, c_21365, c_33887])).
% 16.51/7.97  tff(c_33899, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_21482])).
% 16.51/7.97  tff(c_33940, plain, (![A_1258, B_1259, C_1260]: (k2_relset_1(A_1258, B_1259, C_1260)=k2_relat_1(C_1260) | ~m1_subset_1(C_1260, k1_zfmisc_1(k2_zfmisc_1(A_1258, B_1259))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.51/7.97  tff(c_33964, plain, (k2_relset_1('#skF_8', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_44, c_33940])).
% 16.51/7.97  tff(c_33968, plain, (r2_hidden('#skF_12', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_33964, c_96])).
% 16.51/7.97  tff(c_34176, plain, (![A_1295, C_1296]: (r2_hidden(k4_tarski('#skF_6'(A_1295, k2_relat_1(A_1295), C_1296), C_1296), A_1295) | ~r2_hidden(C_1296, k2_relat_1(A_1295)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.51/7.97  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.51/7.97  tff(c_34212, plain, (![A_1297, C_1298]: (~v1_xboole_0(A_1297) | ~r2_hidden(C_1298, k2_relat_1(A_1297)))), inference(resolution, [status(thm)], [c_34176, c_2])).
% 16.51/7.97  tff(c_34222, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_33968, c_34212])).
% 16.51/7.97  tff(c_34248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33899, c_34222])).
% 16.51/7.97  tff(c_34249, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_52])).
% 16.51/7.97  tff(c_34264, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_34249, c_2])).
% 16.51/7.97  tff(c_34693, plain, (![A_1333, C_1334]: (r2_hidden(k4_tarski('#skF_6'(A_1333, k2_relat_1(A_1333), C_1334), C_1334), A_1333) | ~r2_hidden(C_1334, k2_relat_1(A_1333)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.51/7.97  tff(c_38073, plain, (![A_1558, C_1559]: (m1_subset_1(k4_tarski('#skF_6'(A_1558, k2_relat_1(A_1558), C_1559), C_1559), A_1558) | v1_xboole_0(A_1558) | ~r2_hidden(C_1559, k2_relat_1(A_1558)))), inference(resolution, [status(thm)], [c_34693, c_18])).
% 16.51/7.97  tff(c_36529, plain, (![B_1452, B_1453, A_1454]: (r2_hidden(B_1452, B_1453) | ~r1_tarski(A_1454, B_1453) | ~m1_subset_1(B_1452, A_1454) | v1_xboole_0(A_1454))), inference(resolution, [status(thm)], [c_20, c_21370])).
% 16.51/7.97  tff(c_36549, plain, (![B_1452]: (r2_hidden(B_1452, k2_zfmisc_1('#skF_8', '#skF_7')) | ~m1_subset_1(B_1452, '#skF_9') | v1_xboole_0('#skF_9'))), inference(resolution, [status(thm)], [c_95, c_36529])).
% 16.51/7.97  tff(c_36562, plain, (![B_1455]: (r2_hidden(B_1455, k2_zfmisc_1('#skF_8', '#skF_7')) | ~m1_subset_1(B_1455, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_34264, c_36549])).
% 16.51/7.97  tff(c_36601, plain, (![A_10, B_11]: (r2_hidden(A_10, '#skF_8') | ~m1_subset_1(k4_tarski(A_10, B_11), '#skF_9'))), inference(resolution, [status(thm)], [c_36562, c_16])).
% 16.51/7.97  tff(c_38085, plain, (![C_1559]: (r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_1559), '#skF_8') | v1_xboole_0('#skF_9') | ~r2_hidden(C_1559, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_38073, c_36601])).
% 16.51/7.97  tff(c_38448, plain, (![C_1569]: (r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_1569), '#skF_8') | ~r2_hidden(C_1569, k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_34264, c_38085])).
% 16.51/7.97  tff(c_38455, plain, (![C_1569]: (m1_subset_1('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_1569), '#skF_8') | v1_xboole_0('#skF_8') | ~r2_hidden(C_1569, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_38448, c_18])).
% 16.51/7.97  tff(c_39004, plain, (![C_1602]: (m1_subset_1('#skF_6'('#skF_9', k2_relat_1('#skF_9'), C_1602), '#skF_8') | ~r2_hidden(C_1602, k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_46, c_38455])).
% 16.51/7.97  tff(c_32, plain, (![C_33, A_18, D_36]: (r2_hidden(C_33, k2_relat_1(A_18)) | ~r2_hidden(k4_tarski(D_36, C_33), A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.51/7.97  tff(c_34261, plain, (r2_hidden('#skF_10', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_34249, c_32])).
% 16.51/7.97  tff(c_34292, plain, (![A_1299, B_1300, C_1301]: (k2_relset_1(A_1299, B_1300, C_1301)=k2_relat_1(C_1301) | ~m1_subset_1(C_1301, k1_zfmisc_1(k2_zfmisc_1(A_1299, B_1300))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.51/7.97  tff(c_34316, plain, (k2_relset_1('#skF_8', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_44, c_34292])).
% 16.51/7.97  tff(c_50, plain, (![E_81]: (~r2_hidden('#skF_10', k2_relset_1('#skF_8', '#skF_7', '#skF_9')) | ~r2_hidden(k4_tarski(E_81, '#skF_12'), '#skF_9') | ~m1_subset_1(E_81, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.51/7.97  tff(c_34265, plain, (~r2_hidden('#skF_10', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_50])).
% 16.51/7.97  tff(c_34318, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_34316, c_34265])).
% 16.51/7.97  tff(c_34325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34261, c_34318])).
% 16.51/7.97  tff(c_34326, plain, (![E_81]: (~r2_hidden(k4_tarski(E_81, '#skF_12'), '#skF_9') | ~m1_subset_1(E_81, '#skF_8'))), inference(splitRight, [status(thm)], [c_50])).
% 16.51/7.97  tff(c_34697, plain, (~m1_subset_1('#skF_6'('#skF_9', k2_relat_1('#skF_9'), '#skF_12'), '#skF_8') | ~r2_hidden('#skF_12', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_34693, c_34326])).
% 16.51/7.97  tff(c_34719, plain, (~m1_subset_1('#skF_6'('#skF_9', k2_relat_1('#skF_9'), '#skF_12'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34415, c_34697])).
% 16.51/7.97  tff(c_39007, plain, (~r2_hidden('#skF_12', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_39004, c_34719])).
% 16.51/7.97  tff(c_39014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34415, c_39007])).
% 16.51/7.97  tff(c_39016, plain, (~r2_hidden('#skF_12', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_60])).
% 16.51/7.97  tff(c_58, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9') | r2_hidden('#skF_12', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.51/7.97  tff(c_39103, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_39016, c_58])).
% 16.51/7.97  tff(c_39116, plain, (r2_hidden('#skF_10', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_39103, c_32])).
% 16.51/7.97  tff(c_39339, plain, (![A_1649, B_1650, C_1651]: (k2_relset_1(A_1649, B_1650, C_1651)=k2_relat_1(C_1651) | ~m1_subset_1(C_1651, k1_zfmisc_1(k2_zfmisc_1(A_1649, B_1650))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.51/7.97  tff(c_39358, plain, (k2_relset_1('#skF_8', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_44, c_39339])).
% 16.51/7.97  tff(c_56, plain, (~r2_hidden('#skF_10', k2_relset_1('#skF_8', '#skF_7', '#skF_9')) | r2_hidden('#skF_12', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.51/7.97  tff(c_39176, plain, (~r2_hidden('#skF_10', k2_relset_1('#skF_8', '#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_39016, c_56])).
% 16.51/7.97  tff(c_39359, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_39358, c_39176])).
% 16.51/7.97  tff(c_39363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39116, c_39359])).
% 16.51/7.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.51/7.97  
% 16.51/7.97  Inference rules
% 16.51/7.97  ----------------------
% 16.51/7.97  #Ref     : 0
% 16.51/7.97  #Sup     : 10933
% 16.51/7.97  #Fact    : 0
% 16.51/7.97  #Define  : 0
% 16.51/7.97  #Split   : 36
% 16.51/7.97  #Chain   : 0
% 16.51/7.97  #Close   : 0
% 16.51/7.97  
% 16.51/7.97  Ordering : KBO
% 16.51/7.97  
% 16.51/7.97  Simplification rules
% 16.51/7.97  ----------------------
% 16.51/7.97  #Subsume      : 4497
% 16.51/7.97  #Demod        : 150
% 16.51/7.97  #Tautology    : 257
% 16.51/7.97  #SimpNegUnit  : 147
% 16.51/7.97  #BackRed      : 30
% 16.51/7.97  
% 16.51/7.97  #Partial instantiations: 0
% 16.51/7.97  #Strategies tried      : 1
% 16.51/7.97  
% 16.51/7.97  Timing (in seconds)
% 16.51/7.97  ----------------------
% 16.51/7.97  Preprocessing        : 0.32
% 16.51/7.97  Parsing              : 0.16
% 16.51/7.97  CNF conversion       : 0.03
% 16.51/7.97  Main loop            : 6.88
% 16.51/7.97  Inferencing          : 1.23
% 16.51/7.97  Reduction            : 1.08
% 16.51/7.97  Demodulation         : 0.68
% 16.51/7.97  BG Simplification    : 0.14
% 16.51/7.97  Subsumption          : 4.01
% 16.51/7.97  Abstraction          : 0.22
% 16.51/7.97  MUC search           : 0.00
% 16.51/7.97  Cooper               : 0.00
% 16.51/7.97  Total                : 7.25
% 16.51/7.97  Index Insertion      : 0.00
% 16.51/7.97  Index Deletion       : 0.00
% 16.51/7.97  Index Matching       : 0.00
% 16.51/7.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
