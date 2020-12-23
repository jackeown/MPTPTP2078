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
% DateTime   : Thu Dec  3 09:53:42 EST 2020

% Result     : Theorem 6.25s
% Output     : CNFRefutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :  283 (2841 expanded)
%              Number of leaves         :   24 ( 852 expanded)
%              Depth                    :   14
%              Number of atoms          :  401 (6556 expanded)
%              Number of equality atoms :  161 (4523 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_65,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5488,plain,(
    ! [A_3367,B_3368,C_3369] :
      ( r2_hidden('#skF_1'(A_3367,B_3368,C_3369),A_3367)
      | r2_hidden('#skF_2'(A_3367,B_3368,C_3369),C_3369)
      | k4_xboole_0(A_3367,B_3368) = C_3369 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [E_40,F_41,A_8,B_9] :
      ( r2_hidden(k4_tarski(E_40,F_41),k2_zfmisc_1(A_8,B_9))
      | ~ r2_hidden(F_41,B_9)
      | ~ r2_hidden(E_40,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_8,B_9,D_35] :
      ( r2_hidden('#skF_8'(A_8,B_9,k2_zfmisc_1(A_8,B_9),D_35),B_9)
      | ~ r2_hidden(D_35,k2_zfmisc_1(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3060,plain,(
    ! [A_2463,B_2464,D_2465] :
      ( r2_hidden('#skF_8'(A_2463,B_2464,k2_zfmisc_1(A_2463,B_2464),D_2465),B_2464)
      | ~ r2_hidden(D_2465,k2_zfmisc_1(A_2463,B_2464)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,(
    ! [D_43,B_44,A_45] :
      ( ~ r2_hidden(D_43,B_44)
      | ~ r2_hidden(D_43,k4_xboole_0(A_45,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [D_43,A_7] :
      ( ~ r2_hidden(D_43,A_7)
      | ~ r2_hidden(D_43,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_66])).

tff(c_3251,plain,(
    ! [A_2513,B_2514,D_2515] :
      ( ~ r2_hidden('#skF_8'(A_2513,B_2514,k2_zfmisc_1(A_2513,B_2514),D_2515),k1_xboole_0)
      | ~ r2_hidden(D_2515,k2_zfmisc_1(A_2513,B_2514)) ) ),
    inference(resolution,[status(thm)],[c_3060,c_69])).

tff(c_3265,plain,(
    ! [D_2516,A_2517] : ~ r2_hidden(D_2516,k2_zfmisc_1(A_2517,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_26,c_3251])).

tff(c_3280,plain,(
    ! [F_41,E_40,A_8] :
      ( ~ r2_hidden(F_41,k1_xboole_0)
      | ~ r2_hidden(E_40,A_8) ) ),
    inference(resolution,[status(thm)],[c_22,c_3265])).

tff(c_3295,plain,(
    ! [E_40,A_8] : ~ r2_hidden(E_40,A_8) ),
    inference(splitLeft,[status(thm)],[c_3280])).

tff(c_42,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_5'(A_8,B_9,C_10),B_9)
      | r2_hidden('#skF_6'(A_8,B_9,C_10),C_10)
      | k2_zfmisc_1(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3330,plain,(
    ! [A_2524,B_2525] : k2_zfmisc_1(A_2524,B_2525) = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_3295,c_3295,c_42])).

tff(c_3314,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(A_8,B_9) = C_10 ),
    inference(negUnitSimplification,[status(thm)],[c_3295,c_3295,c_42])).

tff(c_3479,plain,(
    ! [C_2944] : C_2944 = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_3330,c_3314])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_3507,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3479,c_64])).

tff(c_3508,plain,(
    ! [F_41] : ~ r2_hidden(F_41,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3280])).

tff(c_5584,plain,(
    ! [B_3368,C_3369] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_3368,C_3369),C_3369)
      | k4_xboole_0(k1_xboole_0,B_3368) = C_3369 ) ),
    inference(resolution,[status(thm)],[c_5488,c_3508])).

tff(c_5771,plain,(
    ! [B_3370,C_3371] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_3370,C_3371),C_3371)
      | k1_xboole_0 = C_3371 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5584])).

tff(c_4206,plain,(
    ! [A_3292,B_3293,C_3294] :
      ( r2_hidden('#skF_1'(A_3292,B_3293,C_3294),A_3292)
      | r2_hidden('#skF_2'(A_3292,B_3293,C_3294),C_3294)
      | k4_xboole_0(A_3292,B_3293) = C_3294 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4290,plain,(
    ! [B_3293,C_3294] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_3293,C_3294),C_3294)
      | k4_xboole_0(k1_xboole_0,B_3293) = C_3294 ) ),
    inference(resolution,[status(thm)],[c_4206,c_3508])).

tff(c_4448,plain,(
    ! [B_3295,C_3296] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_3295,C_3296),C_3296)
      | k1_xboole_0 = C_3296 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4290])).

tff(c_1189,plain,(
    ! [A_721,B_722,C_723] :
      ( r2_hidden('#skF_1'(A_721,B_722,C_723),A_721)
      | r2_hidden('#skF_2'(A_721,B_722,C_723),C_723)
      | k4_xboole_0(A_721,B_722) = C_723 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_128,plain,(
    ! [A_76,B_77,D_78] :
      ( r2_hidden('#skF_8'(A_76,B_77,k2_zfmisc_1(A_76,B_77),D_78),B_77)
      | ~ r2_hidden(D_78,k2_zfmisc_1(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_222,plain,(
    ! [A_92,B_93,D_94] :
      ( ~ r2_hidden('#skF_8'(A_92,B_93,k2_zfmisc_1(A_92,B_93),D_94),k1_xboole_0)
      | ~ r2_hidden(D_94,k2_zfmisc_1(A_92,B_93)) ) ),
    inference(resolution,[status(thm)],[c_128,c_69])).

tff(c_238,plain,(
    ! [D_98,A_99] : ~ r2_hidden(D_98,k2_zfmisc_1(A_99,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_26,c_222])).

tff(c_253,plain,(
    ! [F_41,E_40,A_8] :
      ( ~ r2_hidden(F_41,k1_xboole_0)
      | ~ r2_hidden(E_40,A_8) ) ),
    inference(resolution,[status(thm)],[c_22,c_238])).

tff(c_254,plain,(
    ! [E_40,A_8] : ~ r2_hidden(E_40,A_8) ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_286,plain,(
    ! [A_102,B_103] : k2_zfmisc_1(A_102,B_103) = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_254,c_42])).

tff(c_270,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(A_8,B_9) = C_10 ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_254,c_42])).

tff(c_410,plain,(
    ! [C_372] : C_372 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_270])).

tff(c_428,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_65])).

tff(c_429,plain,(
    ! [F_41] : ~ r2_hidden(F_41,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_1221,plain,(
    ! [B_722,C_723] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_722,C_723),C_723)
      | k4_xboole_0(k1_xboole_0,B_722) = C_723 ) ),
    inference(resolution,[status(thm)],[c_1189,c_429])).

tff(c_1441,plain,(
    ! [B_739,C_740] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_739,C_740),C_740)
      | k1_xboole_0 = C_740 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1221])).

tff(c_819,plain,(
    ! [A_700,B_701,C_702] :
      ( r2_hidden('#skF_1'(A_700,B_701,C_702),A_700)
      | r2_hidden('#skF_2'(A_700,B_701,C_702),C_702)
      | k4_xboole_0(A_700,B_701) = C_702 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_875,plain,(
    ! [B_701,C_702] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_701,C_702),C_702)
      | k4_xboole_0(k1_xboole_0,B_701) = C_702 ) ),
    inference(resolution,[status(thm)],[c_819,c_429])).

tff(c_990,plain,(
    ! [B_703,C_704] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_703,C_704),C_704)
      | k1_xboole_0 = C_704 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_875])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_72,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_96,plain,(
    ! [E_54,F_55,A_56,B_57] :
      ( r2_hidden(k4_tarski(E_54,F_55),k2_zfmisc_1(A_56,B_57))
      | ~ r2_hidden(F_55,B_57)
      | ~ r2_hidden(E_54,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [E_54,F_55] :
      ( r2_hidden(k4_tarski(E_54,F_55),k1_xboole_0)
      | ~ r2_hidden(F_55,'#skF_12')
      | ~ r2_hidden(E_54,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_96])).

tff(c_430,plain,(
    ! [F_55,E_54] :
      ( ~ r2_hidden(F_55,'#skF_12')
      | ~ r2_hidden(E_54,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_429,c_101])).

tff(c_442,plain,(
    ! [E_54] : ~ r2_hidden(E_54,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_1042,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_990,c_442])).

tff(c_1074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1042])).

tff(c_1075,plain,(
    ! [F_55] : ~ r2_hidden(F_55,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_1489,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1441,c_1075])).

tff(c_1525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_1489])).

tff(c_1526,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1528,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1526])).

tff(c_1532,plain,(
    '#skF_11' != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_64])).

tff(c_1533,plain,(
    ! [A_7] : k4_xboole_0('#skF_10',A_7) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1528,c_20])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_8,B_9,D_35] :
      ( r2_hidden('#skF_7'(A_8,B_9,k2_zfmisc_1(A_8,B_9),D_35),A_8)
      | ~ r2_hidden(D_35,k2_zfmisc_1(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1575,plain,(
    ! [A_761,B_762,D_763] :
      ( r2_hidden('#skF_7'(A_761,B_762,k2_zfmisc_1(A_761,B_762),D_763),A_761)
      | ~ r2_hidden(D_763,k2_zfmisc_1(A_761,B_762)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1538,plain,(
    ! [A_741] : k4_xboole_0('#skF_10',A_741) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1528,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1543,plain,(
    ! [D_6,A_741] :
      ( ~ r2_hidden(D_6,A_741)
      | ~ r2_hidden(D_6,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1538,c_4])).

tff(c_1644,plain,(
    ! [A_770,B_771,D_772] :
      ( ~ r2_hidden('#skF_7'(A_770,B_771,k2_zfmisc_1(A_770,B_771),D_772),'#skF_10')
      | ~ r2_hidden(D_772,k2_zfmisc_1(A_770,B_771)) ) ),
    inference(resolution,[status(thm)],[c_1575,c_1543])).

tff(c_1650,plain,(
    ! [D_773,B_774] : ~ r2_hidden(D_773,k2_zfmisc_1('#skF_10',B_774)) ),
    inference(resolution,[status(thm)],[c_28,c_1644])).

tff(c_1675,plain,(
    ! [F_41,B_9,E_40] :
      ( ~ r2_hidden(F_41,B_9)
      | ~ r2_hidden(E_40,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_22,c_1650])).

tff(c_1677,plain,(
    ! [E_775] : ~ r2_hidden(E_775,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1675])).

tff(c_1681,plain,(
    ! [B_2,C_3] :
      ( r2_hidden('#skF_2'('#skF_10',B_2,C_3),C_3)
      | k4_xboole_0('#skF_10',B_2) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_1677])).

tff(c_1923,plain,(
    ! [B_796,C_797] :
      ( r2_hidden('#skF_2'('#skF_10',B_796,C_797),C_797)
      | C_797 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1533,c_1681])).

tff(c_1694,plain,(
    ! [D_35,A_8] : ~ r2_hidden(D_35,k2_zfmisc_1(A_8,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_26,c_1677])).

tff(c_1964,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1923,c_1694])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_71,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_1529,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_71])).

tff(c_1975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1964,c_1529])).

tff(c_1976,plain,(
    ! [F_41,B_9] : ~ r2_hidden(F_41,B_9) ),
    inference(splitRight,[status(thm)],[c_1675])).

tff(c_1996,plain,(
    ! [A_800,B_801] : k4_xboole_0(A_800,B_801) = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_1976,c_1976,c_18])).

tff(c_1977,plain,(
    ! [A_1,B_2,C_3] : k4_xboole_0(A_1,B_2) = C_3 ),
    inference(negUnitSimplification,[status(thm)],[c_1976,c_1976,c_18])).

tff(c_2264,plain,(
    ! [C_1382] : C_1382 = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_1996,c_1977])).

tff(c_2285,plain,(
    '#skF_11' = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_2264,c_1528])).

tff(c_2296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1532,c_2285])).

tff(c_2297,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1526])).

tff(c_2304,plain,(
    ! [A_7] : k4_xboole_0('#skF_9',A_7) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2297,c_2297,c_20])).

tff(c_2346,plain,(
    ! [A_1787,B_1788,D_1789] :
      ( r2_hidden('#skF_7'(A_1787,B_1788,k2_zfmisc_1(A_1787,B_1788),D_1789),A_1787)
      | ~ r2_hidden(D_1789,k2_zfmisc_1(A_1787,B_1788)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2301,plain,(
    ! [D_43,A_7] :
      ( ~ r2_hidden(D_43,A_7)
      | ~ r2_hidden(D_43,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2297,c_69])).

tff(c_2382,plain,(
    ! [A_1793,B_1794,D_1795] :
      ( ~ r2_hidden('#skF_7'(A_1793,B_1794,k2_zfmisc_1(A_1793,B_1794),D_1795),'#skF_9')
      | ~ r2_hidden(D_1795,k2_zfmisc_1(A_1793,B_1794)) ) ),
    inference(resolution,[status(thm)],[c_2346,c_2301])).

tff(c_2421,plain,(
    ! [D_1799,B_1800] : ~ r2_hidden(D_1799,k2_zfmisc_1('#skF_9',B_1800)) ),
    inference(resolution,[status(thm)],[c_28,c_2382])).

tff(c_2446,plain,(
    ! [F_41,B_9,E_40] :
      ( ~ r2_hidden(F_41,B_9)
      | ~ r2_hidden(E_40,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_22,c_2421])).

tff(c_2448,plain,(
    ! [E_1801] : ~ r2_hidden(E_1801,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2446])).

tff(c_2452,plain,(
    ! [B_2,C_3] :
      ( r2_hidden('#skF_2'('#skF_9',B_2,C_3),C_3)
      | k4_xboole_0('#skF_9',B_2) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_2448])).

tff(c_2731,plain,(
    ! [B_1822,C_1823] :
      ( r2_hidden('#skF_2'('#skF_9',B_1822,C_1823),C_1823)
      | C_1823 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2304,c_2452])).

tff(c_2387,plain,(
    ! [D_35,B_9] : ~ r2_hidden(D_35,k2_zfmisc_1('#skF_9',B_9)) ),
    inference(resolution,[status(thm)],[c_28,c_2382])).

tff(c_2775,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_9',B_9) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2731,c_2387])).

tff(c_2300,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2297,c_71])).

tff(c_2820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2775,c_2300])).

tff(c_2821,plain,(
    ! [F_41,B_9] : ~ r2_hidden(F_41,B_9) ),
    inference(splitRight,[status(thm)],[c_2446])).

tff(c_2859,plain,(
    ! [A_1830,B_1831] : k4_xboole_0(A_1830,B_1831) = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_2821,c_2821,c_18])).

tff(c_2832,plain,(
    ! [A_1,B_2,C_3] : k4_xboole_0(A_1,B_2) = C_3 ),
    inference(negUnitSimplification,[status(thm)],[c_2821,c_2821,c_18])).

tff(c_2973,plain,(
    ! [C_2121] : C_2121 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_2859,c_2832])).

tff(c_2997,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2973,c_2300])).

tff(c_2998,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3029,plain,(
    ! [E_2451,F_2452,A_2453,B_2454] :
      ( r2_hidden(k4_tarski(E_2451,F_2452),k2_zfmisc_1(A_2453,B_2454))
      | ~ r2_hidden(F_2452,B_2454)
      | ~ r2_hidden(E_2451,A_2453) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3037,plain,(
    ! [E_2451,F_2452] :
      ( r2_hidden(k4_tarski(E_2451,F_2452),k1_xboole_0)
      | ~ r2_hidden(F_2452,'#skF_12')
      | ~ r2_hidden(E_2451,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2998,c_3029])).

tff(c_3509,plain,(
    ! [F_2452,E_2451] :
      ( ~ r2_hidden(F_2452,'#skF_12')
      | ~ r2_hidden(E_2451,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3508,c_3037])).

tff(c_3522,plain,(
    ! [E_2451] : ~ r2_hidden(E_2451,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_3509])).

tff(c_4528,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_4448,c_3522])).

tff(c_4567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4528])).

tff(c_4568,plain,(
    ! [F_2452] : ~ r2_hidden(F_2452,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_3509])).

tff(c_5863,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_5771,c_4568])).

tff(c_5910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_5863])).

tff(c_5912,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_5914,plain,(
    ! [A_7] : k4_xboole_0('#skF_12',A_7) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5912,c_5912,c_20])).

tff(c_7275,plain,(
    ! [A_3998,B_3999,C_4000] :
      ( r2_hidden('#skF_1'(A_3998,B_3999,C_4000),A_3998)
      | r2_hidden('#skF_2'(A_3998,B_3999,C_4000),C_4000)
      | k4_xboole_0(A_3998,B_3999) = C_4000 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7114,plain,(
    ! [A_3975,B_3976,D_3977] :
      ( r2_hidden('#skF_7'(A_3975,B_3976,k2_zfmisc_1(A_3975,B_3976),D_3977),A_3975)
      | ~ r2_hidden(D_3977,k2_zfmisc_1(A_3975,B_3976)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7088,plain,(
    ! [D_3956,B_3957,A_3958] :
      ( ~ r2_hidden(D_3956,B_3957)
      | ~ r2_hidden(D_3956,k4_xboole_0(A_3958,B_3957)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7091,plain,(
    ! [D_3956,A_7] :
      ( ~ r2_hidden(D_3956,A_7)
      | ~ r2_hidden(D_3956,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5914,c_7088])).

tff(c_7150,plain,(
    ! [A_3981,B_3982,D_3983] :
      ( ~ r2_hidden('#skF_7'(A_3981,B_3982,k2_zfmisc_1(A_3981,B_3982),D_3983),'#skF_12')
      | ~ r2_hidden(D_3983,k2_zfmisc_1(A_3981,B_3982)) ) ),
    inference(resolution,[status(thm)],[c_7114,c_7091])).

tff(c_7156,plain,(
    ! [D_3984,B_3985] : ~ r2_hidden(D_3984,k2_zfmisc_1('#skF_12',B_3985)) ),
    inference(resolution,[status(thm)],[c_28,c_7150])).

tff(c_7171,plain,(
    ! [F_41,B_9,E_40] :
      ( ~ r2_hidden(F_41,B_9)
      | ~ r2_hidden(E_40,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_22,c_7156])).

tff(c_7195,plain,(
    ! [E_40] : ~ r2_hidden(E_40,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_7171])).

tff(c_7291,plain,(
    ! [B_3999,C_4000] :
      ( r2_hidden('#skF_2'('#skF_12',B_3999,C_4000),C_4000)
      | k4_xboole_0('#skF_12',B_3999) = C_4000 ) ),
    inference(resolution,[status(thm)],[c_7275,c_7195])).

tff(c_7406,plain,(
    ! [B_4007,C_4008] :
      ( r2_hidden('#skF_2'('#skF_12',B_4007,C_4008),C_4008)
      | C_4008 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5914,c_7291])).

tff(c_7155,plain,(
    ! [D_35,B_9] : ~ r2_hidden(D_35,k2_zfmisc_1('#skF_12',B_9)) ),
    inference(resolution,[status(thm)],[c_28,c_7150])).

tff(c_7450,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_12',B_9) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_7406,c_7155])).

tff(c_6650,plain,(
    ! [A_3461,B_3462,C_3463] :
      ( r2_hidden('#skF_1'(A_3461,B_3462,C_3463),A_3461)
      | r2_hidden('#skF_2'(A_3461,B_3462,C_3463),C_3463)
      | k4_xboole_0(A_3461,B_3462) = C_3463 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5967,plain,(
    ! [A_3395,B_3396,D_3397] :
      ( r2_hidden('#skF_7'(A_3395,B_3396,k2_zfmisc_1(A_3395,B_3396),D_3397),A_3395)
      | ~ r2_hidden(D_3397,k2_zfmisc_1(A_3395,B_3396)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5935,plain,(
    ! [D_3373,B_3374,A_3375] :
      ( ~ r2_hidden(D_3373,B_3374)
      | ~ r2_hidden(D_3373,k4_xboole_0(A_3375,B_3374)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5938,plain,(
    ! [D_3373,A_7] :
      ( ~ r2_hidden(D_3373,A_7)
      | ~ r2_hidden(D_3373,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5914,c_5935])).

tff(c_6035,plain,(
    ! [A_3404,B_3405,D_3406] :
      ( ~ r2_hidden('#skF_7'(A_3404,B_3405,k2_zfmisc_1(A_3404,B_3405),D_3406),'#skF_12')
      | ~ r2_hidden(D_3406,k2_zfmisc_1(A_3404,B_3405)) ) ),
    inference(resolution,[status(thm)],[c_5967,c_5938])).

tff(c_6041,plain,(
    ! [D_3407,B_3408] : ~ r2_hidden(D_3407,k2_zfmisc_1('#skF_12',B_3408)) ),
    inference(resolution,[status(thm)],[c_28,c_6035])).

tff(c_6066,plain,(
    ! [F_41,B_9,E_40] :
      ( ~ r2_hidden(F_41,B_9)
      | ~ r2_hidden(E_40,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_22,c_6041])).

tff(c_6067,plain,(
    ! [E_40] : ~ r2_hidden(E_40,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_6066])).

tff(c_6706,plain,(
    ! [B_3462,C_3463] :
      ( r2_hidden('#skF_2'('#skF_12',B_3462,C_3463),C_3463)
      | k4_xboole_0('#skF_12',B_3462) = C_3463 ) ),
    inference(resolution,[status(thm)],[c_6650,c_6067])).

tff(c_6814,plain,(
    ! [B_3464,C_3465] :
      ( r2_hidden('#skF_2'('#skF_12',B_3464,C_3465),C_3465)
      | C_3465 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5914,c_6706])).

tff(c_6091,plain,(
    ! [E_3412] : ~ r2_hidden(E_3412,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_6066])).

tff(c_6112,plain,(
    ! [D_35,A_8] : ~ r2_hidden(D_35,k2_zfmisc_1(A_8,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_26,c_6091])).

tff(c_6890,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6814,c_6112])).

tff(c_5911,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_5920,plain,
    ( '#skF_9' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5912,c_5912,c_5911])).

tff(c_5921,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_5920])).

tff(c_46,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5934,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5912,c_5921,c_5912,c_46])).

tff(c_6904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6890,c_5934])).

tff(c_6905,plain,(
    ! [F_41,B_9] : ~ r2_hidden(F_41,B_9) ),
    inference(splitRight,[status(thm)],[c_6066])).

tff(c_44,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_4'(A_8,B_9,C_10),A_8)
      | r2_hidden('#skF_6'(A_8,B_9,C_10),C_10)
      | k2_zfmisc_1(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6922,plain,(
    ! [A_3468,B_3469] : k2_zfmisc_1(A_3468,B_3469) = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_6905,c_6905,c_44])).

tff(c_6906,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(A_8,B_9) = C_10 ),
    inference(negUnitSimplification,[status(thm)],[c_6905,c_6905,c_44])).

tff(c_7054,plain,(
    ! [C_3727] : C_3727 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_6922,c_6906])).

tff(c_7065,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_7054,c_5934])).

tff(c_7066,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_5920])).

tff(c_7080,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5912,c_7066,c_5912,c_46])).

tff(c_7583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7450,c_7080])).

tff(c_7584,plain,(
    ! [F_41,B_9] : ~ r2_hidden(F_41,B_9) ),
    inference(splitRight,[status(thm)],[c_7171])).

tff(c_7633,plain,(
    ! [A_4015,B_4016] : k4_xboole_0(A_4015,B_4016) = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_7584,c_7584,c_18])).

tff(c_7593,plain,(
    ! [A_1,B_2,C_3] : k4_xboole_0(A_1,B_2) = C_3 ),
    inference(negUnitSimplification,[status(thm)],[c_7584,c_7584,c_18])).

tff(c_7756,plain,(
    ! [C_4563] : C_4563 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_7633,c_7593])).

tff(c_7771,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_7756,c_7080])).

tff(c_7773,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_7772,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_7781,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7773,c_7773,c_7772])).

tff(c_7782,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_7781])).

tff(c_7774,plain,(
    ! [A_7] : k4_xboole_0('#skF_11',A_7) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7773,c_7773,c_20])).

tff(c_7793,plain,(
    ! [A_7] : k4_xboole_0('#skF_10',A_7) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7782,c_7782,c_7774])).

tff(c_8087,plain,(
    ! [A_5442,B_5443,C_5444] :
      ( r2_hidden('#skF_1'(A_5442,B_5443,C_5444),A_5442)
      | r2_hidden('#skF_2'(A_5442,B_5443,C_5444),C_5444)
      | k4_xboole_0(A_5442,B_5443) = C_5444 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7836,plain,(
    ! [A_4907,B_4908,D_4909] :
      ( r2_hidden('#skF_8'(A_4907,B_4908,k2_zfmisc_1(A_4907,B_4908),D_4909),B_4908)
      | ~ r2_hidden(D_4909,k2_zfmisc_1(A_4907,B_4908)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7810,plain,(
    ! [D_4888,B_4889,A_4890] :
      ( ~ r2_hidden(D_4888,B_4889)
      | ~ r2_hidden(D_4888,k4_xboole_0(A_4890,B_4889)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7813,plain,(
    ! [D_4888,A_7] :
      ( ~ r2_hidden(D_4888,A_7)
      | ~ r2_hidden(D_4888,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7793,c_7810])).

tff(c_7877,plain,(
    ! [A_4916,B_4917,D_4918] :
      ( ~ r2_hidden('#skF_8'(A_4916,B_4917,k2_zfmisc_1(A_4916,B_4917),D_4918),'#skF_10')
      | ~ r2_hidden(D_4918,k2_zfmisc_1(A_4916,B_4917)) ) ),
    inference(resolution,[status(thm)],[c_7836,c_7813])).

tff(c_7883,plain,(
    ! [D_4919,A_4920] : ~ r2_hidden(D_4919,k2_zfmisc_1(A_4920,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_26,c_7877])).

tff(c_7898,plain,(
    ! [F_41,E_40,A_8] :
      ( ~ r2_hidden(F_41,'#skF_10')
      | ~ r2_hidden(E_40,A_8) ) ),
    inference(resolution,[status(thm)],[c_22,c_7883])).

tff(c_7899,plain,(
    ! [E_40,A_8] : ~ r2_hidden(E_40,A_8) ),
    inference(splitLeft,[status(thm)],[c_7898])).

tff(c_7912,plain,(
    ! [A_4923,B_4924] : k4_xboole_0(A_4923,B_4924) = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_7899,c_7899,c_18])).

tff(c_7908,plain,(
    ! [A_1,B_2,C_3] : k4_xboole_0(A_1,B_2) = C_3 ),
    inference(negUnitSimplification,[status(thm)],[c_7899,c_7899,c_18])).

tff(c_8042,plain,(
    ! [C_5150] : C_5150 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_7912,c_7908])).

tff(c_7779,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_11' = '#skF_9'
    | '#skF_11' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7773,c_7773,c_7773,c_48])).

tff(c_7780,plain,(
    '#skF_11' != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_7779])).

tff(c_7783,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7782,c_7780])).

tff(c_8058,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_8042,c_7783])).

tff(c_8059,plain,(
    ! [F_41] : ~ r2_hidden(F_41,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_7898])).

tff(c_8095,plain,(
    ! [B_5443,C_5444] :
      ( r2_hidden('#skF_2'('#skF_10',B_5443,C_5444),C_5444)
      | k4_xboole_0('#skF_10',B_5443) = C_5444 ) ),
    inference(resolution,[status(thm)],[c_8087,c_8059])).

tff(c_8244,plain,(
    ! [B_5457,C_5458] :
      ( r2_hidden('#skF_2'('#skF_10',B_5457,C_5458),C_5458)
      | C_5458 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7793,c_8095])).

tff(c_7882,plain,(
    ! [D_35,A_8] : ~ r2_hidden(D_35,k2_zfmisc_1(A_8,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_26,c_7877])).

tff(c_8288,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_8244,c_7882])).

tff(c_7784,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7782,c_7773])).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_7803,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7784,c_7782,c_7784,c_50])).

tff(c_8344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8288,c_7803])).

tff(c_8345,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_7781])).

tff(c_8370,plain,(
    ! [A_7] : k4_xboole_0('#skF_9',A_7) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8345,c_8345,c_7774])).

tff(c_9415,plain,(
    ! [A_5567,B_5568,C_5569] :
      ( r2_hidden('#skF_1'(A_5567,B_5568,C_5569),A_5567)
      | r2_hidden('#skF_2'(A_5567,B_5568,C_5569),C_5569)
      | k4_xboole_0(A_5567,B_5568) = C_5569 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8412,plain,(
    ! [A_5482,B_5483,D_5484] :
      ( r2_hidden('#skF_7'(A_5482,B_5483,k2_zfmisc_1(A_5482,B_5483),D_5484),A_5482)
      | ~ r2_hidden(D_5484,k2_zfmisc_1(A_5482,B_5483)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8381,plain,(
    ! [D_5464,B_5465,A_5466] :
      ( ~ r2_hidden(D_5464,B_5465)
      | ~ r2_hidden(D_5464,k4_xboole_0(A_5466,B_5465)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8384,plain,(
    ! [D_5464,A_7] :
      ( ~ r2_hidden(D_5464,A_7)
      | ~ r2_hidden(D_5464,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8370,c_8381])).

tff(c_8449,plain,(
    ! [A_5492,B_5493,D_5494] :
      ( ~ r2_hidden('#skF_7'(A_5492,B_5493,k2_zfmisc_1(A_5492,B_5493),D_5494),'#skF_9')
      | ~ r2_hidden(D_5494,k2_zfmisc_1(A_5492,B_5493)) ) ),
    inference(resolution,[status(thm)],[c_8412,c_8384])).

tff(c_8455,plain,(
    ! [D_5495,B_5496] : ~ r2_hidden(D_5495,k2_zfmisc_1('#skF_9',B_5496)) ),
    inference(resolution,[status(thm)],[c_28,c_8449])).

tff(c_8470,plain,(
    ! [F_41,B_9,E_40] :
      ( ~ r2_hidden(F_41,B_9)
      | ~ r2_hidden(E_40,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_22,c_8455])).

tff(c_8471,plain,(
    ! [E_40] : ~ r2_hidden(E_40,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_8470])).

tff(c_9431,plain,(
    ! [B_5568,C_5569] :
      ( r2_hidden('#skF_2'('#skF_9',B_5568,C_5569),C_5569)
      | k4_xboole_0('#skF_9',B_5568) = C_5569 ) ),
    inference(resolution,[status(thm)],[c_9415,c_8471])).

tff(c_9483,plain,(
    ! [B_5570,C_5571] :
      ( r2_hidden('#skF_2'('#skF_9',B_5570,C_5571),C_5571)
      | C_5571 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8370,c_9431])).

tff(c_8454,plain,(
    ! [D_35,B_9] : ~ r2_hidden(D_35,k2_zfmisc_1('#skF_9',B_9)) ),
    inference(resolution,[status(thm)],[c_28,c_8449])).

tff(c_9512,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_9',B_9) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_9483,c_8454])).

tff(c_8348,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8345,c_7773])).

tff(c_8353,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8345,c_50])).

tff(c_8354,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_8353])).

tff(c_8361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8348,c_8354])).

tff(c_8362,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8353])).

tff(c_8379,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8348,c_8362])).

tff(c_9524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9512,c_8379])).

tff(c_9525,plain,(
    ! [F_41,B_9] : ~ r2_hidden(F_41,B_9) ),
    inference(splitRight,[status(thm)],[c_8470])).

tff(c_9536,plain,(
    ! [A_5574,B_5575,C_5576] : k2_zfmisc_1(A_5574,B_5575) = C_5576 ),
    inference(negUnitSimplification,[status(thm)],[c_9525,c_9525,c_42])).

tff(c_9606,plain,(
    ! [C_5576] : C_5576 != '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_9536,c_8379])).

tff(c_9678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9606,c_8370])).

tff(c_9680,plain,(
    '#skF_11' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_7779])).

tff(c_10283,plain,(
    ! [A_7] : k4_xboole_0('#skF_12',A_7) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9680,c_9680,c_7774])).

tff(c_10939,plain,(
    ! [A_7257,B_7258,C_7259] :
      ( r2_hidden('#skF_1'(A_7257,B_7258,C_7259),A_7257)
      | r2_hidden('#skF_2'(A_7257,B_7258,C_7259),C_7259)
      | k4_xboole_0(A_7257,B_7258) = C_7259 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10328,plain,(
    ! [A_6692,B_6693,D_6694] :
      ( r2_hidden('#skF_8'(A_6692,B_6693,k2_zfmisc_1(A_6692,B_6693),D_6694),B_6693)
      | ~ r2_hidden(D_6694,k2_zfmisc_1(A_6692,B_6693)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10301,plain,(
    ! [D_6673,B_6674,A_6675] :
      ( ~ r2_hidden(D_6673,B_6674)
      | ~ r2_hidden(D_6673,k4_xboole_0(A_6675,B_6674)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10304,plain,(
    ! [D_6673,A_7] :
      ( ~ r2_hidden(D_6673,A_7)
      | ~ r2_hidden(D_6673,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10283,c_10301])).

tff(c_10364,plain,(
    ! [A_6698,B_6699,D_6700] :
      ( ~ r2_hidden('#skF_8'(A_6698,B_6699,k2_zfmisc_1(A_6698,B_6699),D_6700),'#skF_12')
      | ~ r2_hidden(D_6700,k2_zfmisc_1(A_6698,B_6699)) ) ),
    inference(resolution,[status(thm)],[c_10328,c_10304])).

tff(c_10370,plain,(
    ! [D_6701,A_6702] : ~ r2_hidden(D_6701,k2_zfmisc_1(A_6702,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_26,c_10364])).

tff(c_10385,plain,(
    ! [F_41,E_40,A_8] :
      ( ~ r2_hidden(F_41,'#skF_12')
      | ~ r2_hidden(E_40,A_8) ) ),
    inference(resolution,[status(thm)],[c_22,c_10370])).

tff(c_10428,plain,(
    ! [E_40,A_8] : ~ r2_hidden(E_40,A_8) ),
    inference(splitLeft,[status(thm)],[c_10385])).

tff(c_10456,plain,(
    ! [A_6708,B_6709] : k2_zfmisc_1(A_6708,B_6709) = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_10428,c_10428,c_42])).

tff(c_10429,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(A_8,B_9) = C_10 ),
    inference(negUnitSimplification,[status(thm)],[c_10428,c_10428,c_42])).

tff(c_10576,plain,(
    ! [C_6999] : C_6999 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_10456,c_10429])).

tff(c_9696,plain,(
    ! [A_7] : k4_xboole_0('#skF_12',A_7) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9680,c_9680,c_7774])).

tff(c_10000,plain,(
    ! [A_6646,B_6647,C_6648] :
      ( r2_hidden('#skF_1'(A_6646,B_6647,C_6648),A_6646)
      | r2_hidden('#skF_2'(A_6646,B_6647,C_6648),C_6648)
      | k4_xboole_0(A_6646,B_6647) = C_6648 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_9741,plain,(
    ! [A_5888,B_5889,D_5890] :
      ( r2_hidden('#skF_8'(A_5888,B_5889,k2_zfmisc_1(A_5888,B_5889),D_5890),B_5889)
      | ~ r2_hidden(D_5890,k2_zfmisc_1(A_5888,B_5889)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9715,plain,(
    ! [D_5869,B_5870,A_5871] :
      ( ~ r2_hidden(D_5869,B_5870)
      | ~ r2_hidden(D_5869,k4_xboole_0(A_5871,B_5870)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_9718,plain,(
    ! [D_5869,A_7] :
      ( ~ r2_hidden(D_5869,A_7)
      | ~ r2_hidden(D_5869,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9696,c_9715])).

tff(c_9782,plain,(
    ! [A_5897,B_5898,D_5899] :
      ( ~ r2_hidden('#skF_8'(A_5897,B_5898,k2_zfmisc_1(A_5897,B_5898),D_5899),'#skF_12')
      | ~ r2_hidden(D_5899,k2_zfmisc_1(A_5897,B_5898)) ) ),
    inference(resolution,[status(thm)],[c_9741,c_9718])).

tff(c_9788,plain,(
    ! [D_5900,A_5901] : ~ r2_hidden(D_5900,k2_zfmisc_1(A_5901,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_26,c_9782])).

tff(c_9803,plain,(
    ! [F_41,E_40,A_8] :
      ( ~ r2_hidden(F_41,'#skF_12')
      | ~ r2_hidden(E_40,A_8) ) ),
    inference(resolution,[status(thm)],[c_22,c_9788])).

tff(c_9804,plain,(
    ! [E_40,A_8] : ~ r2_hidden(E_40,A_8) ),
    inference(splitLeft,[status(thm)],[c_9803])).

tff(c_9887,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,B_2) = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_9804,c_9804,c_18])).

tff(c_9814,plain,(
    ! [A_5904,B_5905,C_5906] : k4_xboole_0(A_5904,B_5905) = C_5906 ),
    inference(negUnitSimplification,[status(thm)],[c_9804,c_9804,c_18])).

tff(c_9976,plain,(
    ! [C_6388] : C_6388 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_9887,c_9814])).

tff(c_9681,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9680,c_7773])).

tff(c_9690,plain,
    ( '#skF_9' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9681,c_9681,c_7772])).

tff(c_9691,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_9690])).

tff(c_9706,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9681,c_9691,c_9681,c_46])).

tff(c_9987,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_9976,c_9706])).

tff(c_9988,plain,(
    ! [F_41] : ~ r2_hidden(F_41,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_9803])).

tff(c_10004,plain,(
    ! [B_6647,C_6648] :
      ( r2_hidden('#skF_2'('#skF_12',B_6647,C_6648),C_6648)
      | k4_xboole_0('#skF_12',B_6647) = C_6648 ) ),
    inference(resolution,[status(thm)],[c_10000,c_9988])).

tff(c_10184,plain,(
    ! [B_6666,C_6667] :
      ( r2_hidden('#skF_2'('#skF_12',B_6666,C_6667),C_6667)
      | C_6667 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9696,c_10004])).

tff(c_9787,plain,(
    ! [D_35,A_8] : ~ r2_hidden(D_35,k2_zfmisc_1(A_8,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_26,c_9782])).

tff(c_10228,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_10184,c_9787])).

tff(c_10273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10228,c_9706])).

tff(c_10274,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_9690])).

tff(c_10277,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9680,c_9681,c_9681,c_50])).

tff(c_10278,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10274,c_10277])).

tff(c_10587,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_10576,c_10278])).

tff(c_10588,plain,(
    ! [F_41] : ~ r2_hidden(F_41,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_10385])).

tff(c_10979,plain,(
    ! [B_7258,C_7259] :
      ( r2_hidden('#skF_2'('#skF_12',B_7258,C_7259),C_7259)
      | k4_xboole_0('#skF_12',B_7258) = C_7259 ) ),
    inference(resolution,[status(thm)],[c_10939,c_10588])).

tff(c_11063,plain,(
    ! [B_7260,C_7261] :
      ( r2_hidden('#skF_2'('#skF_12',B_7260,C_7261),C_7261)
      | C_7261 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10283,c_10979])).

tff(c_10589,plain,(
    ! [F_7224] : ~ r2_hidden(F_7224,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_10385])).

tff(c_10605,plain,(
    ! [D_35,B_9] : ~ r2_hidden(D_35,k2_zfmisc_1('#skF_12',B_9)) ),
    inference(resolution,[status(thm)],[c_28,c_10589])).

tff(c_11119,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_12',B_9) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_11063,c_10605])).

tff(c_11130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11119,c_10278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:25:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.25/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.25/2.27  
% 6.25/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.25/2.27  %$ r2_hidden > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12
% 6.25/2.27  
% 6.25/2.27  %Foreground sorts:
% 6.25/2.27  
% 6.25/2.27  
% 6.25/2.27  %Background operators:
% 6.25/2.27  
% 6.25/2.27  
% 6.25/2.27  %Foreground operators:
% 6.25/2.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.25/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.25/2.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.25/2.27  tff('#skF_11', type, '#skF_11': $i).
% 6.25/2.27  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 6.25/2.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.25/2.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.25/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.25/2.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.25/2.27  tff('#skF_10', type, '#skF_10': $i).
% 6.25/2.27  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 6.25/2.27  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.25/2.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.25/2.27  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 6.25/2.27  tff('#skF_9', type, '#skF_9': $i).
% 6.25/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.25/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.25/2.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.25/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.25/2.27  tff('#skF_12', type, '#skF_12': $i).
% 6.25/2.27  
% 6.63/2.31  tff(f_56, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.63/2.31  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 6.63/2.31  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.63/2.31  tff(f_49, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.63/2.31  tff(c_48, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.63/2.31  tff(c_65, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_48])).
% 6.63/2.31  tff(c_20, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.63/2.31  tff(c_5488, plain, (![A_3367, B_3368, C_3369]: (r2_hidden('#skF_1'(A_3367, B_3368, C_3369), A_3367) | r2_hidden('#skF_2'(A_3367, B_3368, C_3369), C_3369) | k4_xboole_0(A_3367, B_3368)=C_3369)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_22, plain, (![E_40, F_41, A_8, B_9]: (r2_hidden(k4_tarski(E_40, F_41), k2_zfmisc_1(A_8, B_9)) | ~r2_hidden(F_41, B_9) | ~r2_hidden(E_40, A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_26, plain, (![A_8, B_9, D_35]: (r2_hidden('#skF_8'(A_8, B_9, k2_zfmisc_1(A_8, B_9), D_35), B_9) | ~r2_hidden(D_35, k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_3060, plain, (![A_2463, B_2464, D_2465]: (r2_hidden('#skF_8'(A_2463, B_2464, k2_zfmisc_1(A_2463, B_2464), D_2465), B_2464) | ~r2_hidden(D_2465, k2_zfmisc_1(A_2463, B_2464)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_66, plain, (![D_43, B_44, A_45]: (~r2_hidden(D_43, B_44) | ~r2_hidden(D_43, k4_xboole_0(A_45, B_44)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_69, plain, (![D_43, A_7]: (~r2_hidden(D_43, A_7) | ~r2_hidden(D_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_66])).
% 6.63/2.31  tff(c_3251, plain, (![A_2513, B_2514, D_2515]: (~r2_hidden('#skF_8'(A_2513, B_2514, k2_zfmisc_1(A_2513, B_2514), D_2515), k1_xboole_0) | ~r2_hidden(D_2515, k2_zfmisc_1(A_2513, B_2514)))), inference(resolution, [status(thm)], [c_3060, c_69])).
% 6.63/2.31  tff(c_3265, plain, (![D_2516, A_2517]: (~r2_hidden(D_2516, k2_zfmisc_1(A_2517, k1_xboole_0)))), inference(resolution, [status(thm)], [c_26, c_3251])).
% 6.63/2.31  tff(c_3280, plain, (![F_41, E_40, A_8]: (~r2_hidden(F_41, k1_xboole_0) | ~r2_hidden(E_40, A_8))), inference(resolution, [status(thm)], [c_22, c_3265])).
% 6.63/2.31  tff(c_3295, plain, (![E_40, A_8]: (~r2_hidden(E_40, A_8))), inference(splitLeft, [status(thm)], [c_3280])).
% 6.63/2.31  tff(c_42, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_5'(A_8, B_9, C_10), B_9) | r2_hidden('#skF_6'(A_8, B_9, C_10), C_10) | k2_zfmisc_1(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_3330, plain, (![A_2524, B_2525]: (k2_zfmisc_1(A_2524, B_2525)='#skF_11')), inference(negUnitSimplification, [status(thm)], [c_3295, c_3295, c_42])).
% 6.63/2.31  tff(c_3314, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(A_8, B_9)=C_10)), inference(negUnitSimplification, [status(thm)], [c_3295, c_3295, c_42])).
% 6.63/2.31  tff(c_3479, plain, (![C_2944]: (C_2944='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_3330, c_3314])).
% 6.63/2.31  tff(c_52, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.63/2.31  tff(c_64, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_52])).
% 6.63/2.31  tff(c_3507, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3479, c_64])).
% 6.63/2.31  tff(c_3508, plain, (![F_41]: (~r2_hidden(F_41, k1_xboole_0))), inference(splitRight, [status(thm)], [c_3280])).
% 6.63/2.31  tff(c_5584, plain, (![B_3368, C_3369]: (r2_hidden('#skF_2'(k1_xboole_0, B_3368, C_3369), C_3369) | k4_xboole_0(k1_xboole_0, B_3368)=C_3369)), inference(resolution, [status(thm)], [c_5488, c_3508])).
% 6.63/2.31  tff(c_5771, plain, (![B_3370, C_3371]: (r2_hidden('#skF_2'(k1_xboole_0, B_3370, C_3371), C_3371) | k1_xboole_0=C_3371)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5584])).
% 6.63/2.31  tff(c_4206, plain, (![A_3292, B_3293, C_3294]: (r2_hidden('#skF_1'(A_3292, B_3293, C_3294), A_3292) | r2_hidden('#skF_2'(A_3292, B_3293, C_3294), C_3294) | k4_xboole_0(A_3292, B_3293)=C_3294)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_4290, plain, (![B_3293, C_3294]: (r2_hidden('#skF_2'(k1_xboole_0, B_3293, C_3294), C_3294) | k4_xboole_0(k1_xboole_0, B_3293)=C_3294)), inference(resolution, [status(thm)], [c_4206, c_3508])).
% 6.63/2.31  tff(c_4448, plain, (![B_3295, C_3296]: (r2_hidden('#skF_2'(k1_xboole_0, B_3295, C_3296), C_3296) | k1_xboole_0=C_3296)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4290])).
% 6.63/2.31  tff(c_1189, plain, (![A_721, B_722, C_723]: (r2_hidden('#skF_1'(A_721, B_722, C_723), A_721) | r2_hidden('#skF_2'(A_721, B_722, C_723), C_723) | k4_xboole_0(A_721, B_722)=C_723)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_128, plain, (![A_76, B_77, D_78]: (r2_hidden('#skF_8'(A_76, B_77, k2_zfmisc_1(A_76, B_77), D_78), B_77) | ~r2_hidden(D_78, k2_zfmisc_1(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_222, plain, (![A_92, B_93, D_94]: (~r2_hidden('#skF_8'(A_92, B_93, k2_zfmisc_1(A_92, B_93), D_94), k1_xboole_0) | ~r2_hidden(D_94, k2_zfmisc_1(A_92, B_93)))), inference(resolution, [status(thm)], [c_128, c_69])).
% 6.63/2.31  tff(c_238, plain, (![D_98, A_99]: (~r2_hidden(D_98, k2_zfmisc_1(A_99, k1_xboole_0)))), inference(resolution, [status(thm)], [c_26, c_222])).
% 6.63/2.31  tff(c_253, plain, (![F_41, E_40, A_8]: (~r2_hidden(F_41, k1_xboole_0) | ~r2_hidden(E_40, A_8))), inference(resolution, [status(thm)], [c_22, c_238])).
% 6.63/2.31  tff(c_254, plain, (![E_40, A_8]: (~r2_hidden(E_40, A_8))), inference(splitLeft, [status(thm)], [c_253])).
% 6.63/2.31  tff(c_286, plain, (![A_102, B_103]: (k2_zfmisc_1(A_102, B_103)='#skF_12')), inference(negUnitSimplification, [status(thm)], [c_254, c_254, c_42])).
% 6.63/2.31  tff(c_270, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(A_8, B_9)=C_10)), inference(negUnitSimplification, [status(thm)], [c_254, c_254, c_42])).
% 6.63/2.31  tff(c_410, plain, (![C_372]: (C_372='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_286, c_270])).
% 6.63/2.31  tff(c_428, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_410, c_65])).
% 6.63/2.31  tff(c_429, plain, (![F_41]: (~r2_hidden(F_41, k1_xboole_0))), inference(splitRight, [status(thm)], [c_253])).
% 6.63/2.31  tff(c_1221, plain, (![B_722, C_723]: (r2_hidden('#skF_2'(k1_xboole_0, B_722, C_723), C_723) | k4_xboole_0(k1_xboole_0, B_722)=C_723)), inference(resolution, [status(thm)], [c_1189, c_429])).
% 6.63/2.31  tff(c_1441, plain, (![B_739, C_740]: (r2_hidden('#skF_2'(k1_xboole_0, B_739, C_740), C_740) | k1_xboole_0=C_740)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1221])).
% 6.63/2.31  tff(c_819, plain, (![A_700, B_701, C_702]: (r2_hidden('#skF_1'(A_700, B_701, C_702), A_700) | r2_hidden('#skF_2'(A_700, B_701, C_702), C_702) | k4_xboole_0(A_700, B_701)=C_702)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_875, plain, (![B_701, C_702]: (r2_hidden('#skF_2'(k1_xboole_0, B_701, C_702), C_702) | k4_xboole_0(k1_xboole_0, B_701)=C_702)), inference(resolution, [status(thm)], [c_819, c_429])).
% 6.63/2.31  tff(c_990, plain, (![B_703, C_704]: (r2_hidden('#skF_2'(k1_xboole_0, B_703, C_704), C_704) | k1_xboole_0=C_704)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_875])).
% 6.63/2.31  tff(c_56, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.63/2.31  tff(c_72, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 6.63/2.31  tff(c_96, plain, (![E_54, F_55, A_56, B_57]: (r2_hidden(k4_tarski(E_54, F_55), k2_zfmisc_1(A_56, B_57)) | ~r2_hidden(F_55, B_57) | ~r2_hidden(E_54, A_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_101, plain, (![E_54, F_55]: (r2_hidden(k4_tarski(E_54, F_55), k1_xboole_0) | ~r2_hidden(F_55, '#skF_12') | ~r2_hidden(E_54, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_96])).
% 6.63/2.31  tff(c_430, plain, (![F_55, E_54]: (~r2_hidden(F_55, '#skF_12') | ~r2_hidden(E_54, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_429, c_101])).
% 6.63/2.31  tff(c_442, plain, (![E_54]: (~r2_hidden(E_54, '#skF_11'))), inference(splitLeft, [status(thm)], [c_430])).
% 6.63/2.31  tff(c_1042, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_990, c_442])).
% 6.63/2.31  tff(c_1074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1042])).
% 6.63/2.31  tff(c_1075, plain, (![F_55]: (~r2_hidden(F_55, '#skF_12'))), inference(splitRight, [status(thm)], [c_430])).
% 6.63/2.31  tff(c_1489, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_1441, c_1075])).
% 6.63/2.31  tff(c_1525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_1489])).
% 6.63/2.31  tff(c_1526, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_56])).
% 6.63/2.31  tff(c_1528, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_1526])).
% 6.63/2.31  tff(c_1532, plain, ('#skF_11'!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_64])).
% 6.63/2.31  tff(c_1533, plain, (![A_7]: (k4_xboole_0('#skF_10', A_7)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_1528, c_20])).
% 6.63/2.31  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_28, plain, (![A_8, B_9, D_35]: (r2_hidden('#skF_7'(A_8, B_9, k2_zfmisc_1(A_8, B_9), D_35), A_8) | ~r2_hidden(D_35, k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_1575, plain, (![A_761, B_762, D_763]: (r2_hidden('#skF_7'(A_761, B_762, k2_zfmisc_1(A_761, B_762), D_763), A_761) | ~r2_hidden(D_763, k2_zfmisc_1(A_761, B_762)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_1538, plain, (![A_741]: (k4_xboole_0('#skF_10', A_741)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_1528, c_20])).
% 6.63/2.31  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_1543, plain, (![D_6, A_741]: (~r2_hidden(D_6, A_741) | ~r2_hidden(D_6, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1538, c_4])).
% 6.63/2.31  tff(c_1644, plain, (![A_770, B_771, D_772]: (~r2_hidden('#skF_7'(A_770, B_771, k2_zfmisc_1(A_770, B_771), D_772), '#skF_10') | ~r2_hidden(D_772, k2_zfmisc_1(A_770, B_771)))), inference(resolution, [status(thm)], [c_1575, c_1543])).
% 6.63/2.31  tff(c_1650, plain, (![D_773, B_774]: (~r2_hidden(D_773, k2_zfmisc_1('#skF_10', B_774)))), inference(resolution, [status(thm)], [c_28, c_1644])).
% 6.63/2.31  tff(c_1675, plain, (![F_41, B_9, E_40]: (~r2_hidden(F_41, B_9) | ~r2_hidden(E_40, '#skF_10'))), inference(resolution, [status(thm)], [c_22, c_1650])).
% 6.63/2.31  tff(c_1677, plain, (![E_775]: (~r2_hidden(E_775, '#skF_10'))), inference(splitLeft, [status(thm)], [c_1675])).
% 6.63/2.31  tff(c_1681, plain, (![B_2, C_3]: (r2_hidden('#skF_2'('#skF_10', B_2, C_3), C_3) | k4_xboole_0('#skF_10', B_2)=C_3)), inference(resolution, [status(thm)], [c_18, c_1677])).
% 6.63/2.31  tff(c_1923, plain, (![B_796, C_797]: (r2_hidden('#skF_2'('#skF_10', B_796, C_797), C_797) | C_797='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1533, c_1681])).
% 6.63/2.31  tff(c_1694, plain, (![D_35, A_8]: (~r2_hidden(D_35, k2_zfmisc_1(A_8, '#skF_10')))), inference(resolution, [status(thm)], [c_26, c_1677])).
% 6.63/2.31  tff(c_1964, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1923, c_1694])).
% 6.63/2.31  tff(c_54, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.63/2.31  tff(c_71, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 6.63/2.31  tff(c_1529, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_71])).
% 6.63/2.31  tff(c_1975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1964, c_1529])).
% 6.63/2.31  tff(c_1976, plain, (![F_41, B_9]: (~r2_hidden(F_41, B_9))), inference(splitRight, [status(thm)], [c_1675])).
% 6.63/2.31  tff(c_1996, plain, (![A_800, B_801]: (k4_xboole_0(A_800, B_801)='#skF_11')), inference(negUnitSimplification, [status(thm)], [c_1976, c_1976, c_18])).
% 6.63/2.31  tff(c_1977, plain, (![A_1, B_2, C_3]: (k4_xboole_0(A_1, B_2)=C_3)), inference(negUnitSimplification, [status(thm)], [c_1976, c_1976, c_18])).
% 6.63/2.31  tff(c_2264, plain, (![C_1382]: (C_1382='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_1996, c_1977])).
% 6.63/2.31  tff(c_2285, plain, ('#skF_11'='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_2264, c_1528])).
% 6.63/2.31  tff(c_2296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1532, c_2285])).
% 6.63/2.31  tff(c_2297, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1526])).
% 6.63/2.31  tff(c_2304, plain, (![A_7]: (k4_xboole_0('#skF_9', A_7)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2297, c_2297, c_20])).
% 6.63/2.31  tff(c_2346, plain, (![A_1787, B_1788, D_1789]: (r2_hidden('#skF_7'(A_1787, B_1788, k2_zfmisc_1(A_1787, B_1788), D_1789), A_1787) | ~r2_hidden(D_1789, k2_zfmisc_1(A_1787, B_1788)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_2301, plain, (![D_43, A_7]: (~r2_hidden(D_43, A_7) | ~r2_hidden(D_43, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2297, c_69])).
% 6.63/2.31  tff(c_2382, plain, (![A_1793, B_1794, D_1795]: (~r2_hidden('#skF_7'(A_1793, B_1794, k2_zfmisc_1(A_1793, B_1794), D_1795), '#skF_9') | ~r2_hidden(D_1795, k2_zfmisc_1(A_1793, B_1794)))), inference(resolution, [status(thm)], [c_2346, c_2301])).
% 6.63/2.31  tff(c_2421, plain, (![D_1799, B_1800]: (~r2_hidden(D_1799, k2_zfmisc_1('#skF_9', B_1800)))), inference(resolution, [status(thm)], [c_28, c_2382])).
% 6.63/2.31  tff(c_2446, plain, (![F_41, B_9, E_40]: (~r2_hidden(F_41, B_9) | ~r2_hidden(E_40, '#skF_9'))), inference(resolution, [status(thm)], [c_22, c_2421])).
% 6.63/2.31  tff(c_2448, plain, (![E_1801]: (~r2_hidden(E_1801, '#skF_9'))), inference(splitLeft, [status(thm)], [c_2446])).
% 6.63/2.31  tff(c_2452, plain, (![B_2, C_3]: (r2_hidden('#skF_2'('#skF_9', B_2, C_3), C_3) | k4_xboole_0('#skF_9', B_2)=C_3)), inference(resolution, [status(thm)], [c_18, c_2448])).
% 6.63/2.31  tff(c_2731, plain, (![B_1822, C_1823]: (r2_hidden('#skF_2'('#skF_9', B_1822, C_1823), C_1823) | C_1823='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2304, c_2452])).
% 6.63/2.31  tff(c_2387, plain, (![D_35, B_9]: (~r2_hidden(D_35, k2_zfmisc_1('#skF_9', B_9)))), inference(resolution, [status(thm)], [c_28, c_2382])).
% 6.63/2.31  tff(c_2775, plain, (![B_9]: (k2_zfmisc_1('#skF_9', B_9)='#skF_9')), inference(resolution, [status(thm)], [c_2731, c_2387])).
% 6.63/2.31  tff(c_2300, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2297, c_71])).
% 6.63/2.31  tff(c_2820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2775, c_2300])).
% 6.63/2.31  tff(c_2821, plain, (![F_41, B_9]: (~r2_hidden(F_41, B_9))), inference(splitRight, [status(thm)], [c_2446])).
% 6.63/2.31  tff(c_2859, plain, (![A_1830, B_1831]: (k4_xboole_0(A_1830, B_1831)='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_2821, c_2821, c_18])).
% 6.63/2.31  tff(c_2832, plain, (![A_1, B_2, C_3]: (k4_xboole_0(A_1, B_2)=C_3)), inference(negUnitSimplification, [status(thm)], [c_2821, c_2821, c_18])).
% 6.63/2.31  tff(c_2973, plain, (![C_2121]: (C_2121='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2859, c_2832])).
% 6.63/2.31  tff(c_2997, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2973, c_2300])).
% 6.63/2.31  tff(c_2998, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 6.63/2.31  tff(c_3029, plain, (![E_2451, F_2452, A_2453, B_2454]: (r2_hidden(k4_tarski(E_2451, F_2452), k2_zfmisc_1(A_2453, B_2454)) | ~r2_hidden(F_2452, B_2454) | ~r2_hidden(E_2451, A_2453))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_3037, plain, (![E_2451, F_2452]: (r2_hidden(k4_tarski(E_2451, F_2452), k1_xboole_0) | ~r2_hidden(F_2452, '#skF_12') | ~r2_hidden(E_2451, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_2998, c_3029])).
% 6.63/2.31  tff(c_3509, plain, (![F_2452, E_2451]: (~r2_hidden(F_2452, '#skF_12') | ~r2_hidden(E_2451, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_3508, c_3037])).
% 6.63/2.31  tff(c_3522, plain, (![E_2451]: (~r2_hidden(E_2451, '#skF_11'))), inference(splitLeft, [status(thm)], [c_3509])).
% 6.63/2.31  tff(c_4528, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_4448, c_3522])).
% 6.63/2.31  tff(c_4567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_4528])).
% 6.63/2.31  tff(c_4568, plain, (![F_2452]: (~r2_hidden(F_2452, '#skF_12'))), inference(splitRight, [status(thm)], [c_3509])).
% 6.63/2.31  tff(c_5863, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_5771, c_4568])).
% 6.63/2.31  tff(c_5910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_5863])).
% 6.63/2.31  tff(c_5912, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_48])).
% 6.63/2.31  tff(c_5914, plain, (![A_7]: (k4_xboole_0('#skF_12', A_7)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_5912, c_5912, c_20])).
% 6.63/2.31  tff(c_7275, plain, (![A_3998, B_3999, C_4000]: (r2_hidden('#skF_1'(A_3998, B_3999, C_4000), A_3998) | r2_hidden('#skF_2'(A_3998, B_3999, C_4000), C_4000) | k4_xboole_0(A_3998, B_3999)=C_4000)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_7114, plain, (![A_3975, B_3976, D_3977]: (r2_hidden('#skF_7'(A_3975, B_3976, k2_zfmisc_1(A_3975, B_3976), D_3977), A_3975) | ~r2_hidden(D_3977, k2_zfmisc_1(A_3975, B_3976)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_7088, plain, (![D_3956, B_3957, A_3958]: (~r2_hidden(D_3956, B_3957) | ~r2_hidden(D_3956, k4_xboole_0(A_3958, B_3957)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_7091, plain, (![D_3956, A_7]: (~r2_hidden(D_3956, A_7) | ~r2_hidden(D_3956, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_5914, c_7088])).
% 6.63/2.31  tff(c_7150, plain, (![A_3981, B_3982, D_3983]: (~r2_hidden('#skF_7'(A_3981, B_3982, k2_zfmisc_1(A_3981, B_3982), D_3983), '#skF_12') | ~r2_hidden(D_3983, k2_zfmisc_1(A_3981, B_3982)))), inference(resolution, [status(thm)], [c_7114, c_7091])).
% 6.63/2.31  tff(c_7156, plain, (![D_3984, B_3985]: (~r2_hidden(D_3984, k2_zfmisc_1('#skF_12', B_3985)))), inference(resolution, [status(thm)], [c_28, c_7150])).
% 6.63/2.31  tff(c_7171, plain, (![F_41, B_9, E_40]: (~r2_hidden(F_41, B_9) | ~r2_hidden(E_40, '#skF_12'))), inference(resolution, [status(thm)], [c_22, c_7156])).
% 6.63/2.31  tff(c_7195, plain, (![E_40]: (~r2_hidden(E_40, '#skF_12'))), inference(splitLeft, [status(thm)], [c_7171])).
% 6.63/2.31  tff(c_7291, plain, (![B_3999, C_4000]: (r2_hidden('#skF_2'('#skF_12', B_3999, C_4000), C_4000) | k4_xboole_0('#skF_12', B_3999)=C_4000)), inference(resolution, [status(thm)], [c_7275, c_7195])).
% 6.63/2.31  tff(c_7406, plain, (![B_4007, C_4008]: (r2_hidden('#skF_2'('#skF_12', B_4007, C_4008), C_4008) | C_4008='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_5914, c_7291])).
% 6.63/2.31  tff(c_7155, plain, (![D_35, B_9]: (~r2_hidden(D_35, k2_zfmisc_1('#skF_12', B_9)))), inference(resolution, [status(thm)], [c_28, c_7150])).
% 6.63/2.31  tff(c_7450, plain, (![B_9]: (k2_zfmisc_1('#skF_12', B_9)='#skF_12')), inference(resolution, [status(thm)], [c_7406, c_7155])).
% 6.63/2.31  tff(c_6650, plain, (![A_3461, B_3462, C_3463]: (r2_hidden('#skF_1'(A_3461, B_3462, C_3463), A_3461) | r2_hidden('#skF_2'(A_3461, B_3462, C_3463), C_3463) | k4_xboole_0(A_3461, B_3462)=C_3463)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_5967, plain, (![A_3395, B_3396, D_3397]: (r2_hidden('#skF_7'(A_3395, B_3396, k2_zfmisc_1(A_3395, B_3396), D_3397), A_3395) | ~r2_hidden(D_3397, k2_zfmisc_1(A_3395, B_3396)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_5935, plain, (![D_3373, B_3374, A_3375]: (~r2_hidden(D_3373, B_3374) | ~r2_hidden(D_3373, k4_xboole_0(A_3375, B_3374)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_5938, plain, (![D_3373, A_7]: (~r2_hidden(D_3373, A_7) | ~r2_hidden(D_3373, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_5914, c_5935])).
% 6.63/2.31  tff(c_6035, plain, (![A_3404, B_3405, D_3406]: (~r2_hidden('#skF_7'(A_3404, B_3405, k2_zfmisc_1(A_3404, B_3405), D_3406), '#skF_12') | ~r2_hidden(D_3406, k2_zfmisc_1(A_3404, B_3405)))), inference(resolution, [status(thm)], [c_5967, c_5938])).
% 6.63/2.31  tff(c_6041, plain, (![D_3407, B_3408]: (~r2_hidden(D_3407, k2_zfmisc_1('#skF_12', B_3408)))), inference(resolution, [status(thm)], [c_28, c_6035])).
% 6.63/2.31  tff(c_6066, plain, (![F_41, B_9, E_40]: (~r2_hidden(F_41, B_9) | ~r2_hidden(E_40, '#skF_12'))), inference(resolution, [status(thm)], [c_22, c_6041])).
% 6.63/2.31  tff(c_6067, plain, (![E_40]: (~r2_hidden(E_40, '#skF_12'))), inference(splitLeft, [status(thm)], [c_6066])).
% 6.63/2.31  tff(c_6706, plain, (![B_3462, C_3463]: (r2_hidden('#skF_2'('#skF_12', B_3462, C_3463), C_3463) | k4_xboole_0('#skF_12', B_3462)=C_3463)), inference(resolution, [status(thm)], [c_6650, c_6067])).
% 6.63/2.31  tff(c_6814, plain, (![B_3464, C_3465]: (r2_hidden('#skF_2'('#skF_12', B_3464, C_3465), C_3465) | C_3465='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_5914, c_6706])).
% 6.63/2.31  tff(c_6091, plain, (![E_3412]: (~r2_hidden(E_3412, '#skF_12'))), inference(splitLeft, [status(thm)], [c_6066])).
% 6.63/2.31  tff(c_6112, plain, (![D_35, A_8]: (~r2_hidden(D_35, k2_zfmisc_1(A_8, '#skF_12')))), inference(resolution, [status(thm)], [c_26, c_6091])).
% 6.63/2.31  tff(c_6890, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_6814, c_6112])).
% 6.63/2.31  tff(c_5911, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_48])).
% 6.63/2.31  tff(c_5920, plain, ('#skF_9'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_5912, c_5912, c_5911])).
% 6.63/2.31  tff(c_5921, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_5920])).
% 6.63/2.31  tff(c_46, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.63/2.31  tff(c_5934, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_5912, c_5921, c_5912, c_46])).
% 6.63/2.31  tff(c_6904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6890, c_5934])).
% 6.63/2.31  tff(c_6905, plain, (![F_41, B_9]: (~r2_hidden(F_41, B_9))), inference(splitRight, [status(thm)], [c_6066])).
% 6.63/2.31  tff(c_44, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_4'(A_8, B_9, C_10), A_8) | r2_hidden('#skF_6'(A_8, B_9, C_10), C_10) | k2_zfmisc_1(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_6922, plain, (![A_3468, B_3469]: (k2_zfmisc_1(A_3468, B_3469)='#skF_12')), inference(negUnitSimplification, [status(thm)], [c_6905, c_6905, c_44])).
% 6.63/2.31  tff(c_6906, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(A_8, B_9)=C_10)), inference(negUnitSimplification, [status(thm)], [c_6905, c_6905, c_44])).
% 6.63/2.31  tff(c_7054, plain, (![C_3727]: (C_3727='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_6922, c_6906])).
% 6.63/2.31  tff(c_7065, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_7054, c_5934])).
% 6.63/2.31  tff(c_7066, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_5920])).
% 6.63/2.31  tff(c_7080, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_5912, c_7066, c_5912, c_46])).
% 6.63/2.31  tff(c_7583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7450, c_7080])).
% 6.63/2.31  tff(c_7584, plain, (![F_41, B_9]: (~r2_hidden(F_41, B_9))), inference(splitRight, [status(thm)], [c_7171])).
% 6.63/2.31  tff(c_7633, plain, (![A_4015, B_4016]: (k4_xboole_0(A_4015, B_4016)='#skF_12')), inference(negUnitSimplification, [status(thm)], [c_7584, c_7584, c_18])).
% 6.63/2.31  tff(c_7593, plain, (![A_1, B_2, C_3]: (k4_xboole_0(A_1, B_2)=C_3)), inference(negUnitSimplification, [status(thm)], [c_7584, c_7584, c_18])).
% 6.63/2.31  tff(c_7756, plain, (![C_4563]: (C_4563='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_7633, c_7593])).
% 6.63/2.31  tff(c_7771, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_7756, c_7080])).
% 6.63/2.31  tff(c_7773, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_52])).
% 6.63/2.31  tff(c_7772, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_52])).
% 6.63/2.31  tff(c_7781, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_7773, c_7773, c_7772])).
% 6.63/2.31  tff(c_7782, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_7781])).
% 6.63/2.31  tff(c_7774, plain, (![A_7]: (k4_xboole_0('#skF_11', A_7)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_7773, c_7773, c_20])).
% 6.63/2.31  tff(c_7793, plain, (![A_7]: (k4_xboole_0('#skF_10', A_7)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_7782, c_7782, c_7774])).
% 6.63/2.31  tff(c_8087, plain, (![A_5442, B_5443, C_5444]: (r2_hidden('#skF_1'(A_5442, B_5443, C_5444), A_5442) | r2_hidden('#skF_2'(A_5442, B_5443, C_5444), C_5444) | k4_xboole_0(A_5442, B_5443)=C_5444)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_7836, plain, (![A_4907, B_4908, D_4909]: (r2_hidden('#skF_8'(A_4907, B_4908, k2_zfmisc_1(A_4907, B_4908), D_4909), B_4908) | ~r2_hidden(D_4909, k2_zfmisc_1(A_4907, B_4908)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_7810, plain, (![D_4888, B_4889, A_4890]: (~r2_hidden(D_4888, B_4889) | ~r2_hidden(D_4888, k4_xboole_0(A_4890, B_4889)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_7813, plain, (![D_4888, A_7]: (~r2_hidden(D_4888, A_7) | ~r2_hidden(D_4888, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_7793, c_7810])).
% 6.63/2.31  tff(c_7877, plain, (![A_4916, B_4917, D_4918]: (~r2_hidden('#skF_8'(A_4916, B_4917, k2_zfmisc_1(A_4916, B_4917), D_4918), '#skF_10') | ~r2_hidden(D_4918, k2_zfmisc_1(A_4916, B_4917)))), inference(resolution, [status(thm)], [c_7836, c_7813])).
% 6.63/2.31  tff(c_7883, plain, (![D_4919, A_4920]: (~r2_hidden(D_4919, k2_zfmisc_1(A_4920, '#skF_10')))), inference(resolution, [status(thm)], [c_26, c_7877])).
% 6.63/2.31  tff(c_7898, plain, (![F_41, E_40, A_8]: (~r2_hidden(F_41, '#skF_10') | ~r2_hidden(E_40, A_8))), inference(resolution, [status(thm)], [c_22, c_7883])).
% 6.63/2.31  tff(c_7899, plain, (![E_40, A_8]: (~r2_hidden(E_40, A_8))), inference(splitLeft, [status(thm)], [c_7898])).
% 6.63/2.31  tff(c_7912, plain, (![A_4923, B_4924]: (k4_xboole_0(A_4923, B_4924)='#skF_12')), inference(negUnitSimplification, [status(thm)], [c_7899, c_7899, c_18])).
% 6.63/2.31  tff(c_7908, plain, (![A_1, B_2, C_3]: (k4_xboole_0(A_1, B_2)=C_3)), inference(negUnitSimplification, [status(thm)], [c_7899, c_7899, c_18])).
% 6.63/2.31  tff(c_8042, plain, (![C_5150]: (C_5150='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_7912, c_7908])).
% 6.63/2.31  tff(c_7779, plain, ('#skF_11'='#skF_10' | '#skF_11'='#skF_9' | '#skF_11'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_7773, c_7773, c_7773, c_48])).
% 6.63/2.31  tff(c_7780, plain, ('#skF_11'!='#skF_12'), inference(splitLeft, [status(thm)], [c_7779])).
% 6.63/2.31  tff(c_7783, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_7782, c_7780])).
% 6.63/2.31  tff(c_8058, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_8042, c_7783])).
% 6.63/2.31  tff(c_8059, plain, (![F_41]: (~r2_hidden(F_41, '#skF_10'))), inference(splitRight, [status(thm)], [c_7898])).
% 6.63/2.31  tff(c_8095, plain, (![B_5443, C_5444]: (r2_hidden('#skF_2'('#skF_10', B_5443, C_5444), C_5444) | k4_xboole_0('#skF_10', B_5443)=C_5444)), inference(resolution, [status(thm)], [c_8087, c_8059])).
% 6.63/2.31  tff(c_8244, plain, (![B_5457, C_5458]: (r2_hidden('#skF_2'('#skF_10', B_5457, C_5458), C_5458) | C_5458='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_7793, c_8095])).
% 6.63/2.31  tff(c_7882, plain, (![D_35, A_8]: (~r2_hidden(D_35, k2_zfmisc_1(A_8, '#skF_10')))), inference(resolution, [status(thm)], [c_26, c_7877])).
% 6.63/2.31  tff(c_8288, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_8244, c_7882])).
% 6.63/2.31  tff(c_7784, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_7782, c_7773])).
% 6.63/2.31  tff(c_50, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.63/2.31  tff(c_7803, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_7784, c_7782, c_7784, c_50])).
% 6.63/2.31  tff(c_8344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8288, c_7803])).
% 6.63/2.31  tff(c_8345, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_7781])).
% 6.63/2.31  tff(c_8370, plain, (![A_7]: (k4_xboole_0('#skF_9', A_7)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_8345, c_8345, c_7774])).
% 6.63/2.31  tff(c_9415, plain, (![A_5567, B_5568, C_5569]: (r2_hidden('#skF_1'(A_5567, B_5568, C_5569), A_5567) | r2_hidden('#skF_2'(A_5567, B_5568, C_5569), C_5569) | k4_xboole_0(A_5567, B_5568)=C_5569)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_8412, plain, (![A_5482, B_5483, D_5484]: (r2_hidden('#skF_7'(A_5482, B_5483, k2_zfmisc_1(A_5482, B_5483), D_5484), A_5482) | ~r2_hidden(D_5484, k2_zfmisc_1(A_5482, B_5483)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_8381, plain, (![D_5464, B_5465, A_5466]: (~r2_hidden(D_5464, B_5465) | ~r2_hidden(D_5464, k4_xboole_0(A_5466, B_5465)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_8384, plain, (![D_5464, A_7]: (~r2_hidden(D_5464, A_7) | ~r2_hidden(D_5464, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_8370, c_8381])).
% 6.63/2.31  tff(c_8449, plain, (![A_5492, B_5493, D_5494]: (~r2_hidden('#skF_7'(A_5492, B_5493, k2_zfmisc_1(A_5492, B_5493), D_5494), '#skF_9') | ~r2_hidden(D_5494, k2_zfmisc_1(A_5492, B_5493)))), inference(resolution, [status(thm)], [c_8412, c_8384])).
% 6.63/2.31  tff(c_8455, plain, (![D_5495, B_5496]: (~r2_hidden(D_5495, k2_zfmisc_1('#skF_9', B_5496)))), inference(resolution, [status(thm)], [c_28, c_8449])).
% 6.63/2.31  tff(c_8470, plain, (![F_41, B_9, E_40]: (~r2_hidden(F_41, B_9) | ~r2_hidden(E_40, '#skF_9'))), inference(resolution, [status(thm)], [c_22, c_8455])).
% 6.63/2.31  tff(c_8471, plain, (![E_40]: (~r2_hidden(E_40, '#skF_9'))), inference(splitLeft, [status(thm)], [c_8470])).
% 6.63/2.31  tff(c_9431, plain, (![B_5568, C_5569]: (r2_hidden('#skF_2'('#skF_9', B_5568, C_5569), C_5569) | k4_xboole_0('#skF_9', B_5568)=C_5569)), inference(resolution, [status(thm)], [c_9415, c_8471])).
% 6.63/2.31  tff(c_9483, plain, (![B_5570, C_5571]: (r2_hidden('#skF_2'('#skF_9', B_5570, C_5571), C_5571) | C_5571='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_8370, c_9431])).
% 6.63/2.31  tff(c_8454, plain, (![D_35, B_9]: (~r2_hidden(D_35, k2_zfmisc_1('#skF_9', B_9)))), inference(resolution, [status(thm)], [c_28, c_8449])).
% 6.63/2.31  tff(c_9512, plain, (![B_9]: (k2_zfmisc_1('#skF_9', B_9)='#skF_9')), inference(resolution, [status(thm)], [c_9483, c_8454])).
% 6.63/2.31  tff(c_8348, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_8345, c_7773])).
% 6.63/2.31  tff(c_8353, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_8345, c_50])).
% 6.63/2.31  tff(c_8354, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_8353])).
% 6.63/2.31  tff(c_8361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8348, c_8354])).
% 6.63/2.31  tff(c_8362, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_8353])).
% 6.63/2.31  tff(c_8379, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_8348, c_8362])).
% 6.63/2.31  tff(c_9524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9512, c_8379])).
% 6.63/2.31  tff(c_9525, plain, (![F_41, B_9]: (~r2_hidden(F_41, B_9))), inference(splitRight, [status(thm)], [c_8470])).
% 6.63/2.31  tff(c_9536, plain, (![A_5574, B_5575, C_5576]: (k2_zfmisc_1(A_5574, B_5575)=C_5576)), inference(negUnitSimplification, [status(thm)], [c_9525, c_9525, c_42])).
% 6.63/2.31  tff(c_9606, plain, (![C_5576]: (C_5576!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_9536, c_8379])).
% 6.63/2.31  tff(c_9678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9606, c_8370])).
% 6.63/2.31  tff(c_9680, plain, ('#skF_11'='#skF_12'), inference(splitRight, [status(thm)], [c_7779])).
% 6.63/2.31  tff(c_10283, plain, (![A_7]: (k4_xboole_0('#skF_12', A_7)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_9680, c_9680, c_7774])).
% 6.63/2.31  tff(c_10939, plain, (![A_7257, B_7258, C_7259]: (r2_hidden('#skF_1'(A_7257, B_7258, C_7259), A_7257) | r2_hidden('#skF_2'(A_7257, B_7258, C_7259), C_7259) | k4_xboole_0(A_7257, B_7258)=C_7259)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_10328, plain, (![A_6692, B_6693, D_6694]: (r2_hidden('#skF_8'(A_6692, B_6693, k2_zfmisc_1(A_6692, B_6693), D_6694), B_6693) | ~r2_hidden(D_6694, k2_zfmisc_1(A_6692, B_6693)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_10301, plain, (![D_6673, B_6674, A_6675]: (~r2_hidden(D_6673, B_6674) | ~r2_hidden(D_6673, k4_xboole_0(A_6675, B_6674)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_10304, plain, (![D_6673, A_7]: (~r2_hidden(D_6673, A_7) | ~r2_hidden(D_6673, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_10283, c_10301])).
% 6.63/2.31  tff(c_10364, plain, (![A_6698, B_6699, D_6700]: (~r2_hidden('#skF_8'(A_6698, B_6699, k2_zfmisc_1(A_6698, B_6699), D_6700), '#skF_12') | ~r2_hidden(D_6700, k2_zfmisc_1(A_6698, B_6699)))), inference(resolution, [status(thm)], [c_10328, c_10304])).
% 6.63/2.31  tff(c_10370, plain, (![D_6701, A_6702]: (~r2_hidden(D_6701, k2_zfmisc_1(A_6702, '#skF_12')))), inference(resolution, [status(thm)], [c_26, c_10364])).
% 6.63/2.31  tff(c_10385, plain, (![F_41, E_40, A_8]: (~r2_hidden(F_41, '#skF_12') | ~r2_hidden(E_40, A_8))), inference(resolution, [status(thm)], [c_22, c_10370])).
% 6.63/2.31  tff(c_10428, plain, (![E_40, A_8]: (~r2_hidden(E_40, A_8))), inference(splitLeft, [status(thm)], [c_10385])).
% 6.63/2.31  tff(c_10456, plain, (![A_6708, B_6709]: (k2_zfmisc_1(A_6708, B_6709)='#skF_12')), inference(negUnitSimplification, [status(thm)], [c_10428, c_10428, c_42])).
% 6.63/2.31  tff(c_10429, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(A_8, B_9)=C_10)), inference(negUnitSimplification, [status(thm)], [c_10428, c_10428, c_42])).
% 6.63/2.31  tff(c_10576, plain, (![C_6999]: (C_6999='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_10456, c_10429])).
% 6.63/2.31  tff(c_9696, plain, (![A_7]: (k4_xboole_0('#skF_12', A_7)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_9680, c_9680, c_7774])).
% 6.63/2.31  tff(c_10000, plain, (![A_6646, B_6647, C_6648]: (r2_hidden('#skF_1'(A_6646, B_6647, C_6648), A_6646) | r2_hidden('#skF_2'(A_6646, B_6647, C_6648), C_6648) | k4_xboole_0(A_6646, B_6647)=C_6648)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_9741, plain, (![A_5888, B_5889, D_5890]: (r2_hidden('#skF_8'(A_5888, B_5889, k2_zfmisc_1(A_5888, B_5889), D_5890), B_5889) | ~r2_hidden(D_5890, k2_zfmisc_1(A_5888, B_5889)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.63/2.31  tff(c_9715, plain, (![D_5869, B_5870, A_5871]: (~r2_hidden(D_5869, B_5870) | ~r2_hidden(D_5869, k4_xboole_0(A_5871, B_5870)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.63/2.31  tff(c_9718, plain, (![D_5869, A_7]: (~r2_hidden(D_5869, A_7) | ~r2_hidden(D_5869, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_9696, c_9715])).
% 6.63/2.31  tff(c_9782, plain, (![A_5897, B_5898, D_5899]: (~r2_hidden('#skF_8'(A_5897, B_5898, k2_zfmisc_1(A_5897, B_5898), D_5899), '#skF_12') | ~r2_hidden(D_5899, k2_zfmisc_1(A_5897, B_5898)))), inference(resolution, [status(thm)], [c_9741, c_9718])).
% 6.63/2.31  tff(c_9788, plain, (![D_5900, A_5901]: (~r2_hidden(D_5900, k2_zfmisc_1(A_5901, '#skF_12')))), inference(resolution, [status(thm)], [c_26, c_9782])).
% 6.63/2.31  tff(c_9803, plain, (![F_41, E_40, A_8]: (~r2_hidden(F_41, '#skF_12') | ~r2_hidden(E_40, A_8))), inference(resolution, [status(thm)], [c_22, c_9788])).
% 6.63/2.31  tff(c_9804, plain, (![E_40, A_8]: (~r2_hidden(E_40, A_8))), inference(splitLeft, [status(thm)], [c_9803])).
% 6.63/2.31  tff(c_9887, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)='#skF_12')), inference(negUnitSimplification, [status(thm)], [c_9804, c_9804, c_18])).
% 6.63/2.31  tff(c_9814, plain, (![A_5904, B_5905, C_5906]: (k4_xboole_0(A_5904, B_5905)=C_5906)), inference(negUnitSimplification, [status(thm)], [c_9804, c_9804, c_18])).
% 6.63/2.31  tff(c_9976, plain, (![C_6388]: (C_6388='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_9887, c_9814])).
% 6.63/2.31  tff(c_9681, plain, (k1_xboole_0='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_9680, c_7773])).
% 6.63/2.31  tff(c_9690, plain, ('#skF_9'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_9681, c_9681, c_7772])).
% 6.63/2.31  tff(c_9691, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_9690])).
% 6.63/2.31  tff(c_9706, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_9681, c_9691, c_9681, c_46])).
% 6.63/2.31  tff(c_9987, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_9976, c_9706])).
% 6.63/2.31  tff(c_9988, plain, (![F_41]: (~r2_hidden(F_41, '#skF_12'))), inference(splitRight, [status(thm)], [c_9803])).
% 6.63/2.31  tff(c_10004, plain, (![B_6647, C_6648]: (r2_hidden('#skF_2'('#skF_12', B_6647, C_6648), C_6648) | k4_xboole_0('#skF_12', B_6647)=C_6648)), inference(resolution, [status(thm)], [c_10000, c_9988])).
% 6.63/2.31  tff(c_10184, plain, (![B_6666, C_6667]: (r2_hidden('#skF_2'('#skF_12', B_6666, C_6667), C_6667) | C_6667='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_9696, c_10004])).
% 6.63/2.31  tff(c_9787, plain, (![D_35, A_8]: (~r2_hidden(D_35, k2_zfmisc_1(A_8, '#skF_12')))), inference(resolution, [status(thm)], [c_26, c_9782])).
% 6.63/2.31  tff(c_10228, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_10184, c_9787])).
% 6.63/2.31  tff(c_10273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10228, c_9706])).
% 6.63/2.31  tff(c_10274, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_9690])).
% 6.63/2.31  tff(c_10277, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_9680, c_9681, c_9681, c_50])).
% 6.63/2.31  tff(c_10278, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_10274, c_10277])).
% 6.63/2.31  tff(c_10587, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_10576, c_10278])).
% 6.63/2.31  tff(c_10588, plain, (![F_41]: (~r2_hidden(F_41, '#skF_12'))), inference(splitRight, [status(thm)], [c_10385])).
% 6.63/2.31  tff(c_10979, plain, (![B_7258, C_7259]: (r2_hidden('#skF_2'('#skF_12', B_7258, C_7259), C_7259) | k4_xboole_0('#skF_12', B_7258)=C_7259)), inference(resolution, [status(thm)], [c_10939, c_10588])).
% 6.63/2.31  tff(c_11063, plain, (![B_7260, C_7261]: (r2_hidden('#skF_2'('#skF_12', B_7260, C_7261), C_7261) | C_7261='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_10283, c_10979])).
% 6.63/2.31  tff(c_10589, plain, (![F_7224]: (~r2_hidden(F_7224, '#skF_12'))), inference(splitRight, [status(thm)], [c_10385])).
% 6.63/2.31  tff(c_10605, plain, (![D_35, B_9]: (~r2_hidden(D_35, k2_zfmisc_1('#skF_12', B_9)))), inference(resolution, [status(thm)], [c_28, c_10589])).
% 6.63/2.31  tff(c_11119, plain, (![B_9]: (k2_zfmisc_1('#skF_12', B_9)='#skF_12')), inference(resolution, [status(thm)], [c_11063, c_10605])).
% 6.63/2.31  tff(c_11130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11119, c_10278])).
% 6.63/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.63/2.31  
% 6.63/2.31  Inference rules
% 6.63/2.31  ----------------------
% 6.63/2.31  #Ref     : 0
% 6.63/2.31  #Sup     : 2342
% 6.63/2.31  #Fact    : 0
% 6.63/2.31  #Define  : 0
% 6.63/2.31  #Split   : 27
% 6.63/2.31  #Chain   : 0
% 6.63/2.31  #Close   : 0
% 6.63/2.31  
% 6.63/2.31  Ordering : KBO
% 6.63/2.31  
% 6.63/2.31  Simplification rules
% 6.63/2.31  ----------------------
% 6.63/2.31  #Subsume      : 718
% 6.63/2.31  #Demod        : 281
% 6.63/2.31  #Tautology    : 141
% 6.63/2.31  #SimpNegUnit  : 126
% 6.63/2.31  #BackRed      : 90
% 6.63/2.31  
% 6.63/2.31  #Partial instantiations: 1772
% 6.63/2.31  #Strategies tried      : 1
% 6.63/2.31  
% 6.63/2.31  Timing (in seconds)
% 6.63/2.31  ----------------------
% 6.63/2.31  Preprocessing        : 0.30
% 6.63/2.31  Parsing              : 0.15
% 6.63/2.31  CNF conversion       : 0.03
% 6.63/2.31  Main loop            : 1.19
% 6.63/2.31  Inferencing          : 0.50
% 6.63/2.31  Reduction            : 0.30
% 6.63/2.31  Demodulation         : 0.16
% 6.63/2.31  BG Simplification    : 0.06
% 6.63/2.31  Subsumption          : 0.21
% 6.63/2.31  Abstraction          : 0.07
% 6.63/2.31  MUC search           : 0.00
% 6.63/2.31  Cooper               : 0.00
% 6.63/2.31  Total                : 1.58
% 6.63/2.31  Index Insertion      : 0.00
% 6.63/2.31  Index Deletion       : 0.00
% 6.63/2.31  Index Matching       : 0.00
% 6.63/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
