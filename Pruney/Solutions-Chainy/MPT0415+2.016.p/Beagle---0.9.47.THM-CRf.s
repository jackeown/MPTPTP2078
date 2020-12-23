%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:47 EST 2020

% Result     : Theorem 4.49s
% Output     : CNFRefutation 4.49s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 429 expanded)
%              Number of leaves         :   20 ( 152 expanded)
%              Depth                    :   14
%              Number of atoms          :  133 ( 935 expanded)
%              Number of equality atoms :   39 ( 360 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_96,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k7_setfam_1(A_33,B_34),k1_zfmisc_1(k1_zfmisc_1(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(A_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_101,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_96])).

tff(c_104,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_101])).

tff(c_116,plain,(
    ! [A_35,B_36,C_37] :
      ( m1_subset_1('#skF_1'(A_35,B_36,C_37),k1_zfmisc_1(A_35))
      | k7_setfam_1(A_35,B_36) = C_37
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k1_zfmisc_1(A_35)))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k3_subset_1(A_7,k3_subset_1(A_7,B_8)) = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_353,plain,(
    ! [A_64,B_65,C_66] :
      ( k3_subset_1(A_64,k3_subset_1(A_64,'#skF_1'(A_64,B_65,C_66))) = '#skF_1'(A_64,B_65,C_66)
      | k7_setfam_1(A_64,B_65) = C_66
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k1_zfmisc_1(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_64))) ) ),
    inference(resolution,[status(thm)],[c_116,c_12])).

tff(c_374,plain,(
    ! [B_67] :
      ( k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_1'('#skF_2',B_67,k1_xboole_0))) = '#skF_1'('#skF_2',B_67,k1_xboole_0)
      | k7_setfam_1('#skF_2',B_67) = k1_xboole_0
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_104,c_353])).

tff(c_398,plain,
    ( k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0))) = '#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0)
    | k7_setfam_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_104,c_374])).

tff(c_403,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_398])).

tff(c_14,plain,(
    ! [A_9,B_10,C_16] :
      ( m1_subset_1('#skF_1'(A_9,B_10,C_16),k1_zfmisc_1(A_9))
      | k7_setfam_1(A_9,B_10) = C_16
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k1_zfmisc_1(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_470,plain,(
    ! [B_73] :
      ( k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_1'('#skF_2',B_73,'#skF_3'))) = '#skF_1'('#skF_2',B_73,'#skF_3')
      | k7_setfam_1('#skF_2',B_73) = '#skF_3'
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_34,c_353])).

tff(c_480,plain,
    ( k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3'))) = '#skF_1'('#skF_2',k1_xboole_0,'#skF_3')
    | k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_104,c_470])).

tff(c_495,plain,
    ( k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3'))) = '#skF_1'('#skF_2',k1_xboole_0,'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_480])).

tff(c_496,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3'))) = '#skF_1'('#skF_2',k1_xboole_0,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_495])).

tff(c_618,plain,
    ( m1_subset_1('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3')),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_10])).

tff(c_657,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3')),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_618])).

tff(c_665,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_657])).

tff(c_668,plain,
    ( k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_14,c_665])).

tff(c_671,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_34,c_403,c_668])).

tff(c_673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_671])).

tff(c_675,plain,(
    m1_subset_1(k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3')),k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_618])).

tff(c_426,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_hidden('#skF_1'(A_68,B_69,C_70),C_70)
      | r2_hidden(k3_subset_1(A_68,'#skF_1'(A_68,B_69,C_70)),B_69)
      | k7_setfam_1(A_68,B_69) = C_70
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k1_zfmisc_1(A_68)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_24,B_25] : ~ r2_hidden(A_24,k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_61])).

tff(c_440,plain,(
    ! [A_71,C_72] :
      ( r2_hidden('#skF_1'(A_71,k1_xboole_0,C_72),C_72)
      | k7_setfam_1(A_71,k1_xboole_0) = C_72
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k1_zfmisc_1(A_71)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_71))) ) ),
    inference(resolution,[status(thm)],[c_426,c_64])).

tff(c_454,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_3')
    | k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3'
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_34,c_440])).

tff(c_467,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_403,c_454])).

tff(c_468,plain,(
    r2_hidden('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_467])).

tff(c_88,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k3_subset_1(A_31,B_32),k1_zfmisc_1(A_31))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_94,plain,(
    ! [A_31,B_32] :
      ( k3_subset_1(A_31,k3_subset_1(A_31,k3_subset_1(A_31,B_32))) = k3_subset_1(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(resolution,[status(thm)],[c_88,c_12])).

tff(c_193,plain,(
    ! [D_42,A_43,B_44] :
      ( r2_hidden(D_42,k7_setfam_1(A_43,B_44))
      | ~ r2_hidden(k3_subset_1(A_43,D_42),B_44)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(A_43))
      | ~ m1_subset_1(k7_setfam_1(A_43,B_44),k1_zfmisc_1(k1_zfmisc_1(A_43)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(A_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1626,plain,(
    ! [A_125,B_126,B_127] :
      ( r2_hidden(k3_subset_1(A_125,k3_subset_1(A_125,B_126)),k7_setfam_1(A_125,B_127))
      | ~ r2_hidden(k3_subset_1(A_125,B_126),B_127)
      | ~ m1_subset_1(k3_subset_1(A_125,k3_subset_1(A_125,B_126)),k1_zfmisc_1(A_125))
      | ~ m1_subset_1(k7_setfam_1(A_125,B_127),k1_zfmisc_1(k1_zfmisc_1(A_125)))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k1_zfmisc_1(A_125)))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_193])).

tff(c_1700,plain,(
    ! [B_126] :
      ( r2_hidden(k3_subset_1('#skF_2',k3_subset_1('#skF_2',B_126)),k1_xboole_0)
      | ~ r2_hidden(k3_subset_1('#skF_2',B_126),'#skF_3')
      | ~ m1_subset_1(k3_subset_1('#skF_2',k3_subset_1('#skF_2',B_126)),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(B_126,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1626])).

tff(c_1718,plain,(
    ! [B_126] :
      ( r2_hidden(k3_subset_1('#skF_2',k3_subset_1('#skF_2',B_126)),k1_xboole_0)
      | ~ r2_hidden(k3_subset_1('#skF_2',B_126),'#skF_3')
      | ~ m1_subset_1(k3_subset_1('#skF_2',k3_subset_1('#skF_2',B_126)),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_126,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_104,c_30,c_1700])).

tff(c_1720,plain,(
    ! [B_128] :
      ( ~ r2_hidden(k3_subset_1('#skF_2',B_128),'#skF_3')
      | ~ m1_subset_1(k3_subset_1('#skF_2',k3_subset_1('#skF_2',B_128)),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_128,k1_zfmisc_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1718])).

tff(c_1763,plain,
    ( ~ r2_hidden(k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3'))),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3')),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3')),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_1720])).

tff(c_1786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_675,c_468,c_496,c_1763])).

tff(c_1788,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_398])).

tff(c_2058,plain,(
    ! [A_138,B_139,C_140] :
      ( r2_hidden('#skF_1'(A_138,B_139,C_140),C_140)
      | r2_hidden(k3_subset_1(A_138,'#skF_1'(A_138,B_139,C_140)),B_139)
      | k7_setfam_1(A_138,B_139) = C_140
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k1_zfmisc_1(A_138)))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k1_zfmisc_1(A_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2263,plain,(
    ! [A_149,C_150] :
      ( r2_hidden('#skF_1'(A_149,k1_xboole_0,C_150),C_150)
      | k7_setfam_1(A_149,k1_xboole_0) = C_150
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k1_zfmisc_1(A_149)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_149))) ) ),
    inference(resolution,[status(thm)],[c_2058,c_64])).

tff(c_2270,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k7_setfam_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_104,c_2263])).

tff(c_2284,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k7_setfam_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2270])).

tff(c_2286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1788,c_64,c_2284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:35:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.49/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.87  
% 4.49/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.87  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 4.49/1.87  
% 4.49/1.87  %Foreground sorts:
% 4.49/1.87  
% 4.49/1.87  
% 4.49/1.87  %Background operators:
% 4.49/1.87  
% 4.49/1.87  
% 4.49/1.87  %Foreground operators:
% 4.49/1.87  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.49/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.49/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.49/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.49/1.87  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 4.49/1.87  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.49/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.49/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.49/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.49/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.49/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.49/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.49/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.49/1.87  
% 4.49/1.88  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 4.49/1.88  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 4.49/1.88  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 4.49/1.88  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.49/1.88  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.49/1.88  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.49/1.88  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 4.49/1.88  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.49/1.88  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.49/1.88  tff(c_30, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.49/1.88  tff(c_96, plain, (![A_33, B_34]: (m1_subset_1(k7_setfam_1(A_33, B_34), k1_zfmisc_1(k1_zfmisc_1(A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(k1_zfmisc_1(A_33))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.49/1.88  tff(c_101, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_30, c_96])).
% 4.49/1.88  tff(c_104, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_101])).
% 4.49/1.88  tff(c_116, plain, (![A_35, B_36, C_37]: (m1_subset_1('#skF_1'(A_35, B_36, C_37), k1_zfmisc_1(A_35)) | k7_setfam_1(A_35, B_36)=C_37 | ~m1_subset_1(C_37, k1_zfmisc_1(k1_zfmisc_1(A_35))) | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(A_35))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.49/1.88  tff(c_12, plain, (![A_7, B_8]: (k3_subset_1(A_7, k3_subset_1(A_7, B_8))=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.49/1.88  tff(c_353, plain, (![A_64, B_65, C_66]: (k3_subset_1(A_64, k3_subset_1(A_64, '#skF_1'(A_64, B_65, C_66)))='#skF_1'(A_64, B_65, C_66) | k7_setfam_1(A_64, B_65)=C_66 | ~m1_subset_1(C_66, k1_zfmisc_1(k1_zfmisc_1(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_64))))), inference(resolution, [status(thm)], [c_116, c_12])).
% 4.49/1.88  tff(c_374, plain, (![B_67]: (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_1'('#skF_2', B_67, k1_xboole_0)))='#skF_1'('#skF_2', B_67, k1_xboole_0) | k7_setfam_1('#skF_2', B_67)=k1_xboole_0 | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_104, c_353])).
% 4.49/1.88  tff(c_398, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0)))='#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0) | k7_setfam_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_104, c_374])).
% 4.49/1.88  tff(c_403, plain, (k7_setfam_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_398])).
% 4.49/1.88  tff(c_14, plain, (![A_9, B_10, C_16]: (m1_subset_1('#skF_1'(A_9, B_10, C_16), k1_zfmisc_1(A_9)) | k7_setfam_1(A_9, B_10)=C_16 | ~m1_subset_1(C_16, k1_zfmisc_1(k1_zfmisc_1(A_9))) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.49/1.88  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.49/1.88  tff(c_470, plain, (![B_73]: (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_1'('#skF_2', B_73, '#skF_3')))='#skF_1'('#skF_2', B_73, '#skF_3') | k7_setfam_1('#skF_2', B_73)='#skF_3' | ~m1_subset_1(B_73, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_34, c_353])).
% 4.49/1.88  tff(c_480, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3')))='#skF_1'('#skF_2', k1_xboole_0, '#skF_3') | k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_104, c_470])).
% 4.49/1.88  tff(c_495, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3')))='#skF_1'('#skF_2', k1_xboole_0, '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_403, c_480])).
% 4.49/1.88  tff(c_496, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3')))='#skF_1'('#skF_2', k1_xboole_0, '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_495])).
% 4.49/1.88  tff(c_618, plain, (m1_subset_1('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3')), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_496, c_10])).
% 4.49/1.88  tff(c_657, plain, (~m1_subset_1(k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3')), k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_618])).
% 4.49/1.88  tff(c_665, plain, (~m1_subset_1('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_657])).
% 4.49/1.88  tff(c_668, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_665])).
% 4.49/1.88  tff(c_671, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_34, c_403, c_668])).
% 4.49/1.88  tff(c_673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_671])).
% 4.49/1.88  tff(c_675, plain, (m1_subset_1(k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3')), k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_618])).
% 4.49/1.88  tff(c_426, plain, (![A_68, B_69, C_70]: (r2_hidden('#skF_1'(A_68, B_69, C_70), C_70) | r2_hidden(k3_subset_1(A_68, '#skF_1'(A_68, B_69, C_70)), B_69) | k7_setfam_1(A_68, B_69)=C_70 | ~m1_subset_1(C_70, k1_zfmisc_1(k1_zfmisc_1(A_68))) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.49/1.88  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.49/1.88  tff(c_61, plain, (![A_24, B_25]: (~r2_hidden(A_24, k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.49/1.88  tff(c_64, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_61])).
% 4.49/1.88  tff(c_440, plain, (![A_71, C_72]: (r2_hidden('#skF_1'(A_71, k1_xboole_0, C_72), C_72) | k7_setfam_1(A_71, k1_xboole_0)=C_72 | ~m1_subset_1(C_72, k1_zfmisc_1(k1_zfmisc_1(A_71))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_71))))), inference(resolution, [status(thm)], [c_426, c_64])).
% 4.49/1.88  tff(c_454, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_3') | k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3' | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_34, c_440])).
% 4.49/1.88  tff(c_467, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_403, c_454])).
% 4.49/1.88  tff(c_468, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_467])).
% 4.49/1.88  tff(c_88, plain, (![A_31, B_32]: (m1_subset_1(k3_subset_1(A_31, B_32), k1_zfmisc_1(A_31)) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.49/1.88  tff(c_94, plain, (![A_31, B_32]: (k3_subset_1(A_31, k3_subset_1(A_31, k3_subset_1(A_31, B_32)))=k3_subset_1(A_31, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(resolution, [status(thm)], [c_88, c_12])).
% 4.49/1.88  tff(c_193, plain, (![D_42, A_43, B_44]: (r2_hidden(D_42, k7_setfam_1(A_43, B_44)) | ~r2_hidden(k3_subset_1(A_43, D_42), B_44) | ~m1_subset_1(D_42, k1_zfmisc_1(A_43)) | ~m1_subset_1(k7_setfam_1(A_43, B_44), k1_zfmisc_1(k1_zfmisc_1(A_43))) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(A_43))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.49/1.88  tff(c_1626, plain, (![A_125, B_126, B_127]: (r2_hidden(k3_subset_1(A_125, k3_subset_1(A_125, B_126)), k7_setfam_1(A_125, B_127)) | ~r2_hidden(k3_subset_1(A_125, B_126), B_127) | ~m1_subset_1(k3_subset_1(A_125, k3_subset_1(A_125, B_126)), k1_zfmisc_1(A_125)) | ~m1_subset_1(k7_setfam_1(A_125, B_127), k1_zfmisc_1(k1_zfmisc_1(A_125))) | ~m1_subset_1(B_127, k1_zfmisc_1(k1_zfmisc_1(A_125))) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_193])).
% 4.49/1.88  tff(c_1700, plain, (![B_126]: (r2_hidden(k3_subset_1('#skF_2', k3_subset_1('#skF_2', B_126)), k1_xboole_0) | ~r2_hidden(k3_subset_1('#skF_2', B_126), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_2', k3_subset_1('#skF_2', B_126)), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(B_126, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1626])).
% 4.49/1.88  tff(c_1718, plain, (![B_126]: (r2_hidden(k3_subset_1('#skF_2', k3_subset_1('#skF_2', B_126)), k1_xboole_0) | ~r2_hidden(k3_subset_1('#skF_2', B_126), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_2', k3_subset_1('#skF_2', B_126)), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_126, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_104, c_30, c_1700])).
% 4.49/1.88  tff(c_1720, plain, (![B_128]: (~r2_hidden(k3_subset_1('#skF_2', B_128), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_2', k3_subset_1('#skF_2', B_128)), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_128, k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_64, c_1718])).
% 4.49/1.88  tff(c_1763, plain, (~r2_hidden(k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3'))), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3')), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3')), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_496, c_1720])).
% 4.49/1.88  tff(c_1786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_675, c_675, c_468, c_496, c_1763])).
% 4.49/1.88  tff(c_1788, plain, (k7_setfam_1('#skF_2', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_398])).
% 4.49/1.88  tff(c_2058, plain, (![A_138, B_139, C_140]: (r2_hidden('#skF_1'(A_138, B_139, C_140), C_140) | r2_hidden(k3_subset_1(A_138, '#skF_1'(A_138, B_139, C_140)), B_139) | k7_setfam_1(A_138, B_139)=C_140 | ~m1_subset_1(C_140, k1_zfmisc_1(k1_zfmisc_1(A_138))) | ~m1_subset_1(B_139, k1_zfmisc_1(k1_zfmisc_1(A_138))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.49/1.88  tff(c_2263, plain, (![A_149, C_150]: (r2_hidden('#skF_1'(A_149, k1_xboole_0, C_150), C_150) | k7_setfam_1(A_149, k1_xboole_0)=C_150 | ~m1_subset_1(C_150, k1_zfmisc_1(k1_zfmisc_1(A_149))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_149))))), inference(resolution, [status(thm)], [c_2058, c_64])).
% 4.49/1.88  tff(c_2270, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_104, c_2263])).
% 4.49/1.88  tff(c_2284, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_2270])).
% 4.49/1.88  tff(c_2286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1788, c_64, c_2284])).
% 4.49/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.88  
% 4.49/1.88  Inference rules
% 4.49/1.88  ----------------------
% 4.49/1.88  #Ref     : 0
% 4.49/1.88  #Sup     : 504
% 4.49/1.88  #Fact    : 2
% 4.49/1.88  #Define  : 0
% 4.49/1.88  #Split   : 14
% 4.49/1.88  #Chain   : 0
% 4.49/1.88  #Close   : 0
% 4.49/1.88  
% 4.49/1.88  Ordering : KBO
% 4.49/1.88  
% 4.49/1.88  Simplification rules
% 4.49/1.88  ----------------------
% 4.49/1.88  #Subsume      : 68
% 4.49/1.88  #Demod        : 495
% 4.49/1.88  #Tautology    : 182
% 4.49/1.88  #SimpNegUnit  : 82
% 4.49/1.88  #BackRed      : 11
% 4.49/1.88  
% 4.49/1.88  #Partial instantiations: 0
% 4.49/1.88  #Strategies tried      : 1
% 4.49/1.88  
% 4.49/1.88  Timing (in seconds)
% 4.49/1.88  ----------------------
% 4.49/1.88  Preprocessing        : 0.33
% 4.49/1.88  Parsing              : 0.17
% 4.49/1.89  CNF conversion       : 0.02
% 4.49/1.89  Main loop            : 0.75
% 4.49/1.89  Inferencing          : 0.27
% 4.49/1.89  Reduction            : 0.25
% 4.49/1.89  Demodulation         : 0.18
% 4.49/1.89  BG Simplification    : 0.04
% 4.49/1.89  Subsumption          : 0.16
% 4.49/1.89  Abstraction          : 0.05
% 4.49/1.89  MUC search           : 0.00
% 4.49/1.89  Cooper               : 0.00
% 4.49/1.89  Total                : 1.11
% 4.49/1.89  Index Insertion      : 0.00
% 4.49/1.89  Index Deletion       : 0.00
% 4.49/1.89  Index Matching       : 0.00
% 4.49/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
