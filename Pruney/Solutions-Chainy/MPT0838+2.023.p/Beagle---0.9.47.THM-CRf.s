%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:12 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 150 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 273 expanded)
%              Number of equality atoms :   31 (  87 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_48,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_42,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_75,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_88,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_75])).

tff(c_90,plain,(
    ! [A_65] :
      ( k2_relat_1(A_65) = k1_xboole_0
      | k1_relat_1(A_65) != k1_xboole_0
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_94,plain,
    ( k2_relat_1('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_90])).

tff(c_101,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_102,plain,(
    ! [A_66] :
      ( k1_relat_1(A_66) = k1_xboole_0
      | k2_relat_1(A_66) != k1_xboole_0
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_108,plain,
    ( k1_relat_1('#skF_7') = k1_xboole_0
    | k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_102])).

tff(c_114,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_108])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_433,plain,(
    ! [A_131,B_132] :
      ( r2_hidden(k4_tarski('#skF_1'(A_131,B_132),'#skF_2'(A_131,B_132)),A_131)
      | r2_hidden('#skF_3'(A_131,B_132),B_132)
      | k1_relat_1(A_131) = B_132 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_59,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(resolution,[status(thm)],[c_2,c_59])).

tff(c_251,plain,(
    ! [C_100,A_101] :
      ( r2_hidden(k4_tarski(C_100,'#skF_4'(A_101,k1_relat_1(A_101),C_100)),A_101)
      | ~ r2_hidden(C_100,k1_relat_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_273,plain,(
    ! [C_100] :
      ( r2_hidden(k4_tarski(C_100,'#skF_4'(k1_xboole_0,k1_xboole_0,C_100)),k1_xboole_0)
      | ~ r2_hidden(C_100,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_251])).

tff(c_294,plain,(
    ! [C_105] :
      ( r2_hidden(k4_tarski(C_105,'#skF_4'(k1_xboole_0,k1_xboole_0,C_105)),k1_xboole_0)
      | ~ r2_hidden(C_105,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_273])).

tff(c_30,plain,(
    ! [B_28,A_27] :
      ( ~ r1_tarski(B_28,A_27)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_304,plain,(
    ! [C_105] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(C_105,'#skF_4'(k1_xboole_0,k1_xboole_0,C_105)))
      | ~ r2_hidden(C_105,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_294,c_30])).

tff(c_313,plain,(
    ! [C_105] : ~ r2_hidden(C_105,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_304])).

tff(c_440,plain,(
    ! [B_132] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_132),B_132)
      | k1_relat_1(k1_xboole_0) = B_132 ) ),
    inference(resolution,[status(thm)],[c_433,c_313])).

tff(c_465,plain,(
    ! [B_133] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_133),B_133)
      | k1_xboole_0 = B_133 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_440])).

tff(c_168,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_relset_1(A_84,B_85,C_86) = k2_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_181,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_168])).

tff(c_210,plain,(
    ! [A_96,B_97,C_98] :
      ( m1_subset_1(k2_relset_1(A_96,B_97,C_98),k1_zfmisc_1(B_97))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_230,plain,
    ( m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_210])).

tff(c_240,plain,(
    m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_230])).

tff(c_8,plain,(
    ! [A_4,C_6,B_5] :
      ( m1_subset_1(A_4,C_6)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(C_6))
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_248,plain,(
    ! [A_4] :
      ( m1_subset_1(A_4,'#skF_6')
      | ~ r2_hidden(A_4,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_240,c_8])).

tff(c_476,plain,
    ( m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6')
    | k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_465,c_248])).

tff(c_491,plain,(
    m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_476])).

tff(c_40,plain,(
    ! [D_52] :
      ( ~ r2_hidden(D_52,k2_relset_1('#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1(D_52,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_191,plain,(
    ! [D_52] :
      ( ~ r2_hidden(D_52,k2_relat_1('#skF_7'))
      | ~ m1_subset_1(D_52,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_40])).

tff(c_482,plain,
    ( ~ m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6')
    | k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_465,c_191])).

tff(c_495,plain,(
    ~ m1_subset_1('#skF_3'(k1_xboole_0,k2_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_482])).

tff(c_498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_495])).

tff(c_500,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_545,plain,(
    ! [A_144,B_145,C_146] :
      ( k1_relset_1(A_144,B_145,C_146) = k1_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_552,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_545])).

tff(c_559,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_552])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_559])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:27:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.41  
% 2.74/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.41  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.74/1.41  
% 2.74/1.41  %Foreground sorts:
% 2.74/1.41  
% 2.74/1.41  
% 2.74/1.41  %Background operators:
% 2.74/1.41  
% 2.74/1.41  
% 2.74/1.41  %Foreground operators:
% 2.74/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.74/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.74/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.74/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.74/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.74/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.74/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.74/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.74/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.41  
% 2.74/1.42  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.74/1.42  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.74/1.42  tff(f_54, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.74/1.42  tff(f_48, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.74/1.42  tff(f_45, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.74/1.42  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.74/1.42  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.74/1.42  tff(f_59, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.74/1.42  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.74/1.42  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.74/1.42  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.74/1.42  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.74/1.42  tff(c_42, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.74/1.42  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.74/1.42  tff(c_75, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.74/1.42  tff(c_88, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_75])).
% 2.74/1.42  tff(c_90, plain, (![A_65]: (k2_relat_1(A_65)=k1_xboole_0 | k1_relat_1(A_65)!=k1_xboole_0 | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.74/1.42  tff(c_94, plain, (k2_relat_1('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_90])).
% 2.74/1.42  tff(c_101, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_94])).
% 2.74/1.42  tff(c_102, plain, (![A_66]: (k1_relat_1(A_66)=k1_xboole_0 | k2_relat_1(A_66)!=k1_xboole_0 | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.74/1.42  tff(c_108, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | k2_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_102])).
% 2.74/1.42  tff(c_114, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_101, c_108])).
% 2.74/1.42  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.74/1.42  tff(c_433, plain, (![A_131, B_132]: (r2_hidden(k4_tarski('#skF_1'(A_131, B_132), '#skF_2'(A_131, B_132)), A_131) | r2_hidden('#skF_3'(A_131, B_132), B_132) | k1_relat_1(A_131)=B_132)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.74/1.42  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.42  tff(c_59, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.42  tff(c_67, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(resolution, [status(thm)], [c_2, c_59])).
% 2.74/1.42  tff(c_251, plain, (![C_100, A_101]: (r2_hidden(k4_tarski(C_100, '#skF_4'(A_101, k1_relat_1(A_101), C_100)), A_101) | ~r2_hidden(C_100, k1_relat_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.74/1.42  tff(c_273, plain, (![C_100]: (r2_hidden(k4_tarski(C_100, '#skF_4'(k1_xboole_0, k1_xboole_0, C_100)), k1_xboole_0) | ~r2_hidden(C_100, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_251])).
% 2.74/1.42  tff(c_294, plain, (![C_105]: (r2_hidden(k4_tarski(C_105, '#skF_4'(k1_xboole_0, k1_xboole_0, C_105)), k1_xboole_0) | ~r2_hidden(C_105, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_273])).
% 2.74/1.42  tff(c_30, plain, (![B_28, A_27]: (~r1_tarski(B_28, A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.74/1.42  tff(c_304, plain, (![C_105]: (~r1_tarski(k1_xboole_0, k4_tarski(C_105, '#skF_4'(k1_xboole_0, k1_xboole_0, C_105))) | ~r2_hidden(C_105, k1_xboole_0))), inference(resolution, [status(thm)], [c_294, c_30])).
% 2.74/1.42  tff(c_313, plain, (![C_105]: (~r2_hidden(C_105, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_304])).
% 2.74/1.42  tff(c_440, plain, (![B_132]: (r2_hidden('#skF_3'(k1_xboole_0, B_132), B_132) | k1_relat_1(k1_xboole_0)=B_132)), inference(resolution, [status(thm)], [c_433, c_313])).
% 2.74/1.42  tff(c_465, plain, (![B_133]: (r2_hidden('#skF_3'(k1_xboole_0, B_133), B_133) | k1_xboole_0=B_133)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_440])).
% 2.74/1.42  tff(c_168, plain, (![A_84, B_85, C_86]: (k2_relset_1(A_84, B_85, C_86)=k2_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.74/1.42  tff(c_181, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_168])).
% 2.74/1.42  tff(c_210, plain, (![A_96, B_97, C_98]: (m1_subset_1(k2_relset_1(A_96, B_97, C_98), k1_zfmisc_1(B_97)) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.74/1.42  tff(c_230, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_181, c_210])).
% 2.74/1.42  tff(c_240, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_230])).
% 2.74/1.42  tff(c_8, plain, (![A_4, C_6, B_5]: (m1_subset_1(A_4, C_6) | ~m1_subset_1(B_5, k1_zfmisc_1(C_6)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.42  tff(c_248, plain, (![A_4]: (m1_subset_1(A_4, '#skF_6') | ~r2_hidden(A_4, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_240, c_8])).
% 2.74/1.42  tff(c_476, plain, (m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6') | k2_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_465, c_248])).
% 2.74/1.42  tff(c_491, plain, (m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_114, c_476])).
% 2.74/1.42  tff(c_40, plain, (![D_52]: (~r2_hidden(D_52, k2_relset_1('#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1(D_52, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.74/1.42  tff(c_191, plain, (![D_52]: (~r2_hidden(D_52, k2_relat_1('#skF_7')) | ~m1_subset_1(D_52, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_40])).
% 2.74/1.42  tff(c_482, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6') | k2_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_465, c_191])).
% 2.74/1.42  tff(c_495, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k2_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_114, c_482])).
% 2.74/1.42  tff(c_498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_491, c_495])).
% 2.74/1.42  tff(c_500, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_94])).
% 2.74/1.42  tff(c_545, plain, (![A_144, B_145, C_146]: (k1_relset_1(A_144, B_145, C_146)=k1_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.74/1.42  tff(c_552, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_545])).
% 2.74/1.42  tff(c_559, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_500, c_552])).
% 2.74/1.42  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_559])).
% 2.74/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.42  
% 2.74/1.42  Inference rules
% 2.74/1.42  ----------------------
% 2.74/1.42  #Ref     : 0
% 2.74/1.42  #Sup     : 107
% 2.74/1.42  #Fact    : 0
% 2.74/1.42  #Define  : 0
% 2.74/1.42  #Split   : 1
% 2.74/1.42  #Chain   : 0
% 2.74/1.42  #Close   : 0
% 2.74/1.42  
% 2.74/1.42  Ordering : KBO
% 2.74/1.42  
% 2.74/1.42  Simplification rules
% 2.74/1.42  ----------------------
% 2.74/1.42  #Subsume      : 12
% 2.74/1.42  #Demod        : 50
% 2.74/1.42  #Tautology    : 38
% 2.74/1.42  #SimpNegUnit  : 5
% 2.74/1.42  #BackRed      : 2
% 2.74/1.42  
% 2.74/1.42  #Partial instantiations: 0
% 2.74/1.42  #Strategies tried      : 1
% 2.74/1.42  
% 2.74/1.42  Timing (in seconds)
% 2.74/1.42  ----------------------
% 2.74/1.43  Preprocessing        : 0.31
% 2.74/1.43  Parsing              : 0.15
% 2.74/1.43  CNF conversion       : 0.02
% 2.74/1.43  Main loop            : 0.28
% 2.74/1.43  Inferencing          : 0.11
% 2.74/1.43  Reduction            : 0.08
% 2.74/1.43  Demodulation         : 0.06
% 2.74/1.43  BG Simplification    : 0.02
% 2.74/1.43  Subsumption          : 0.05
% 2.74/1.43  Abstraction          : 0.02
% 2.74/1.43  MUC search           : 0.00
% 2.74/1.43  Cooper               : 0.00
% 2.74/1.43  Total                : 0.62
% 2.74/1.43  Index Insertion      : 0.00
% 2.74/1.43  Index Deletion       : 0.00
% 2.74/1.43  Index Matching       : 0.00
% 2.74/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
