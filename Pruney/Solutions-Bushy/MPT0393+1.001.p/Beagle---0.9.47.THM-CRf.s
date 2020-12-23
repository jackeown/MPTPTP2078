%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0393+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:14 EST 2020

% Result     : Theorem 14.39s
% Output     : CNFRefutation 14.39s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 297 expanded)
%              Number of leaves         :   29 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  139 ( 867 expanded)
%              Number of equality atoms :   51 ( 508 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_8 > #skF_2 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_64,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_32,plain,(
    ! [C_26] : r2_hidden(C_26,k1_tarski(C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_68,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_72,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_68])).

tff(c_73,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_48])).

tff(c_965,plain,(
    ! [A_148,B_149,D_150] :
      ( r2_hidden('#skF_2'(A_148,B_149),D_150)
      | ~ r2_hidden(D_150,A_148)
      | r2_hidden('#skF_4'(A_148,B_149),A_148)
      | k1_setfam_1(A_148) = B_149
      | k1_xboole_0 = A_148 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_2'(A_3,B_4),B_4)
      | r2_hidden('#skF_4'(A_3,B_4),A_3)
      | k1_setfam_1(A_3) = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1730,plain,(
    ! [D_187,A_188] :
      ( ~ r2_hidden(D_187,A_188)
      | r2_hidden('#skF_4'(A_188,D_187),A_188)
      | k1_setfam_1(A_188) = D_187
      | k1_xboole_0 = A_188 ) ),
    inference(resolution,[status(thm)],[c_965,c_12])).

tff(c_30,plain,(
    ! [C_26,A_22] :
      ( C_26 = A_22
      | ~ r2_hidden(C_26,k1_tarski(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30845,plain,(
    ! [A_13925,D_13926] :
      ( '#skF_4'(k1_tarski(A_13925),D_13926) = A_13925
      | ~ r2_hidden(D_13926,k1_tarski(A_13925))
      | k1_setfam_1(k1_tarski(A_13925)) = D_13926
      | k1_tarski(A_13925) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1730,c_30])).

tff(c_30991,plain,(
    ! [C_13981] :
      ( '#skF_4'(k1_tarski(C_13981),C_13981) = C_13981
      | k1_setfam_1(k1_tarski(C_13981)) = C_13981
      | k1_tarski(C_13981) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_30845])).

tff(c_60,plain,(
    k1_setfam_1(k1_tarski('#skF_8')) != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_31385,plain,
    ( '#skF_4'(k1_tarski('#skF_8'),'#skF_8') = '#skF_8'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30991,c_60])).

tff(c_31391,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_31385])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_52,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(A_32,k1_zfmisc_1(B_33))
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_133,plain,(
    ! [C_59,B_60,A_61] :
      ( ~ v1_xboole_0(C_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(C_59))
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_137,plain,(
    ! [B_62,A_63,A_64] :
      ( ~ v1_xboole_0(B_62)
      | ~ r2_hidden(A_63,A_64)
      | ~ r1_tarski(A_64,B_62) ) ),
    inference(resolution,[status(thm)],[c_52,c_133])).

tff(c_151,plain,(
    ! [B_68,C_69] :
      ( ~ v1_xboole_0(B_68)
      | ~ r1_tarski(k1_tarski(C_69),B_68) ) ),
    inference(resolution,[status(thm)],[c_32,c_137])).

tff(c_156,plain,(
    ! [C_69] : ~ v1_xboole_0(k1_tarski(C_69)) ),
    inference(resolution,[status(thm)],[c_6,c_151])).

tff(c_31677,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_31391,c_156])).

tff(c_31775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_31677])).

tff(c_31777,plain,(
    k1_tarski('#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_31385])).

tff(c_1324,plain,(
    ! [A_164,B_165,D_166] :
      ( r2_hidden('#skF_2'(A_164,B_165),D_166)
      | ~ r2_hidden(D_166,A_164)
      | r2_hidden('#skF_3'(A_164,B_165),B_165)
      | k1_setfam_1(A_164) = B_165
      | k1_xboole_0 = A_164 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    ! [C_31,B_28,A_27] :
      ( r2_hidden(C_31,B_28)
      | ~ r2_hidden(C_31,A_27)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1395,plain,(
    ! [A_164,B_165,B_28,D_166] :
      ( r2_hidden('#skF_3'(A_164,B_165),B_28)
      | ~ r1_tarski(B_165,B_28)
      | r2_hidden('#skF_2'(A_164,B_165),D_166)
      | ~ r2_hidden(D_166,A_164)
      | k1_setfam_1(A_164) = B_165
      | k1_xboole_0 = A_164 ) ),
    inference(resolution,[status(thm)],[c_1324,c_42])).

tff(c_31776,plain,(
    '#skF_4'(k1_tarski('#skF_8'),'#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_31385])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_2'(A_3,B_4),B_4)
      | ~ r2_hidden('#skF_3'(A_3,B_4),'#skF_4'(A_3,B_4))
      | k1_setfam_1(A_3) = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31796,plain,
    ( ~ r2_hidden('#skF_2'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8')
    | ~ r2_hidden('#skF_3'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8')
    | k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_31776,c_8])).

tff(c_31809,plain,
    ( ~ r2_hidden('#skF_2'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8')
    | ~ r2_hidden('#skF_3'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_31777,c_60,c_31796])).

tff(c_31811,plain,(
    ~ r2_hidden('#skF_3'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_31809])).

tff(c_31821,plain,(
    ! [D_166] :
      ( ~ r1_tarski('#skF_8','#skF_8')
      | r2_hidden('#skF_2'(k1_tarski('#skF_8'),'#skF_8'),D_166)
      | ~ r2_hidden(D_166,k1_tarski('#skF_8'))
      | k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
      | k1_tarski('#skF_8') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1395,c_31811])).

tff(c_31837,plain,(
    ! [D_166] :
      ( r2_hidden('#skF_2'(k1_tarski('#skF_8'),'#skF_8'),D_166)
      | ~ r2_hidden(D_166,k1_tarski('#skF_8'))
      | k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
      | k1_tarski('#skF_8') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_31821])).

tff(c_32032,plain,(
    ! [D_14417] :
      ( r2_hidden('#skF_2'(k1_tarski('#skF_8'),'#skF_8'),D_14417)
      | ~ r2_hidden(D_14417,k1_tarski('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_31777,c_60,c_31837])).

tff(c_16,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_2'(A_3,B_4),B_4)
      | r2_hidden('#skF_3'(A_3,B_4),B_4)
      | k1_setfam_1(A_3) = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31831,plain,
    ( ~ r2_hidden('#skF_2'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8')
    | k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_31811])).

tff(c_31844,plain,(
    ~ r2_hidden('#skF_2'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_31777,c_60,c_31831])).

tff(c_32035,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_32032,c_31844])).

tff(c_32151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32035])).

tff(c_32153,plain,(
    r2_hidden('#skF_3'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_31809])).

tff(c_10,plain,(
    ! [A_3,B_4,D_20] :
      ( r2_hidden('#skF_2'(A_3,B_4),D_20)
      | ~ r2_hidden(D_20,A_3)
      | ~ r2_hidden('#skF_3'(A_3,B_4),'#skF_4'(A_3,B_4))
      | k1_setfam_1(A_3) = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31790,plain,(
    ! [D_20] :
      ( r2_hidden('#skF_2'(k1_tarski('#skF_8'),'#skF_8'),D_20)
      | ~ r2_hidden(D_20,k1_tarski('#skF_8'))
      | ~ r2_hidden('#skF_3'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8')
      | k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
      | k1_tarski('#skF_8') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31776,c_10])).

tff(c_31806,plain,(
    ! [D_20] :
      ( r2_hidden('#skF_2'(k1_tarski('#skF_8'),'#skF_8'),D_20)
      | ~ r2_hidden(D_20,k1_tarski('#skF_8'))
      | ~ r2_hidden('#skF_3'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_31777,c_60,c_31790])).

tff(c_32243,plain,(
    ! [D_14580] :
      ( r2_hidden('#skF_2'(k1_tarski('#skF_8'),'#skF_8'),D_14580)
      | ~ r2_hidden(D_14580,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32153,c_31806])).

tff(c_32152,plain,(
    ~ r2_hidden('#skF_2'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_31809])).

tff(c_32246,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_32243,c_32152])).

tff(c_32362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32246])).

%------------------------------------------------------------------------------
