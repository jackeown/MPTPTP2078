%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:41 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 189 expanded)
%              Number of leaves         :   29 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  129 ( 389 expanded)
%              Number of equality atoms :   33 ( 100 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_44,plain,(
    k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) != k3_subset_1('#skF_3',k6_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k7_setfam_1(A_12,B_13),k1_zfmisc_1(k1_zfmisc_1(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_241,plain,(
    ! [A_65,B_66] :
      ( k7_setfam_1(A_65,k7_setfam_1(A_65,B_66)) = B_66
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_255,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_241])).

tff(c_1035,plain,(
    ! [C_153,B_154,A_155] :
      ( r2_hidden(C_153,B_154)
      | ~ r2_hidden(k3_subset_1(A_155,C_153),k7_setfam_1(A_155,B_154))
      | ~ m1_subset_1(C_153,k1_zfmisc_1(A_155))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k1_zfmisc_1(A_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1047,plain,(
    ! [C_153] :
      ( r2_hidden(C_153,k7_setfam_1('#skF_3','#skF_4'))
      | ~ r2_hidden(k3_subset_1('#skF_3',C_153),'#skF_4')
      | ~ m1_subset_1(C_153,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_1035])).

tff(c_1102,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1047])).

tff(c_1105,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_26,c_1102])).

tff(c_1112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1105])).

tff(c_1114,plain,(
    m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1047])).

tff(c_214,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k5_setfam_1(A_61,B_62),k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_224,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k5_setfam_1(A_61,B_62),A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(resolution,[status(thm)],[c_214,c_30])).

tff(c_1136,plain,(
    r1_tarski(k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1114,c_224])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(resolution,[status(thm)],[c_22,c_52])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_693,plain,(
    ! [A_125,B_126,C_127] :
      ( ~ r2_hidden('#skF_1'(A_125,B_126,C_127),B_126)
      | r2_hidden('#skF_2'(A_125,B_126,C_127),C_127)
      | k4_xboole_0(A_125,B_126) = C_127 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_702,plain,(
    ! [A_128,C_129] :
      ( r2_hidden('#skF_2'(A_128,A_128,C_129),C_129)
      | k4_xboole_0(A_128,A_128) = C_129 ) ),
    inference(resolution,[status(thm)],[c_18,c_693])).

tff(c_40,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_779,plain,(
    ! [C_132,A_133] :
      ( ~ r1_tarski(C_132,'#skF_2'(A_133,A_133,C_132))
      | k4_xboole_0(A_133,A_133) = C_132 ) ),
    inference(resolution,[status(thm)],[c_702,c_40])).

tff(c_784,plain,(
    ! [A_133] : k4_xboole_0(A_133,A_133) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_779])).

tff(c_700,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_693])).

tff(c_789,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k1_xboole_0 = C_3 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_700])).

tff(c_139,plain,(
    ! [A_48,C_49,B_50] :
      ( m1_subset_1(A_48,C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_147,plain,(
    ! [A_48] :
      ( m1_subset_1(A_48,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_139])).

tff(c_38,plain,(
    ! [A_22,C_24,B_23] :
      ( m1_subset_1(A_22,C_24)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(C_24))
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1144,plain,(
    ! [A_164] :
      ( m1_subset_1(A_164,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_164,k7_setfam_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1114,c_38])).

tff(c_1166,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_2'(A_1,A_1,k7_setfam_1('#skF_3','#skF_4')),k1_zfmisc_1('#skF_3'))
      | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_789,c_1144])).

tff(c_1356,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1166])).

tff(c_34,plain,(
    ! [A_18,C_21,B_19] :
      ( r2_hidden(k3_subset_1(A_18,C_21),k7_setfam_1(A_18,B_19))
      | ~ r2_hidden(C_21,B_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1372,plain,(
    ! [C_21] :
      ( r2_hidden(k3_subset_1('#skF_3',C_21),k1_xboole_0)
      | ~ r2_hidden(C_21,'#skF_4')
      | ~ m1_subset_1(C_21,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1356,c_34])).

tff(c_1655,plain,(
    ! [C_186] :
      ( r2_hidden(k3_subset_1('#skF_3',C_186),k1_xboole_0)
      | ~ r2_hidden(C_186,'#skF_4')
      | ~ m1_subset_1(C_186,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1372])).

tff(c_1671,plain,(
    ! [C_186] :
      ( ~ r1_tarski(k1_xboole_0,k3_subset_1('#skF_3',C_186))
      | ~ r2_hidden(C_186,'#skF_4')
      | ~ m1_subset_1(C_186,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1655,c_40])).

tff(c_1700,plain,(
    ! [C_187] :
      ( ~ r2_hidden(C_187,'#skF_4')
      | ~ m1_subset_1(C_187,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1671])).

tff(c_1732,plain,(
    ! [A_188] : ~ r2_hidden(A_188,'#skF_4') ),
    inference(resolution,[status(thm)],[c_147,c_1700])).

tff(c_1746,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_789,c_1732])).

tff(c_1762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1746])).

tff(c_1764,plain,(
    k7_setfam_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1166])).

tff(c_42,plain,(
    ! [A_27,B_28] :
      ( k6_setfam_1(A_27,k7_setfam_1(A_27,B_28)) = k3_subset_1(A_27,k5_setfam_1(A_27,B_28))
      | k1_xboole_0 = B_28
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1116,plain,
    ( k6_setfam_1('#skF_3',k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4'))) = k3_subset_1('#skF_3',k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')))
    | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1114,c_42])).

tff(c_1131,plain,
    ( k3_subset_1('#skF_3',k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4'))) = k6_setfam_1('#skF_3','#skF_4')
    | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_1116])).

tff(c_1973,plain,(
    k3_subset_1('#skF_3',k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4'))) = k6_setfam_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1764,c_1131])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_68,plain,(
    ! [A_43,B_44] :
      ( k3_subset_1(A_43,k3_subset_1(A_43,B_44)) = B_44
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    ! [B_17,A_16] :
      ( k3_subset_1(B_17,k3_subset_1(B_17,A_16)) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_1998,plain,
    ( k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3',k6_setfam_1('#skF_3','#skF_4'))
    | ~ r1_tarski(k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1973,c_75])).

tff(c_2003,plain,(
    k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3',k6_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1136,c_1998])).

tff(c_2005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.67  
% 3.92/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.68  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.92/1.68  
% 3.92/1.68  %Foreground sorts:
% 3.92/1.68  
% 3.92/1.68  
% 3.92/1.68  %Background operators:
% 3.92/1.68  
% 3.92/1.68  
% 3.92/1.68  %Foreground operators:
% 3.92/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.92/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.92/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.92/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.92/1.68  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.92/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.92/1.68  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.92/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.92/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.92/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.92/1.68  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.92/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.92/1.68  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.92/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.92/1.68  
% 3.92/1.69  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 3.92/1.69  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 3.92/1.69  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 3.92/1.69  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 3.92/1.69  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.92/1.69  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.92/1.69  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.92/1.69  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.92/1.69  tff(f_77, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.92/1.69  tff(f_72, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.92/1.69  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 3.92/1.69  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.92/1.69  tff(c_44, plain, (k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))!=k3_subset_1('#skF_3', k6_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.92/1.69  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.92/1.69  tff(c_26, plain, (![A_12, B_13]: (m1_subset_1(k7_setfam_1(A_12, B_13), k1_zfmisc_1(k1_zfmisc_1(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.92/1.69  tff(c_241, plain, (![A_65, B_66]: (k7_setfam_1(A_65, k7_setfam_1(A_65, B_66))=B_66 | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.92/1.69  tff(c_255, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_48, c_241])).
% 3.92/1.69  tff(c_1035, plain, (![C_153, B_154, A_155]: (r2_hidden(C_153, B_154) | ~r2_hidden(k3_subset_1(A_155, C_153), k7_setfam_1(A_155, B_154)) | ~m1_subset_1(C_153, k1_zfmisc_1(A_155)) | ~m1_subset_1(B_154, k1_zfmisc_1(k1_zfmisc_1(A_155))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.92/1.69  tff(c_1047, plain, (![C_153]: (r2_hidden(C_153, k7_setfam_1('#skF_3', '#skF_4')) | ~r2_hidden(k3_subset_1('#skF_3', C_153), '#skF_4') | ~m1_subset_1(C_153, k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_255, c_1035])).
% 3.92/1.69  tff(c_1102, plain, (~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1047])).
% 3.92/1.69  tff(c_1105, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_26, c_1102])).
% 3.92/1.69  tff(c_1112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1105])).
% 3.92/1.69  tff(c_1114, plain, (m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1047])).
% 3.92/1.69  tff(c_214, plain, (![A_61, B_62]: (m1_subset_1(k5_setfam_1(A_61, B_62), k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(A_61))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.92/1.69  tff(c_30, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.92/1.69  tff(c_224, plain, (![A_61, B_62]: (r1_tarski(k5_setfam_1(A_61, B_62), A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(A_61))))), inference(resolution, [status(thm)], [c_214, c_30])).
% 3.92/1.69  tff(c_1136, plain, (r1_tarski(k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_1114, c_224])).
% 3.92/1.69  tff(c_46, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.92/1.69  tff(c_22, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.92/1.69  tff(c_52, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.92/1.69  tff(c_64, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(resolution, [status(thm)], [c_22, c_52])).
% 3.92/1.69  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.92/1.69  tff(c_693, plain, (![A_125, B_126, C_127]: (~r2_hidden('#skF_1'(A_125, B_126, C_127), B_126) | r2_hidden('#skF_2'(A_125, B_126, C_127), C_127) | k4_xboole_0(A_125, B_126)=C_127)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.92/1.69  tff(c_702, plain, (![A_128, C_129]: (r2_hidden('#skF_2'(A_128, A_128, C_129), C_129) | k4_xboole_0(A_128, A_128)=C_129)), inference(resolution, [status(thm)], [c_18, c_693])).
% 3.92/1.69  tff(c_40, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.92/1.69  tff(c_779, plain, (![C_132, A_133]: (~r1_tarski(C_132, '#skF_2'(A_133, A_133, C_132)) | k4_xboole_0(A_133, A_133)=C_132)), inference(resolution, [status(thm)], [c_702, c_40])).
% 3.92/1.69  tff(c_784, plain, (![A_133]: (k4_xboole_0(A_133, A_133)=k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_779])).
% 3.92/1.69  tff(c_700, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_693])).
% 3.92/1.69  tff(c_789, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k1_xboole_0=C_3)), inference(demodulation, [status(thm), theory('equality')], [c_784, c_700])).
% 3.92/1.69  tff(c_139, plain, (![A_48, C_49, B_50]: (m1_subset_1(A_48, C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.92/1.69  tff(c_147, plain, (![A_48]: (m1_subset_1(A_48, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_139])).
% 3.92/1.69  tff(c_38, plain, (![A_22, C_24, B_23]: (m1_subset_1(A_22, C_24) | ~m1_subset_1(B_23, k1_zfmisc_1(C_24)) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.92/1.69  tff(c_1144, plain, (![A_164]: (m1_subset_1(A_164, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_164, k7_setfam_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_1114, c_38])).
% 3.92/1.69  tff(c_1166, plain, (![A_1]: (m1_subset_1('#skF_2'(A_1, A_1, k7_setfam_1('#skF_3', '#skF_4')), k1_zfmisc_1('#skF_3')) | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0)), inference(resolution, [status(thm)], [c_789, c_1144])).
% 3.92/1.69  tff(c_1356, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1166])).
% 3.92/1.69  tff(c_34, plain, (![A_18, C_21, B_19]: (r2_hidden(k3_subset_1(A_18, C_21), k7_setfam_1(A_18, B_19)) | ~r2_hidden(C_21, B_19) | ~m1_subset_1(C_21, k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.92/1.69  tff(c_1372, plain, (![C_21]: (r2_hidden(k3_subset_1('#skF_3', C_21), k1_xboole_0) | ~r2_hidden(C_21, '#skF_4') | ~m1_subset_1(C_21, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_1356, c_34])).
% 3.92/1.69  tff(c_1655, plain, (![C_186]: (r2_hidden(k3_subset_1('#skF_3', C_186), k1_xboole_0) | ~r2_hidden(C_186, '#skF_4') | ~m1_subset_1(C_186, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1372])).
% 3.92/1.69  tff(c_1671, plain, (![C_186]: (~r1_tarski(k1_xboole_0, k3_subset_1('#skF_3', C_186)) | ~r2_hidden(C_186, '#skF_4') | ~m1_subset_1(C_186, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_1655, c_40])).
% 3.92/1.69  tff(c_1700, plain, (![C_187]: (~r2_hidden(C_187, '#skF_4') | ~m1_subset_1(C_187, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1671])).
% 3.92/1.69  tff(c_1732, plain, (![A_188]: (~r2_hidden(A_188, '#skF_4'))), inference(resolution, [status(thm)], [c_147, c_1700])).
% 3.92/1.69  tff(c_1746, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_789, c_1732])).
% 3.92/1.69  tff(c_1762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1746])).
% 3.92/1.69  tff(c_1764, plain, (k7_setfam_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1166])).
% 3.92/1.69  tff(c_42, plain, (![A_27, B_28]: (k6_setfam_1(A_27, k7_setfam_1(A_27, B_28))=k3_subset_1(A_27, k5_setfam_1(A_27, B_28)) | k1_xboole_0=B_28 | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.92/1.69  tff(c_1116, plain, (k6_setfam_1('#skF_3', k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4')))=k3_subset_1('#skF_3', k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))) | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1114, c_42])).
% 3.92/1.69  tff(c_1131, plain, (k3_subset_1('#skF_3', k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4')))=k6_setfam_1('#skF_3', '#skF_4') | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_255, c_1116])).
% 3.92/1.69  tff(c_1973, plain, (k3_subset_1('#skF_3', k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4')))=k6_setfam_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1764, c_1131])).
% 3.92/1.69  tff(c_32, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.92/1.69  tff(c_68, plain, (![A_43, B_44]: (k3_subset_1(A_43, k3_subset_1(A_43, B_44))=B_44 | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.92/1.69  tff(c_75, plain, (![B_17, A_16]: (k3_subset_1(B_17, k3_subset_1(B_17, A_16))=A_16 | ~r1_tarski(A_16, B_17))), inference(resolution, [status(thm)], [c_32, c_68])).
% 3.92/1.69  tff(c_1998, plain, (k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', k6_setfam_1('#skF_3', '#skF_4')) | ~r1_tarski(k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4')), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1973, c_75])).
% 3.92/1.69  tff(c_2003, plain, (k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', k6_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1136, c_1998])).
% 3.92/1.69  tff(c_2005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2003])).
% 3.92/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.69  
% 3.92/1.69  Inference rules
% 3.92/1.69  ----------------------
% 3.92/1.69  #Ref     : 0
% 3.92/1.69  #Sup     : 455
% 3.92/1.69  #Fact    : 0
% 3.92/1.69  #Define  : 0
% 3.92/1.69  #Split   : 3
% 3.92/1.69  #Chain   : 0
% 3.92/1.69  #Close   : 0
% 3.92/1.69  
% 3.92/1.69  Ordering : KBO
% 3.92/1.69  
% 3.92/1.69  Simplification rules
% 3.92/1.69  ----------------------
% 3.92/1.69  #Subsume      : 42
% 3.92/1.69  #Demod        : 137
% 3.92/1.69  #Tautology    : 148
% 3.92/1.69  #SimpNegUnit  : 9
% 3.92/1.69  #BackRed      : 13
% 3.92/1.69  
% 3.92/1.69  #Partial instantiations: 0
% 3.92/1.69  #Strategies tried      : 1
% 3.92/1.69  
% 3.92/1.69  Timing (in seconds)
% 3.92/1.69  ----------------------
% 3.92/1.70  Preprocessing        : 0.32
% 3.92/1.70  Parsing              : 0.16
% 3.92/1.70  CNF conversion       : 0.02
% 3.92/1.70  Main loop            : 0.59
% 3.92/1.70  Inferencing          : 0.21
% 3.92/1.70  Reduction            : 0.17
% 3.92/1.70  Demodulation         : 0.12
% 3.92/1.70  BG Simplification    : 0.03
% 3.92/1.70  Subsumption          : 0.13
% 3.92/1.70  Abstraction          : 0.03
% 3.92/1.70  MUC search           : 0.00
% 3.92/1.70  Cooper               : 0.00
% 3.92/1.70  Total                : 0.94
% 3.92/1.70  Index Insertion      : 0.00
% 3.92/1.70  Index Deletion       : 0.00
% 3.92/1.70  Index Matching       : 0.00
% 3.92/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
