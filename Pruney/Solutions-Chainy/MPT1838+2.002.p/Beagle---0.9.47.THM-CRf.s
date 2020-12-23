%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:14 EST 2020

% Result     : Theorem 14.16s
% Output     : CNFRefutation 14.16s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 318 expanded)
%              Number of leaves         :   43 ( 122 expanded)
%              Depth                    :   12
%              Number of atoms          :  166 ( 564 expanded)
%              Number of equality atoms :   69 ( 243 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_4 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_108,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_53,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_74,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_89,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_244,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,B_73)
      | k4_xboole_0(A_72,B_73) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_749,plain,(
    ! [A_122,B_123] :
      ( k3_xboole_0(A_122,B_123) = A_122
      | k4_xboole_0(A_122,B_123) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_244,c_36])).

tff(c_764,plain,(
    ! [A_124] : k3_xboole_0(k1_xboole_0,A_124) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_749])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_869,plain,(
    ! [D_130,A_131] :
      ( r2_hidden(D_130,A_131)
      | ~ r2_hidden(D_130,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_14])).

tff(c_877,plain,(
    ! [A_131] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_131)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_869])).

tff(c_878,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_877])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_567,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_2'(A_102,B_103),A_102)
      | r1_tarski(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_595,plain,(
    ! [A_102] : r1_tarski(A_102,A_102) ),
    inference(resolution,[status(thm)],[c_567,c_8])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_78,plain,(
    v1_zfmisc_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_72,plain,(
    ! [A_43] :
      ( m1_subset_1('#skF_7'(A_43),A_43)
      | ~ v1_zfmisc_1(A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_801,plain,(
    ! [A_125,B_126] :
      ( k6_domain_1(A_125,B_126) = k1_tarski(B_126)
      | ~ m1_subset_1(B_126,A_125)
      | v1_xboole_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4465,plain,(
    ! [A_330] :
      ( k6_domain_1(A_330,'#skF_7'(A_330)) = k1_tarski('#skF_7'(A_330))
      | ~ v1_zfmisc_1(A_330)
      | v1_xboole_0(A_330) ) ),
    inference(resolution,[status(thm)],[c_72,c_801])).

tff(c_70,plain,(
    ! [A_43] :
      ( k6_domain_1(A_43,'#skF_7'(A_43)) = A_43
      | ~ v1_zfmisc_1(A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_35776,plain,(
    ! [A_841] :
      ( k1_tarski('#skF_7'(A_841)) = A_841
      | ~ v1_zfmisc_1(A_841)
      | v1_xboole_0(A_841)
      | ~ v1_zfmisc_1(A_841)
      | v1_xboole_0(A_841) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4465,c_70])).

tff(c_74,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_34,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_427,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k4_xboole_0(B_86,A_85)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_439,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = k2_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_427])).

tff(c_443,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_439])).

tff(c_42,plain,(
    ! [B_25,A_24] : k2_tarski(B_25,A_24) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_195,plain,(
    ! [A_66,B_67] : k3_tarski(k2_tarski(A_66,B_67)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_288,plain,(
    ! [B_77,A_78] : k3_tarski(k2_tarski(B_77,A_78)) = k2_xboole_0(A_78,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_195])).

tff(c_58,plain,(
    ! [A_32,B_33] : k3_tarski(k2_tarski(A_32,B_33)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_294,plain,(
    ! [B_77,A_78] : k2_xboole_0(B_77,A_78) = k2_xboole_0(A_78,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_58])).

tff(c_76,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_186,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = k1_xboole_0
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_190,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_186])).

tff(c_436,plain,(
    k5_xboole_0('#skF_9',k1_xboole_0) = k2_xboole_0('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_427])).

tff(c_442,plain,(
    k5_xboole_0('#skF_9',k1_xboole_0) = k2_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_436])).

tff(c_453,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_442])).

tff(c_1077,plain,(
    ! [C_147,B_148,A_149] :
      ( k1_xboole_0 = C_147
      | k1_xboole_0 = B_148
      | C_147 = B_148
      | k2_xboole_0(B_148,C_147) != k1_tarski(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1083,plain,(
    ! [A_149] :
      ( k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = '#skF_8'
      | '#skF_9' = '#skF_8'
      | k1_tarski(A_149) != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_1077])).

tff(c_1097,plain,(
    ! [A_149] :
      ( k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = '#skF_8'
      | k1_tarski(A_149) != '#skF_9' ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1083])).

tff(c_1124,plain,(
    ! [A_149] : k1_tarski(A_149) != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1097])).

tff(c_35959,plain,(
    ! [A_843] :
      ( A_843 != '#skF_9'
      | ~ v1_zfmisc_1(A_843)
      | v1_xboole_0(A_843)
      | ~ v1_zfmisc_1(A_843)
      | v1_xboole_0(A_843) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35776,c_1124])).

tff(c_35961,plain,
    ( ~ v1_zfmisc_1('#skF_9')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_35959])).

tff(c_35964,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_35961])).

tff(c_35966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_35964])).

tff(c_35967,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1097])).

tff(c_35968,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_35967])).

tff(c_235,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,B_71) = A_70
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_239,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_76,c_235])).

tff(c_538,plain,(
    ! [D_97,B_98,A_99] :
      ( r2_hidden(D_97,B_98)
      | ~ r2_hidden(D_97,k3_xboole_0(A_99,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_550,plain,(
    ! [D_97] :
      ( r2_hidden(D_97,'#skF_9')
      | ~ r2_hidden(D_97,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_538])).

tff(c_717,plain,(
    ! [C_113,B_114,A_115] :
      ( r2_hidden(C_113,B_114)
      | ~ r2_hidden(C_113,A_115)
      | ~ r1_tarski(A_115,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_857,plain,(
    ! [D_128,B_129] :
      ( r2_hidden(D_128,B_129)
      | ~ r1_tarski('#skF_9',B_129)
      | ~ r2_hidden(D_128,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_550,c_717])).

tff(c_863,plain,(
    ! [B_129] :
      ( r2_hidden('#skF_1'('#skF_8'),B_129)
      | ~ r1_tarski('#skF_9',B_129)
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4,c_857])).

tff(c_926,plain,(
    ! [B_135] :
      ( r2_hidden('#skF_1'('#skF_8'),B_135)
      | ~ r1_tarski('#skF_9',B_135) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_863])).

tff(c_773,plain,(
    ! [D_15,A_124] :
      ( r2_hidden(D_15,A_124)
      | ~ r2_hidden(D_15,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_14])).

tff(c_950,plain,(
    ! [A_124] :
      ( r2_hidden('#skF_1'('#skF_8'),A_124)
      | ~ r1_tarski('#skF_9',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_926,c_773])).

tff(c_978,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_950])).

tff(c_35995,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35968,c_978])).

tff(c_36016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_35995])).

tff(c_36017,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_35967])).

tff(c_36026,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36017,c_878])).

tff(c_36044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_36026])).

tff(c_36046,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_950])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_956,plain,(
    ! [B_135] :
      ( ~ v1_xboole_0(B_135)
      | ~ r1_tarski('#skF_9',B_135) ) ),
    inference(resolution,[status(thm)],[c_926,c_2])).

tff(c_36049,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36046,c_956])).

tff(c_36059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_36049])).

tff(c_36062,plain,(
    ! [A_846] : r2_hidden('#skF_1'(k1_xboole_0),A_846) ),
    inference(splitRight,[status(thm)],[c_877])).

tff(c_44,plain,(
    ! [C_30,A_26] :
      ( C_30 = A_26
      | ~ r2_hidden(C_30,k1_tarski(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36146,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36062,c_44])).

tff(c_36096,plain,(
    ! [A_26] : A_26 = '#skF_1'(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36062,c_44])).

tff(c_36328,plain,(
    ! [A_2406] : k1_xboole_0 = A_2406 ),
    inference(superposition,[status(thm),theory(equality)],[c_36146,c_36096])).

tff(c_314,plain,(
    ! [B_79,A_80] : k2_xboole_0(B_79,A_80) = k2_xboole_0(A_80,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_58])).

tff(c_62,plain,(
    ! [A_37,B_38] : k2_xboole_0(k1_tarski(A_37),B_38) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_330,plain,(
    ! [B_79,A_37] : k2_xboole_0(B_79,k1_tarski(A_37)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_62])).

tff(c_36470,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_36328,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:54:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.16/6.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.16/6.75  
% 14.16/6.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.16/6.76  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_4 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_5
% 14.16/6.76  
% 14.16/6.76  %Foreground sorts:
% 14.16/6.76  
% 14.16/6.76  
% 14.16/6.76  %Background operators:
% 14.16/6.76  
% 14.16/6.76  
% 14.16/6.76  %Foreground operators:
% 14.16/6.76  tff('#skF_7', type, '#skF_7': $i > $i).
% 14.16/6.76  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 14.16/6.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.16/6.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.16/6.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.16/6.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.16/6.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.16/6.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.16/6.76  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 14.16/6.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.16/6.76  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 14.16/6.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.16/6.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.16/6.76  tff('#skF_9', type, '#skF_9': $i).
% 14.16/6.76  tff('#skF_8', type, '#skF_8': $i).
% 14.16/6.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.16/6.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.16/6.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.16/6.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.16/6.76  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.16/6.76  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 14.16/6.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.16/6.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.16/6.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.16/6.76  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 14.16/6.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.16/6.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.16/6.76  
% 14.16/6.77  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 14.16/6.77  tff(f_59, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 14.16/6.77  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 14.16/6.77  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.16/6.77  tff(f_47, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 14.16/6.77  tff(f_122, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 14.16/6.77  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 14.16/6.77  tff(f_108, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 14.16/6.77  tff(f_98, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 14.16/6.77  tff(f_53, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 14.16/6.77  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 14.16/6.77  tff(f_63, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 14.16/6.77  tff(f_74, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 14.16/6.77  tff(f_86, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 14.16/6.77  tff(f_70, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 14.16/6.77  tff(f_89, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 14.16/6.77  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.16/6.77  tff(c_38, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.16/6.77  tff(c_244, plain, (![A_72, B_73]: (r1_tarski(A_72, B_73) | k4_xboole_0(A_72, B_73)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.16/6.77  tff(c_36, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.16/6.77  tff(c_749, plain, (![A_122, B_123]: (k3_xboole_0(A_122, B_123)=A_122 | k4_xboole_0(A_122, B_123)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_244, c_36])).
% 14.16/6.77  tff(c_764, plain, (![A_124]: (k3_xboole_0(k1_xboole_0, A_124)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_749])).
% 14.16/6.77  tff(c_14, plain, (![D_15, B_11, A_10]: (r2_hidden(D_15, B_11) | ~r2_hidden(D_15, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.16/6.77  tff(c_869, plain, (![D_130, A_131]: (r2_hidden(D_130, A_131) | ~r2_hidden(D_130, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_764, c_14])).
% 14.16/6.77  tff(c_877, plain, (![A_131]: (r2_hidden('#skF_1'(k1_xboole_0), A_131) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_869])).
% 14.16/6.77  tff(c_878, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_877])).
% 14.16/6.77  tff(c_82, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_122])).
% 14.16/6.77  tff(c_567, plain, (![A_102, B_103]: (r2_hidden('#skF_2'(A_102, B_103), A_102) | r1_tarski(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.16/6.77  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.16/6.77  tff(c_595, plain, (![A_102]: (r1_tarski(A_102, A_102))), inference(resolution, [status(thm)], [c_567, c_8])).
% 14.16/6.77  tff(c_80, plain, (~v1_xboole_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_122])).
% 14.16/6.77  tff(c_78, plain, (v1_zfmisc_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_122])).
% 14.16/6.77  tff(c_72, plain, (![A_43]: (m1_subset_1('#skF_7'(A_43), A_43) | ~v1_zfmisc_1(A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_108])).
% 14.16/6.77  tff(c_801, plain, (![A_125, B_126]: (k6_domain_1(A_125, B_126)=k1_tarski(B_126) | ~m1_subset_1(B_126, A_125) | v1_xboole_0(A_125))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.16/6.77  tff(c_4465, plain, (![A_330]: (k6_domain_1(A_330, '#skF_7'(A_330))=k1_tarski('#skF_7'(A_330)) | ~v1_zfmisc_1(A_330) | v1_xboole_0(A_330))), inference(resolution, [status(thm)], [c_72, c_801])).
% 14.16/6.77  tff(c_70, plain, (![A_43]: (k6_domain_1(A_43, '#skF_7'(A_43))=A_43 | ~v1_zfmisc_1(A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_108])).
% 14.16/6.77  tff(c_35776, plain, (![A_841]: (k1_tarski('#skF_7'(A_841))=A_841 | ~v1_zfmisc_1(A_841) | v1_xboole_0(A_841) | ~v1_zfmisc_1(A_841) | v1_xboole_0(A_841))), inference(superposition, [status(thm), theory('equality')], [c_4465, c_70])).
% 14.16/6.77  tff(c_74, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_122])).
% 14.16/6.77  tff(c_34, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.16/6.77  tff(c_427, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k4_xboole_0(B_86, A_85))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.16/6.77  tff(c_439, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=k2_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_427])).
% 14.16/6.77  tff(c_443, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_439])).
% 14.16/6.77  tff(c_42, plain, (![B_25, A_24]: (k2_tarski(B_25, A_24)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.16/6.77  tff(c_195, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.16/6.77  tff(c_288, plain, (![B_77, A_78]: (k3_tarski(k2_tarski(B_77, A_78))=k2_xboole_0(A_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_42, c_195])).
% 14.16/6.77  tff(c_58, plain, (![A_32, B_33]: (k3_tarski(k2_tarski(A_32, B_33))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.16/6.77  tff(c_294, plain, (![B_77, A_78]: (k2_xboole_0(B_77, A_78)=k2_xboole_0(A_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_288, c_58])).
% 14.16/6.77  tff(c_76, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_122])).
% 14.16/6.77  tff(c_186, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=k1_xboole_0 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.16/6.77  tff(c_190, plain, (k4_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_186])).
% 14.16/6.77  tff(c_436, plain, (k5_xboole_0('#skF_9', k1_xboole_0)=k2_xboole_0('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_190, c_427])).
% 14.16/6.77  tff(c_442, plain, (k5_xboole_0('#skF_9', k1_xboole_0)=k2_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_436])).
% 14.16/6.77  tff(c_453, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_443, c_442])).
% 14.16/6.77  tff(c_1077, plain, (![C_147, B_148, A_149]: (k1_xboole_0=C_147 | k1_xboole_0=B_148 | C_147=B_148 | k2_xboole_0(B_148, C_147)!=k1_tarski(A_149))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.16/6.77  tff(c_1083, plain, (![A_149]: (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | '#skF_9'='#skF_8' | k1_tarski(A_149)!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_453, c_1077])).
% 14.16/6.77  tff(c_1097, plain, (![A_149]: (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_tarski(A_149)!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_74, c_1083])).
% 14.16/6.77  tff(c_1124, plain, (![A_149]: (k1_tarski(A_149)!='#skF_9')), inference(splitLeft, [status(thm)], [c_1097])).
% 14.16/6.77  tff(c_35959, plain, (![A_843]: (A_843!='#skF_9' | ~v1_zfmisc_1(A_843) | v1_xboole_0(A_843) | ~v1_zfmisc_1(A_843) | v1_xboole_0(A_843))), inference(superposition, [status(thm), theory('equality')], [c_35776, c_1124])).
% 14.16/6.77  tff(c_35961, plain, (~v1_zfmisc_1('#skF_9') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_78, c_35959])).
% 14.16/6.77  tff(c_35964, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_35961])).
% 14.16/6.77  tff(c_35966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_35964])).
% 14.16/6.77  tff(c_35967, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1097])).
% 14.16/6.77  tff(c_35968, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_35967])).
% 14.16/6.77  tff(c_235, plain, (![A_70, B_71]: (k3_xboole_0(A_70, B_71)=A_70 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.16/6.77  tff(c_239, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_76, c_235])).
% 14.16/6.77  tff(c_538, plain, (![D_97, B_98, A_99]: (r2_hidden(D_97, B_98) | ~r2_hidden(D_97, k3_xboole_0(A_99, B_98)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.16/6.77  tff(c_550, plain, (![D_97]: (r2_hidden(D_97, '#skF_9') | ~r2_hidden(D_97, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_239, c_538])).
% 14.16/6.77  tff(c_717, plain, (![C_113, B_114, A_115]: (r2_hidden(C_113, B_114) | ~r2_hidden(C_113, A_115) | ~r1_tarski(A_115, B_114))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.16/6.77  tff(c_857, plain, (![D_128, B_129]: (r2_hidden(D_128, B_129) | ~r1_tarski('#skF_9', B_129) | ~r2_hidden(D_128, '#skF_8'))), inference(resolution, [status(thm)], [c_550, c_717])).
% 14.16/6.77  tff(c_863, plain, (![B_129]: (r2_hidden('#skF_1'('#skF_8'), B_129) | ~r1_tarski('#skF_9', B_129) | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_4, c_857])).
% 14.16/6.77  tff(c_926, plain, (![B_135]: (r2_hidden('#skF_1'('#skF_8'), B_135) | ~r1_tarski('#skF_9', B_135))), inference(negUnitSimplification, [status(thm)], [c_82, c_863])).
% 14.16/6.77  tff(c_773, plain, (![D_15, A_124]: (r2_hidden(D_15, A_124) | ~r2_hidden(D_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_764, c_14])).
% 14.16/6.77  tff(c_950, plain, (![A_124]: (r2_hidden('#skF_1'('#skF_8'), A_124) | ~r1_tarski('#skF_9', k1_xboole_0))), inference(resolution, [status(thm)], [c_926, c_773])).
% 14.16/6.77  tff(c_978, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_950])).
% 14.16/6.77  tff(c_35995, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_35968, c_978])).
% 14.16/6.77  tff(c_36016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_595, c_35995])).
% 14.16/6.77  tff(c_36017, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_35967])).
% 14.16/6.77  tff(c_36026, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36017, c_878])).
% 14.16/6.77  tff(c_36044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_36026])).
% 14.16/6.77  tff(c_36046, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_950])).
% 14.16/6.77  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.16/6.77  tff(c_956, plain, (![B_135]: (~v1_xboole_0(B_135) | ~r1_tarski('#skF_9', B_135))), inference(resolution, [status(thm)], [c_926, c_2])).
% 14.16/6.77  tff(c_36049, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_36046, c_956])).
% 14.16/6.77  tff(c_36059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_878, c_36049])).
% 14.16/6.77  tff(c_36062, plain, (![A_846]: (r2_hidden('#skF_1'(k1_xboole_0), A_846))), inference(splitRight, [status(thm)], [c_877])).
% 14.16/6.77  tff(c_44, plain, (![C_30, A_26]: (C_30=A_26 | ~r2_hidden(C_30, k1_tarski(A_26)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.16/6.77  tff(c_36146, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36062, c_44])).
% 14.16/6.77  tff(c_36096, plain, (![A_26]: (A_26='#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_36062, c_44])).
% 14.16/6.77  tff(c_36328, plain, (![A_2406]: (k1_xboole_0=A_2406)), inference(superposition, [status(thm), theory('equality')], [c_36146, c_36096])).
% 14.16/6.77  tff(c_314, plain, (![B_79, A_80]: (k2_xboole_0(B_79, A_80)=k2_xboole_0(A_80, B_79))), inference(superposition, [status(thm), theory('equality')], [c_288, c_58])).
% 14.16/6.77  tff(c_62, plain, (![A_37, B_38]: (k2_xboole_0(k1_tarski(A_37), B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.16/6.77  tff(c_330, plain, (![B_79, A_37]: (k2_xboole_0(B_79, k1_tarski(A_37))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_314, c_62])).
% 14.16/6.77  tff(c_36470, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_36328, c_330])).
% 14.16/6.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.16/6.77  
% 14.16/6.77  Inference rules
% 14.16/6.77  ----------------------
% 14.16/6.77  #Ref     : 0
% 14.16/6.77  #Sup     : 9931
% 14.16/6.77  #Fact    : 0
% 14.16/6.77  #Define  : 0
% 14.16/6.77  #Split   : 10
% 14.16/6.77  #Chain   : 0
% 14.16/6.77  #Close   : 0
% 14.16/6.77  
% 14.16/6.77  Ordering : KBO
% 14.16/6.77  
% 14.16/6.77  Simplification rules
% 14.16/6.77  ----------------------
% 14.16/6.77  #Subsume      : 4812
% 14.16/6.77  #Demod        : 5566
% 14.16/6.77  #Tautology    : 1870
% 14.16/6.77  #SimpNegUnit  : 265
% 14.16/6.77  #BackRed      : 65
% 14.16/6.77  
% 14.16/6.77  #Partial instantiations: 518
% 14.16/6.77  #Strategies tried      : 1
% 14.16/6.77  
% 14.16/6.77  Timing (in seconds)
% 14.16/6.77  ----------------------
% 14.16/6.78  Preprocessing        : 0.35
% 14.16/6.78  Parsing              : 0.18
% 14.16/6.78  CNF conversion       : 0.03
% 14.16/6.78  Main loop            : 5.63
% 14.16/6.78  Inferencing          : 1.02
% 14.16/6.78  Reduction            : 2.47
% 14.16/6.78  Demodulation         : 2.04
% 14.16/6.78  BG Simplification    : 0.11
% 14.16/6.78  Subsumption          : 1.75
% 14.16/6.78  Abstraction          : 0.16
% 14.16/6.78  MUC search           : 0.00
% 14.16/6.78  Cooper               : 0.00
% 14.16/6.78  Total                : 6.02
% 14.16/6.78  Index Insertion      : 0.00
% 14.16/6.78  Index Deletion       : 0.00
% 14.16/6.78  Index Matching       : 0.00
% 14.16/6.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
