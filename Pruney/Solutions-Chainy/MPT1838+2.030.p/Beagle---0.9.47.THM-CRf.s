%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:18 EST 2020

% Result     : Theorem 12.61s
% Output     : CNFRefutation 12.90s
% Verified   : 
% Statistics : Number of formulae       :  248 (4618 expanded)
%              Number of leaves         :   32 (1559 expanded)
%              Depth                    :   24
%              Number of atoms          :  449 (11381 expanded)
%              Number of equality atoms :  164 (2546 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_48,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_78,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_46,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_18,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_48,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_2'(A_56,B_57),A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_200,plain,(
    ! [A_17,B_57] :
      ( '#skF_2'(k1_tarski(A_17),B_57) = A_17
      | r1_tarski(k1_tarski(A_17),B_57) ) ),
    inference(resolution,[status(thm)],[c_187,c_22])).

tff(c_24,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    ! [B_34,A_35] :
      ( ~ r2_hidden(B_34,A_35)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [C_21] : ~ v1_xboole_0(k1_tarski(C_21)) ),
    inference(resolution,[status(thm)],[c_24,c_65])).

tff(c_85,plain,(
    ! [C_39,A_40] :
      ( C_39 = A_40
      | ~ r2_hidden(C_39,k1_tarski(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,(
    ! [A_40] :
      ( '#skF_1'(k1_tarski(A_40)) = A_40
      | v1_xboole_0(k1_tarski(A_40)) ) ),
    inference(resolution,[status(thm)],[c_4,c_85])).

tff(c_95,plain,(
    ! [A_40] : '#skF_1'(k1_tarski(A_40)) = A_40 ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_89])).

tff(c_202,plain,(
    ! [C_58,B_59,A_60] :
      ( r2_hidden(C_58,B_59)
      | ~ r2_hidden(C_58,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_321,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_1'(A_80),B_81)
      | ~ r1_tarski(A_80,B_81)
      | v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_4,c_202])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6143,plain,(
    ! [A_12502,B_12503,B_12504] :
      ( r2_hidden('#skF_1'(A_12502),B_12503)
      | ~ r1_tarski(B_12504,B_12503)
      | ~ r1_tarski(A_12502,B_12504)
      | v1_xboole_0(A_12502) ) ),
    inference(resolution,[status(thm)],[c_321,c_6])).

tff(c_6176,plain,(
    ! [A_12613] :
      ( r2_hidden('#skF_1'(A_12613),'#skF_7')
      | ~ r1_tarski(A_12613,'#skF_6')
      | v1_xboole_0(A_12613) ) ),
    inference(resolution,[status(thm)],[c_48,c_6143])).

tff(c_6244,plain,(
    ! [A_40] :
      ( r2_hidden(A_40,'#skF_7')
      | ~ r1_tarski(k1_tarski(A_40),'#skF_6')
      | v1_xboole_0(k1_tarski(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_6176])).

tff(c_6263,plain,(
    ! [A_12722] :
      ( r2_hidden(A_12722,'#skF_7')
      | ~ r1_tarski(k1_tarski(A_12722),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_6244])).

tff(c_6297,plain,(
    ! [A_12831] :
      ( r2_hidden(A_12831,'#skF_7')
      | '#skF_2'(k1_tarski(A_12831),'#skF_6') = A_12831 ) ),
    inference(resolution,[status(thm)],[c_200,c_6263])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6465,plain,(
    ! [A_13049] :
      ( ~ r2_hidden(A_13049,'#skF_6')
      | r1_tarski(k1_tarski(A_13049),'#skF_6')
      | r2_hidden(A_13049,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6297,c_8])).

tff(c_6262,plain,(
    ! [A_40] :
      ( r2_hidden(A_40,'#skF_7')
      | ~ r1_tarski(k1_tarski(A_40),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_6244])).

tff(c_6593,plain,(
    ! [A_13266] :
      ( ~ r2_hidden(A_13266,'#skF_6')
      | r2_hidden(A_13266,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6465,c_6262])).

tff(c_6986,plain,(
    ! [A_14356,B_14357] :
      ( r2_hidden(A_14356,B_14357)
      | ~ r1_tarski('#skF_7',B_14357)
      | ~ r2_hidden(A_14356,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6593,c_6])).

tff(c_7009,plain,(
    ! [B_14357] :
      ( r2_hidden('#skF_1'('#skF_6'),B_14357)
      | ~ r1_tarski('#skF_7',B_14357)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_6986])).

tff(c_7020,plain,(
    ! [B_14466] :
      ( r2_hidden('#skF_1'('#skF_6'),B_14466)
      | ~ r1_tarski('#skF_7',B_14466) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_7009])).

tff(c_7378,plain,(
    ! [B_15771,B_15772] :
      ( r2_hidden('#skF_1'('#skF_6'),B_15771)
      | ~ r1_tarski(B_15772,B_15771)
      | ~ r1_tarski('#skF_7',B_15772) ) ),
    inference(resolution,[status(thm)],[c_7020,c_6])).

tff(c_7413,plain,
    ( r2_hidden('#skF_1'('#skF_6'),'#skF_7')
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_7378])).

tff(c_7414,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_7413])).

tff(c_199,plain,(
    ! [A_56] : r1_tarski(A_56,A_56) ),
    inference(resolution,[status(thm)],[c_187,c_8])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50,plain,(
    v1_zfmisc_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    ! [A_27] :
      ( k6_domain_1(A_27,'#skF_5'(A_27)) = A_27
      | ~ v1_zfmisc_1(A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_44,plain,(
    ! [A_27] :
      ( m1_subset_1('#skF_5'(A_27),A_27)
      | ~ v1_zfmisc_1(A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_298,plain,(
    ! [A_74,B_75] :
      ( k6_domain_1(A_74,B_75) = k1_tarski(B_75)
      | ~ m1_subset_1(B_75,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2176,plain,(
    ! [A_1577] :
      ( k6_domain_1(A_1577,'#skF_5'(A_1577)) = k1_tarski('#skF_5'(A_1577))
      | ~ v1_zfmisc_1(A_1577)
      | v1_xboole_0(A_1577) ) ),
    inference(resolution,[status(thm)],[c_44,c_298])).

tff(c_5708,plain,(
    ! [A_11955] :
      ( k1_tarski('#skF_5'(A_11955)) = A_11955
      | ~ v1_zfmisc_1(A_11955)
      | v1_xboole_0(A_11955)
      | ~ v1_zfmisc_1(A_11955)
      | v1_xboole_0(A_11955) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2176])).

tff(c_15495,plain,(
    ! [A_39927] :
      ( '#skF_5'(A_39927) = '#skF_1'(A_39927)
      | ~ v1_zfmisc_1(A_39927)
      | v1_xboole_0(A_39927)
      | ~ v1_zfmisc_1(A_39927)
      | v1_xboole_0(A_39927) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5708,c_95])).

tff(c_15532,plain,
    ( '#skF_5'('#skF_7') = '#skF_1'('#skF_7')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_15495])).

tff(c_15535,plain,
    ( '#skF_5'('#skF_7') = '#skF_1'('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_15532])).

tff(c_15536,plain,(
    '#skF_5'('#skF_7') = '#skF_1'('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_15535])).

tff(c_2204,plain,(
    ! [A_27] :
      ( k1_tarski('#skF_5'(A_27)) = A_27
      | ~ v1_zfmisc_1(A_27)
      | v1_xboole_0(A_27)
      | ~ v1_zfmisc_1(A_27)
      | v1_xboole_0(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2176])).

tff(c_15546,plain,
    ( k1_tarski('#skF_1'('#skF_7')) = '#skF_7'
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_15536,c_2204])).

tff(c_15604,plain,
    ( k1_tarski('#skF_1'('#skF_7')) = '#skF_7'
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_15546])).

tff(c_15605,plain,(
    k1_tarski('#skF_1'('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_15604])).

tff(c_7071,plain,(
    ! [A_17] :
      ( A_17 = '#skF_1'('#skF_6')
      | ~ r1_tarski('#skF_7',k1_tarski(A_17)) ) ),
    inference(resolution,[status(thm)],[c_7020,c_22])).

tff(c_15830,plain,
    ( '#skF_1'('#skF_7') = '#skF_1'('#skF_6')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_15605,c_7071])).

tff(c_16057,plain,(
    '#skF_1'('#skF_7') = '#skF_1'('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_15830])).

tff(c_362,plain,(
    ! [A_88,B_89] :
      ( '#skF_2'(k1_tarski(A_88),B_89) = A_88
      | r1_tarski(k1_tarski(A_88),B_89) ) ),
    inference(resolution,[status(thm)],[c_187,c_22])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_380,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(k1_tarski(A_88),B_89) = k1_xboole_0
      | '#skF_2'(k1_tarski(A_88),B_89) = A_88 ) ),
    inference(resolution,[status(thm)],[c_362,c_14])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1063,plain,(
    ! [A_1039,B_1040] :
      ( k2_xboole_0(k1_tarski(A_1039),B_1040) = B_1040
      | '#skF_2'(k1_tarski(A_1039),B_1040) = A_1039 ) ),
    inference(resolution,[status(thm)],[c_362,c_16])).

tff(c_1152,plain,(
    ! [A_1059] :
      ( k1_tarski(A_1059) = k1_xboole_0
      | '#skF_2'(k1_tarski(A_1059),k1_xboole_0) = A_1059 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_18])).

tff(c_1404,plain,(
    ! [A_1198] :
      ( ~ r2_hidden(A_1198,k1_xboole_0)
      | r1_tarski(k1_tarski(A_1198),k1_xboole_0)
      | k1_tarski(A_1198) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1152,c_8])).

tff(c_1413,plain,(
    ! [A_1198] :
      ( k2_xboole_0(k1_tarski(A_1198),k1_xboole_0) = k1_xboole_0
      | ~ r2_hidden(A_1198,k1_xboole_0)
      | k1_tarski(A_1198) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1404,c_16])).

tff(c_1476,plain,(
    ! [A_1217] :
      ( k1_tarski(A_1217) = k1_xboole_0
      | ~ r2_hidden(A_1217,k1_xboole_0)
      | k1_tarski(A_1217) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1413])).

tff(c_1524,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_1476])).

tff(c_1525,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1524])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_270,plain,(
    ! [A_66,B_67] :
      ( ~ v1_xboole_0(A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_187,c_2])).

tff(c_277,plain,(
    ! [A_66,B_67] :
      ( k2_xboole_0(A_66,B_67) = B_67
      | ~ v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_270,c_16])).

tff(c_1540,plain,(
    ! [B_67] : k2_xboole_0(k1_xboole_0,B_67) = B_67 ),
    inference(resolution,[status(thm)],[c_1525,c_277])).

tff(c_1594,plain,(
    ! [B_1292] : k2_xboole_0(k1_xboole_0,B_1292) = B_1292 ),
    inference(resolution,[status(thm)],[c_1525,c_277])).

tff(c_20,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1609,plain,(
    ! [B_16] : k4_xboole_0(B_16,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_1594,c_20])).

tff(c_1636,plain,(
    ! [B_16] : k4_xboole_0(B_16,k1_xboole_0) = B_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1609])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_343,plain,(
    ! [B_84,A_85] :
      ( ~ v1_xboole_0(B_84)
      | ~ r1_tarski(A_85,B_84)
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_321,c_2])).

tff(c_358,plain,(
    ! [B_11,A_10] :
      ( ~ v1_xboole_0(B_11)
      | v1_xboole_0(A_10)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_343])).

tff(c_1538,plain,(
    ! [A_10] :
      ( v1_xboole_0(A_10)
      | k4_xboole_0(A_10,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1525,c_358])).

tff(c_1837,plain,(
    ! [A_1368] :
      ( v1_xboole_0(A_1368)
      | k1_xboole_0 != A_1368 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1636,c_1538])).

tff(c_2351,plain,(
    ! [A_1656,A_1657] :
      ( v1_xboole_0(A_1656)
      | k4_xboole_0(A_1656,A_1657) != k1_xboole_0
      | k1_xboole_0 != A_1657 ) ),
    inference(resolution,[status(thm)],[c_1837,c_358])).

tff(c_2359,plain,(
    ! [A_88,B_89] :
      ( v1_xboole_0(k1_tarski(A_88))
      | k1_xboole_0 != B_89
      | '#skF_2'(k1_tarski(A_88),B_89) = A_88 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_2351])).

tff(c_2369,plain,(
    ! [B_89,A_88] :
      ( k1_xboole_0 != B_89
      | '#skF_2'(k1_tarski(A_88),B_89) = A_88 ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_2359])).

tff(c_15856,plain,(
    ! [B_89] :
      ( k1_xboole_0 != B_89
      | '#skF_2'('#skF_7',B_89) = '#skF_1'('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15605,c_2369])).

tff(c_17121,plain,(
    '#skF_1'('#skF_6') = '#skF_2'('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16057,c_15856])).

tff(c_17130,plain,(
    '#skF_1'('#skF_7') = '#skF_2'('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17121,c_16057])).

tff(c_15891,plain,(
    ! [B_57] :
      ( '#skF_2'(k1_tarski('#skF_1'('#skF_7')),B_57) = '#skF_1'('#skF_7')
      | r1_tarski('#skF_7',B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15605,c_200])).

tff(c_16066,plain,(
    ! [B_57] :
      ( '#skF_2'('#skF_7',B_57) = '#skF_1'('#skF_7')
      | r1_tarski('#skF_7',B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15605,c_15891])).

tff(c_20760,plain,(
    ! [B_47142] :
      ( '#skF_2'('#skF_7',k1_xboole_0) = '#skF_2'('#skF_7',B_47142)
      | r1_tarski('#skF_7',B_47142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17130,c_16066])).

tff(c_20872,plain,(
    '#skF_2'('#skF_7',k1_xboole_0) = '#skF_2'('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_20760,c_7414])).

tff(c_17143,plain,(
    ! [B_42262] :
      ( k1_xboole_0 != B_42262
      | '#skF_2'('#skF_7',B_42262) = '#skF_1'('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16057,c_15856])).

tff(c_17170,plain,(
    ! [B_42262] :
      ( v1_xboole_0('#skF_6')
      | r2_hidden('#skF_2'('#skF_7',B_42262),'#skF_6')
      | k1_xboole_0 != B_42262 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17143,c_4])).

tff(c_17212,plain,(
    ! [B_42262] :
      ( r2_hidden('#skF_2'('#skF_7',B_42262),'#skF_6')
      | k1_xboole_0 != B_42262 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_17170])).

tff(c_20977,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_20872,c_17212])).

tff(c_21498,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_20977,c_8])).

tff(c_21531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7414,c_21498])).

tff(c_21533,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_7413])).

tff(c_21585,plain,(
    k2_xboole_0('#skF_7','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_21533,c_16])).

tff(c_142,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k1_xboole_0
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_150,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_142])).

tff(c_170,plain,(
    ! [A_54,B_55] : k2_xboole_0(A_54,k4_xboole_0(B_55,A_54)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_179,plain,(
    k2_xboole_0('#skF_7',k1_xboole_0) = k2_xboole_0('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_170])).

tff(c_182,plain,(
    k2_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_179])).

tff(c_21625,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21585,c_182])).

tff(c_21627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_21625])).

tff(c_21628,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1524])).

tff(c_819,plain,(
    ! [A_959,A_960] :
      ( A_959 = '#skF_1'(A_960)
      | ~ r1_tarski(A_960,k1_tarski(A_959))
      | v1_xboole_0(A_960) ) ),
    inference(resolution,[status(thm)],[c_321,c_22])).

tff(c_847,plain,(
    ! [A_959,A_10] :
      ( A_959 = '#skF_1'(A_10)
      | v1_xboole_0(A_10)
      | k4_xboole_0(A_10,k1_tarski(A_959)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_819])).

tff(c_22802,plain,(
    ! [A_48764] :
      ( '#skF_1'(k1_xboole_0) = '#skF_1'(A_48764)
      | v1_xboole_0(A_48764)
      | k4_xboole_0(A_48764,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21628,c_847])).

tff(c_22847,plain,
    ( '#skF_1'(k1_xboole_0) = '#skF_1'('#skF_7')
    | k4_xboole_0('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22802,c_52])).

tff(c_22876,plain,(
    k4_xboole_0('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_22847])).

tff(c_155,plain,(
    ! [A_49,B_50] :
      ( k2_xboole_0(A_49,B_50) = B_50
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_163,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_48,c_155])).

tff(c_26137,plain,(
    ! [A_58961,B_58962,B_58963] :
      ( r2_hidden('#skF_1'(A_58961),B_58962)
      | ~ r1_tarski(B_58963,B_58962)
      | ~ r1_tarski(A_58961,B_58963)
      | v1_xboole_0(A_58961) ) ),
    inference(resolution,[status(thm)],[c_321,c_6])).

tff(c_26173,plain,(
    ! [A_59054] :
      ( r2_hidden('#skF_1'(A_59054),'#skF_7')
      | ~ r1_tarski(A_59054,'#skF_6')
      | v1_xboole_0(A_59054) ) ),
    inference(resolution,[status(thm)],[c_48,c_26137])).

tff(c_26240,plain,(
    ! [A_40] :
      ( r2_hidden(A_40,'#skF_7')
      | ~ r1_tarski(k1_tarski(A_40),'#skF_6')
      | v1_xboole_0(k1_tarski(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_26173])).

tff(c_26259,plain,(
    ! [A_59145] :
      ( r2_hidden(A_59145,'#skF_7')
      | ~ r1_tarski(k1_tarski(A_59145),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_26240])).

tff(c_26346,plain,(
    ! [A_59327] :
      ( r2_hidden(A_59327,'#skF_7')
      | '#skF_2'(k1_tarski(A_59327),'#skF_6') = A_59327 ) ),
    inference(resolution,[status(thm)],[c_200,c_26259])).

tff(c_26475,plain,(
    ! [A_59509] :
      ( ~ r2_hidden(A_59509,'#skF_6')
      | r1_tarski(k1_tarski(A_59509),'#skF_6')
      | r2_hidden(A_59509,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26346,c_8])).

tff(c_26258,plain,(
    ! [A_40] :
      ( r2_hidden(A_40,'#skF_7')
      | ~ r1_tarski(k1_tarski(A_40),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_26240])).

tff(c_26570,plain,(
    ! [A_59690] :
      ( ~ r2_hidden(A_59690,'#skF_6')
      | r2_hidden(A_59690,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_26475,c_26258])).

tff(c_26998,plain,(
    ! [A_60509,B_60510] :
      ( r2_hidden(A_60509,B_60510)
      | ~ r1_tarski('#skF_7',B_60510)
      | ~ r2_hidden(A_60509,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26570,c_6])).

tff(c_27030,plain,(
    ! [B_60510] :
      ( r2_hidden('#skF_1'('#skF_6'),B_60510)
      | ~ r1_tarski('#skF_7',B_60510)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_26998])).

tff(c_27045,plain,(
    ! [B_60601] :
      ( r2_hidden('#skF_1'('#skF_6'),B_60601)
      | ~ r1_tarski('#skF_7',B_60601) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_27030])).

tff(c_27357,plain,(
    ! [B_61420,B_61421] :
      ( r2_hidden('#skF_1'('#skF_6'),B_61420)
      | ~ r1_tarski(B_61421,B_61420)
      | ~ r1_tarski('#skF_7',B_61421) ) ),
    inference(resolution,[status(thm)],[c_27045,c_6])).

tff(c_27395,plain,
    ( r2_hidden('#skF_1'('#skF_6'),'#skF_7')
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_27357])).

tff(c_27396,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_27395])).

tff(c_21756,plain,(
    ! [A_48244] :
      ( k6_domain_1(A_48244,'#skF_5'(A_48244)) = k1_tarski('#skF_5'(A_48244))
      | ~ v1_zfmisc_1(A_48244)
      | v1_xboole_0(A_48244) ) ),
    inference(resolution,[status(thm)],[c_44,c_298])).

tff(c_26700,plain,(
    ! [A_60054] :
      ( k1_tarski('#skF_5'(A_60054)) = A_60054
      | ~ v1_zfmisc_1(A_60054)
      | v1_xboole_0(A_60054)
      | ~ v1_zfmisc_1(A_60054)
      | v1_xboole_0(A_60054) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_21756])).

tff(c_29562,plain,(
    ! [A_67563] :
      ( '#skF_5'(A_67563) = '#skF_1'(A_67563)
      | ~ v1_zfmisc_1(A_67563)
      | v1_xboole_0(A_67563)
      | ~ v1_zfmisc_1(A_67563)
      | v1_xboole_0(A_67563) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26700,c_95])).

tff(c_29592,plain,
    ( '#skF_5'('#skF_7') = '#skF_1'('#skF_7')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_29562])).

tff(c_29595,plain,
    ( '#skF_5'('#skF_7') = '#skF_1'('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_29592])).

tff(c_29596,plain,(
    '#skF_5'('#skF_7') = '#skF_1'('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_29595])).

tff(c_21784,plain,(
    ! [A_27] :
      ( k1_tarski('#skF_5'(A_27)) = A_27
      | ~ v1_zfmisc_1(A_27)
      | v1_xboole_0(A_27)
      | ~ v1_zfmisc_1(A_27)
      | v1_xboole_0(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_21756])).

tff(c_29600,plain,
    ( k1_tarski('#skF_1'('#skF_7')) = '#skF_7'
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_29596,c_21784])).

tff(c_29644,plain,
    ( k1_tarski('#skF_1'('#skF_7')) = '#skF_7'
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_29600])).

tff(c_29645,plain,(
    k1_tarski('#skF_1'('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_29644])).

tff(c_27105,plain,(
    ! [A_17] :
      ( A_17 = '#skF_1'('#skF_6')
      | ~ r1_tarski('#skF_7',k1_tarski(A_17)) ) ),
    inference(resolution,[status(thm)],[c_27045,c_22])).

tff(c_29682,plain,
    ( '#skF_1'('#skF_7') = '#skF_1'('#skF_6')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_29645,c_27105])).

tff(c_29889,plain,(
    '#skF_1'('#skF_7') = '#skF_1'('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_29682])).

tff(c_30101,plain,(
    k1_tarski('#skF_1'('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29889,c_29645])).

tff(c_212,plain,(
    ! [A_61] : r1_tarski(A_61,A_61) ),
    inference(resolution,[status(thm)],[c_187,c_8])).

tff(c_220,plain,(
    ! [A_61] : k4_xboole_0(A_61,A_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_212,c_14])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_209,plain,(
    ! [A_5,B_6,B_59] :
      ( r2_hidden('#skF_2'(A_5,B_6),B_59)
      | ~ r1_tarski(A_5,B_59)
      | r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_202])).

tff(c_26600,plain,(
    ! [A_59781] :
      ( r1_tarski(A_59781,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_59781,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26570,c_8])).

tff(c_26625,plain,(
    ! [A_5] :
      ( ~ r1_tarski(A_5,'#skF_6')
      | r1_tarski(A_5,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_209,c_26600])).

tff(c_27388,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'('#skF_6'),'#skF_7')
      | ~ r1_tarski('#skF_7',A_5)
      | ~ r1_tarski(A_5,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26625,c_27357])).

tff(c_27411,plain,(
    ! [A_61692] :
      ( ~ r1_tarski('#skF_7',A_61692)
      | ~ r1_tarski(A_61692,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_27388])).

tff(c_27428,plain,(
    ! [B_61783] :
      ( ~ r1_tarski(B_61783,'#skF_6')
      | k4_xboole_0('#skF_7',B_61783) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_27411])).

tff(c_27450,plain,(
    ! [A_17] :
      ( k4_xboole_0('#skF_7',k1_tarski(A_17)) != k1_xboole_0
      | '#skF_2'(k1_tarski(A_17),'#skF_6') = A_17 ) ),
    inference(resolution,[status(thm)],[c_200,c_27428])).

tff(c_30338,plain,
    ( k4_xboole_0('#skF_7','#skF_7') != k1_xboole_0
    | '#skF_2'(k1_tarski('#skF_1'('#skF_6')),'#skF_6') = '#skF_1'('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_30101,c_27450])).

tff(c_30545,plain,(
    '#skF_1'('#skF_6') = '#skF_2'('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30101,c_220,c_30338])).

tff(c_30714,plain,
    ( v1_xboole_0('#skF_6')
    | r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_30545,c_4])).

tff(c_30747,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_30714])).

tff(c_33550,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_30747,c_8])).

tff(c_33585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27396,c_33550])).

tff(c_33586,plain,(
    r2_hidden('#skF_1'('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_27388])).

tff(c_36260,plain,(
    ! [A_81572] :
      ( '#skF_5'(A_81572) = '#skF_1'(A_81572)
      | ~ v1_zfmisc_1(A_81572)
      | v1_xboole_0(A_81572)
      | ~ v1_zfmisc_1(A_81572)
      | v1_xboole_0(A_81572) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26700,c_95])).

tff(c_36297,plain,
    ( '#skF_5'('#skF_7') = '#skF_1'('#skF_7')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_36260])).

tff(c_36300,plain,
    ( '#skF_5'('#skF_7') = '#skF_1'('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36297])).

tff(c_36301,plain,(
    '#skF_5'('#skF_7') = '#skF_1'('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_36300])).

tff(c_36305,plain,
    ( k1_tarski('#skF_1'('#skF_7')) = '#skF_7'
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36301,c_21784])).

tff(c_36357,plain,
    ( k1_tarski('#skF_1'('#skF_7')) = '#skF_7'
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_36305])).

tff(c_36358,plain,(
    k1_tarski('#skF_1'('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_36357])).

tff(c_36392,plain,
    ( '#skF_1'('#skF_7') = '#skF_1'('#skF_6')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_36358,c_27105])).

tff(c_36606,plain,(
    '#skF_1'('#skF_7') = '#skF_1'('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_36392])).

tff(c_1078,plain,(
    ! [A_1039] :
      ( k1_tarski(A_1039) = k1_xboole_0
      | '#skF_2'(k1_tarski(A_1039),k1_xboole_0) = A_1039 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_18])).

tff(c_36448,plain,
    ( k1_tarski('#skF_1'('#skF_7')) = k1_xboole_0
    | '#skF_1'('#skF_7') = '#skF_2'('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36358,c_1078])).

tff(c_36617,plain,
    ( k1_xboole_0 = '#skF_7'
    | '#skF_1'('#skF_7') = '#skF_2'('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36358,c_36448])).

tff(c_37737,plain,
    ( k1_xboole_0 = '#skF_7'
    | '#skF_1'('#skF_6') = '#skF_2'('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36606,c_36617])).

tff(c_37738,plain,(
    '#skF_1'('#skF_6') = '#skF_2'('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_37737])).

tff(c_37749,plain,(
    '#skF_1'('#skF_7') = '#skF_2'('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37738,c_36606])).

tff(c_36475,plain,(
    ! [B_57] :
      ( '#skF_2'(k1_tarski('#skF_1'('#skF_7')),B_57) = '#skF_1'('#skF_7')
      | r1_tarski('#skF_7',B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36358,c_200])).

tff(c_36620,plain,(
    ! [B_57] :
      ( '#skF_2'('#skF_7',B_57) = '#skF_1'('#skF_7')
      | r1_tarski('#skF_7',B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36358,c_36475])).

tff(c_41328,plain,(
    ! [B_87879] :
      ( '#skF_2'('#skF_7',k1_xboole_0) = '#skF_2'('#skF_7',B_87879)
      | r1_tarski('#skF_7',B_87879) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37749,c_36620])).

tff(c_41440,plain,(
    '#skF_2'('#skF_7',k1_xboole_0) = '#skF_2'('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_41328,c_27396])).

tff(c_37779,plain,
    ( v1_xboole_0('#skF_6')
    | r2_hidden('#skF_2'('#skF_7',k1_xboole_0),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_37738,c_4])).

tff(c_37812,plain,(
    r2_hidden('#skF_2'('#skF_7',k1_xboole_0),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_37779])).

tff(c_41475,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41440,c_37812])).

tff(c_41553,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_41475,c_8])).

tff(c_41585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27396,c_41553])).

tff(c_41586,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_37737])).

tff(c_1473,plain,(
    ! [A_1198] :
      ( k1_tarski(A_1198) = k1_xboole_0
      | ~ r2_hidden(A_1198,k1_xboole_0)
      | k1_tarski(A_1198) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1413])).

tff(c_27103,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = k1_xboole_0
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_27045,c_1473])).

tff(c_27133,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_27103])).

tff(c_1167,plain,(
    ! [A_1059] :
      ( ~ r2_hidden(A_1059,k1_xboole_0)
      | r1_tarski(k1_tarski(A_1059),k1_xboole_0)
      | k1_tarski(A_1059) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1152,c_8])).

tff(c_36439,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7'),k1_xboole_0)
    | r1_tarski('#skF_7',k1_xboole_0)
    | k1_tarski('#skF_1'('#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36358,c_1167])).

tff(c_36614,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7'),k1_xboole_0)
    | r1_tarski('#skF_7',k1_xboole_0)
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36358,c_36439])).

tff(c_36615,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7'),k1_xboole_0)
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_27133,c_36614])).

tff(c_37568,plain,
    ( ~ r2_hidden('#skF_1'('#skF_6'),k1_xboole_0)
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36606,c_36615])).

tff(c_37569,plain,(
    ~ r2_hidden('#skF_1'('#skF_6'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_37568])).

tff(c_41589,plain,(
    ~ r2_hidden('#skF_1'('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41586,c_37569])).

tff(c_41675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33586,c_41589])).

tff(c_41676,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_37568])).

tff(c_210,plain,(
    ! [A_1,B_59] :
      ( r2_hidden('#skF_1'(A_1),B_59)
      | ~ r1_tarski(A_1,B_59)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_202])).

tff(c_1522,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = k1_xboole_0
      | ~ r1_tarski(A_1,k1_xboole_0)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_210,c_1476])).

tff(c_36814,plain,(
    k1_tarski('#skF_1'('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36606,c_36358])).

tff(c_37203,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski('#skF_6',k1_xboole_0)
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1522,c_36814])).

tff(c_37277,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_37203])).

tff(c_37400,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_37277])).

tff(c_41678,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41676,c_37400])).

tff(c_41763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_41678])).

tff(c_41764,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_37277])).

tff(c_41781,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41764,c_27133])).

tff(c_41850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_41781])).

tff(c_41852,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_27395])).

tff(c_41899,plain,(
    k4_xboole_0('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41852,c_14])).

tff(c_42110,plain,(
    k2_xboole_0('#skF_6',k1_xboole_0) = k2_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_41899,c_20])).

tff(c_42123,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_163,c_42110])).

tff(c_42125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42123])).

tff(c_42127,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_27103])).

tff(c_42152,plain,(
    k4_xboole_0('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42127,c_14])).

tff(c_42171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22876,c_42152])).

tff(c_42173,plain,(
    k4_xboole_0('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_22847])).

tff(c_162,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_155])).

tff(c_42214,plain,(
    k2_xboole_0('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42173,c_162])).

tff(c_42222,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_42214])).

tff(c_42250,plain,(
    ! [A_14] : k2_xboole_0(A_14,'#skF_7') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42222,c_18])).

tff(c_42394,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42250,c_163])).

tff(c_42396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:39:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.61/4.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.90/4.95  
% 12.90/4.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.90/4.95  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4
% 12.90/4.95  
% 12.90/4.95  %Foreground sorts:
% 12.90/4.95  
% 12.90/4.95  
% 12.90/4.95  %Background operators:
% 12.90/4.95  
% 12.90/4.95  
% 12.90/4.95  %Foreground operators:
% 12.90/4.95  tff('#skF_5', type, '#skF_5': $i > $i).
% 12.90/4.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.90/4.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.90/4.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.90/4.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.90/4.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.90/4.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.90/4.95  tff('#skF_7', type, '#skF_7': $i).
% 12.90/4.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.90/4.95  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 12.90/4.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.90/4.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.90/4.95  tff('#skF_6', type, '#skF_6': $i).
% 12.90/4.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.90/4.95  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.90/4.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.90/4.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.90/4.95  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 12.90/4.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.90/4.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.90/4.95  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.90/4.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.90/4.95  
% 12.90/4.99  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 12.90/4.99  tff(f_48, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 12.90/4.99  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 12.90/4.99  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.90/4.99  tff(f_57, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 12.90/4.99  tff(f_78, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 12.90/4.99  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 12.90/4.99  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.90/4.99  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.90/4.99  tff(f_50, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.90/4.99  tff(c_46, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.90/4.99  tff(c_18, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.90/4.99  tff(c_48, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.90/4.99  tff(c_54, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.90/4.99  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.90/4.99  tff(c_187, plain, (![A_56, B_57]: (r2_hidden('#skF_2'(A_56, B_57), A_56) | r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.90/4.99  tff(c_22, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.90/4.99  tff(c_200, plain, (![A_17, B_57]: ('#skF_2'(k1_tarski(A_17), B_57)=A_17 | r1_tarski(k1_tarski(A_17), B_57))), inference(resolution, [status(thm)], [c_187, c_22])).
% 12.90/4.99  tff(c_24, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.90/4.99  tff(c_65, plain, (![B_34, A_35]: (~r2_hidden(B_34, A_35) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.90/4.99  tff(c_69, plain, (![C_21]: (~v1_xboole_0(k1_tarski(C_21)))), inference(resolution, [status(thm)], [c_24, c_65])).
% 12.90/4.99  tff(c_85, plain, (![C_39, A_40]: (C_39=A_40 | ~r2_hidden(C_39, k1_tarski(A_40)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.90/4.99  tff(c_89, plain, (![A_40]: ('#skF_1'(k1_tarski(A_40))=A_40 | v1_xboole_0(k1_tarski(A_40)))), inference(resolution, [status(thm)], [c_4, c_85])).
% 12.90/4.99  tff(c_95, plain, (![A_40]: ('#skF_1'(k1_tarski(A_40))=A_40)), inference(negUnitSimplification, [status(thm)], [c_69, c_89])).
% 12.90/4.99  tff(c_202, plain, (![C_58, B_59, A_60]: (r2_hidden(C_58, B_59) | ~r2_hidden(C_58, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.90/4.99  tff(c_321, plain, (![A_80, B_81]: (r2_hidden('#skF_1'(A_80), B_81) | ~r1_tarski(A_80, B_81) | v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_4, c_202])).
% 12.90/4.99  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.90/4.99  tff(c_6143, plain, (![A_12502, B_12503, B_12504]: (r2_hidden('#skF_1'(A_12502), B_12503) | ~r1_tarski(B_12504, B_12503) | ~r1_tarski(A_12502, B_12504) | v1_xboole_0(A_12502))), inference(resolution, [status(thm)], [c_321, c_6])).
% 12.90/4.99  tff(c_6176, plain, (![A_12613]: (r2_hidden('#skF_1'(A_12613), '#skF_7') | ~r1_tarski(A_12613, '#skF_6') | v1_xboole_0(A_12613))), inference(resolution, [status(thm)], [c_48, c_6143])).
% 12.90/4.99  tff(c_6244, plain, (![A_40]: (r2_hidden(A_40, '#skF_7') | ~r1_tarski(k1_tarski(A_40), '#skF_6') | v1_xboole_0(k1_tarski(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_95, c_6176])).
% 12.90/4.99  tff(c_6263, plain, (![A_12722]: (r2_hidden(A_12722, '#skF_7') | ~r1_tarski(k1_tarski(A_12722), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_69, c_6244])).
% 12.90/4.99  tff(c_6297, plain, (![A_12831]: (r2_hidden(A_12831, '#skF_7') | '#skF_2'(k1_tarski(A_12831), '#skF_6')=A_12831)), inference(resolution, [status(thm)], [c_200, c_6263])).
% 12.90/4.99  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.90/4.99  tff(c_6465, plain, (![A_13049]: (~r2_hidden(A_13049, '#skF_6') | r1_tarski(k1_tarski(A_13049), '#skF_6') | r2_hidden(A_13049, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6297, c_8])).
% 12.90/4.99  tff(c_6262, plain, (![A_40]: (r2_hidden(A_40, '#skF_7') | ~r1_tarski(k1_tarski(A_40), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_69, c_6244])).
% 12.90/4.99  tff(c_6593, plain, (![A_13266]: (~r2_hidden(A_13266, '#skF_6') | r2_hidden(A_13266, '#skF_7'))), inference(resolution, [status(thm)], [c_6465, c_6262])).
% 12.90/4.99  tff(c_6986, plain, (![A_14356, B_14357]: (r2_hidden(A_14356, B_14357) | ~r1_tarski('#skF_7', B_14357) | ~r2_hidden(A_14356, '#skF_6'))), inference(resolution, [status(thm)], [c_6593, c_6])).
% 12.90/4.99  tff(c_7009, plain, (![B_14357]: (r2_hidden('#skF_1'('#skF_6'), B_14357) | ~r1_tarski('#skF_7', B_14357) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_6986])).
% 12.90/4.99  tff(c_7020, plain, (![B_14466]: (r2_hidden('#skF_1'('#skF_6'), B_14466) | ~r1_tarski('#skF_7', B_14466))), inference(negUnitSimplification, [status(thm)], [c_54, c_7009])).
% 12.90/4.99  tff(c_7378, plain, (![B_15771, B_15772]: (r2_hidden('#skF_1'('#skF_6'), B_15771) | ~r1_tarski(B_15772, B_15771) | ~r1_tarski('#skF_7', B_15772))), inference(resolution, [status(thm)], [c_7020, c_6])).
% 12.90/4.99  tff(c_7413, plain, (r2_hidden('#skF_1'('#skF_6'), '#skF_7') | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_7378])).
% 12.90/4.99  tff(c_7414, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_7413])).
% 12.90/4.99  tff(c_199, plain, (![A_56]: (r1_tarski(A_56, A_56))), inference(resolution, [status(thm)], [c_187, c_8])).
% 12.90/4.99  tff(c_52, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.90/4.99  tff(c_50, plain, (v1_zfmisc_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.90/4.99  tff(c_42, plain, (![A_27]: (k6_domain_1(A_27, '#skF_5'(A_27))=A_27 | ~v1_zfmisc_1(A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.90/4.99  tff(c_44, plain, (![A_27]: (m1_subset_1('#skF_5'(A_27), A_27) | ~v1_zfmisc_1(A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.90/4.99  tff(c_298, plain, (![A_74, B_75]: (k6_domain_1(A_74, B_75)=k1_tarski(B_75) | ~m1_subset_1(B_75, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.90/4.99  tff(c_2176, plain, (![A_1577]: (k6_domain_1(A_1577, '#skF_5'(A_1577))=k1_tarski('#skF_5'(A_1577)) | ~v1_zfmisc_1(A_1577) | v1_xboole_0(A_1577))), inference(resolution, [status(thm)], [c_44, c_298])).
% 12.90/4.99  tff(c_5708, plain, (![A_11955]: (k1_tarski('#skF_5'(A_11955))=A_11955 | ~v1_zfmisc_1(A_11955) | v1_xboole_0(A_11955) | ~v1_zfmisc_1(A_11955) | v1_xboole_0(A_11955))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2176])).
% 12.90/4.99  tff(c_15495, plain, (![A_39927]: ('#skF_5'(A_39927)='#skF_1'(A_39927) | ~v1_zfmisc_1(A_39927) | v1_xboole_0(A_39927) | ~v1_zfmisc_1(A_39927) | v1_xboole_0(A_39927))), inference(superposition, [status(thm), theory('equality')], [c_5708, c_95])).
% 12.90/4.99  tff(c_15532, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_50, c_15495])).
% 12.90/4.99  tff(c_15535, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_15532])).
% 12.90/4.99  tff(c_15536, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_52, c_15535])).
% 12.90/4.99  tff(c_2204, plain, (![A_27]: (k1_tarski('#skF_5'(A_27))=A_27 | ~v1_zfmisc_1(A_27) | v1_xboole_0(A_27) | ~v1_zfmisc_1(A_27) | v1_xboole_0(A_27))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2176])).
% 12.90/4.99  tff(c_15546, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7' | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_15536, c_2204])).
% 12.90/4.99  tff(c_15604, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7' | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_15546])).
% 12.90/4.99  tff(c_15605, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_52, c_15604])).
% 12.90/4.99  tff(c_7071, plain, (![A_17]: (A_17='#skF_1'('#skF_6') | ~r1_tarski('#skF_7', k1_tarski(A_17)))), inference(resolution, [status(thm)], [c_7020, c_22])).
% 12.90/4.99  tff(c_15830, plain, ('#skF_1'('#skF_7')='#skF_1'('#skF_6') | ~r1_tarski('#skF_7', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_15605, c_7071])).
% 12.90/4.99  tff(c_16057, plain, ('#skF_1'('#skF_7')='#skF_1'('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_15830])).
% 12.90/4.99  tff(c_362, plain, (![A_88, B_89]: ('#skF_2'(k1_tarski(A_88), B_89)=A_88 | r1_tarski(k1_tarski(A_88), B_89))), inference(resolution, [status(thm)], [c_187, c_22])).
% 12.90/4.99  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.90/4.99  tff(c_380, plain, (![A_88, B_89]: (k4_xboole_0(k1_tarski(A_88), B_89)=k1_xboole_0 | '#skF_2'(k1_tarski(A_88), B_89)=A_88)), inference(resolution, [status(thm)], [c_362, c_14])).
% 12.90/4.99  tff(c_16, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.90/4.99  tff(c_1063, plain, (![A_1039, B_1040]: (k2_xboole_0(k1_tarski(A_1039), B_1040)=B_1040 | '#skF_2'(k1_tarski(A_1039), B_1040)=A_1039)), inference(resolution, [status(thm)], [c_362, c_16])).
% 12.90/4.99  tff(c_1152, plain, (![A_1059]: (k1_tarski(A_1059)=k1_xboole_0 | '#skF_2'(k1_tarski(A_1059), k1_xboole_0)=A_1059)), inference(superposition, [status(thm), theory('equality')], [c_1063, c_18])).
% 12.90/4.99  tff(c_1404, plain, (![A_1198]: (~r2_hidden(A_1198, k1_xboole_0) | r1_tarski(k1_tarski(A_1198), k1_xboole_0) | k1_tarski(A_1198)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1152, c_8])).
% 12.90/4.99  tff(c_1413, plain, (![A_1198]: (k2_xboole_0(k1_tarski(A_1198), k1_xboole_0)=k1_xboole_0 | ~r2_hidden(A_1198, k1_xboole_0) | k1_tarski(A_1198)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1404, c_16])).
% 12.90/4.99  tff(c_1476, plain, (![A_1217]: (k1_tarski(A_1217)=k1_xboole_0 | ~r2_hidden(A_1217, k1_xboole_0) | k1_tarski(A_1217)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1413])).
% 12.90/4.99  tff(c_1524, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1476])).
% 12.90/4.99  tff(c_1525, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1524])).
% 12.90/4.99  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.90/4.99  tff(c_270, plain, (![A_66, B_67]: (~v1_xboole_0(A_66) | r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_187, c_2])).
% 12.90/4.99  tff(c_277, plain, (![A_66, B_67]: (k2_xboole_0(A_66, B_67)=B_67 | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_270, c_16])).
% 12.90/4.99  tff(c_1540, plain, (![B_67]: (k2_xboole_0(k1_xboole_0, B_67)=B_67)), inference(resolution, [status(thm)], [c_1525, c_277])).
% 12.90/4.99  tff(c_1594, plain, (![B_1292]: (k2_xboole_0(k1_xboole_0, B_1292)=B_1292)), inference(resolution, [status(thm)], [c_1525, c_277])).
% 12.90/4.99  tff(c_20, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.90/4.99  tff(c_1609, plain, (![B_16]: (k4_xboole_0(B_16, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_16))), inference(superposition, [status(thm), theory('equality')], [c_1594, c_20])).
% 12.90/4.99  tff(c_1636, plain, (![B_16]: (k4_xboole_0(B_16, k1_xboole_0)=B_16)), inference(demodulation, [status(thm), theory('equality')], [c_1540, c_1609])).
% 12.90/4.99  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.90/4.99  tff(c_343, plain, (![B_84, A_85]: (~v1_xboole_0(B_84) | ~r1_tarski(A_85, B_84) | v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_321, c_2])).
% 12.90/4.99  tff(c_358, plain, (![B_11, A_10]: (~v1_xboole_0(B_11) | v1_xboole_0(A_10) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_343])).
% 12.90/4.99  tff(c_1538, plain, (![A_10]: (v1_xboole_0(A_10) | k4_xboole_0(A_10, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1525, c_358])).
% 12.90/4.99  tff(c_1837, plain, (![A_1368]: (v1_xboole_0(A_1368) | k1_xboole_0!=A_1368)), inference(demodulation, [status(thm), theory('equality')], [c_1636, c_1538])).
% 12.90/4.99  tff(c_2351, plain, (![A_1656, A_1657]: (v1_xboole_0(A_1656) | k4_xboole_0(A_1656, A_1657)!=k1_xboole_0 | k1_xboole_0!=A_1657)), inference(resolution, [status(thm)], [c_1837, c_358])).
% 12.90/4.99  tff(c_2359, plain, (![A_88, B_89]: (v1_xboole_0(k1_tarski(A_88)) | k1_xboole_0!=B_89 | '#skF_2'(k1_tarski(A_88), B_89)=A_88)), inference(superposition, [status(thm), theory('equality')], [c_380, c_2351])).
% 12.90/4.99  tff(c_2369, plain, (![B_89, A_88]: (k1_xboole_0!=B_89 | '#skF_2'(k1_tarski(A_88), B_89)=A_88)), inference(negUnitSimplification, [status(thm)], [c_69, c_2359])).
% 12.90/4.99  tff(c_15856, plain, (![B_89]: (k1_xboole_0!=B_89 | '#skF_2'('#skF_7', B_89)='#skF_1'('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_15605, c_2369])).
% 12.90/4.99  tff(c_17121, plain, ('#skF_1'('#skF_6')='#skF_2'('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16057, c_15856])).
% 12.90/4.99  tff(c_17130, plain, ('#skF_1'('#skF_7')='#skF_2'('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_17121, c_16057])).
% 12.90/4.99  tff(c_15891, plain, (![B_57]: ('#skF_2'(k1_tarski('#skF_1'('#skF_7')), B_57)='#skF_1'('#skF_7') | r1_tarski('#skF_7', B_57))), inference(superposition, [status(thm), theory('equality')], [c_15605, c_200])).
% 12.90/4.99  tff(c_16066, plain, (![B_57]: ('#skF_2'('#skF_7', B_57)='#skF_1'('#skF_7') | r1_tarski('#skF_7', B_57))), inference(demodulation, [status(thm), theory('equality')], [c_15605, c_15891])).
% 12.90/4.99  tff(c_20760, plain, (![B_47142]: ('#skF_2'('#skF_7', k1_xboole_0)='#skF_2'('#skF_7', B_47142) | r1_tarski('#skF_7', B_47142))), inference(demodulation, [status(thm), theory('equality')], [c_17130, c_16066])).
% 12.90/4.99  tff(c_20872, plain, ('#skF_2'('#skF_7', k1_xboole_0)='#skF_2'('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_20760, c_7414])).
% 12.90/4.99  tff(c_17143, plain, (![B_42262]: (k1_xboole_0!=B_42262 | '#skF_2'('#skF_7', B_42262)='#skF_1'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_16057, c_15856])).
% 12.90/4.99  tff(c_17170, plain, (![B_42262]: (v1_xboole_0('#skF_6') | r2_hidden('#skF_2'('#skF_7', B_42262), '#skF_6') | k1_xboole_0!=B_42262)), inference(superposition, [status(thm), theory('equality')], [c_17143, c_4])).
% 12.90/4.99  tff(c_17212, plain, (![B_42262]: (r2_hidden('#skF_2'('#skF_7', B_42262), '#skF_6') | k1_xboole_0!=B_42262)), inference(negUnitSimplification, [status(thm)], [c_54, c_17170])).
% 12.90/4.99  tff(c_20977, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_20872, c_17212])).
% 12.90/4.99  tff(c_21498, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_20977, c_8])).
% 12.90/4.99  tff(c_21531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7414, c_21498])).
% 12.90/4.99  tff(c_21533, plain, (r1_tarski('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_7413])).
% 12.90/4.99  tff(c_21585, plain, (k2_xboole_0('#skF_7', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_21533, c_16])).
% 12.90/4.99  tff(c_142, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k1_xboole_0 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.90/4.99  tff(c_150, plain, (k4_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_142])).
% 12.90/4.99  tff(c_170, plain, (![A_54, B_55]: (k2_xboole_0(A_54, k4_xboole_0(B_55, A_54))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.90/4.99  tff(c_179, plain, (k2_xboole_0('#skF_7', k1_xboole_0)=k2_xboole_0('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_150, c_170])).
% 12.90/4.99  tff(c_182, plain, (k2_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_179])).
% 12.90/4.99  tff(c_21625, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_21585, c_182])).
% 12.90/4.99  tff(c_21627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_21625])).
% 12.90/4.99  tff(c_21628, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1524])).
% 12.90/4.99  tff(c_819, plain, (![A_959, A_960]: (A_959='#skF_1'(A_960) | ~r1_tarski(A_960, k1_tarski(A_959)) | v1_xboole_0(A_960))), inference(resolution, [status(thm)], [c_321, c_22])).
% 12.90/4.99  tff(c_847, plain, (![A_959, A_10]: (A_959='#skF_1'(A_10) | v1_xboole_0(A_10) | k4_xboole_0(A_10, k1_tarski(A_959))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_819])).
% 12.90/4.99  tff(c_22802, plain, (![A_48764]: ('#skF_1'(k1_xboole_0)='#skF_1'(A_48764) | v1_xboole_0(A_48764) | k4_xboole_0(A_48764, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_21628, c_847])).
% 12.90/4.99  tff(c_22847, plain, ('#skF_1'(k1_xboole_0)='#skF_1'('#skF_7') | k4_xboole_0('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_22802, c_52])).
% 12.90/4.99  tff(c_22876, plain, (k4_xboole_0('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_22847])).
% 12.90/4.99  tff(c_155, plain, (![A_49, B_50]: (k2_xboole_0(A_49, B_50)=B_50 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.90/4.99  tff(c_163, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_48, c_155])).
% 12.90/4.99  tff(c_26137, plain, (![A_58961, B_58962, B_58963]: (r2_hidden('#skF_1'(A_58961), B_58962) | ~r1_tarski(B_58963, B_58962) | ~r1_tarski(A_58961, B_58963) | v1_xboole_0(A_58961))), inference(resolution, [status(thm)], [c_321, c_6])).
% 12.90/4.99  tff(c_26173, plain, (![A_59054]: (r2_hidden('#skF_1'(A_59054), '#skF_7') | ~r1_tarski(A_59054, '#skF_6') | v1_xboole_0(A_59054))), inference(resolution, [status(thm)], [c_48, c_26137])).
% 12.90/4.99  tff(c_26240, plain, (![A_40]: (r2_hidden(A_40, '#skF_7') | ~r1_tarski(k1_tarski(A_40), '#skF_6') | v1_xboole_0(k1_tarski(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_95, c_26173])).
% 12.90/4.99  tff(c_26259, plain, (![A_59145]: (r2_hidden(A_59145, '#skF_7') | ~r1_tarski(k1_tarski(A_59145), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_69, c_26240])).
% 12.90/4.99  tff(c_26346, plain, (![A_59327]: (r2_hidden(A_59327, '#skF_7') | '#skF_2'(k1_tarski(A_59327), '#skF_6')=A_59327)), inference(resolution, [status(thm)], [c_200, c_26259])).
% 12.90/4.99  tff(c_26475, plain, (![A_59509]: (~r2_hidden(A_59509, '#skF_6') | r1_tarski(k1_tarski(A_59509), '#skF_6') | r2_hidden(A_59509, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_26346, c_8])).
% 12.90/4.99  tff(c_26258, plain, (![A_40]: (r2_hidden(A_40, '#skF_7') | ~r1_tarski(k1_tarski(A_40), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_69, c_26240])).
% 12.90/4.99  tff(c_26570, plain, (![A_59690]: (~r2_hidden(A_59690, '#skF_6') | r2_hidden(A_59690, '#skF_7'))), inference(resolution, [status(thm)], [c_26475, c_26258])).
% 12.90/4.99  tff(c_26998, plain, (![A_60509, B_60510]: (r2_hidden(A_60509, B_60510) | ~r1_tarski('#skF_7', B_60510) | ~r2_hidden(A_60509, '#skF_6'))), inference(resolution, [status(thm)], [c_26570, c_6])).
% 12.90/4.99  tff(c_27030, plain, (![B_60510]: (r2_hidden('#skF_1'('#skF_6'), B_60510) | ~r1_tarski('#skF_7', B_60510) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_26998])).
% 12.90/4.99  tff(c_27045, plain, (![B_60601]: (r2_hidden('#skF_1'('#skF_6'), B_60601) | ~r1_tarski('#skF_7', B_60601))), inference(negUnitSimplification, [status(thm)], [c_54, c_27030])).
% 12.90/4.99  tff(c_27357, plain, (![B_61420, B_61421]: (r2_hidden('#skF_1'('#skF_6'), B_61420) | ~r1_tarski(B_61421, B_61420) | ~r1_tarski('#skF_7', B_61421))), inference(resolution, [status(thm)], [c_27045, c_6])).
% 12.90/4.99  tff(c_27395, plain, (r2_hidden('#skF_1'('#skF_6'), '#skF_7') | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_27357])).
% 12.90/4.99  tff(c_27396, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_27395])).
% 12.90/4.99  tff(c_21756, plain, (![A_48244]: (k6_domain_1(A_48244, '#skF_5'(A_48244))=k1_tarski('#skF_5'(A_48244)) | ~v1_zfmisc_1(A_48244) | v1_xboole_0(A_48244))), inference(resolution, [status(thm)], [c_44, c_298])).
% 12.90/4.99  tff(c_26700, plain, (![A_60054]: (k1_tarski('#skF_5'(A_60054))=A_60054 | ~v1_zfmisc_1(A_60054) | v1_xboole_0(A_60054) | ~v1_zfmisc_1(A_60054) | v1_xboole_0(A_60054))), inference(superposition, [status(thm), theory('equality')], [c_42, c_21756])).
% 12.90/4.99  tff(c_29562, plain, (![A_67563]: ('#skF_5'(A_67563)='#skF_1'(A_67563) | ~v1_zfmisc_1(A_67563) | v1_xboole_0(A_67563) | ~v1_zfmisc_1(A_67563) | v1_xboole_0(A_67563))), inference(superposition, [status(thm), theory('equality')], [c_26700, c_95])).
% 12.90/4.99  tff(c_29592, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_50, c_29562])).
% 12.90/4.99  tff(c_29595, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_29592])).
% 12.90/4.99  tff(c_29596, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_52, c_29595])).
% 12.90/4.99  tff(c_21784, plain, (![A_27]: (k1_tarski('#skF_5'(A_27))=A_27 | ~v1_zfmisc_1(A_27) | v1_xboole_0(A_27) | ~v1_zfmisc_1(A_27) | v1_xboole_0(A_27))), inference(superposition, [status(thm), theory('equality')], [c_42, c_21756])).
% 12.90/4.99  tff(c_29600, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7' | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_29596, c_21784])).
% 12.90/4.99  tff(c_29644, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7' | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_29600])).
% 12.90/4.99  tff(c_29645, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_52, c_29644])).
% 12.90/4.99  tff(c_27105, plain, (![A_17]: (A_17='#skF_1'('#skF_6') | ~r1_tarski('#skF_7', k1_tarski(A_17)))), inference(resolution, [status(thm)], [c_27045, c_22])).
% 12.90/4.99  tff(c_29682, plain, ('#skF_1'('#skF_7')='#skF_1'('#skF_6') | ~r1_tarski('#skF_7', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_29645, c_27105])).
% 12.90/4.99  tff(c_29889, plain, ('#skF_1'('#skF_7')='#skF_1'('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_29682])).
% 12.90/4.99  tff(c_30101, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_29889, c_29645])).
% 12.90/4.99  tff(c_212, plain, (![A_61]: (r1_tarski(A_61, A_61))), inference(resolution, [status(thm)], [c_187, c_8])).
% 12.90/4.99  tff(c_220, plain, (![A_61]: (k4_xboole_0(A_61, A_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_212, c_14])).
% 12.90/4.99  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.90/4.99  tff(c_209, plain, (![A_5, B_6, B_59]: (r2_hidden('#skF_2'(A_5, B_6), B_59) | ~r1_tarski(A_5, B_59) | r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_10, c_202])).
% 12.90/4.99  tff(c_26600, plain, (![A_59781]: (r1_tarski(A_59781, '#skF_7') | ~r2_hidden('#skF_2'(A_59781, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_26570, c_8])).
% 12.90/4.99  tff(c_26625, plain, (![A_5]: (~r1_tarski(A_5, '#skF_6') | r1_tarski(A_5, '#skF_7'))), inference(resolution, [status(thm)], [c_209, c_26600])).
% 12.90/4.99  tff(c_27388, plain, (![A_5]: (r2_hidden('#skF_1'('#skF_6'), '#skF_7') | ~r1_tarski('#skF_7', A_5) | ~r1_tarski(A_5, '#skF_6'))), inference(resolution, [status(thm)], [c_26625, c_27357])).
% 12.90/4.99  tff(c_27411, plain, (![A_61692]: (~r1_tarski('#skF_7', A_61692) | ~r1_tarski(A_61692, '#skF_6'))), inference(splitLeft, [status(thm)], [c_27388])).
% 12.90/4.99  tff(c_27428, plain, (![B_61783]: (~r1_tarski(B_61783, '#skF_6') | k4_xboole_0('#skF_7', B_61783)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_27411])).
% 12.90/4.99  tff(c_27450, plain, (![A_17]: (k4_xboole_0('#skF_7', k1_tarski(A_17))!=k1_xboole_0 | '#skF_2'(k1_tarski(A_17), '#skF_6')=A_17)), inference(resolution, [status(thm)], [c_200, c_27428])).
% 12.90/4.99  tff(c_30338, plain, (k4_xboole_0('#skF_7', '#skF_7')!=k1_xboole_0 | '#skF_2'(k1_tarski('#skF_1'('#skF_6')), '#skF_6')='#skF_1'('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_30101, c_27450])).
% 12.90/4.99  tff(c_30545, plain, ('#skF_1'('#skF_6')='#skF_2'('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30101, c_220, c_30338])).
% 12.90/4.99  tff(c_30714, plain, (v1_xboole_0('#skF_6') | r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_30545, c_4])).
% 12.90/4.99  tff(c_30747, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_30714])).
% 12.90/4.99  tff(c_33550, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_30747, c_8])).
% 12.90/4.99  tff(c_33585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27396, c_33550])).
% 12.90/4.99  tff(c_33586, plain, (r2_hidden('#skF_1'('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_27388])).
% 12.90/4.99  tff(c_36260, plain, (![A_81572]: ('#skF_5'(A_81572)='#skF_1'(A_81572) | ~v1_zfmisc_1(A_81572) | v1_xboole_0(A_81572) | ~v1_zfmisc_1(A_81572) | v1_xboole_0(A_81572))), inference(superposition, [status(thm), theory('equality')], [c_26700, c_95])).
% 12.90/4.99  tff(c_36297, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_50, c_36260])).
% 12.90/4.99  tff(c_36300, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36297])).
% 12.90/4.99  tff(c_36301, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_52, c_36300])).
% 12.90/4.99  tff(c_36305, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7' | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36301, c_21784])).
% 12.90/4.99  tff(c_36357, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7' | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_36305])).
% 12.90/4.99  tff(c_36358, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_52, c_36357])).
% 12.90/4.99  tff(c_36392, plain, ('#skF_1'('#skF_7')='#skF_1'('#skF_6') | ~r1_tarski('#skF_7', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_36358, c_27105])).
% 12.90/4.99  tff(c_36606, plain, ('#skF_1'('#skF_7')='#skF_1'('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_36392])).
% 12.90/4.99  tff(c_1078, plain, (![A_1039]: (k1_tarski(A_1039)=k1_xboole_0 | '#skF_2'(k1_tarski(A_1039), k1_xboole_0)=A_1039)), inference(superposition, [status(thm), theory('equality')], [c_1063, c_18])).
% 12.90/4.99  tff(c_36448, plain, (k1_tarski('#skF_1'('#skF_7'))=k1_xboole_0 | '#skF_1'('#skF_7')='#skF_2'('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36358, c_1078])).
% 12.90/4.99  tff(c_36617, plain, (k1_xboole_0='#skF_7' | '#skF_1'('#skF_7')='#skF_2'('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36358, c_36448])).
% 12.90/4.99  tff(c_37737, plain, (k1_xboole_0='#skF_7' | '#skF_1'('#skF_6')='#skF_2'('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36606, c_36617])).
% 12.90/4.99  tff(c_37738, plain, ('#skF_1'('#skF_6')='#skF_2'('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_37737])).
% 12.90/4.99  tff(c_37749, plain, ('#skF_1'('#skF_7')='#skF_2'('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_37738, c_36606])).
% 12.90/4.99  tff(c_36475, plain, (![B_57]: ('#skF_2'(k1_tarski('#skF_1'('#skF_7')), B_57)='#skF_1'('#skF_7') | r1_tarski('#skF_7', B_57))), inference(superposition, [status(thm), theory('equality')], [c_36358, c_200])).
% 12.90/4.99  tff(c_36620, plain, (![B_57]: ('#skF_2'('#skF_7', B_57)='#skF_1'('#skF_7') | r1_tarski('#skF_7', B_57))), inference(demodulation, [status(thm), theory('equality')], [c_36358, c_36475])).
% 12.90/4.99  tff(c_41328, plain, (![B_87879]: ('#skF_2'('#skF_7', k1_xboole_0)='#skF_2'('#skF_7', B_87879) | r1_tarski('#skF_7', B_87879))), inference(demodulation, [status(thm), theory('equality')], [c_37749, c_36620])).
% 12.90/4.99  tff(c_41440, plain, ('#skF_2'('#skF_7', k1_xboole_0)='#skF_2'('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_41328, c_27396])).
% 12.90/4.99  tff(c_37779, plain, (v1_xboole_0('#skF_6') | r2_hidden('#skF_2'('#skF_7', k1_xboole_0), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_37738, c_4])).
% 12.90/4.99  tff(c_37812, plain, (r2_hidden('#skF_2'('#skF_7', k1_xboole_0), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_37779])).
% 12.90/4.99  tff(c_41475, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_41440, c_37812])).
% 12.90/4.99  tff(c_41553, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_41475, c_8])).
% 12.90/4.99  tff(c_41585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27396, c_41553])).
% 12.90/4.99  tff(c_41586, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_37737])).
% 12.90/4.99  tff(c_1473, plain, (![A_1198]: (k1_tarski(A_1198)=k1_xboole_0 | ~r2_hidden(A_1198, k1_xboole_0) | k1_tarski(A_1198)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1413])).
% 12.90/4.99  tff(c_27103, plain, (k1_tarski('#skF_1'('#skF_6'))=k1_xboole_0 | ~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_27045, c_1473])).
% 12.90/4.99  tff(c_27133, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_27103])).
% 12.90/4.99  tff(c_1167, plain, (![A_1059]: (~r2_hidden(A_1059, k1_xboole_0) | r1_tarski(k1_tarski(A_1059), k1_xboole_0) | k1_tarski(A_1059)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1152, c_8])).
% 12.90/4.99  tff(c_36439, plain, (~r2_hidden('#skF_1'('#skF_7'), k1_xboole_0) | r1_tarski('#skF_7', k1_xboole_0) | k1_tarski('#skF_1'('#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_36358, c_1167])).
% 12.90/4.99  tff(c_36614, plain, (~r2_hidden('#skF_1'('#skF_7'), k1_xboole_0) | r1_tarski('#skF_7', k1_xboole_0) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_36358, c_36439])).
% 12.90/4.99  tff(c_36615, plain, (~r2_hidden('#skF_1'('#skF_7'), k1_xboole_0) | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_27133, c_36614])).
% 12.90/4.99  tff(c_37568, plain, (~r2_hidden('#skF_1'('#skF_6'), k1_xboole_0) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_36606, c_36615])).
% 12.90/4.99  tff(c_37569, plain, (~r2_hidden('#skF_1'('#skF_6'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_37568])).
% 12.90/4.99  tff(c_41589, plain, (~r2_hidden('#skF_1'('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_41586, c_37569])).
% 12.90/4.99  tff(c_41675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33586, c_41589])).
% 12.90/4.99  tff(c_41676, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_37568])).
% 12.90/4.99  tff(c_210, plain, (![A_1, B_59]: (r2_hidden('#skF_1'(A_1), B_59) | ~r1_tarski(A_1, B_59) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_202])).
% 12.90/4.99  tff(c_1522, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=k1_xboole_0 | ~r1_tarski(A_1, k1_xboole_0) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_210, c_1476])).
% 12.90/4.99  tff(c_36814, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_36606, c_36358])).
% 12.90/4.99  tff(c_37203, plain, (k1_xboole_0='#skF_7' | ~r1_tarski('#skF_6', k1_xboole_0) | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1522, c_36814])).
% 12.90/4.99  tff(c_37277, plain, (k1_xboole_0='#skF_7' | ~r1_tarski('#skF_6', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_37203])).
% 12.90/4.99  tff(c_37400, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_37277])).
% 12.90/4.99  tff(c_41678, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_41676, c_37400])).
% 12.90/4.99  tff(c_41763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_41678])).
% 12.90/4.99  tff(c_41764, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_37277])).
% 12.90/4.99  tff(c_41781, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_41764, c_27133])).
% 12.90/4.99  tff(c_41850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_41781])).
% 12.90/4.99  tff(c_41852, plain, (r1_tarski('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_27395])).
% 12.90/4.99  tff(c_41899, plain, (k4_xboole_0('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_41852, c_14])).
% 12.90/4.99  tff(c_42110, plain, (k2_xboole_0('#skF_6', k1_xboole_0)=k2_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_41899, c_20])).
% 12.90/4.99  tff(c_42123, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_163, c_42110])).
% 12.90/4.99  tff(c_42125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_42123])).
% 12.90/4.99  tff(c_42127, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_27103])).
% 12.90/4.99  tff(c_42152, plain, (k4_xboole_0('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42127, c_14])).
% 12.90/4.99  tff(c_42171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22876, c_42152])).
% 12.90/4.99  tff(c_42173, plain, (k4_xboole_0('#skF_7', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_22847])).
% 12.90/4.99  tff(c_162, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_155])).
% 12.90/4.99  tff(c_42214, plain, (k2_xboole_0('#skF_7', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42173, c_162])).
% 12.90/4.99  tff(c_42222, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_42214])).
% 12.90/4.99  tff(c_42250, plain, (![A_14]: (k2_xboole_0(A_14, '#skF_7')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_42222, c_18])).
% 12.90/4.99  tff(c_42394, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42250, c_163])).
% 12.90/4.99  tff(c_42396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_42394])).
% 12.90/4.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.90/4.99  
% 12.90/4.99  Inference rules
% 12.90/4.99  ----------------------
% 12.90/4.99  #Ref     : 1
% 12.90/4.99  #Sup     : 6139
% 12.90/4.99  #Fact    : 10
% 12.90/4.99  #Define  : 0
% 12.90/4.99  #Split   : 36
% 12.90/4.99  #Chain   : 0
% 12.90/4.99  #Close   : 0
% 12.90/4.99  
% 12.90/4.99  Ordering : KBO
% 12.90/4.99  
% 12.90/4.99  Simplification rules
% 12.90/4.99  ----------------------
% 12.90/4.99  #Subsume      : 2189
% 12.90/4.99  #Demod        : 2124
% 12.90/4.99  #Tautology    : 1447
% 12.90/4.99  #SimpNegUnit  : 676
% 12.90/4.99  #BackRed      : 444
% 12.90/4.99  
% 12.90/4.99  #Partial instantiations: 54029
% 12.90/4.99  #Strategies tried      : 1
% 12.90/4.99  
% 12.90/4.99  Timing (in seconds)
% 12.90/4.99  ----------------------
% 12.90/4.99  Preprocessing        : 0.32
% 12.90/4.99  Parsing              : 0.17
% 12.90/4.99  CNF conversion       : 0.02
% 12.90/4.99  Main loop            : 3.84
% 12.90/4.99  Inferencing          : 1.60
% 12.90/4.99  Reduction            : 0.99
% 12.90/4.99  Demodulation         : 0.64
% 12.90/4.99  BG Simplification    : 0.11
% 12.90/4.99  Subsumption          : 0.91
% 12.90/4.99  Abstraction          : 0.16
% 12.90/4.99  MUC search           : 0.00
% 12.90/4.99  Cooper               : 0.00
% 12.90/4.99  Total                : 4.24
% 12.90/4.99  Index Insertion      : 0.00
% 12.90/4.99  Index Deletion       : 0.00
% 12.90/4.99  Index Matching       : 0.00
% 12.90/4.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
