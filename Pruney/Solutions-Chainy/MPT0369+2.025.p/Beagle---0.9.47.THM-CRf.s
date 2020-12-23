%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:54 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 331 expanded)
%              Number of leaves         :   32 ( 116 expanded)
%              Depth                    :   20
%              Number of atoms          :  176 ( 763 expanded)
%              Number of equality atoms :   50 ( 122 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_34,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_91,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_99,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_91])).

tff(c_100,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_38,plain,(
    ! [B_22,A_21] :
      ( r2_hidden(B_22,A_21)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden('#skF_1'(A_45,B_46),B_46)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_115,plain,(
    ! [A_47] : r1_tarski(A_47,A_47) ),
    inference(resolution,[status(thm)],[c_6,c_109])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_119,plain,(
    ! [A_47] : k3_xboole_0(A_47,A_47) = A_47 ),
    inference(resolution,[status(thm)],[c_115,c_26])).

tff(c_205,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_214,plain,(
    ! [A_47] : k5_xboole_0(A_47,A_47) = k4_xboole_0(A_47,A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_205])).

tff(c_220,plain,(
    ! [A_47] : k4_xboole_0(A_47,A_47) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_214])).

tff(c_132,plain,(
    ! [A_50] : k3_xboole_0(A_50,A_50) = A_50 ),
    inference(resolution,[status(thm)],[c_115,c_26])).

tff(c_30,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_138,plain,(
    ! [A_50] : k2_xboole_0(A_50,k4_xboole_0(A_50,A_50)) = A_50 ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_30])).

tff(c_266,plain,(
    ! [A_50] : k2_xboole_0(A_50,k1_xboole_0) = A_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_138])).

tff(c_40,plain,(
    ! [B_22,A_21] :
      ( m1_subset_1(B_22,A_21)
      | ~ v1_xboole_0(B_22)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_187,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(B_55,A_56)
      | ~ m1_subset_1(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_204,plain,
    ( ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_50])).

tff(c_260,plain,(
    ~ m1_subset_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_264,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_260])).

tff(c_265,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_182,plain,(
    ! [B_53,A_54] :
      ( m1_subset_1(B_53,A_54)
      | ~ r2_hidden(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_186,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_182])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_322,plain,(
    ! [C_66,A_67,B_68] :
      ( r2_hidden(C_66,A_67)
      | ~ r2_hidden(C_66,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_811,plain,(
    ! [B_110,A_111,A_112] :
      ( r2_hidden(B_110,A_111)
      | ~ m1_subset_1(A_112,k1_zfmisc_1(A_111))
      | ~ m1_subset_1(B_110,A_112)
      | v1_xboole_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_38,c_322])).

tff(c_819,plain,(
    ! [B_110] :
      ( r2_hidden(B_110,'#skF_2')
      | ~ m1_subset_1(B_110,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_811])).

tff(c_825,plain,(
    ! [B_113] :
      ( r2_hidden(B_113,'#skF_2')
      | ~ m1_subset_1(B_113,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_819])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_855,plain,(
    ! [A_115] :
      ( r1_tarski(A_115,'#skF_2')
      | ~ m1_subset_1('#skF_1'(A_115,'#skF_2'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_825,c_4])).

tff(c_859,plain,
    ( v1_xboole_0('#skF_3')
    | r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_186,c_855])).

tff(c_865,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_859])).

tff(c_874,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_865,c_26])).

tff(c_24,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_878,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_874,c_24])).

tff(c_884,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_878])).

tff(c_382,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k3_subset_1(A_72,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_391,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_382])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(k4_xboole_0(A_6,B_7),k4_xboole_0(B_7,A_6)) = k5_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_395,plain,(
    k2_xboole_0(k3_subset_1('#skF_2','#skF_3'),k4_xboole_0('#skF_3','#skF_2')) = k5_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_8])).

tff(c_886,plain,(
    k2_xboole_0(k3_subset_1('#skF_2','#skF_3'),k1_xboole_0) = k5_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_395])).

tff(c_888,plain,(
    k5_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_886])).

tff(c_22,plain,(
    ! [A_9,C_11,B_10] :
      ( r2_hidden(A_9,C_11)
      | ~ r2_hidden(A_9,B_10)
      | r2_hidden(A_9,k5_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1263,plain,(
    ! [A_146] :
      ( r2_hidden(A_146,'#skF_3')
      | ~ r2_hidden(A_146,'#skF_2')
      | r2_hidden(A_146,k3_subset_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_22])).

tff(c_48,plain,(
    ~ r2_hidden('#skF_4',k3_subset_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1280,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_1263,c_48])).

tff(c_1290,plain,(
    ~ r2_hidden('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1280])).

tff(c_1299,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1290])).

tff(c_1306,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1299])).

tff(c_1308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1306])).

tff(c_1309,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_1310,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_10,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1314,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1310,c_10])).

tff(c_32,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_217,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = k4_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_205])).

tff(c_221,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_217])).

tff(c_1316,plain,(
    ! [A_16] : k4_xboole_0(A_16,'#skF_3') = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1314,c_221])).

tff(c_1551,plain,(
    ! [A_165,B_166] :
      ( k4_xboole_0(A_165,B_166) = k3_subset_1(A_165,B_166)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(A_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1558,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1551])).

tff(c_1561,plain,(
    k3_subset_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1316,c_1558])).

tff(c_203,plain,
    ( ~ m1_subset_1('#skF_4',k3_subset_1('#skF_2','#skF_3'))
    | v1_xboole_0(k3_subset_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_187,c_48])).

tff(c_1352,plain,(
    ~ m1_subset_1('#skF_4',k3_subset_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_1562,plain,(
    ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_1352])).

tff(c_1566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1562])).

tff(c_1567,plain,(
    v1_xboole_0(k3_subset_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_1568,plain,(
    m1_subset_1('#skF_4',k3_subset_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_42,plain,(
    ! [B_22,A_21] :
      ( v1_xboole_0(B_22)
      | ~ m1_subset_1(B_22,A_21)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1582,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k3_subset_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1568,c_42])).

tff(c_1585,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1567,c_1582])).

tff(c_1587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1309,c_1585])).

tff(c_1588,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_1589,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_1607,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1589,c_42])).

tff(c_1610,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_1607])).

tff(c_1593,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1588,c_10])).

tff(c_1618,plain,(
    ! [A_171] :
      ( A_171 = '#skF_3'
      | ~ v1_xboole_0(A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1593,c_10])).

tff(c_1625,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1610,c_1618])).

tff(c_1595,plain,(
    ! [A_16] : k4_xboole_0(A_16,'#skF_3') = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1593,c_221])).

tff(c_1664,plain,(
    ! [A_16] : k4_xboole_0(A_16,'#skF_4') = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1625,c_1595])).

tff(c_1634,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1625,c_54])).

tff(c_1810,plain,(
    ! [A_183,B_184] :
      ( k4_xboole_0(A_183,B_184) = k3_subset_1(A_183,B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(A_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1813,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_1634,c_1810])).

tff(c_1819,plain,(
    k3_subset_1('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_1813])).

tff(c_1633,plain,(
    ~ r2_hidden('#skF_4',k3_subset_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1625,c_48])).

tff(c_1826,plain,(
    ~ r2_hidden('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1819,c_1633])).

tff(c_1829,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1826])).

tff(c_1832,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1829])).

tff(c_1834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1832])).

tff(c_1836,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_1844,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1836,c_10])).

tff(c_1848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.32  % Computer   : n015.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % DateTime   : Tue Dec  1 14:17:38 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.57  
% 3.23/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.57  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.23/1.57  
% 3.23/1.57  %Foreground sorts:
% 3.23/1.57  
% 3.23/1.57  
% 3.23/1.57  %Background operators:
% 3.23/1.57  
% 3.23/1.57  
% 3.23/1.57  %Foreground operators:
% 3.23/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.23/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.57  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.23/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.23/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.23/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.23/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.57  
% 3.23/1.59  tff(f_98, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 3.23/1.59  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.23/1.59  tff(f_59, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.23/1.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.23/1.59  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.23/1.59  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.23/1.59  tff(f_55, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.23/1.59  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.23/1.59  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.23/1.59  tff(f_34, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 3.23/1.59  tff(f_45, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.23/1.59  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.23/1.59  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.23/1.59  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.23/1.59  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.59  tff(c_52, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.59  tff(c_91, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.23/1.59  tff(c_99, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_91])).
% 3.23/1.59  tff(c_100, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_99])).
% 3.23/1.59  tff(c_38, plain, (![B_22, A_21]: (r2_hidden(B_22, A_21) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.23/1.59  tff(c_50, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.59  tff(c_34, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.23/1.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/1.59  tff(c_109, plain, (![A_45, B_46]: (~r2_hidden('#skF_1'(A_45, B_46), B_46) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/1.59  tff(c_115, plain, (![A_47]: (r1_tarski(A_47, A_47))), inference(resolution, [status(thm)], [c_6, c_109])).
% 3.23/1.59  tff(c_26, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.23/1.59  tff(c_119, plain, (![A_47]: (k3_xboole_0(A_47, A_47)=A_47)), inference(resolution, [status(thm)], [c_115, c_26])).
% 3.23/1.59  tff(c_205, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.59  tff(c_214, plain, (![A_47]: (k5_xboole_0(A_47, A_47)=k4_xboole_0(A_47, A_47))), inference(superposition, [status(thm), theory('equality')], [c_119, c_205])).
% 3.23/1.59  tff(c_220, plain, (![A_47]: (k4_xboole_0(A_47, A_47)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_214])).
% 3.23/1.59  tff(c_132, plain, (![A_50]: (k3_xboole_0(A_50, A_50)=A_50)), inference(resolution, [status(thm)], [c_115, c_26])).
% 3.23/1.59  tff(c_30, plain, (![A_17, B_18]: (k2_xboole_0(k3_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.59  tff(c_138, plain, (![A_50]: (k2_xboole_0(A_50, k4_xboole_0(A_50, A_50))=A_50)), inference(superposition, [status(thm), theory('equality')], [c_132, c_30])).
% 3.23/1.59  tff(c_266, plain, (![A_50]: (k2_xboole_0(A_50, k1_xboole_0)=A_50)), inference(demodulation, [status(thm), theory('equality')], [c_220, c_138])).
% 3.23/1.59  tff(c_40, plain, (![B_22, A_21]: (m1_subset_1(B_22, A_21) | ~v1_xboole_0(B_22) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.23/1.59  tff(c_187, plain, (![B_55, A_56]: (r2_hidden(B_55, A_56) | ~m1_subset_1(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.23/1.59  tff(c_204, plain, (~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_187, c_50])).
% 3.23/1.59  tff(c_260, plain, (~m1_subset_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_204])).
% 3.23/1.59  tff(c_264, plain, (~v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_260])).
% 3.23/1.59  tff(c_265, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_264])).
% 3.23/1.59  tff(c_182, plain, (![B_53, A_54]: (m1_subset_1(B_53, A_54) | ~r2_hidden(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.23/1.59  tff(c_186, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_182])).
% 3.23/1.59  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.59  tff(c_322, plain, (![C_66, A_67, B_68]: (r2_hidden(C_66, A_67) | ~r2_hidden(C_66, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/1.59  tff(c_811, plain, (![B_110, A_111, A_112]: (r2_hidden(B_110, A_111) | ~m1_subset_1(A_112, k1_zfmisc_1(A_111)) | ~m1_subset_1(B_110, A_112) | v1_xboole_0(A_112))), inference(resolution, [status(thm)], [c_38, c_322])).
% 3.23/1.59  tff(c_819, plain, (![B_110]: (r2_hidden(B_110, '#skF_2') | ~m1_subset_1(B_110, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_811])).
% 3.23/1.59  tff(c_825, plain, (![B_113]: (r2_hidden(B_113, '#skF_2') | ~m1_subset_1(B_113, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_265, c_819])).
% 3.23/1.59  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/1.59  tff(c_855, plain, (![A_115]: (r1_tarski(A_115, '#skF_2') | ~m1_subset_1('#skF_1'(A_115, '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_825, c_4])).
% 3.23/1.59  tff(c_859, plain, (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_186, c_855])).
% 3.23/1.59  tff(c_865, plain, (r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_265, c_859])).
% 3.23/1.59  tff(c_874, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_865, c_26])).
% 3.23/1.59  tff(c_24, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.59  tff(c_878, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_874, c_24])).
% 3.23/1.59  tff(c_884, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_878])).
% 3.23/1.59  tff(c_382, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k3_subset_1(A_72, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.59  tff(c_391, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_382])).
% 3.23/1.59  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(k4_xboole_0(A_6, B_7), k4_xboole_0(B_7, A_6))=k5_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.23/1.59  tff(c_395, plain, (k2_xboole_0(k3_subset_1('#skF_2', '#skF_3'), k4_xboole_0('#skF_3', '#skF_2'))=k5_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_391, c_8])).
% 3.23/1.59  tff(c_886, plain, (k2_xboole_0(k3_subset_1('#skF_2', '#skF_3'), k1_xboole_0)=k5_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_884, c_395])).
% 3.23/1.59  tff(c_888, plain, (k5_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_886])).
% 3.23/1.59  tff(c_22, plain, (![A_9, C_11, B_10]: (r2_hidden(A_9, C_11) | ~r2_hidden(A_9, B_10) | r2_hidden(A_9, k5_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.23/1.59  tff(c_1263, plain, (![A_146]: (r2_hidden(A_146, '#skF_3') | ~r2_hidden(A_146, '#skF_2') | r2_hidden(A_146, k3_subset_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_888, c_22])).
% 3.23/1.59  tff(c_48, plain, (~r2_hidden('#skF_4', k3_subset_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.59  tff(c_1280, plain, (r2_hidden('#skF_4', '#skF_3') | ~r2_hidden('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_1263, c_48])).
% 3.23/1.59  tff(c_1290, plain, (~r2_hidden('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_1280])).
% 3.23/1.59  tff(c_1299, plain, (~m1_subset_1('#skF_4', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_1290])).
% 3.23/1.59  tff(c_1306, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1299])).
% 3.23/1.59  tff(c_1308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_1306])).
% 3.23/1.59  tff(c_1309, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_264])).
% 3.23/1.59  tff(c_1310, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_264])).
% 3.23/1.59  tff(c_10, plain, (![A_8]: (k1_xboole_0=A_8 | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.23/1.59  tff(c_1314, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1310, c_10])).
% 3.23/1.59  tff(c_32, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.23/1.59  tff(c_28, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.23/1.59  tff(c_217, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=k4_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_205])).
% 3.23/1.59  tff(c_221, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_217])).
% 3.23/1.59  tff(c_1316, plain, (![A_16]: (k4_xboole_0(A_16, '#skF_3')=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_1314, c_221])).
% 3.23/1.59  tff(c_1551, plain, (![A_165, B_166]: (k4_xboole_0(A_165, B_166)=k3_subset_1(A_165, B_166) | ~m1_subset_1(B_166, k1_zfmisc_1(A_165)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.59  tff(c_1558, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_1551])).
% 3.23/1.59  tff(c_1561, plain, (k3_subset_1('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1316, c_1558])).
% 3.23/1.59  tff(c_203, plain, (~m1_subset_1('#skF_4', k3_subset_1('#skF_2', '#skF_3')) | v1_xboole_0(k3_subset_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_187, c_48])).
% 3.23/1.59  tff(c_1352, plain, (~m1_subset_1('#skF_4', k3_subset_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_203])).
% 3.23/1.59  tff(c_1562, plain, (~m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1561, c_1352])).
% 3.23/1.59  tff(c_1566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1562])).
% 3.23/1.59  tff(c_1567, plain, (v1_xboole_0(k3_subset_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_203])).
% 3.23/1.59  tff(c_1568, plain, (m1_subset_1('#skF_4', k3_subset_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_203])).
% 3.23/1.59  tff(c_42, plain, (![B_22, A_21]: (v1_xboole_0(B_22) | ~m1_subset_1(B_22, A_21) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.23/1.59  tff(c_1582, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k3_subset_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1568, c_42])).
% 3.23/1.59  tff(c_1585, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1567, c_1582])).
% 3.23/1.59  tff(c_1587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1309, c_1585])).
% 3.23/1.59  tff(c_1588, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_204])).
% 3.23/1.59  tff(c_1589, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_204])).
% 3.23/1.59  tff(c_1607, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1589, c_42])).
% 3.23/1.59  tff(c_1610, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_1607])).
% 3.23/1.59  tff(c_1593, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1588, c_10])).
% 3.23/1.59  tff(c_1618, plain, (![A_171]: (A_171='#skF_3' | ~v1_xboole_0(A_171))), inference(demodulation, [status(thm), theory('equality')], [c_1593, c_10])).
% 3.23/1.59  tff(c_1625, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1610, c_1618])).
% 3.23/1.59  tff(c_1595, plain, (![A_16]: (k4_xboole_0(A_16, '#skF_3')=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_1593, c_221])).
% 3.23/1.59  tff(c_1664, plain, (![A_16]: (k4_xboole_0(A_16, '#skF_4')=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_1625, c_1595])).
% 3.23/1.59  tff(c_1634, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1625, c_54])).
% 3.23/1.59  tff(c_1810, plain, (![A_183, B_184]: (k4_xboole_0(A_183, B_184)=k3_subset_1(A_183, B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(A_183)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.59  tff(c_1813, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_1634, c_1810])).
% 3.23/1.59  tff(c_1819, plain, (k3_subset_1('#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_1813])).
% 3.23/1.59  tff(c_1633, plain, (~r2_hidden('#skF_4', k3_subset_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1625, c_48])).
% 3.23/1.59  tff(c_1826, plain, (~r2_hidden('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1819, c_1633])).
% 3.23/1.59  tff(c_1829, plain, (~m1_subset_1('#skF_4', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_1826])).
% 3.23/1.59  tff(c_1832, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1829])).
% 3.23/1.59  tff(c_1834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_1832])).
% 3.23/1.59  tff(c_1836, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_99])).
% 3.23/1.59  tff(c_1844, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1836, c_10])).
% 3.23/1.59  tff(c_1848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1844])).
% 3.23/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.59  
% 3.23/1.59  Inference rules
% 3.23/1.59  ----------------------
% 3.23/1.59  #Ref     : 0
% 3.23/1.59  #Sup     : 401
% 3.23/1.59  #Fact    : 0
% 3.23/1.59  #Define  : 0
% 3.23/1.59  #Split   : 10
% 3.23/1.59  #Chain   : 0
% 3.23/1.59  #Close   : 0
% 3.23/1.59  
% 3.23/1.59  Ordering : KBO
% 3.23/1.59  
% 3.23/1.59  Simplification rules
% 3.23/1.59  ----------------------
% 3.23/1.59  #Subsume      : 35
% 3.23/1.59  #Demod        : 177
% 3.23/1.59  #Tautology    : 226
% 3.23/1.59  #SimpNegUnit  : 14
% 3.23/1.59  #BackRed      : 32
% 3.23/1.59  
% 3.23/1.59  #Partial instantiations: 0
% 3.23/1.59  #Strategies tried      : 1
% 3.23/1.59  
% 3.23/1.59  Timing (in seconds)
% 3.23/1.59  ----------------------
% 3.23/1.59  Preprocessing        : 0.30
% 3.23/1.59  Parsing              : 0.16
% 3.23/1.59  CNF conversion       : 0.02
% 3.23/1.59  Main loop            : 0.49
% 3.23/1.59  Inferencing          : 0.18
% 3.23/1.59  Reduction            : 0.15
% 3.23/1.59  Demodulation         : 0.10
% 3.23/1.59  BG Simplification    : 0.02
% 3.23/1.59  Subsumption          : 0.09
% 3.23/1.59  Abstraction          : 0.02
% 3.23/1.59  MUC search           : 0.00
% 3.23/1.59  Cooper               : 0.00
% 3.23/1.59  Total                : 0.84
% 3.23/1.59  Index Insertion      : 0.00
% 3.23/1.59  Index Deletion       : 0.00
% 3.23/1.59  Index Matching       : 0.00
% 3.23/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
