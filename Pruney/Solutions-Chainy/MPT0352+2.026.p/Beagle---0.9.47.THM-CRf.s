%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:50 EST 2020

% Result     : Theorem 14.53s
% Output     : CNFRefutation 14.53s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 340 expanded)
%              Number of leaves         :   38 ( 126 expanded)
%              Depth                    :   17
%              Number of atoms          :  209 ( 602 expanded)
%              Number of equality atoms :   31 (  93 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_130,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_120,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_72,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_125,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_197,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_78])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_779,plain,(
    ! [A_128,B_129] :
      ( k4_xboole_0(A_128,B_129) = k3_subset_1(A_128,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_796,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_779])).

tff(c_28,plain,(
    ! [A_27,B_28] : r1_xboole_0(k4_xboole_0(A_27,B_28),B_28) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_136,plain,(
    ! [B_68,A_69] :
      ( r1_xboole_0(B_68,A_69)
      | ~ r1_xboole_0(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k4_xboole_0(A_27,B_28)) ),
    inference(resolution,[status(thm)],[c_28,c_136])).

tff(c_833,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_139])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    ! [A_34,B_35,C_36] :
      ( r1_tarski(A_34,k4_xboole_0(B_35,C_36))
      | ~ r1_xboole_0(A_34,C_36)
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_431,plain,(
    ! [B_101,A_102] :
      ( B_101 = A_102
      | ~ r1_tarski(B_101,A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3685,plain,(
    ! [A_252,B_253] :
      ( k4_xboole_0(A_252,B_253) = A_252
      | ~ r1_tarski(A_252,k4_xboole_0(A_252,B_253)) ) ),
    inference(resolution,[status(thm)],[c_22,c_431])).

tff(c_3689,plain,(
    ! [B_35,C_36] :
      ( k4_xboole_0(B_35,C_36) = B_35
      | ~ r1_xboole_0(B_35,C_36)
      | ~ r1_tarski(B_35,B_35) ) ),
    inference(resolution,[status(thm)],[c_34,c_3685])).

tff(c_3714,plain,(
    ! [B_254,C_255] :
      ( k4_xboole_0(B_254,C_255) = B_254
      | ~ r1_xboole_0(B_254,C_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3689])).

tff(c_3769,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_833,c_3714])).

tff(c_32,plain,(
    ! [A_31,C_33,B_32] :
      ( r1_xboole_0(A_31,k4_xboole_0(C_33,B_32))
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_31490,plain,(
    ! [A_673] :
      ( r1_xboole_0(A_673,'#skF_4')
      | ~ r1_tarski(A_673,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3769,c_32])).

tff(c_31639,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_197,c_31490])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31655,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_31639,c_4])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_795,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_779])).

tff(c_865,plain,(
    ! [A_130,B_131,C_132] :
      ( r1_tarski(A_130,k2_xboole_0(B_131,C_132))
      | ~ r1_tarski(k4_xboole_0(A_130,B_131),C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1049,plain,(
    ! [A_142,B_143] : r1_tarski(A_142,k2_xboole_0(B_143,k4_xboole_0(A_142,B_143))) ),
    inference(resolution,[status(thm)],[c_10,c_865])).

tff(c_1074,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_1049])).

tff(c_66,plain,(
    ! [A_52] : ~ v1_xboole_0(k1_zfmisc_1(A_52)) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    ! [C_41,A_37] :
      ( r2_hidden(C_41,k1_zfmisc_1(A_37))
      | ~ r1_tarski(C_41,A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_560,plain,(
    ! [B_114,A_115] :
      ( m1_subset_1(B_114,A_115)
      | ~ r2_hidden(B_114,A_115)
      | v1_xboole_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_572,plain,(
    ! [C_41,A_37] :
      ( m1_subset_1(C_41,k1_zfmisc_1(A_37))
      | v1_xboole_0(k1_zfmisc_1(A_37))
      | ~ r1_tarski(C_41,A_37) ) ),
    inference(resolution,[status(thm)],[c_38,c_560])).

tff(c_578,plain,(
    ! [C_41,A_37] :
      ( m1_subset_1(C_41,k1_zfmisc_1(A_37))
      | ~ r1_tarski(C_41,A_37) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_572])).

tff(c_22248,plain,(
    ! [A_566,C_567] :
      ( k4_xboole_0(A_566,C_567) = k3_subset_1(A_566,C_567)
      | ~ r1_tarski(C_567,A_566) ) ),
    inference(resolution,[status(thm)],[c_578,c_779])).

tff(c_22736,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k3_subset_1(B_6,B_6) ),
    inference(resolution,[status(thm)],[c_10,c_22248])).

tff(c_1249,plain,(
    ! [A_156,B_157,C_158] :
      ( r1_tarski(A_156,B_157)
      | ~ r1_xboole_0(A_156,C_158)
      | ~ r1_tarski(A_156,k2_xboole_0(B_157,C_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_11915,plain,(
    ! [B_419,C_420,B_421] :
      ( r1_tarski(k4_xboole_0(k2_xboole_0(B_419,C_420),B_421),B_419)
      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(B_419,C_420),B_421),C_420) ) ),
    inference(resolution,[status(thm)],[c_22,c_1249])).

tff(c_11956,plain,(
    ! [B_422,B_423] : r1_tarski(k4_xboole_0(k2_xboole_0(B_422,B_423),B_423),B_422) ),
    inference(resolution,[status(thm)],[c_28,c_11915])).

tff(c_24,plain,(
    ! [A_21,B_22,C_23] :
      ( r1_tarski(A_21,k2_xboole_0(B_22,C_23))
      | ~ r1_tarski(k4_xboole_0(A_21,B_22),C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12035,plain,(
    ! [B_422,B_423] : r1_tarski(k2_xboole_0(B_422,B_423),k2_xboole_0(B_423,B_422)) ),
    inference(resolution,[status(thm)],[c_11956,c_24])).

tff(c_12043,plain,(
    ! [B_424,B_425] : r1_tarski(k2_xboole_0(B_424,B_425),k2_xboole_0(B_425,B_424)) ),
    inference(resolution,[status(thm)],[c_11956,c_24])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12055,plain,(
    ! [B_425,B_424] :
      ( k2_xboole_0(B_425,B_424) = k2_xboole_0(B_424,B_425)
      | ~ r1_tarski(k2_xboole_0(B_425,B_424),k2_xboole_0(B_424,B_425)) ) ),
    inference(resolution,[status(thm)],[c_12043,c_6])).

tff(c_12089,plain,(
    ! [B_427,B_426] : k2_xboole_0(B_427,B_426) = k2_xboole_0(B_426,B_427) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12035,c_12055])).

tff(c_155,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = A_76
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_179,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_155])).

tff(c_333,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k3_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_354,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_333])).

tff(c_30,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_178,plain,(
    ! [A_29,B_30] : k3_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = A_29 ),
    inference(resolution,[status(thm)],[c_30,c_155])).

tff(c_351,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = k5_xboole_0(A_29,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_333])).

tff(c_9861,plain,(
    ! [A_383,B_384] : k4_xboole_0(A_383,k2_xboole_0(A_383,B_384)) = k4_xboole_0(A_383,A_383) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_351])).

tff(c_9995,plain,(
    ! [A_383,B_384] : r1_xboole_0(k4_xboole_0(A_383,A_383),k2_xboole_0(A_383,B_384)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9861,c_28])).

tff(c_12170,plain,(
    ! [B_426,B_427] : r1_xboole_0(k4_xboole_0(B_426,B_426),k2_xboole_0(B_427,B_426)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12089,c_9995])).

tff(c_907,plain,(
    ! [A_133,B_134] : r1_tarski(A_133,k2_xboole_0(B_134,A_133)) ),
    inference(resolution,[status(thm)],[c_22,c_865])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(k2_xboole_0(A_9,B_10),C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_932,plain,(
    ! [A_9,B_134,B_10] : r1_tarski(A_9,k2_xboole_0(B_134,k2_xboole_0(A_9,B_10))) ),
    inference(resolution,[status(thm)],[c_907,c_14])).

tff(c_16867,plain,(
    ! [A_511,B_512,B_513] :
      ( r1_tarski(A_511,B_512)
      | ~ r1_xboole_0(A_511,k2_xboole_0(A_511,B_513)) ) ),
    inference(resolution,[status(thm)],[c_932,c_1249])).

tff(c_16895,plain,(
    ! [B_426,B_512] : r1_tarski(k4_xboole_0(B_426,B_426),B_512) ),
    inference(resolution,[status(thm)],[c_12170,c_16867])).

tff(c_22738,plain,(
    ! [B_426,B_512] : r1_tarski(k3_subset_1(B_426,B_426),B_512) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22736,c_16895])).

tff(c_3932,plain,(
    ! [B_256,A_257] : k4_xboole_0(B_256,k4_xboole_0(A_257,B_256)) = B_256 ),
    inference(resolution,[status(thm)],[c_139,c_3714])).

tff(c_550,plain,(
    ! [A_111,C_112,B_113] :
      ( r1_xboole_0(A_111,k4_xboole_0(C_112,B_113))
      | ~ r1_tarski(A_111,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_559,plain,(
    ! [C_112,B_113,A_111] :
      ( r1_xboole_0(k4_xboole_0(C_112,B_113),A_111)
      | ~ r1_tarski(A_111,B_113) ) ),
    inference(resolution,[status(thm)],[c_550,c_4])).

tff(c_34486,plain,(
    ! [B_709,A_710,A_711] :
      ( r1_xboole_0(B_709,A_710)
      | ~ r1_tarski(A_710,k4_xboole_0(A_711,B_709)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3932,c_559])).

tff(c_34688,plain,(
    ! [B_709,B_426] : r1_xboole_0(B_709,k3_subset_1(B_426,B_426)) ),
    inference(resolution,[status(thm)],[c_22738,c_34486])).

tff(c_34724,plain,(
    ! [B_712,B_713] : r1_xboole_0(B_712,k3_subset_1(B_713,B_713)) ),
    inference(resolution,[status(thm)],[c_22738,c_34486])).

tff(c_3708,plain,(
    ! [B_35,C_36] :
      ( k4_xboole_0(B_35,C_36) = B_35
      | ~ r1_xboole_0(B_35,C_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3689])).

tff(c_34982,plain,(
    ! [B_718,B_719] : k4_xboole_0(B_718,k3_subset_1(B_719,B_719)) = B_718 ),
    inference(resolution,[status(thm)],[c_34724,c_3708])).

tff(c_247,plain,(
    ! [B_92,A_93] :
      ( r2_hidden(B_92,A_93)
      | ~ m1_subset_1(B_92,A_93)
      | v1_xboole_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    ! [C_41,A_37] :
      ( r1_tarski(C_41,A_37)
      | ~ r2_hidden(C_41,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_251,plain,(
    ! [B_92,A_37] :
      ( r1_tarski(B_92,A_37)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_37))
      | v1_xboole_0(k1_zfmisc_1(A_37)) ) ),
    inference(resolution,[status(thm)],[c_247,c_36])).

tff(c_255,plain,(
    ! [B_94,A_95] :
      ( r1_tarski(B_94,A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_95)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_251])).

tff(c_268,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_255])).

tff(c_1092,plain,(
    ! [A_144,B_145,C_146] :
      ( r1_tarski(A_144,k4_xboole_0(B_145,C_146))
      | ~ r1_xboole_0(A_144,C_146)
      | ~ r1_tarski(A_144,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_tarski(A_14,C_16)
      | ~ r1_tarski(B_15,C_16)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_13153,plain,(
    ! [A_434,B_435,C_436,A_437] :
      ( r1_tarski(A_434,k4_xboole_0(B_435,C_436))
      | ~ r1_tarski(A_434,A_437)
      | ~ r1_xboole_0(A_437,C_436)
      | ~ r1_tarski(A_437,B_435) ) ),
    inference(resolution,[status(thm)],[c_1092,c_18])).

tff(c_13448,plain,(
    ! [B_435,C_436] :
      ( r1_tarski('#skF_4',k4_xboole_0(B_435,C_436))
      | ~ r1_xboole_0('#skF_3',C_436)
      | ~ r1_tarski('#skF_3',B_435) ) ),
    inference(resolution,[status(thm)],[c_268,c_13153])).

tff(c_35094,plain,(
    ! [B_718,B_719] :
      ( r1_tarski('#skF_4',B_718)
      | ~ r1_xboole_0('#skF_3',k3_subset_1(B_719,B_719))
      | ~ r1_tarski('#skF_3',B_718) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34982,c_13448])).

tff(c_35362,plain,(
    ! [B_720] :
      ( r1_tarski('#skF_4',B_720)
      | ~ r1_tarski('#skF_3',B_720) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34688,c_35094])).

tff(c_35500,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_1074,c_35362])).

tff(c_26,plain,(
    ! [A_24,B_25,C_26] :
      ( r1_tarski(A_24,B_25)
      | ~ r1_xboole_0(A_24,C_26)
      | ~ r1_tarski(A_24,k2_xboole_0(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36694,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_35500,c_26])).

tff(c_36707,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31655,c_36694])).

tff(c_36709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_36707])).

tff(c_36711,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_37360,plain,(
    ! [A_803,B_804] :
      ( k4_xboole_0(A_803,B_804) = k3_subset_1(A_803,B_804)
      | ~ m1_subset_1(B_804,k1_zfmisc_1(A_803)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_37376,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_37360])).

tff(c_36845,plain,(
    ! [A_767,C_768,B_769] :
      ( r1_xboole_0(A_767,k4_xboole_0(C_768,B_769))
      | ~ r1_tarski(A_767,B_769) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38107,plain,(
    ! [C_842,B_843,A_844] :
      ( r1_xboole_0(k4_xboole_0(C_842,B_843),A_844)
      | ~ r1_tarski(A_844,B_843) ) ),
    inference(resolution,[status(thm)],[c_36845,c_4])).

tff(c_38121,plain,(
    ! [A_844] :
      ( r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),A_844)
      | ~ r1_tarski(A_844,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37376,c_38107])).

tff(c_37387,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_37376,c_22])).

tff(c_37377,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_37360])).

tff(c_37782,plain,(
    ! [A_825,B_826,C_827] :
      ( r1_tarski(A_825,k4_xboole_0(B_826,C_827))
      | ~ r1_xboole_0(A_825,C_827)
      | ~ r1_tarski(A_825,B_826) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40892,plain,(
    ! [A_937] :
      ( r1_tarski(A_937,k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_xboole_0(A_937,'#skF_4')
      | ~ r1_tarski(A_937,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37377,c_37782])).

tff(c_36710,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_40926,plain,
    ( ~ r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4')
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_40892,c_36710])).

tff(c_40945,plain,(
    ~ r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37387,c_40926])).

tff(c_40949,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_38121,c_40945])).

tff(c_40953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36711,c_40949])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.53/7.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.53/7.12  
% 14.53/7.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.53/7.13  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 14.53/7.13  
% 14.53/7.13  %Foreground sorts:
% 14.53/7.13  
% 14.53/7.13  
% 14.53/7.13  %Background operators:
% 14.53/7.13  
% 14.53/7.13  
% 14.53/7.13  %Foreground operators:
% 14.53/7.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.53/7.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.53/7.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.53/7.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.53/7.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.53/7.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.53/7.13  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.53/7.13  tff('#skF_5', type, '#skF_5': $i).
% 14.53/7.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.53/7.13  tff('#skF_3', type, '#skF_3': $i).
% 14.53/7.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.53/7.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.53/7.13  tff('#skF_4', type, '#skF_4': $i).
% 14.53/7.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.53/7.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.53/7.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.53/7.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.53/7.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.53/7.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.53/7.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.53/7.13  
% 14.53/7.15  tff(f_130, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 14.53/7.15  tff(f_117, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 14.53/7.15  tff(f_69, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 14.53/7.15  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 14.53/7.15  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.53/7.15  tff(f_81, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 14.53/7.15  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.53/7.15  tff(f_75, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 14.53/7.15  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 14.53/7.15  tff(f_120, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 14.53/7.15  tff(f_88, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 14.53/7.15  tff(f_113, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 14.53/7.15  tff(f_67, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 14.53/7.15  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.53/7.15  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.53/7.15  tff(f_71, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 14.53/7.15  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 14.53/7.15  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 14.53/7.15  tff(c_72, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.53/7.15  tff(c_125, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 14.53/7.15  tff(c_78, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.53/7.15  tff(c_197, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_125, c_78])).
% 14.53/7.15  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.53/7.15  tff(c_779, plain, (![A_128, B_129]: (k4_xboole_0(A_128, B_129)=k3_subset_1(A_128, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 14.53/7.15  tff(c_796, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_779])).
% 14.53/7.15  tff(c_28, plain, (![A_27, B_28]: (r1_xboole_0(k4_xboole_0(A_27, B_28), B_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.53/7.15  tff(c_136, plain, (![B_68, A_69]: (r1_xboole_0(B_68, A_69) | ~r1_xboole_0(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.53/7.15  tff(c_139, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k4_xboole_0(A_27, B_28)))), inference(resolution, [status(thm)], [c_28, c_136])).
% 14.53/7.15  tff(c_833, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_796, c_139])).
% 14.53/7.15  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.53/7.15  tff(c_34, plain, (![A_34, B_35, C_36]: (r1_tarski(A_34, k4_xboole_0(B_35, C_36)) | ~r1_xboole_0(A_34, C_36) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.53/7.15  tff(c_22, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.53/7.15  tff(c_431, plain, (![B_101, A_102]: (B_101=A_102 | ~r1_tarski(B_101, A_102) | ~r1_tarski(A_102, B_101))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.53/7.15  tff(c_3685, plain, (![A_252, B_253]: (k4_xboole_0(A_252, B_253)=A_252 | ~r1_tarski(A_252, k4_xboole_0(A_252, B_253)))), inference(resolution, [status(thm)], [c_22, c_431])).
% 14.53/7.15  tff(c_3689, plain, (![B_35, C_36]: (k4_xboole_0(B_35, C_36)=B_35 | ~r1_xboole_0(B_35, C_36) | ~r1_tarski(B_35, B_35))), inference(resolution, [status(thm)], [c_34, c_3685])).
% 14.53/7.15  tff(c_3714, plain, (![B_254, C_255]: (k4_xboole_0(B_254, C_255)=B_254 | ~r1_xboole_0(B_254, C_255))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3689])).
% 14.53/7.15  tff(c_3769, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_833, c_3714])).
% 14.53/7.15  tff(c_32, plain, (![A_31, C_33, B_32]: (r1_xboole_0(A_31, k4_xboole_0(C_33, B_32)) | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.53/7.15  tff(c_31490, plain, (![A_673]: (r1_xboole_0(A_673, '#skF_4') | ~r1_tarski(A_673, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3769, c_32])).
% 14.53/7.15  tff(c_31639, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_197, c_31490])).
% 14.53/7.15  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.53/7.15  tff(c_31655, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_31639, c_4])).
% 14.53/7.15  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.53/7.15  tff(c_795, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_779])).
% 14.53/7.15  tff(c_865, plain, (![A_130, B_131, C_132]: (r1_tarski(A_130, k2_xboole_0(B_131, C_132)) | ~r1_tarski(k4_xboole_0(A_130, B_131), C_132))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.53/7.15  tff(c_1049, plain, (![A_142, B_143]: (r1_tarski(A_142, k2_xboole_0(B_143, k4_xboole_0(A_142, B_143))))), inference(resolution, [status(thm)], [c_10, c_865])).
% 14.53/7.15  tff(c_1074, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_795, c_1049])).
% 14.53/7.15  tff(c_66, plain, (![A_52]: (~v1_xboole_0(k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_120])).
% 14.53/7.15  tff(c_38, plain, (![C_41, A_37]: (r2_hidden(C_41, k1_zfmisc_1(A_37)) | ~r1_tarski(C_41, A_37))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.53/7.15  tff(c_560, plain, (![B_114, A_115]: (m1_subset_1(B_114, A_115) | ~r2_hidden(B_114, A_115) | v1_xboole_0(A_115))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.53/7.15  tff(c_572, plain, (![C_41, A_37]: (m1_subset_1(C_41, k1_zfmisc_1(A_37)) | v1_xboole_0(k1_zfmisc_1(A_37)) | ~r1_tarski(C_41, A_37))), inference(resolution, [status(thm)], [c_38, c_560])).
% 14.53/7.15  tff(c_578, plain, (![C_41, A_37]: (m1_subset_1(C_41, k1_zfmisc_1(A_37)) | ~r1_tarski(C_41, A_37))), inference(negUnitSimplification, [status(thm)], [c_66, c_572])).
% 14.53/7.15  tff(c_22248, plain, (![A_566, C_567]: (k4_xboole_0(A_566, C_567)=k3_subset_1(A_566, C_567) | ~r1_tarski(C_567, A_566))), inference(resolution, [status(thm)], [c_578, c_779])).
% 14.53/7.15  tff(c_22736, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k3_subset_1(B_6, B_6))), inference(resolution, [status(thm)], [c_10, c_22248])).
% 14.53/7.15  tff(c_1249, plain, (![A_156, B_157, C_158]: (r1_tarski(A_156, B_157) | ~r1_xboole_0(A_156, C_158) | ~r1_tarski(A_156, k2_xboole_0(B_157, C_158)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.53/7.15  tff(c_11915, plain, (![B_419, C_420, B_421]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_419, C_420), B_421), B_419) | ~r1_xboole_0(k4_xboole_0(k2_xboole_0(B_419, C_420), B_421), C_420))), inference(resolution, [status(thm)], [c_22, c_1249])).
% 14.53/7.15  tff(c_11956, plain, (![B_422, B_423]: (r1_tarski(k4_xboole_0(k2_xboole_0(B_422, B_423), B_423), B_422))), inference(resolution, [status(thm)], [c_28, c_11915])).
% 14.53/7.15  tff(c_24, plain, (![A_21, B_22, C_23]: (r1_tarski(A_21, k2_xboole_0(B_22, C_23)) | ~r1_tarski(k4_xboole_0(A_21, B_22), C_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.53/7.15  tff(c_12035, plain, (![B_422, B_423]: (r1_tarski(k2_xboole_0(B_422, B_423), k2_xboole_0(B_423, B_422)))), inference(resolution, [status(thm)], [c_11956, c_24])).
% 14.53/7.15  tff(c_12043, plain, (![B_424, B_425]: (r1_tarski(k2_xboole_0(B_424, B_425), k2_xboole_0(B_425, B_424)))), inference(resolution, [status(thm)], [c_11956, c_24])).
% 14.53/7.15  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.53/7.15  tff(c_12055, plain, (![B_425, B_424]: (k2_xboole_0(B_425, B_424)=k2_xboole_0(B_424, B_425) | ~r1_tarski(k2_xboole_0(B_425, B_424), k2_xboole_0(B_424, B_425)))), inference(resolution, [status(thm)], [c_12043, c_6])).
% 14.53/7.15  tff(c_12089, plain, (![B_427, B_426]: (k2_xboole_0(B_427, B_426)=k2_xboole_0(B_426, B_427))), inference(demodulation, [status(thm), theory('equality')], [c_12035, c_12055])).
% 14.53/7.15  tff(c_155, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=A_76 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.53/7.15  tff(c_179, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_155])).
% 14.53/7.15  tff(c_333, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k3_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.53/7.15  tff(c_354, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_179, c_333])).
% 14.53/7.15  tff(c_30, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.53/7.15  tff(c_178, plain, (![A_29, B_30]: (k3_xboole_0(A_29, k2_xboole_0(A_29, B_30))=A_29)), inference(resolution, [status(thm)], [c_30, c_155])).
% 14.53/7.15  tff(c_351, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k2_xboole_0(A_29, B_30))=k5_xboole_0(A_29, A_29))), inference(superposition, [status(thm), theory('equality')], [c_178, c_333])).
% 14.53/7.15  tff(c_9861, plain, (![A_383, B_384]: (k4_xboole_0(A_383, k2_xboole_0(A_383, B_384))=k4_xboole_0(A_383, A_383))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_351])).
% 14.53/7.15  tff(c_9995, plain, (![A_383, B_384]: (r1_xboole_0(k4_xboole_0(A_383, A_383), k2_xboole_0(A_383, B_384)))), inference(superposition, [status(thm), theory('equality')], [c_9861, c_28])).
% 14.53/7.15  tff(c_12170, plain, (![B_426, B_427]: (r1_xboole_0(k4_xboole_0(B_426, B_426), k2_xboole_0(B_427, B_426)))), inference(superposition, [status(thm), theory('equality')], [c_12089, c_9995])).
% 14.53/7.15  tff(c_907, plain, (![A_133, B_134]: (r1_tarski(A_133, k2_xboole_0(B_134, A_133)))), inference(resolution, [status(thm)], [c_22, c_865])).
% 14.53/7.15  tff(c_14, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(k2_xboole_0(A_9, B_10), C_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.53/7.15  tff(c_932, plain, (![A_9, B_134, B_10]: (r1_tarski(A_9, k2_xboole_0(B_134, k2_xboole_0(A_9, B_10))))), inference(resolution, [status(thm)], [c_907, c_14])).
% 14.53/7.15  tff(c_16867, plain, (![A_511, B_512, B_513]: (r1_tarski(A_511, B_512) | ~r1_xboole_0(A_511, k2_xboole_0(A_511, B_513)))), inference(resolution, [status(thm)], [c_932, c_1249])).
% 14.53/7.15  tff(c_16895, plain, (![B_426, B_512]: (r1_tarski(k4_xboole_0(B_426, B_426), B_512))), inference(resolution, [status(thm)], [c_12170, c_16867])).
% 14.53/7.15  tff(c_22738, plain, (![B_426, B_512]: (r1_tarski(k3_subset_1(B_426, B_426), B_512))), inference(demodulation, [status(thm), theory('equality')], [c_22736, c_16895])).
% 14.53/7.15  tff(c_3932, plain, (![B_256, A_257]: (k4_xboole_0(B_256, k4_xboole_0(A_257, B_256))=B_256)), inference(resolution, [status(thm)], [c_139, c_3714])).
% 14.53/7.15  tff(c_550, plain, (![A_111, C_112, B_113]: (r1_xboole_0(A_111, k4_xboole_0(C_112, B_113)) | ~r1_tarski(A_111, B_113))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.53/7.15  tff(c_559, plain, (![C_112, B_113, A_111]: (r1_xboole_0(k4_xboole_0(C_112, B_113), A_111) | ~r1_tarski(A_111, B_113))), inference(resolution, [status(thm)], [c_550, c_4])).
% 14.53/7.15  tff(c_34486, plain, (![B_709, A_710, A_711]: (r1_xboole_0(B_709, A_710) | ~r1_tarski(A_710, k4_xboole_0(A_711, B_709)))), inference(superposition, [status(thm), theory('equality')], [c_3932, c_559])).
% 14.53/7.15  tff(c_34688, plain, (![B_709, B_426]: (r1_xboole_0(B_709, k3_subset_1(B_426, B_426)))), inference(resolution, [status(thm)], [c_22738, c_34486])).
% 14.53/7.15  tff(c_34724, plain, (![B_712, B_713]: (r1_xboole_0(B_712, k3_subset_1(B_713, B_713)))), inference(resolution, [status(thm)], [c_22738, c_34486])).
% 14.53/7.15  tff(c_3708, plain, (![B_35, C_36]: (k4_xboole_0(B_35, C_36)=B_35 | ~r1_xboole_0(B_35, C_36))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3689])).
% 14.53/7.15  tff(c_34982, plain, (![B_718, B_719]: (k4_xboole_0(B_718, k3_subset_1(B_719, B_719))=B_718)), inference(resolution, [status(thm)], [c_34724, c_3708])).
% 14.53/7.15  tff(c_247, plain, (![B_92, A_93]: (r2_hidden(B_92, A_93) | ~m1_subset_1(B_92, A_93) | v1_xboole_0(A_93))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.53/7.15  tff(c_36, plain, (![C_41, A_37]: (r1_tarski(C_41, A_37) | ~r2_hidden(C_41, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.53/7.15  tff(c_251, plain, (![B_92, A_37]: (r1_tarski(B_92, A_37) | ~m1_subset_1(B_92, k1_zfmisc_1(A_37)) | v1_xboole_0(k1_zfmisc_1(A_37)))), inference(resolution, [status(thm)], [c_247, c_36])).
% 14.53/7.15  tff(c_255, plain, (![B_94, A_95]: (r1_tarski(B_94, A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(A_95)))), inference(negUnitSimplification, [status(thm)], [c_66, c_251])).
% 14.53/7.15  tff(c_268, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_255])).
% 14.53/7.15  tff(c_1092, plain, (![A_144, B_145, C_146]: (r1_tarski(A_144, k4_xboole_0(B_145, C_146)) | ~r1_xboole_0(A_144, C_146) | ~r1_tarski(A_144, B_145))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.53/7.15  tff(c_18, plain, (![A_14, C_16, B_15]: (r1_tarski(A_14, C_16) | ~r1_tarski(B_15, C_16) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.53/7.15  tff(c_13153, plain, (![A_434, B_435, C_436, A_437]: (r1_tarski(A_434, k4_xboole_0(B_435, C_436)) | ~r1_tarski(A_434, A_437) | ~r1_xboole_0(A_437, C_436) | ~r1_tarski(A_437, B_435))), inference(resolution, [status(thm)], [c_1092, c_18])).
% 14.53/7.15  tff(c_13448, plain, (![B_435, C_436]: (r1_tarski('#skF_4', k4_xboole_0(B_435, C_436)) | ~r1_xboole_0('#skF_3', C_436) | ~r1_tarski('#skF_3', B_435))), inference(resolution, [status(thm)], [c_268, c_13153])).
% 14.53/7.15  tff(c_35094, plain, (![B_718, B_719]: (r1_tarski('#skF_4', B_718) | ~r1_xboole_0('#skF_3', k3_subset_1(B_719, B_719)) | ~r1_tarski('#skF_3', B_718))), inference(superposition, [status(thm), theory('equality')], [c_34982, c_13448])).
% 14.53/7.15  tff(c_35362, plain, (![B_720]: (r1_tarski('#skF_4', B_720) | ~r1_tarski('#skF_3', B_720))), inference(demodulation, [status(thm), theory('equality')], [c_34688, c_35094])).
% 14.53/7.15  tff(c_35500, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_1074, c_35362])).
% 14.53/7.15  tff(c_26, plain, (![A_24, B_25, C_26]: (r1_tarski(A_24, B_25) | ~r1_xboole_0(A_24, C_26) | ~r1_tarski(A_24, k2_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.53/7.15  tff(c_36694, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_35500, c_26])).
% 14.53/7.15  tff(c_36707, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31655, c_36694])).
% 14.53/7.15  tff(c_36709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_36707])).
% 14.53/7.15  tff(c_36711, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 14.53/7.15  tff(c_37360, plain, (![A_803, B_804]: (k4_xboole_0(A_803, B_804)=k3_subset_1(A_803, B_804) | ~m1_subset_1(B_804, k1_zfmisc_1(A_803)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 14.53/7.15  tff(c_37376, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_37360])).
% 14.53/7.15  tff(c_36845, plain, (![A_767, C_768, B_769]: (r1_xboole_0(A_767, k4_xboole_0(C_768, B_769)) | ~r1_tarski(A_767, B_769))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.53/7.15  tff(c_38107, plain, (![C_842, B_843, A_844]: (r1_xboole_0(k4_xboole_0(C_842, B_843), A_844) | ~r1_tarski(A_844, B_843))), inference(resolution, [status(thm)], [c_36845, c_4])).
% 14.53/7.15  tff(c_38121, plain, (![A_844]: (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), A_844) | ~r1_tarski(A_844, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_37376, c_38107])).
% 14.53/7.15  tff(c_37387, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37376, c_22])).
% 14.53/7.15  tff(c_37377, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_37360])).
% 14.53/7.15  tff(c_37782, plain, (![A_825, B_826, C_827]: (r1_tarski(A_825, k4_xboole_0(B_826, C_827)) | ~r1_xboole_0(A_825, C_827) | ~r1_tarski(A_825, B_826))), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.53/7.15  tff(c_40892, plain, (![A_937]: (r1_tarski(A_937, k3_subset_1('#skF_3', '#skF_4')) | ~r1_xboole_0(A_937, '#skF_4') | ~r1_tarski(A_937, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_37377, c_37782])).
% 14.53/7.15  tff(c_36710, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_72])).
% 14.53/7.15  tff(c_40926, plain, (~r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_40892, c_36710])).
% 14.53/7.15  tff(c_40945, plain, (~r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37387, c_40926])).
% 14.53/7.15  tff(c_40949, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_38121, c_40945])).
% 14.53/7.15  tff(c_40953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36711, c_40949])).
% 14.53/7.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.53/7.15  
% 14.53/7.15  Inference rules
% 14.53/7.15  ----------------------
% 14.53/7.15  #Ref     : 0
% 14.53/7.15  #Sup     : 9913
% 14.53/7.15  #Fact    : 0
% 14.53/7.15  #Define  : 0
% 14.53/7.15  #Split   : 16
% 14.53/7.15  #Chain   : 0
% 14.53/7.15  #Close   : 0
% 14.53/7.15  
% 14.53/7.15  Ordering : KBO
% 14.53/7.15  
% 14.53/7.15  Simplification rules
% 14.53/7.15  ----------------------
% 14.53/7.15  #Subsume      : 684
% 14.53/7.15  #Demod        : 6187
% 14.53/7.15  #Tautology    : 4990
% 14.53/7.15  #SimpNegUnit  : 31
% 14.53/7.15  #BackRed      : 35
% 14.53/7.15  
% 14.53/7.15  #Partial instantiations: 0
% 14.53/7.15  #Strategies tried      : 1
% 14.53/7.15  
% 14.53/7.15  Timing (in seconds)
% 14.53/7.15  ----------------------
% 14.53/7.15  Preprocessing        : 0.33
% 14.53/7.15  Parsing              : 0.18
% 14.53/7.15  CNF conversion       : 0.02
% 14.53/7.15  Main loop            : 6.01
% 14.53/7.15  Inferencing          : 0.99
% 14.53/7.15  Reduction            : 3.11
% 14.53/7.15  Demodulation         : 2.64
% 14.53/7.15  BG Simplification    : 0.10
% 14.53/7.15  Subsumption          : 1.42
% 14.53/7.15  Abstraction          : 0.13
% 14.53/7.15  MUC search           : 0.00
% 14.53/7.15  Cooper               : 0.00
% 14.53/7.15  Total                : 6.39
% 14.53/7.15  Index Insertion      : 0.00
% 14.53/7.15  Index Deletion       : 0.00
% 14.53/7.15  Index Matching       : 0.00
% 14.53/7.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
