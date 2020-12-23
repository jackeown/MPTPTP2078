%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:21 EST 2020

% Result     : Theorem 10.95s
% Output     : CNFRefutation 11.11s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 653 expanded)
%              Number of leaves         :   31 ( 225 expanded)
%              Depth                    :   17
%              Number of atoms          :  174 (1329 expanded)
%              Number of equality atoms :   29 ( 241 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_68,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_74,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_91,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_124,plain,(
    ! [B_47,A_48] :
      ( r2_hidden(B_47,A_48)
      | ~ m1_subset_1(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_128,plain,(
    ! [B_47,A_8] :
      ( r1_tarski(B_47,A_8)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_124,c_8])).

tff(c_136,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_128])).

tff(c_148,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_136])).

tff(c_187,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(A_57,C_58)
      | ~ r1_tarski(B_59,C_58)
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_268,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,'#skF_4')
      | ~ r1_tarski(A_66,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_148,c_187])).

tff(c_298,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_268])).

tff(c_28,plain,(
    ! [A_15] : k1_subset_1(A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_16] : k2_subset_1(A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [A_22] : k3_subset_1(A_22,k1_subset_1(A_22)) = k2_subset_1(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    ! [A_22] : k3_subset_1(A_22,k1_subset_1(A_22)) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_38])).

tff(c_58,plain,(
    ! [A_22] : k3_subset_1(A_22,k1_xboole_0) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_56])).

tff(c_46,plain,(
    ! [A_29] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_484,plain,(
    ! [A_76,B_77] :
      ( k3_subset_1(A_76,k3_subset_1(A_76,B_77)) = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_500,plain,(
    ! [A_29] : k3_subset_1(A_29,k3_subset_1(A_29,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_484])).

tff(c_510,plain,(
    ! [A_29] : k3_subset_1(A_29,A_29) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_500])).

tff(c_332,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k3_subset_1(A_68,B_69),k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_341,plain,(
    ! [A_22] :
      ( m1_subset_1(A_22,k1_zfmisc_1(A_22))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_332])).

tff(c_348,plain,(
    ! [A_70] : m1_subset_1(A_70,k1_zfmisc_1(A_70)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_341])).

tff(c_134,plain,(
    ! [B_47,A_8] :
      ( r1_tarski(B_47,A_8)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_8)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_128])).

tff(c_355,plain,(
    ! [A_70] : r1_tarski(A_70,A_70) ),
    inference(resolution,[status(thm)],[c_348,c_134])).

tff(c_10,plain,(
    ! [C_12,A_8] :
      ( r2_hidden(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_150,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(B_51,A_52)
      | ~ r2_hidden(B_51,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_156,plain,(
    ! [C_12,A_8] :
      ( m1_subset_1(C_12,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_150])).

tff(c_163,plain,(
    ! [C_12,A_8] :
      ( m1_subset_1(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_156])).

tff(c_50,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1520,plain,(
    ! [C_111,A_112,B_113] :
      ( r1_tarski(C_111,k3_subset_1(A_112,B_113))
      | ~ r1_tarski(B_113,k3_subset_1(A_112,C_111))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(A_112))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1554,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_1520])).

tff(c_1576,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1554])).

tff(c_1587,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1576])).

tff(c_1606,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_163,c_1587])).

tff(c_1613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_1606])).

tff(c_1615,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1576])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k3_subset_1(A_17,B_18),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_264,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,k3_subset_1('#skF_4','#skF_6'))
      | ~ r1_tarski(A_65,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_187])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_791,plain,(
    ! [A_87,A_88] :
      ( r1_tarski(A_87,k3_subset_1('#skF_4','#skF_6'))
      | ~ r1_tarski(A_87,A_88)
      | ~ r1_tarski(A_88,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_264,c_6])).

tff(c_838,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_148,c_791])).

tff(c_844,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_838])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( k3_subset_1(A_20,k3_subset_1(A_20,B_21)) = B_21
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1624,plain,(
    k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1615,c_36])).

tff(c_345,plain,(
    ! [A_22] : m1_subset_1(A_22,k1_zfmisc_1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_341])).

tff(c_1538,plain,(
    ! [A_29,B_113] :
      ( r1_tarski(A_29,k3_subset_1(A_29,B_113))
      | ~ r1_tarski(B_113,k1_xboole_0)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_1520])).

tff(c_3948,plain,(
    ! [A_169,B_170] :
      ( r1_tarski(A_169,k3_subset_1(A_169,B_170))
      | ~ r1_tarski(B_170,k1_xboole_0)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(A_169)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_1538])).

tff(c_3977,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1624,c_3948])).

tff(c_4002,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_844,c_3977])).

tff(c_4010,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4002])).

tff(c_4138,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_4010])).

tff(c_4148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1615,c_4138])).

tff(c_4150,plain,(
    m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4002])).

tff(c_1614,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1576])).

tff(c_1739,plain,(
    ! [A_117] :
      ( r1_tarski(A_117,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_117,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1614,c_6])).

tff(c_2712,plain,(
    ! [A_143,A_144] :
      ( r1_tarski(A_143,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_143,A_144)
      | ~ r1_tarski(A_144,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1739,c_6])).

tff(c_2792,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_2712])).

tff(c_2849,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_2792])).

tff(c_1920,plain,(
    ! [A_124,B_125] :
      ( k3_subset_1(A_124,k3_subset_1(A_124,k3_subset_1(A_124,B_125))) = k3_subset_1(A_124,B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(A_124)) ) ),
    inference(resolution,[status(thm)],[c_32,c_484])).

tff(c_44,plain,(
    ! [A_27,B_28] :
      ( k2_subset_1(A_27) = B_28
      | ~ r1_tarski(k3_subset_1(A_27,B_28),B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_57,plain,(
    ! [B_28,A_27] :
      ( B_28 = A_27
      | ~ r1_tarski(k3_subset_1(A_27,B_28),B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_44])).

tff(c_20242,plain,(
    ! [A_343,B_344] :
      ( k3_subset_1(A_343,k3_subset_1(A_343,B_344)) = A_343
      | ~ r1_tarski(k3_subset_1(A_343,B_344),k3_subset_1(A_343,k3_subset_1(A_343,B_344)))
      | ~ m1_subset_1(k3_subset_1(A_343,k3_subset_1(A_343,B_344)),k1_zfmisc_1(A_343))
      | ~ m1_subset_1(B_344,k1_zfmisc_1(A_343)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1920,c_57])).

tff(c_20321,plain,
    ( k3_subset_1('#skF_4',k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5'))) = '#skF_4'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4',k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5'))))
    | ~ m1_subset_1(k3_subset_1('#skF_4',k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5'))),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1624,c_20242])).

tff(c_20388,plain,(
    k3_subset_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4150,c_4150,c_1624,c_2849,c_1624,c_1624,c_20321])).

tff(c_342,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k3_subset_1(A_68,B_69),A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_332,c_134])).

tff(c_4161,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4150,c_134])).

tff(c_4177,plain,(
    ! [A_172] :
      ( r1_tarski(A_172,'#skF_4')
      | ~ r1_tarski(A_172,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4161,c_6])).

tff(c_14575,plain,(
    ! [B_310] :
      ( r1_tarski(k3_subset_1(k3_subset_1('#skF_4','#skF_5'),B_310),'#skF_4')
      | ~ m1_subset_1(B_310,k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_342,c_4177])).

tff(c_14611,plain,
    ( k3_subset_1('#skF_4','#skF_5') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_14575,c_57])).

tff(c_14618,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k3_subset_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_14611])).

tff(c_14625,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_163,c_14618])).

tff(c_20411,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20388,c_14625])).

tff(c_20459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_20411])).

tff(c_20460,plain,(
    k3_subset_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14611])).

tff(c_503,plain,(
    ! [A_8,C_12] :
      ( k3_subset_1(A_8,k3_subset_1(A_8,C_12)) = C_12
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(resolution,[status(thm)],[c_163,c_484])).

tff(c_20564,plain,
    ( k3_subset_1('#skF_4','#skF_4') = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20460,c_503])).

tff(c_20605,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_510,c_20564])).

tff(c_20607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_20605])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.95/4.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.11/4.32  
% 11.11/4.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.11/4.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 11.11/4.32  
% 11.11/4.32  %Foreground sorts:
% 11.11/4.32  
% 11.11/4.32  
% 11.11/4.32  %Background operators:
% 11.11/4.32  
% 11.11/4.32  
% 11.11/4.32  %Foreground operators:
% 11.11/4.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.11/4.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.11/4.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.11/4.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.11/4.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.11/4.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.11/4.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.11/4.32  tff('#skF_5', type, '#skF_5': $i).
% 11.11/4.32  tff('#skF_6', type, '#skF_6': $i).
% 11.11/4.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.11/4.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.11/4.32  tff('#skF_4', type, '#skF_4': $i).
% 11.11/4.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.11/4.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.11/4.32  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 11.11/4.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.11/4.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.11/4.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.11/4.32  
% 11.11/4.34  tff(f_100, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 11.11/4.34  tff(f_68, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.11/4.34  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 11.11/4.34  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.11/4.34  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.11/4.34  tff(f_59, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 11.11/4.34  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 11.11/4.34  tff(f_74, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 11.11/4.34  tff(f_91, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 11.11/4.34  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.11/4.34  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.11/4.34  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 11.11/4.34  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 11.11/4.34  tff(c_48, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.11/4.34  tff(c_52, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.11/4.34  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.11/4.34  tff(c_34, plain, (![A_19]: (~v1_xboole_0(k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.11/4.34  tff(c_124, plain, (![B_47, A_48]: (r2_hidden(B_47, A_48) | ~m1_subset_1(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.11/4.34  tff(c_8, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.11/4.34  tff(c_128, plain, (![B_47, A_8]: (r1_tarski(B_47, A_8) | ~m1_subset_1(B_47, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_124, c_8])).
% 11.11/4.34  tff(c_136, plain, (![B_49, A_50]: (r1_tarski(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)))), inference(negUnitSimplification, [status(thm)], [c_34, c_128])).
% 11.11/4.34  tff(c_148, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_136])).
% 11.11/4.34  tff(c_187, plain, (![A_57, C_58, B_59]: (r1_tarski(A_57, C_58) | ~r1_tarski(B_59, C_58) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.11/4.34  tff(c_268, plain, (![A_66]: (r1_tarski(A_66, '#skF_4') | ~r1_tarski(A_66, '#skF_6'))), inference(resolution, [status(thm)], [c_148, c_187])).
% 11.11/4.34  tff(c_298, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_268])).
% 11.11/4.34  tff(c_28, plain, (![A_15]: (k1_subset_1(A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.11/4.34  tff(c_30, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.11/4.34  tff(c_38, plain, (![A_22]: (k3_subset_1(A_22, k1_subset_1(A_22))=k2_subset_1(A_22))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.11/4.34  tff(c_56, plain, (![A_22]: (k3_subset_1(A_22, k1_subset_1(A_22))=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_38])).
% 11.11/4.34  tff(c_58, plain, (![A_22]: (k3_subset_1(A_22, k1_xboole_0)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_56])).
% 11.11/4.34  tff(c_46, plain, (![A_29]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.11/4.34  tff(c_484, plain, (![A_76, B_77]: (k3_subset_1(A_76, k3_subset_1(A_76, B_77))=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.11/4.34  tff(c_500, plain, (![A_29]: (k3_subset_1(A_29, k3_subset_1(A_29, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_484])).
% 11.11/4.34  tff(c_510, plain, (![A_29]: (k3_subset_1(A_29, A_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_500])).
% 11.11/4.34  tff(c_332, plain, (![A_68, B_69]: (m1_subset_1(k3_subset_1(A_68, B_69), k1_zfmisc_1(A_68)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.11/4.34  tff(c_341, plain, (![A_22]: (m1_subset_1(A_22, k1_zfmisc_1(A_22)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_332])).
% 11.11/4.34  tff(c_348, plain, (![A_70]: (m1_subset_1(A_70, k1_zfmisc_1(A_70)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_341])).
% 11.11/4.34  tff(c_134, plain, (![B_47, A_8]: (r1_tarski(B_47, A_8) | ~m1_subset_1(B_47, k1_zfmisc_1(A_8)))), inference(negUnitSimplification, [status(thm)], [c_34, c_128])).
% 11.11/4.34  tff(c_355, plain, (![A_70]: (r1_tarski(A_70, A_70))), inference(resolution, [status(thm)], [c_348, c_134])).
% 11.11/4.34  tff(c_10, plain, (![C_12, A_8]: (r2_hidden(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.11/4.34  tff(c_150, plain, (![B_51, A_52]: (m1_subset_1(B_51, A_52) | ~r2_hidden(B_51, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.11/4.34  tff(c_156, plain, (![C_12, A_8]: (m1_subset_1(C_12, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(resolution, [status(thm)], [c_10, c_150])).
% 11.11/4.34  tff(c_163, plain, (![C_12, A_8]: (m1_subset_1(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(negUnitSimplification, [status(thm)], [c_34, c_156])).
% 11.11/4.34  tff(c_50, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.11/4.34  tff(c_1520, plain, (![C_111, A_112, B_113]: (r1_tarski(C_111, k3_subset_1(A_112, B_113)) | ~r1_tarski(B_113, k3_subset_1(A_112, C_111)) | ~m1_subset_1(C_111, k1_zfmisc_1(A_112)) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.11/4.34  tff(c_1554, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_1520])).
% 11.11/4.34  tff(c_1576, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1554])).
% 11.11/4.34  tff(c_1587, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1576])).
% 11.11/4.34  tff(c_1606, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_163, c_1587])).
% 11.11/4.34  tff(c_1613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_298, c_1606])).
% 11.11/4.34  tff(c_1615, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1576])).
% 11.11/4.34  tff(c_32, plain, (![A_17, B_18]: (m1_subset_1(k3_subset_1(A_17, B_18), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.11/4.34  tff(c_264, plain, (![A_65]: (r1_tarski(A_65, k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski(A_65, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_187])).
% 11.11/4.34  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.11/4.34  tff(c_791, plain, (![A_87, A_88]: (r1_tarski(A_87, k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski(A_87, A_88) | ~r1_tarski(A_88, '#skF_5'))), inference(resolution, [status(thm)], [c_264, c_6])).
% 11.11/4.34  tff(c_838, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_148, c_791])).
% 11.11/4.34  tff(c_844, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_838])).
% 11.11/4.34  tff(c_36, plain, (![A_20, B_21]: (k3_subset_1(A_20, k3_subset_1(A_20, B_21))=B_21 | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.11/4.34  tff(c_1624, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_1615, c_36])).
% 11.11/4.34  tff(c_345, plain, (![A_22]: (m1_subset_1(A_22, k1_zfmisc_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_341])).
% 11.11/4.34  tff(c_1538, plain, (![A_29, B_113]: (r1_tarski(A_29, k3_subset_1(A_29, B_113)) | ~r1_tarski(B_113, k1_xboole_0) | ~m1_subset_1(A_29, k1_zfmisc_1(A_29)) | ~m1_subset_1(B_113, k1_zfmisc_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_510, c_1520])).
% 11.11/4.34  tff(c_3948, plain, (![A_169, B_170]: (r1_tarski(A_169, k3_subset_1(A_169, B_170)) | ~r1_tarski(B_170, k1_xboole_0) | ~m1_subset_1(B_170, k1_zfmisc_1(A_169)))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_1538])).
% 11.11/4.34  tff(c_3977, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k1_xboole_0) | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1624, c_3948])).
% 11.11/4.34  tff(c_4002, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k1_xboole_0) | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_844, c_3977])).
% 11.11/4.34  tff(c_4010, plain, (~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4002])).
% 11.11/4.34  tff(c_4138, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_4010])).
% 11.11/4.34  tff(c_4148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1615, c_4138])).
% 11.11/4.34  tff(c_4150, plain, (m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4002])).
% 11.11/4.34  tff(c_1614, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1576])).
% 11.11/4.34  tff(c_1739, plain, (![A_117]: (r1_tarski(A_117, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_117, '#skF_6'))), inference(resolution, [status(thm)], [c_1614, c_6])).
% 11.11/4.34  tff(c_2712, plain, (![A_143, A_144]: (r1_tarski(A_143, k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_143, A_144) | ~r1_tarski(A_144, '#skF_6'))), inference(resolution, [status(thm)], [c_1739, c_6])).
% 11.11/4.34  tff(c_2792, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_2712])).
% 11.11/4.34  tff(c_2849, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_355, c_2792])).
% 11.11/4.34  tff(c_1920, plain, (![A_124, B_125]: (k3_subset_1(A_124, k3_subset_1(A_124, k3_subset_1(A_124, B_125)))=k3_subset_1(A_124, B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(A_124)))), inference(resolution, [status(thm)], [c_32, c_484])).
% 11.11/4.34  tff(c_44, plain, (![A_27, B_28]: (k2_subset_1(A_27)=B_28 | ~r1_tarski(k3_subset_1(A_27, B_28), B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.11/4.34  tff(c_57, plain, (![B_28, A_27]: (B_28=A_27 | ~r1_tarski(k3_subset_1(A_27, B_28), B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_44])).
% 11.11/4.34  tff(c_20242, plain, (![A_343, B_344]: (k3_subset_1(A_343, k3_subset_1(A_343, B_344))=A_343 | ~r1_tarski(k3_subset_1(A_343, B_344), k3_subset_1(A_343, k3_subset_1(A_343, B_344))) | ~m1_subset_1(k3_subset_1(A_343, k3_subset_1(A_343, B_344)), k1_zfmisc_1(A_343)) | ~m1_subset_1(B_344, k1_zfmisc_1(A_343)))), inference(superposition, [status(thm), theory('equality')], [c_1920, c_57])).
% 11.11/4.34  tff(c_20321, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5')))='#skF_4' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5')))) | ~m1_subset_1(k3_subset_1('#skF_4', k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), k1_zfmisc_1('#skF_4')) | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1624, c_20242])).
% 11.11/4.34  tff(c_20388, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4150, c_4150, c_1624, c_2849, c_1624, c_1624, c_20321])).
% 11.11/4.34  tff(c_342, plain, (![A_68, B_69]: (r1_tarski(k3_subset_1(A_68, B_69), A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(resolution, [status(thm)], [c_332, c_134])).
% 11.11/4.34  tff(c_4161, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_4150, c_134])).
% 11.11/4.34  tff(c_4177, plain, (![A_172]: (r1_tarski(A_172, '#skF_4') | ~r1_tarski(A_172, k3_subset_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_4161, c_6])).
% 11.11/4.34  tff(c_14575, plain, (![B_310]: (r1_tarski(k3_subset_1(k3_subset_1('#skF_4', '#skF_5'), B_310), '#skF_4') | ~m1_subset_1(B_310, k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_342, c_4177])).
% 11.11/4.34  tff(c_14611, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_14575, c_57])).
% 11.11/4.34  tff(c_14618, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k3_subset_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_14611])).
% 11.11/4.34  tff(c_14625, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_163, c_14618])).
% 11.11/4.34  tff(c_20411, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20388, c_14625])).
% 11.11/4.34  tff(c_20459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_355, c_20411])).
% 11.11/4.34  tff(c_20460, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_14611])).
% 11.11/4.34  tff(c_503, plain, (![A_8, C_12]: (k3_subset_1(A_8, k3_subset_1(A_8, C_12))=C_12 | ~r1_tarski(C_12, A_8))), inference(resolution, [status(thm)], [c_163, c_484])).
% 11.11/4.34  tff(c_20564, plain, (k3_subset_1('#skF_4', '#skF_4')='#skF_5' | ~r1_tarski('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20460, c_503])).
% 11.11/4.34  tff(c_20605, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_510, c_20564])).
% 11.11/4.34  tff(c_20607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_20605])).
% 11.11/4.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.11/4.34  
% 11.11/4.34  Inference rules
% 11.11/4.34  ----------------------
% 11.11/4.34  #Ref     : 0
% 11.11/4.34  #Sup     : 4656
% 11.11/4.34  #Fact    : 0
% 11.11/4.34  #Define  : 0
% 11.11/4.34  #Split   : 19
% 11.11/4.34  #Chain   : 0
% 11.11/4.34  #Close   : 0
% 11.11/4.34  
% 11.11/4.34  Ordering : KBO
% 11.11/4.34  
% 11.11/4.34  Simplification rules
% 11.11/4.34  ----------------------
% 11.11/4.34  #Subsume      : 1638
% 11.11/4.34  #Demod        : 2698
% 11.11/4.34  #Tautology    : 1201
% 11.11/4.34  #SimpNegUnit  : 85
% 11.11/4.34  #BackRed      : 160
% 11.11/4.34  
% 11.11/4.34  #Partial instantiations: 0
% 11.11/4.34  #Strategies tried      : 1
% 11.11/4.34  
% 11.11/4.34  Timing (in seconds)
% 11.11/4.34  ----------------------
% 11.11/4.35  Preprocessing        : 0.31
% 11.11/4.35  Parsing              : 0.17
% 11.11/4.35  CNF conversion       : 0.02
% 11.11/4.35  Main loop            : 3.27
% 11.11/4.35  Inferencing          : 0.73
% 11.11/4.35  Reduction            : 1.32
% 11.11/4.35  Demodulation         : 1.00
% 11.11/4.35  BG Simplification    : 0.08
% 11.11/4.35  Subsumption          : 0.96
% 11.11/4.35  Abstraction          : 0.12
% 11.11/4.35  MUC search           : 0.00
% 11.11/4.35  Cooper               : 0.00
% 11.11/4.35  Total                : 3.62
% 11.11/4.35  Index Insertion      : 0.00
% 11.11/4.35  Index Deletion       : 0.00
% 11.11/4.35  Index Matching       : 0.00
% 11.11/4.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
