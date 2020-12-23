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
% DateTime   : Thu Dec  3 09:55:57 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 265 expanded)
%              Number of leaves         :   27 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  123 ( 571 expanded)
%              Number of equality atoms :   12 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_29,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_14] : ~ v1_xboole_0(k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [C_9,A_5] :
      ( r2_hidden(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,(
    ! [B_39,A_40] :
      ( m1_subset_1(B_39,A_40)
      | ~ r2_hidden(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_113,plain,(
    ! [C_9,A_5] :
      ( m1_subset_1(C_9,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_107])).

tff(c_117,plain,(
    ! [C_9,A_5] :
      ( m1_subset_1(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_113])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k3_subset_1(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_153,plain,(
    ! [A_45,C_46] :
      ( k4_xboole_0(A_45,C_46) = k3_subset_1(A_45,C_46)
      | ~ r1_tarski(C_46,A_45) ) ),
    inference(resolution,[status(thm)],[c_117,c_127])).

tff(c_165,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = k3_subset_1(A_3,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_153])).

tff(c_172,plain,(
    ! [A_3] : k3_subset_1(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_165])).

tff(c_476,plain,(
    ! [A_78,C_79,B_80] :
      ( r1_tarski(k3_subset_1(A_78,C_79),k3_subset_1(A_78,B_80))
      | ~ r1_tarski(B_80,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_512,plain,(
    ! [A_3,C_79] :
      ( r1_tarski(k3_subset_1(A_3,C_79),A_3)
      | ~ r1_tarski(k1_xboole_0,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_476])).

tff(c_518,plain,(
    ! [A_81,C_82] :
      ( r1_tarski(k3_subset_1(A_81,C_82),A_81)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_81)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_512])).

tff(c_182,plain,(
    ! [A_48,B_49] :
      ( k3_subset_1(A_48,k3_subset_1(A_48,B_49)) = B_49
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_194,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_182])).

tff(c_347,plain,(
    ! [B_65,C_66,A_67] :
      ( r1_tarski(B_65,C_66)
      | ~ r1_tarski(k3_subset_1(A_67,C_66),k3_subset_1(A_67,B_65))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_368,plain,(
    ! [B_65] :
      ( r1_tarski(B_65,k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3',B_65))
      | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(B_65,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_347])).

tff(c_420,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_427,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_420])).

tff(c_521,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_518,c_427])).

tff(c_542,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_521])).

tff(c_549,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_542])).

tff(c_556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_549])).

tff(c_558,plain,(
    m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_371,plain,(
    ! [C_66] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),C_66)
      | ~ r1_tarski(k3_subset_1('#skF_3',C_66),'#skF_4')
      | ~ m1_subset_1(C_66,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_347])).

tff(c_578,plain,(
    ! [C_83] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),C_83)
      | ~ r1_tarski(k3_subset_1('#skF_3',C_83),'#skF_4')
      | ~ m1_subset_1(C_83,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_371])).

tff(c_591,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_578])).

tff(c_654,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_591])).

tff(c_657,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_654])).

tff(c_664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_657])).

tff(c_666,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_591])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_608,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_tarski(k3_subset_1(A_84,C_85),k3_subset_1(A_84,B_86))
      | ~ r1_tarski(B_86,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_644,plain,(
    ! [A_3,C_85] :
      ( r1_tarski(k3_subset_1(A_3,C_85),A_3)
      | ~ r1_tarski(k1_xboole_0,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_608])).

tff(c_720,plain,(
    ! [A_89,C_90] :
      ( r1_tarski(k3_subset_1(A_89,C_90),A_89)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(A_89))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_89)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_644])).

tff(c_195,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_182])).

tff(c_586,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_578])).

tff(c_667,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_3','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_586])).

tff(c_692,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_667])).

tff(c_723,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_720,c_692])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_42,c_723])).

tff(c_747,plain,(
    m1_subset_1(k3_subset_1('#skF_3','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_586])).

tff(c_629,plain,(
    ! [B_86] :
      ( r1_tarski('#skF_5',k3_subset_1('#skF_3',B_86))
      | ~ r1_tarski(B_86,k3_subset_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_5'),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(B_86,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_608])).

tff(c_884,plain,(
    ! [B_97] :
      ( r1_tarski('#skF_5',k3_subset_1('#skF_3',B_97))
      | ~ r1_tarski(B_97,k3_subset_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(B_97,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_629])).

tff(c_901,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_884])).

tff(c_914,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_901])).

tff(c_916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_914])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:52:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.55  
% 2.96/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.55  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.96/1.55  
% 2.96/1.55  %Foreground sorts:
% 2.96/1.55  
% 2.96/1.55  
% 2.96/1.55  %Background operators:
% 2.96/1.55  
% 2.96/1.55  
% 2.96/1.55  %Foreground operators:
% 2.96/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.96/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.96/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.96/1.55  tff('#skF_5', type, '#skF_5': $i).
% 2.96/1.55  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.55  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.96/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.96/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.96/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.55  
% 3.08/1.57  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 3.08/1.57  tff(f_29, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.08/1.57  tff(f_58, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.08/1.57  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.08/1.57  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.08/1.57  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.08/1.57  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.08/1.57  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 3.08/1.57  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.08/1.57  tff(c_38, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.08/1.57  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.08/1.57  tff(c_40, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.08/1.57  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.08/1.57  tff(c_30, plain, (![A_14]: (~v1_xboole_0(k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.08/1.57  tff(c_10, plain, (![C_9, A_5]: (r2_hidden(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.08/1.57  tff(c_107, plain, (![B_39, A_40]: (m1_subset_1(B_39, A_40) | ~r2_hidden(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.08/1.57  tff(c_113, plain, (![C_9, A_5]: (m1_subset_1(C_9, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(resolution, [status(thm)], [c_10, c_107])).
% 3.08/1.57  tff(c_117, plain, (![C_9, A_5]: (m1_subset_1(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(negUnitSimplification, [status(thm)], [c_30, c_113])).
% 3.08/1.57  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.08/1.57  tff(c_127, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k3_subset_1(A_43, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.08/1.57  tff(c_153, plain, (![A_45, C_46]: (k4_xboole_0(A_45, C_46)=k3_subset_1(A_45, C_46) | ~r1_tarski(C_46, A_45))), inference(resolution, [status(thm)], [c_117, c_127])).
% 3.08/1.57  tff(c_165, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=k3_subset_1(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_153])).
% 3.08/1.57  tff(c_172, plain, (![A_3]: (k3_subset_1(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_165])).
% 3.08/1.57  tff(c_476, plain, (![A_78, C_79, B_80]: (r1_tarski(k3_subset_1(A_78, C_79), k3_subset_1(A_78, B_80)) | ~r1_tarski(B_80, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_78)) | ~m1_subset_1(B_80, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.08/1.57  tff(c_512, plain, (![A_3, C_79]: (r1_tarski(k3_subset_1(A_3, C_79), A_3) | ~r1_tarski(k1_xboole_0, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_3)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_476])).
% 3.08/1.57  tff(c_518, plain, (![A_81, C_82]: (r1_tarski(k3_subset_1(A_81, C_82), A_81) | ~m1_subset_1(C_82, k1_zfmisc_1(A_81)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_81)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_512])).
% 3.08/1.57  tff(c_182, plain, (![A_48, B_49]: (k3_subset_1(A_48, k3_subset_1(A_48, B_49))=B_49 | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.08/1.57  tff(c_194, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_44, c_182])).
% 3.08/1.57  tff(c_347, plain, (![B_65, C_66, A_67]: (r1_tarski(B_65, C_66) | ~r1_tarski(k3_subset_1(A_67, C_66), k3_subset_1(A_67, B_65)) | ~m1_subset_1(C_66, k1_zfmisc_1(A_67)) | ~m1_subset_1(B_65, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.08/1.57  tff(c_368, plain, (![B_65]: (r1_tarski(B_65, k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', B_65)) | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(B_65, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_194, c_347])).
% 3.08/1.57  tff(c_420, plain, (~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_368])).
% 3.08/1.57  tff(c_427, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_117, c_420])).
% 3.08/1.57  tff(c_521, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_518, c_427])).
% 3.08/1.57  tff(c_542, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_521])).
% 3.08/1.57  tff(c_549, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_117, c_542])).
% 3.08/1.57  tff(c_556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_549])).
% 3.08/1.57  tff(c_558, plain, (m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_368])).
% 3.08/1.57  tff(c_371, plain, (![C_66]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), C_66) | ~r1_tarski(k3_subset_1('#skF_3', C_66), '#skF_4') | ~m1_subset_1(C_66, k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_194, c_347])).
% 3.08/1.57  tff(c_578, plain, (![C_83]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), C_83) | ~r1_tarski(k3_subset_1('#skF_3', C_83), '#skF_4') | ~m1_subset_1(C_83, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_371])).
% 3.08/1.57  tff(c_591, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_578])).
% 3.08/1.57  tff(c_654, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_591])).
% 3.08/1.57  tff(c_657, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_117, c_654])).
% 3.08/1.57  tff(c_664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_657])).
% 3.08/1.57  tff(c_666, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_591])).
% 3.08/1.57  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.08/1.57  tff(c_608, plain, (![A_84, C_85, B_86]: (r1_tarski(k3_subset_1(A_84, C_85), k3_subset_1(A_84, B_86)) | ~r1_tarski(B_86, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_86, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.08/1.57  tff(c_644, plain, (![A_3, C_85]: (r1_tarski(k3_subset_1(A_3, C_85), A_3) | ~r1_tarski(k1_xboole_0, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(A_3)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_608])).
% 3.08/1.57  tff(c_720, plain, (![A_89, C_90]: (r1_tarski(k3_subset_1(A_89, C_90), A_89) | ~m1_subset_1(C_90, k1_zfmisc_1(A_89)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_89)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_644])).
% 3.08/1.57  tff(c_195, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_42, c_182])).
% 3.08/1.57  tff(c_586, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_578])).
% 3.08/1.57  tff(c_667, plain, (~m1_subset_1(k3_subset_1('#skF_3', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_586])).
% 3.08/1.57  tff(c_692, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_117, c_667])).
% 3.08/1.57  tff(c_723, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_720, c_692])).
% 3.08/1.57  tff(c_745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_666, c_42, c_723])).
% 3.08/1.57  tff(c_747, plain, (m1_subset_1(k3_subset_1('#skF_3', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_586])).
% 3.08/1.57  tff(c_629, plain, (![B_86]: (r1_tarski('#skF_5', k3_subset_1('#skF_3', B_86)) | ~r1_tarski(B_86, k3_subset_1('#skF_3', '#skF_5')) | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(B_86, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_195, c_608])).
% 3.08/1.57  tff(c_884, plain, (![B_97]: (r1_tarski('#skF_5', k3_subset_1('#skF_3', B_97)) | ~r1_tarski(B_97, k3_subset_1('#skF_3', '#skF_5')) | ~m1_subset_1(B_97, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_747, c_629])).
% 3.08/1.57  tff(c_901, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_884])).
% 3.08/1.57  tff(c_914, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_901])).
% 3.08/1.57  tff(c_916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_914])).
% 3.08/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.57  
% 3.08/1.57  Inference rules
% 3.08/1.57  ----------------------
% 3.08/1.57  #Ref     : 0
% 3.08/1.57  #Sup     : 197
% 3.08/1.57  #Fact    : 0
% 3.08/1.57  #Define  : 0
% 3.08/1.57  #Split   : 11
% 3.08/1.57  #Chain   : 0
% 3.08/1.57  #Close   : 0
% 3.08/1.57  
% 3.08/1.57  Ordering : KBO
% 3.08/1.57  
% 3.08/1.57  Simplification rules
% 3.08/1.57  ----------------------
% 3.08/1.57  #Subsume      : 24
% 3.08/1.57  #Demod        : 63
% 3.08/1.57  #Tautology    : 72
% 3.08/1.57  #SimpNegUnit  : 14
% 3.08/1.57  #BackRed      : 0
% 3.08/1.57  
% 3.08/1.57  #Partial instantiations: 0
% 3.08/1.57  #Strategies tried      : 1
% 3.08/1.57  
% 3.08/1.57  Timing (in seconds)
% 3.08/1.57  ----------------------
% 3.08/1.57  Preprocessing        : 0.40
% 3.08/1.57  Parsing              : 0.21
% 3.08/1.57  CNF conversion       : 0.02
% 3.08/1.57  Main loop            : 0.38
% 3.08/1.57  Inferencing          : 0.14
% 3.08/1.58  Reduction            : 0.12
% 3.08/1.58  Demodulation         : 0.08
% 3.08/1.58  BG Simplification    : 0.02
% 3.08/1.58  Subsumption          : 0.08
% 3.08/1.58  Abstraction          : 0.02
% 3.08/1.58  MUC search           : 0.00
% 3.08/1.58  Cooper               : 0.00
% 3.08/1.58  Total                : 0.82
% 3.08/1.58  Index Insertion      : 0.00
% 3.08/1.58  Index Deletion       : 0.00
% 3.08/1.58  Index Matching       : 0.00
% 3.08/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
