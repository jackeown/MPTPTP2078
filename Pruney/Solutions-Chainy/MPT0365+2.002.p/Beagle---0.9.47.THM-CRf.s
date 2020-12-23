%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:42 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 273 expanded)
%              Number of leaves         :   26 ( 102 expanded)
%              Depth                    :   14
%              Number of atoms          :  140 ( 664 expanded)
%              Number of equality atoms :   15 (  81 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_72,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_42,plain,(
    k3_subset_1('#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_96,plain,(
    ! [B_39,A_40] :
      ( r2_hidden(B_39,A_40)
      | ~ m1_subset_1(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_100,plain,(
    ! [B_39,A_8] :
      ( r1_tarski(B_39,A_8)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_96,c_12])).

tff(c_104,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(B_41,A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_100])).

tff(c_116,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_104])).

tff(c_46,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_146,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k3_subset_1(A_47,B_48),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_103,plain,(
    ! [B_39,A_8] :
      ( r1_tarski(B_39,A_8)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_8)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_100])).

tff(c_153,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k3_subset_1(A_47,B_48),A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_146,c_103])).

tff(c_117,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_104])).

tff(c_54,plain,(
    ! [B_27,A_28] :
      ( r1_xboole_0(B_27,A_28)
      | ~ r1_xboole_0(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_54])).

tff(c_34,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k3_subset_1(A_17,B_18),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_499,plain,(
    ! [B_84,C_85,A_86] :
      ( r1_tarski(B_84,C_85)
      | ~ r1_xboole_0(B_84,k3_subset_1(A_86,C_85))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_508,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_499])).

tff(c_515,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_5')
    | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_508])).

tff(c_516,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_515])).

tff(c_519,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_516])).

tff(c_529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_519])).

tff(c_530,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_515])).

tff(c_159,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k3_subset_1(A_51,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_179,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_159])).

tff(c_217,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,k4_xboole_0(B_57,C_58))
      | ~ r1_xboole_0(A_56,C_58)
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_242,plain,(
    ! [A_60] :
      ( r1_tarski(A_60,k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_xboole_0(A_60,'#skF_4')
      | ~ r1_tarski(A_60,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_217])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_249,plain,(
    ! [A_60] :
      ( k3_subset_1('#skF_3','#skF_4') = A_60
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),A_60)
      | ~ r1_xboole_0(A_60,'#skF_4')
      | ~ r1_tarski(A_60,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_242,c_4])).

tff(c_534,plain,
    ( k3_subset_1('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_xboole_0('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_530,c_249])).

tff(c_542,plain,(
    k3_subset_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_57,c_534])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_583,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_65])).

tff(c_14,plain,(
    ! [C_12,A_8] :
      ( r2_hidden(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_126,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(B_43,A_44)
      | ~ r2_hidden(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_132,plain,(
    ! [C_12,A_8] :
      ( m1_subset_1(C_12,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_126])).

tff(c_136,plain,(
    ! [C_12,A_8] :
      ( m1_subset_1(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_132])).

tff(c_40,plain,(
    ! [B_21,C_23,A_20] :
      ( r1_tarski(B_21,C_23)
      | ~ r1_xboole_0(B_21,k3_subset_1(A_20,C_23))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_590,plain,(
    ! [B_21] :
      ( r1_tarski(B_21,'#skF_4')
      | ~ r1_xboole_0(B_21,'#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(B_21,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_40])).

tff(c_678,plain,(
    ! [B_90] :
      ( r1_tarski(B_90,'#skF_4')
      | ~ r1_xboole_0(B_90,'#skF_5')
      | ~ m1_subset_1(B_90,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_590])).

tff(c_705,plain,(
    ! [C_91] :
      ( r1_tarski(C_91,'#skF_4')
      | ~ r1_xboole_0(C_91,'#skF_5')
      | ~ r1_tarski(C_91,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_136,c_678])).

tff(c_712,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_4')
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_583,c_705])).

tff(c_788,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_712])).

tff(c_791,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_153,c_788])).

tff(c_795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_791])).

tff(c_796,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_712])).

tff(c_180,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_159])).

tff(c_234,plain,(
    ! [A_59] :
      ( r1_tarski(A_59,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_xboole_0(A_59,'#skF_5')
      | ~ r1_tarski(A_59,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_217])).

tff(c_241,plain,(
    ! [A_59] :
      ( k3_subset_1('#skF_3','#skF_5') = A_59
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),A_59)
      | ~ r1_xboole_0(A_59,'#skF_5')
      | ~ r1_tarski(A_59,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_234,c_4])).

tff(c_800,plain,
    ( k3_subset_1('#skF_3','#skF_5') = '#skF_4'
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_796,c_241])).

tff(c_808,plain,(
    k3_subset_1('#skF_3','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_46,c_800])).

tff(c_810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:44:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.78  
% 2.95/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.79  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.95/1.79  
% 2.95/1.79  %Foreground sorts:
% 2.95/1.79  
% 2.95/1.79  
% 2.95/1.79  %Background operators:
% 2.95/1.79  
% 2.95/1.79  
% 2.95/1.79  %Foreground operators:
% 2.95/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.95/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.79  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.95/1.79  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.79  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.95/1.79  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.79  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.95/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.95/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.95/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.79  
% 3.09/1.80  tff(f_93, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_xboole_0(B, C) & r1_xboole_0(k3_subset_1(A, B), k3_subset_1(A, C))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_subset_1)).
% 3.09/1.80  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.09/1.80  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.09/1.80  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.09/1.80  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.09/1.80  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.09/1.80  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 3.09/1.80  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.09/1.80  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.09/1.80  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.09/1.80  tff(c_42, plain, (k3_subset_1('#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.09/1.80  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.09/1.80  tff(c_36, plain, (![A_19]: (~v1_xboole_0(k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.09/1.80  tff(c_96, plain, (![B_39, A_40]: (r2_hidden(B_39, A_40) | ~m1_subset_1(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.09/1.80  tff(c_12, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.09/1.80  tff(c_100, plain, (![B_39, A_8]: (r1_tarski(B_39, A_8) | ~m1_subset_1(B_39, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_96, c_12])).
% 3.09/1.80  tff(c_104, plain, (![B_41, A_42]: (r1_tarski(B_41, A_42) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)))), inference(negUnitSimplification, [status(thm)], [c_36, c_100])).
% 3.09/1.80  tff(c_116, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_104])).
% 3.09/1.80  tff(c_46, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.09/1.80  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.09/1.80  tff(c_146, plain, (![A_47, B_48]: (m1_subset_1(k3_subset_1(A_47, B_48), k1_zfmisc_1(A_47)) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.09/1.80  tff(c_103, plain, (![B_39, A_8]: (r1_tarski(B_39, A_8) | ~m1_subset_1(B_39, k1_zfmisc_1(A_8)))), inference(negUnitSimplification, [status(thm)], [c_36, c_100])).
% 3.09/1.80  tff(c_153, plain, (![A_47, B_48]: (r1_tarski(k3_subset_1(A_47, B_48), A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_146, c_103])).
% 3.09/1.80  tff(c_117, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_104])).
% 3.09/1.80  tff(c_54, plain, (![B_27, A_28]: (r1_xboole_0(B_27, A_28) | ~r1_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.09/1.80  tff(c_57, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_54])).
% 3.09/1.80  tff(c_34, plain, (![A_17, B_18]: (m1_subset_1(k3_subset_1(A_17, B_18), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.09/1.80  tff(c_44, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.09/1.80  tff(c_499, plain, (![B_84, C_85, A_86]: (r1_tarski(B_84, C_85) | ~r1_xboole_0(B_84, k3_subset_1(A_86, C_85)) | ~m1_subset_1(C_85, k1_zfmisc_1(A_86)) | ~m1_subset_1(B_84, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.09/1.80  tff(c_508, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_499])).
% 3.09/1.80  tff(c_515, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_5') | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_508])).
% 3.09/1.80  tff(c_516, plain, (~m1_subset_1(k3_subset_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_515])).
% 3.09/1.80  tff(c_519, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_516])).
% 3.09/1.80  tff(c_529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_519])).
% 3.09/1.80  tff(c_530, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_515])).
% 3.09/1.80  tff(c_159, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k3_subset_1(A_51, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.09/1.80  tff(c_179, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_159])).
% 3.09/1.80  tff(c_217, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, k4_xboole_0(B_57, C_58)) | ~r1_xboole_0(A_56, C_58) | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.09/1.80  tff(c_242, plain, (![A_60]: (r1_tarski(A_60, k3_subset_1('#skF_3', '#skF_4')) | ~r1_xboole_0(A_60, '#skF_4') | ~r1_tarski(A_60, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_179, c_217])).
% 3.09/1.80  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.09/1.80  tff(c_249, plain, (![A_60]: (k3_subset_1('#skF_3', '#skF_4')=A_60 | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), A_60) | ~r1_xboole_0(A_60, '#skF_4') | ~r1_tarski(A_60, '#skF_3'))), inference(resolution, [status(thm)], [c_242, c_4])).
% 3.09/1.80  tff(c_534, plain, (k3_subset_1('#skF_3', '#skF_4')='#skF_5' | ~r1_xboole_0('#skF_5', '#skF_4') | ~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_530, c_249])).
% 3.09/1.80  tff(c_542, plain, (k3_subset_1('#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_57, c_534])).
% 3.09/1.80  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.09/1.80  tff(c_65, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_2])).
% 3.09/1.80  tff(c_583, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_542, c_65])).
% 3.09/1.80  tff(c_14, plain, (![C_12, A_8]: (r2_hidden(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.09/1.80  tff(c_126, plain, (![B_43, A_44]: (m1_subset_1(B_43, A_44) | ~r2_hidden(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.09/1.80  tff(c_132, plain, (![C_12, A_8]: (m1_subset_1(C_12, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(resolution, [status(thm)], [c_14, c_126])).
% 3.09/1.80  tff(c_136, plain, (![C_12, A_8]: (m1_subset_1(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(negUnitSimplification, [status(thm)], [c_36, c_132])).
% 3.09/1.80  tff(c_40, plain, (![B_21, C_23, A_20]: (r1_tarski(B_21, C_23) | ~r1_xboole_0(B_21, k3_subset_1(A_20, C_23)) | ~m1_subset_1(C_23, k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.09/1.80  tff(c_590, plain, (![B_21]: (r1_tarski(B_21, '#skF_4') | ~r1_xboole_0(B_21, '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(B_21, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_542, c_40])).
% 3.09/1.80  tff(c_678, plain, (![B_90]: (r1_tarski(B_90, '#skF_4') | ~r1_xboole_0(B_90, '#skF_5') | ~m1_subset_1(B_90, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_590])).
% 3.09/1.80  tff(c_705, plain, (![C_91]: (r1_tarski(C_91, '#skF_4') | ~r1_xboole_0(C_91, '#skF_5') | ~r1_tarski(C_91, '#skF_3'))), inference(resolution, [status(thm)], [c_136, c_678])).
% 3.09/1.80  tff(c_712, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_4') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_583, c_705])).
% 3.09/1.80  tff(c_788, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_712])).
% 3.09/1.80  tff(c_791, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_153, c_788])).
% 3.09/1.80  tff(c_795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_791])).
% 3.09/1.80  tff(c_796, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_712])).
% 3.09/1.80  tff(c_180, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_159])).
% 3.09/1.80  tff(c_234, plain, (![A_59]: (r1_tarski(A_59, k3_subset_1('#skF_3', '#skF_5')) | ~r1_xboole_0(A_59, '#skF_5') | ~r1_tarski(A_59, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_180, c_217])).
% 3.09/1.80  tff(c_241, plain, (![A_59]: (k3_subset_1('#skF_3', '#skF_5')=A_59 | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), A_59) | ~r1_xboole_0(A_59, '#skF_5') | ~r1_tarski(A_59, '#skF_3'))), inference(resolution, [status(thm)], [c_234, c_4])).
% 3.09/1.80  tff(c_800, plain, (k3_subset_1('#skF_3', '#skF_5')='#skF_4' | ~r1_xboole_0('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_796, c_241])).
% 3.09/1.80  tff(c_808, plain, (k3_subset_1('#skF_3', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_46, c_800])).
% 3.09/1.80  tff(c_810, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_808])).
% 3.09/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.80  
% 3.09/1.80  Inference rules
% 3.09/1.80  ----------------------
% 3.09/1.80  #Ref     : 0
% 3.09/1.80  #Sup     : 157
% 3.09/1.80  #Fact    : 0
% 3.09/1.80  #Define  : 0
% 3.09/1.80  #Split   : 7
% 3.09/1.80  #Chain   : 0
% 3.09/1.80  #Close   : 0
% 3.09/1.80  
% 3.09/1.80  Ordering : KBO
% 3.09/1.80  
% 3.09/1.80  Simplification rules
% 3.09/1.80  ----------------------
% 3.09/1.80  #Subsume      : 20
% 3.09/1.80  #Demod        : 78
% 3.09/1.80  #Tautology    : 51
% 3.09/1.80  #SimpNegUnit  : 4
% 3.09/1.80  #BackRed      : 8
% 3.09/1.80  
% 3.09/1.80  #Partial instantiations: 0
% 3.09/1.80  #Strategies tried      : 1
% 3.09/1.80  
% 3.09/1.80  Timing (in seconds)
% 3.09/1.80  ----------------------
% 3.09/1.81  Preprocessing        : 0.57
% 3.09/1.81  Parsing              : 0.36
% 3.09/1.81  CNF conversion       : 0.03
% 3.09/1.81  Main loop            : 0.35
% 3.09/1.81  Inferencing          : 0.12
% 3.09/1.81  Reduction            : 0.10
% 3.09/1.81  Demodulation         : 0.07
% 3.09/1.81  BG Simplification    : 0.03
% 3.09/1.81  Subsumption          : 0.08
% 3.09/1.81  Abstraction          : 0.02
% 3.09/1.81  MUC search           : 0.00
% 3.09/1.81  Cooper               : 0.00
% 3.09/1.81  Total                : 0.95
% 3.09/1.81  Index Insertion      : 0.00
% 3.09/1.81  Index Deletion       : 0.00
% 3.09/1.81  Index Matching       : 0.00
% 3.09/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
