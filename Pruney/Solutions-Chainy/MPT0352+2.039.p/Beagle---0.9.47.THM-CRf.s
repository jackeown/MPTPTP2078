%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:51 EST 2020

% Result     : Theorem 13.06s
% Output     : CNFRefutation 13.07s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 100 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 166 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_90,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_80,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_84,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_80])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_48,plain,(
    ! [A_32] : ~ v1_xboole_0(k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_217,plain,(
    ! [B_66,A_67] :
      ( r2_hidden(B_66,A_67)
      | ~ m1_subset_1(B_66,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    ! [C_27,A_23] :
      ( r1_tarski(C_27,A_23)
      | ~ r2_hidden(C_27,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_221,plain,(
    ! [B_66,A_23] :
      ( r1_tarski(B_66,A_23)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_23))
      | v1_xboole_0(k1_zfmisc_1(A_23)) ) ),
    inference(resolution,[status(thm)],[c_217,c_26])).

tff(c_225,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(B_68,A_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_221])).

tff(c_238,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_225])).

tff(c_693,plain,(
    ! [A_93,C_94,B_95] :
      ( r1_tarski(A_93,C_94)
      | ~ r1_tarski(B_95,C_94)
      | ~ r1_tarski(A_93,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_805,plain,(
    ! [A_102] :
      ( r1_tarski(A_102,'#skF_3')
      | ~ r1_tarski(A_102,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_238,c_693])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3747,plain,(
    ! [A_181] :
      ( k4_xboole_0(A_181,'#skF_3') = k1_xboole_0
      | ~ r1_tarski(A_181,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_805,c_6])).

tff(c_3775,plain,(
    ! [B_15] : k4_xboole_0(k4_xboole_0('#skF_4',B_15),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_3747])).

tff(c_60,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_156,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_60])).

tff(c_1251,plain,(
    ! [A_123,B_124] :
      ( k4_xboole_0(A_123,B_124) = k3_subset_1(A_123,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1264,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1251])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,C_7)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6968,plain,(
    ! [A_254] :
      ( r1_xboole_0(A_254,'#skF_4')
      | ~ r1_tarski(A_254,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_8])).

tff(c_7016,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_156,c_6968])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7026,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_7016,c_2])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1263,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_1251])).

tff(c_1398,plain,(
    ! [B_125,A_126,C_127] :
      ( r1_xboole_0(B_125,k4_xboole_0(A_126,C_127))
      | ~ r1_xboole_0(A_126,k4_xboole_0(B_125,C_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_19167,plain,(
    ! [A_411] :
      ( r1_xboole_0('#skF_3',k4_xboole_0(A_411,'#skF_5'))
      | ~ r1_xboole_0(A_411,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1263,c_1398])).

tff(c_19250,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_7026,c_19167])).

tff(c_19291,plain,(
    r1_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_19250,c_2])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = A_21
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_19295,plain,(
    k4_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_3') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_19291,c_22])).

tff(c_19311,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3775,c_19295])).

tff(c_19313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_19311])).

tff(c_19314,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_19315,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_20865,plain,(
    ! [A_495,B_496] :
      ( k4_xboole_0(A_495,B_496) = k3_subset_1(A_495,B_496)
      | ~ m1_subset_1(B_496,k1_zfmisc_1(A_495)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_20878,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_20865])).

tff(c_20877,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_20865])).

tff(c_21014,plain,(
    ! [C_497,B_498,A_499] :
      ( r1_tarski(k4_xboole_0(C_497,B_498),k4_xboole_0(C_497,A_499))
      | ~ r1_tarski(A_499,B_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_43894,plain,(
    ! [A_828] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k4_xboole_0('#skF_3',A_828))
      | ~ r1_tarski(A_828,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20877,c_21014])).

tff(c_43944,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_20878,c_43894])).

tff(c_43983,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19315,c_43944])).

tff(c_43985,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19314,c_43983])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:43:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.06/5.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.07/5.80  
% 13.07/5.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.07/5.81  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 13.07/5.81  
% 13.07/5.81  %Foreground sorts:
% 13.07/5.81  
% 13.07/5.81  
% 13.07/5.81  %Background operators:
% 13.07/5.81  
% 13.07/5.81  
% 13.07/5.81  %Foreground operators:
% 13.07/5.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.07/5.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.07/5.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.07/5.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.07/5.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.07/5.81  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 13.07/5.81  tff('#skF_5', type, '#skF_5': $i).
% 13.07/5.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.07/5.81  tff('#skF_3', type, '#skF_3': $i).
% 13.07/5.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.07/5.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.07/5.81  tff('#skF_4', type, '#skF_4': $i).
% 13.07/5.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.07/5.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.07/5.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.07/5.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.07/5.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.07/5.81  
% 13.07/5.82  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 13.07/5.82  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 13.07/5.82  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.07/5.82  tff(f_90, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 13.07/5.82  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 13.07/5.82  tff(f_70, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 13.07/5.82  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 13.07/5.82  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 13.07/5.82  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 13.07/5.82  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 13.07/5.82  tff(f_59, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 13.07/5.82  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 13.07/5.82  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 13.07/5.82  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.07/5.82  tff(c_54, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.07/5.82  tff(c_80, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 13.07/5.82  tff(c_84, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_80])).
% 13.07/5.82  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.07/5.82  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.07/5.82  tff(c_48, plain, (![A_32]: (~v1_xboole_0(k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.07/5.82  tff(c_217, plain, (![B_66, A_67]: (r2_hidden(B_66, A_67) | ~m1_subset_1(B_66, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.07/5.82  tff(c_26, plain, (![C_27, A_23]: (r1_tarski(C_27, A_23) | ~r2_hidden(C_27, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.07/5.82  tff(c_221, plain, (![B_66, A_23]: (r1_tarski(B_66, A_23) | ~m1_subset_1(B_66, k1_zfmisc_1(A_23)) | v1_xboole_0(k1_zfmisc_1(A_23)))), inference(resolution, [status(thm)], [c_217, c_26])).
% 13.07/5.82  tff(c_225, plain, (![B_68, A_69]: (r1_tarski(B_68, A_69) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)))), inference(negUnitSimplification, [status(thm)], [c_48, c_221])).
% 13.07/5.82  tff(c_238, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_225])).
% 13.07/5.82  tff(c_693, plain, (![A_93, C_94, B_95]: (r1_tarski(A_93, C_94) | ~r1_tarski(B_95, C_94) | ~r1_tarski(A_93, B_95))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.07/5.82  tff(c_805, plain, (![A_102]: (r1_tarski(A_102, '#skF_3') | ~r1_tarski(A_102, '#skF_4'))), inference(resolution, [status(thm)], [c_238, c_693])).
% 13.07/5.82  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.07/5.82  tff(c_3747, plain, (![A_181]: (k4_xboole_0(A_181, '#skF_3')=k1_xboole_0 | ~r1_tarski(A_181, '#skF_4'))), inference(resolution, [status(thm)], [c_805, c_6])).
% 13.07/5.82  tff(c_3775, plain, (![B_15]: (k4_xboole_0(k4_xboole_0('#skF_4', B_15), '#skF_3')=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_3747])).
% 13.07/5.82  tff(c_60, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.07/5.82  tff(c_156, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_60])).
% 13.07/5.82  tff(c_1251, plain, (![A_123, B_124]: (k4_xboole_0(A_123, B_124)=k3_subset_1(A_123, B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.07/5.82  tff(c_1264, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_1251])).
% 13.07/5.82  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, C_7) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.07/5.82  tff(c_6968, plain, (![A_254]: (r1_xboole_0(A_254, '#skF_4') | ~r1_tarski(A_254, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1264, c_8])).
% 13.07/5.82  tff(c_7016, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_156, c_6968])).
% 13.07/5.82  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.07/5.82  tff(c_7026, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_7016, c_2])).
% 13.07/5.82  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.07/5.82  tff(c_1263, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_1251])).
% 13.07/5.82  tff(c_1398, plain, (![B_125, A_126, C_127]: (r1_xboole_0(B_125, k4_xboole_0(A_126, C_127)) | ~r1_xboole_0(A_126, k4_xboole_0(B_125, C_127)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.07/5.82  tff(c_19167, plain, (![A_411]: (r1_xboole_0('#skF_3', k4_xboole_0(A_411, '#skF_5')) | ~r1_xboole_0(A_411, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1263, c_1398])).
% 13.07/5.82  tff(c_19250, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_7026, c_19167])).
% 13.07/5.82  tff(c_19291, plain, (r1_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_19250, c_2])).
% 13.07/5.82  tff(c_22, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=A_21 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.07/5.82  tff(c_19295, plain, (k4_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_3')=k4_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_19291, c_22])).
% 13.07/5.82  tff(c_19311, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3775, c_19295])).
% 13.07/5.82  tff(c_19313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_19311])).
% 13.07/5.82  tff(c_19314, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 13.07/5.82  tff(c_19315, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 13.07/5.82  tff(c_20865, plain, (![A_495, B_496]: (k4_xboole_0(A_495, B_496)=k3_subset_1(A_495, B_496) | ~m1_subset_1(B_496, k1_zfmisc_1(A_495)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.07/5.82  tff(c_20878, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_20865])).
% 13.07/5.82  tff(c_20877, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_20865])).
% 13.07/5.82  tff(c_21014, plain, (![C_497, B_498, A_499]: (r1_tarski(k4_xboole_0(C_497, B_498), k4_xboole_0(C_497, A_499)) | ~r1_tarski(A_499, B_498))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.07/5.82  tff(c_43894, plain, (![A_828]: (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k4_xboole_0('#skF_3', A_828)) | ~r1_tarski(A_828, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_20877, c_21014])).
% 13.07/5.82  tff(c_43944, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_20878, c_43894])).
% 13.07/5.82  tff(c_43983, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19315, c_43944])).
% 13.07/5.82  tff(c_43985, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19314, c_43983])).
% 13.07/5.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.07/5.82  
% 13.07/5.82  Inference rules
% 13.07/5.82  ----------------------
% 13.07/5.82  #Ref     : 0
% 13.07/5.82  #Sup     : 10978
% 13.07/5.82  #Fact    : 0
% 13.07/5.82  #Define  : 0
% 13.07/5.82  #Split   : 9
% 13.07/5.82  #Chain   : 0
% 13.07/5.82  #Close   : 0
% 13.07/5.82  
% 13.07/5.82  Ordering : KBO
% 13.07/5.82  
% 13.07/5.82  Simplification rules
% 13.07/5.82  ----------------------
% 13.07/5.82  #Subsume      : 3584
% 13.07/5.82  #Demod        : 6645
% 13.07/5.82  #Tautology    : 4946
% 13.07/5.82  #SimpNegUnit  : 274
% 13.07/5.82  #BackRed      : 11
% 13.07/5.82  
% 13.07/5.82  #Partial instantiations: 0
% 13.07/5.82  #Strategies tried      : 1
% 13.07/5.82  
% 13.07/5.82  Timing (in seconds)
% 13.07/5.82  ----------------------
% 13.07/5.82  Preprocessing        : 0.32
% 13.07/5.82  Parsing              : 0.17
% 13.07/5.82  CNF conversion       : 0.02
% 13.07/5.82  Main loop            : 4.73
% 13.07/5.82  Inferencing          : 0.97
% 13.07/5.82  Reduction            : 2.26
% 13.07/5.82  Demodulation         : 1.73
% 13.07/5.82  BG Simplification    : 0.09
% 13.07/5.82  Subsumption          : 1.17
% 13.07/5.82  Abstraction          : 0.13
% 13.07/5.82  MUC search           : 0.00
% 13.07/5.82  Cooper               : 0.00
% 13.07/5.83  Total                : 5.09
% 13.07/5.83  Index Insertion      : 0.00
% 13.07/5.83  Index Deletion       : 0.00
% 13.07/5.83  Index Matching       : 0.00
% 13.07/5.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
