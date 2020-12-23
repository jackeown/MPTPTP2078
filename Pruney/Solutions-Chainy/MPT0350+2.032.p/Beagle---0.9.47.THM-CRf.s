%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:30 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   71 (  94 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 137 expanded)
%              Number of equality atoms :   33 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_74,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_330,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(k3_subset_1(A_71,B_72),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_217,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(B_55,A_56)
      | ~ m1_subset_1(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_221,plain,(
    ! [B_55,A_13] :
      ( r1_tarski(B_55,A_13)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_217,c_16])).

tff(c_224,plain,(
    ! [B_55,A_13] :
      ( r1_tarski(B_55,A_13)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_13)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_221])).

tff(c_343,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k3_subset_1(A_73,B_74),A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(resolution,[status(thm)],[c_330,c_224])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_444,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(k3_subset_1(A_83,B_84),A_83) = k1_xboole_0
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_343,c_6])).

tff(c_457,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_444])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_239,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(B_58,A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_221])).

tff(c_248,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_239])).

tff(c_252,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_248,c_6])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_256,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_10])).

tff(c_259,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_256])).

tff(c_294,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k3_subset_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_307,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_294])).

tff(c_311,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_10])).

tff(c_314,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_311])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [C_17,A_13] :
      ( r2_hidden(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_261,plain,(
    ! [B_60,A_61] :
      ( m1_subset_1(B_60,A_61)
      | ~ r2_hidden(B_60,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_267,plain,(
    ! [C_17,A_13] :
      ( m1_subset_1(C_17,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_261])).

tff(c_271,plain,(
    ! [C_17,A_13] :
      ( m1_subset_1(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_267])).

tff(c_983,plain,(
    ! [A_113,B_114,C_115] :
      ( k4_subset_1(A_113,B_114,C_115) = k2_xboole_0(B_114,C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(A_113))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2269,plain,(
    ! [A_157,B_158,C_159] :
      ( k4_subset_1(A_157,B_158,C_159) = k2_xboole_0(B_158,C_159)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_157))
      | ~ r1_tarski(C_159,A_157) ) ),
    inference(resolution,[status(thm)],[c_271,c_983])).

tff(c_2344,plain,(
    ! [C_162] :
      ( k4_subset_1('#skF_3','#skF_4',C_162) = k2_xboole_0('#skF_4',C_162)
      | ~ r1_tarski(C_162,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_2269])).

tff(c_2373,plain,(
    ! [A_163] :
      ( k4_subset_1('#skF_3','#skF_4',A_163) = k2_xboole_0('#skF_4',A_163)
      | k4_xboole_0(A_163,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2344])).

tff(c_38,plain,(
    ! [A_22] : k2_subset_1(A_22) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_51,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_2386,plain,
    ( k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3'
    | k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2373,c_51])).

tff(c_2404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_314,c_2386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 21:08:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.66  
% 3.89/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.66  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.89/1.66  
% 3.89/1.66  %Foreground sorts:
% 3.89/1.66  
% 3.89/1.66  
% 3.89/1.66  %Background operators:
% 3.89/1.66  
% 3.89/1.66  
% 3.89/1.66  %Foreground operators:
% 3.89/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.89/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.89/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.89/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.89/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.89/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.89/1.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.89/1.66  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.89/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.89/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.89/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.89/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.89/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.89/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.89/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.89/1.66  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.89/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.89/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.66  
% 3.89/1.67  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 3.89/1.67  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.89/1.67  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.89/1.67  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.89/1.67  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.89/1.67  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.89/1.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.89/1.67  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.89/1.67  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.89/1.67  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.89/1.67  tff(f_80, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.89/1.67  tff(f_63, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.89/1.67  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.89/1.67  tff(c_330, plain, (![A_71, B_72]: (m1_subset_1(k3_subset_1(A_71, B_72), k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.89/1.67  tff(c_44, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.89/1.67  tff(c_217, plain, (![B_55, A_56]: (r2_hidden(B_55, A_56) | ~m1_subset_1(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.89/1.67  tff(c_16, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.89/1.67  tff(c_221, plain, (![B_55, A_13]: (r1_tarski(B_55, A_13) | ~m1_subset_1(B_55, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_217, c_16])).
% 3.89/1.67  tff(c_224, plain, (![B_55, A_13]: (r1_tarski(B_55, A_13) | ~m1_subset_1(B_55, k1_zfmisc_1(A_13)))), inference(negUnitSimplification, [status(thm)], [c_44, c_221])).
% 3.89/1.67  tff(c_343, plain, (![A_73, B_74]: (r1_tarski(k3_subset_1(A_73, B_74), A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(resolution, [status(thm)], [c_330, c_224])).
% 3.89/1.67  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.89/1.67  tff(c_444, plain, (![A_83, B_84]: (k4_xboole_0(k3_subset_1(A_83, B_84), A_83)=k1_xboole_0 | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(resolution, [status(thm)], [c_343, c_6])).
% 3.89/1.67  tff(c_457, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_444])).
% 3.89/1.67  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.89/1.67  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.89/1.67  tff(c_239, plain, (![B_58, A_59]: (r1_tarski(B_58, A_59) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)))), inference(negUnitSimplification, [status(thm)], [c_44, c_221])).
% 3.89/1.67  tff(c_248, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_239])).
% 3.89/1.67  tff(c_252, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_248, c_6])).
% 3.89/1.67  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.89/1.67  tff(c_256, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_252, c_10])).
% 3.89/1.67  tff(c_259, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_256])).
% 3.89/1.67  tff(c_294, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k3_subset_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.89/1.67  tff(c_307, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_294])).
% 3.89/1.67  tff(c_311, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_307, c_10])).
% 3.89/1.67  tff(c_314, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_259, c_311])).
% 3.89/1.67  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.89/1.67  tff(c_18, plain, (![C_17, A_13]: (r2_hidden(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.89/1.67  tff(c_261, plain, (![B_60, A_61]: (m1_subset_1(B_60, A_61) | ~r2_hidden(B_60, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.89/1.67  tff(c_267, plain, (![C_17, A_13]: (m1_subset_1(C_17, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(resolution, [status(thm)], [c_18, c_261])).
% 3.89/1.67  tff(c_271, plain, (![C_17, A_13]: (m1_subset_1(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(negUnitSimplification, [status(thm)], [c_44, c_267])).
% 3.89/1.67  tff(c_983, plain, (![A_113, B_114, C_115]: (k4_subset_1(A_113, B_114, C_115)=k2_xboole_0(B_114, C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(A_113)) | ~m1_subset_1(B_114, k1_zfmisc_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.89/1.67  tff(c_2269, plain, (![A_157, B_158, C_159]: (k4_subset_1(A_157, B_158, C_159)=k2_xboole_0(B_158, C_159) | ~m1_subset_1(B_158, k1_zfmisc_1(A_157)) | ~r1_tarski(C_159, A_157))), inference(resolution, [status(thm)], [c_271, c_983])).
% 3.89/1.67  tff(c_2344, plain, (![C_162]: (k4_subset_1('#skF_3', '#skF_4', C_162)=k2_xboole_0('#skF_4', C_162) | ~r1_tarski(C_162, '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_2269])).
% 3.89/1.67  tff(c_2373, plain, (![A_163]: (k4_subset_1('#skF_3', '#skF_4', A_163)=k2_xboole_0('#skF_4', A_163) | k4_xboole_0(A_163, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2344])).
% 3.89/1.67  tff(c_38, plain, (![A_22]: (k2_subset_1(A_22)=A_22)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.89/1.67  tff(c_48, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.89/1.67  tff(c_51, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_48])).
% 3.89/1.67  tff(c_2386, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3' | k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2373, c_51])).
% 3.89/1.67  tff(c_2404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_457, c_314, c_2386])).
% 3.89/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.67  
% 3.89/1.67  Inference rules
% 3.89/1.67  ----------------------
% 3.89/1.67  #Ref     : 1
% 3.89/1.67  #Sup     : 504
% 3.89/1.67  #Fact    : 0
% 3.89/1.67  #Define  : 0
% 3.89/1.67  #Split   : 6
% 3.89/1.67  #Chain   : 0
% 3.89/1.67  #Close   : 0
% 3.89/1.67  
% 3.89/1.67  Ordering : KBO
% 3.89/1.67  
% 3.89/1.67  Simplification rules
% 3.89/1.67  ----------------------
% 3.89/1.67  #Subsume      : 71
% 3.89/1.67  #Demod        : 323
% 3.89/1.67  #Tautology    : 292
% 3.89/1.67  #SimpNegUnit  : 4
% 3.89/1.67  #BackRed      : 1
% 3.89/1.67  
% 3.89/1.67  #Partial instantiations: 0
% 3.89/1.67  #Strategies tried      : 1
% 3.89/1.67  
% 3.89/1.67  Timing (in seconds)
% 3.89/1.67  ----------------------
% 3.89/1.67  Preprocessing        : 0.33
% 3.89/1.67  Parsing              : 0.17
% 3.89/1.67  CNF conversion       : 0.02
% 3.89/1.68  Main loop            : 0.58
% 3.89/1.68  Inferencing          : 0.21
% 3.89/1.68  Reduction            : 0.19
% 3.89/1.68  Demodulation         : 0.14
% 3.89/1.68  BG Simplification    : 0.03
% 3.89/1.68  Subsumption          : 0.11
% 3.89/1.68  Abstraction          : 0.03
% 3.89/1.68  MUC search           : 0.00
% 3.89/1.68  Cooper               : 0.00
% 3.89/1.68  Total                : 0.94
% 3.89/1.68  Index Insertion      : 0.00
% 3.89/1.68  Index Deletion       : 0.00
% 3.89/1.68  Index Matching       : 0.00
% 3.89/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
