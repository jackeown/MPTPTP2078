%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:32 EST 2020

% Result     : Theorem 11.62s
% Output     : CNFRefutation 11.62s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 109 expanded)
%              Number of leaves         :   47 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :   92 ( 116 expanded)
%              Number of equality atoms :   49 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_96,axiom,(
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

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_58,plain,(
    ! [A_56] : k2_subset_1(A_56) = A_56 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_71,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_68])).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1085,plain,(
    ! [A_126,B_127] :
      ( k4_xboole_0(A_126,B_127) = k3_subset_1(A_126,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1098,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_1085])).

tff(c_64,plain,(
    ! [A_61] : ~ v1_xboole_0(k1_zfmisc_1(A_61)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_327,plain,(
    ! [B_102,A_103] :
      ( r2_hidden(B_102,A_103)
      | ~ m1_subset_1(B_102,A_103)
      | v1_xboole_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [C_51,A_47] :
      ( r1_tarski(C_51,A_47)
      | ~ r2_hidden(C_51,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_334,plain,(
    ! [B_102,A_47] :
      ( r1_tarski(B_102,A_47)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_47))
      | v1_xboole_0(k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_327,c_36])).

tff(c_339,plain,(
    ! [B_104,A_105] :
      ( r1_tarski(B_104,A_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_105)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_334])).

tff(c_352,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_339])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_356,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_352,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_361,plain,(
    ! [A_106,B_107] : k5_xboole_0(A_106,k3_xboole_0(A_106,B_107)) = k4_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2357,plain,(
    ! [B_174,A_175] : k5_xboole_0(B_174,k3_xboole_0(A_175,B_174)) = k4_xboole_0(B_174,A_175) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_361])).

tff(c_2445,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_2357])).

tff(c_2479,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_2445])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_142,plain,(
    ! [B_73,A_74] : k5_xboole_0(B_73,A_74) = k5_xboole_0(A_74,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_158,plain,(
    ! [A_74] : k5_xboole_0(k1_xboole_0,A_74) = A_74 ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_14])).

tff(c_20,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_674,plain,(
    ! [A_117,B_118,C_119] : k5_xboole_0(k5_xboole_0(A_117,B_118),C_119) = k5_xboole_0(A_117,k5_xboole_0(B_118,C_119)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_760,plain,(
    ! [A_17,C_119] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_119)) = k5_xboole_0(k1_xboole_0,C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_674])).

tff(c_781,plain,(
    ! [A_120,C_121] : k5_xboole_0(A_120,k5_xboole_0(A_120,C_121)) = C_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_760])).

tff(c_836,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k5_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_781])).

tff(c_2493,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2479,c_836])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_259,plain,(
    ! [A_84,B_85] :
      ( k3_xboole_0(A_84,B_85) = k1_xboole_0
      | ~ r1_xboole_0(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_268,plain,(
    ! [A_86,B_87] : k3_xboole_0(k4_xboole_0(A_86,B_87),B_87) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_259])).

tff(c_273,plain,(
    ! [B_87,A_86] : k3_xboole_0(B_87,k4_xboole_0(A_86,B_87)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_2])).

tff(c_1102,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1098,c_273])).

tff(c_22,plain,(
    ! [A_18,B_19] : k5_xboole_0(k5_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1143,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')),k1_xboole_0) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1102,c_22])).

tff(c_2684,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k5_xboole_0('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2493,c_1143])).

tff(c_2685,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2684])).

tff(c_62,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k3_subset_1(A_59,B_60),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2711,plain,(
    ! [A_177,B_178,C_179] :
      ( k4_subset_1(A_177,B_178,C_179) = k2_xboole_0(B_178,C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(A_177))
      | ~ m1_subset_1(B_178,k1_zfmisc_1(A_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_21928,plain,(
    ! [A_351,B_352,B_353] :
      ( k4_subset_1(A_351,B_352,k3_subset_1(A_351,B_353)) = k2_xboole_0(B_352,k3_subset_1(A_351,B_353))
      | ~ m1_subset_1(B_352,k1_zfmisc_1(A_351))
      | ~ m1_subset_1(B_353,k1_zfmisc_1(A_351)) ) ),
    inference(resolution,[status(thm)],[c_62,c_2711])).

tff(c_22188,plain,(
    ! [B_356] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_356)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_356))
      | ~ m1_subset_1(B_356,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_70,c_21928])).

tff(c_22207,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_70,c_22188])).

tff(c_22215,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_22207])).

tff(c_22217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_22215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.62/5.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.62/5.12  
% 11.62/5.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.62/5.13  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.62/5.13  
% 11.62/5.13  %Foreground sorts:
% 11.62/5.13  
% 11.62/5.13  
% 11.62/5.13  %Background operators:
% 11.62/5.13  
% 11.62/5.13  
% 11.62/5.13  %Foreground operators:
% 11.62/5.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.62/5.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.62/5.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.62/5.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.62/5.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.62/5.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.62/5.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.62/5.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.62/5.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.62/5.13  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.62/5.13  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.62/5.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.62/5.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.62/5.13  tff('#skF_3', type, '#skF_3': $i).
% 11.62/5.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.62/5.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.62/5.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.62/5.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.62/5.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.62/5.13  tff('#skF_4', type, '#skF_4': $i).
% 11.62/5.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.62/5.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.62/5.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.62/5.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.62/5.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.62/5.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.62/5.13  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.62/5.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.62/5.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.62/5.13  
% 11.62/5.14  tff(f_85, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 11.62/5.14  tff(f_107, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 11.62/5.14  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 11.62/5.14  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 11.62/5.14  tff(f_96, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.62/5.14  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 11.62/5.14  tff(f_68, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.62/5.14  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.62/5.14  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.62/5.14  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.62/5.14  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.62/5.14  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.62/5.14  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.62/5.14  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.62/5.14  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.62/5.14  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 11.62/5.14  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.62/5.14  tff(f_102, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.62/5.14  tff(c_58, plain, (![A_56]: (k2_subset_1(A_56)=A_56)), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.62/5.14  tff(c_68, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.62/5.14  tff(c_71, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_68])).
% 11.62/5.14  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.62/5.14  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.62/5.14  tff(c_1085, plain, (![A_126, B_127]: (k4_xboole_0(A_126, B_127)=k3_subset_1(A_126, B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.62/5.14  tff(c_1098, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_1085])).
% 11.62/5.14  tff(c_64, plain, (![A_61]: (~v1_xboole_0(k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.62/5.14  tff(c_327, plain, (![B_102, A_103]: (r2_hidden(B_102, A_103) | ~m1_subset_1(B_102, A_103) | v1_xboole_0(A_103))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.62/5.14  tff(c_36, plain, (![C_51, A_47]: (r1_tarski(C_51, A_47) | ~r2_hidden(C_51, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.62/5.14  tff(c_334, plain, (![B_102, A_47]: (r1_tarski(B_102, A_47) | ~m1_subset_1(B_102, k1_zfmisc_1(A_47)) | v1_xboole_0(k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_327, c_36])).
% 11.62/5.14  tff(c_339, plain, (![B_104, A_105]: (r1_tarski(B_104, A_105) | ~m1_subset_1(B_104, k1_zfmisc_1(A_105)))), inference(negUnitSimplification, [status(thm)], [c_64, c_334])).
% 11.62/5.14  tff(c_352, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_339])).
% 11.62/5.14  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.62/5.14  tff(c_356, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_352, c_12])).
% 11.62/5.14  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.62/5.14  tff(c_361, plain, (![A_106, B_107]: (k5_xboole_0(A_106, k3_xboole_0(A_106, B_107))=k4_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.62/5.14  tff(c_2357, plain, (![B_174, A_175]: (k5_xboole_0(B_174, k3_xboole_0(A_175, B_174))=k4_xboole_0(B_174, A_175))), inference(superposition, [status(thm), theory('equality')], [c_2, c_361])).
% 11.62/5.14  tff(c_2445, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_356, c_2357])).
% 11.62/5.14  tff(c_2479, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_2445])).
% 11.62/5.14  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.62/5.14  tff(c_142, plain, (![B_73, A_74]: (k5_xboole_0(B_73, A_74)=k5_xboole_0(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.62/5.14  tff(c_158, plain, (![A_74]: (k5_xboole_0(k1_xboole_0, A_74)=A_74)), inference(superposition, [status(thm), theory('equality')], [c_142, c_14])).
% 11.62/5.14  tff(c_20, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.62/5.14  tff(c_674, plain, (![A_117, B_118, C_119]: (k5_xboole_0(k5_xboole_0(A_117, B_118), C_119)=k5_xboole_0(A_117, k5_xboole_0(B_118, C_119)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.62/5.14  tff(c_760, plain, (![A_17, C_119]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_119))=k5_xboole_0(k1_xboole_0, C_119))), inference(superposition, [status(thm), theory('equality')], [c_20, c_674])).
% 11.62/5.14  tff(c_781, plain, (![A_120, C_121]: (k5_xboole_0(A_120, k5_xboole_0(A_120, C_121))=C_121)), inference(demodulation, [status(thm), theory('equality')], [c_158, c_760])).
% 11.62/5.14  tff(c_836, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k5_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_781])).
% 11.62/5.14  tff(c_2493, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2479, c_836])).
% 11.62/5.14  tff(c_16, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.62/5.14  tff(c_259, plain, (![A_84, B_85]: (k3_xboole_0(A_84, B_85)=k1_xboole_0 | ~r1_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.62/5.14  tff(c_268, plain, (![A_86, B_87]: (k3_xboole_0(k4_xboole_0(A_86, B_87), B_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_259])).
% 11.62/5.14  tff(c_273, plain, (![B_87, A_86]: (k3_xboole_0(B_87, k4_xboole_0(A_86, B_87))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_268, c_2])).
% 11.62/5.14  tff(c_1102, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1098, c_273])).
% 11.62/5.14  tff(c_22, plain, (![A_18, B_19]: (k5_xboole_0(k5_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.62/5.14  tff(c_1143, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')), k1_xboole_0)=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1102, c_22])).
% 11.62/5.14  tff(c_2684, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k5_xboole_0('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2493, c_1143])).
% 11.62/5.14  tff(c_2685, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2684])).
% 11.62/5.14  tff(c_62, plain, (![A_59, B_60]: (m1_subset_1(k3_subset_1(A_59, B_60), k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.62/5.14  tff(c_2711, plain, (![A_177, B_178, C_179]: (k4_subset_1(A_177, B_178, C_179)=k2_xboole_0(B_178, C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(A_177)) | ~m1_subset_1(B_178, k1_zfmisc_1(A_177)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.62/5.14  tff(c_21928, plain, (![A_351, B_352, B_353]: (k4_subset_1(A_351, B_352, k3_subset_1(A_351, B_353))=k2_xboole_0(B_352, k3_subset_1(A_351, B_353)) | ~m1_subset_1(B_352, k1_zfmisc_1(A_351)) | ~m1_subset_1(B_353, k1_zfmisc_1(A_351)))), inference(resolution, [status(thm)], [c_62, c_2711])).
% 11.62/5.14  tff(c_22188, plain, (![B_356]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_356))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_356)) | ~m1_subset_1(B_356, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_70, c_21928])).
% 11.62/5.14  tff(c_22207, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_70, c_22188])).
% 11.62/5.14  tff(c_22215, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2685, c_22207])).
% 11.62/5.14  tff(c_22217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_22215])).
% 11.62/5.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.62/5.14  
% 11.62/5.14  Inference rules
% 11.62/5.14  ----------------------
% 11.62/5.14  #Ref     : 0
% 11.62/5.14  #Sup     : 5491
% 11.62/5.14  #Fact    : 0
% 11.62/5.14  #Define  : 0
% 11.62/5.14  #Split   : 0
% 11.62/5.14  #Chain   : 0
% 11.62/5.14  #Close   : 0
% 11.62/5.14  
% 11.62/5.14  Ordering : KBO
% 11.62/5.14  
% 11.62/5.14  Simplification rules
% 11.62/5.14  ----------------------
% 11.62/5.14  #Subsume      : 257
% 11.62/5.14  #Demod        : 8453
% 11.62/5.14  #Tautology    : 3080
% 11.62/5.14  #SimpNegUnit  : 14
% 11.62/5.14  #BackRed      : 7
% 11.62/5.14  
% 11.62/5.14  #Partial instantiations: 0
% 11.62/5.14  #Strategies tried      : 1
% 11.62/5.14  
% 11.62/5.14  Timing (in seconds)
% 11.62/5.14  ----------------------
% 11.62/5.14  Preprocessing        : 0.36
% 11.62/5.14  Parsing              : 0.19
% 11.62/5.14  CNF conversion       : 0.03
% 11.62/5.14  Main loop            : 4.01
% 11.62/5.15  Inferencing          : 0.71
% 11.62/5.15  Reduction            : 2.48
% 11.62/5.15  Demodulation         : 2.25
% 11.62/5.15  BG Simplification    : 0.10
% 11.62/5.15  Subsumption          : 0.54
% 11.62/5.15  Abstraction          : 0.15
% 11.62/5.15  MUC search           : 0.00
% 11.62/5.15  Cooper               : 0.00
% 11.62/5.15  Total                : 4.41
% 11.62/5.15  Index Insertion      : 0.00
% 11.62/5.15  Index Deletion       : 0.00
% 11.62/5.15  Index Matching       : 0.00
% 11.62/5.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
