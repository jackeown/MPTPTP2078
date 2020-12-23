%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:44 EST 2020

% Result     : Theorem 8.59s
% Output     : CNFRefutation 8.79s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 135 expanded)
%              Number of leaves         :   45 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :   85 ( 162 expanded)
%              Number of equality atoms :   46 (  69 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_87,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

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

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_58,plain,(
    ! [A_58] : k2_subset_1(A_58) = A_58 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_66,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_69,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_66])).

tff(c_125,plain,(
    ! [B_72,A_73] : k5_xboole_0(B_72,A_73) = k5_xboole_0(A_73,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_141,plain,(
    ! [A_73] : k5_xboole_0(k1_xboole_0,A_73) = A_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_16])).

tff(c_60,plain,(
    ! [A_59] : m1_subset_1(k2_subset_1(A_59),k1_zfmisc_1(A_59)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_70,plain,(
    ! [A_59] : m1_subset_1(A_59,k1_zfmisc_1(A_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60])).

tff(c_62,plain,(
    ! [A_60] : ~ v1_xboole_0(k1_zfmisc_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_304,plain,(
    ! [B_101,A_102] :
      ( r2_hidden(B_101,A_102)
      | ~ m1_subset_1(B_101,A_102)
      | v1_xboole_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [C_53,A_49] :
      ( r1_tarski(C_53,A_49)
      | ~ r2_hidden(C_53,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_311,plain,(
    ! [B_101,A_49] :
      ( r1_tarski(B_101,A_49)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_49))
      | v1_xboole_0(k1_zfmisc_1(A_49)) ) ),
    inference(resolution,[status(thm)],[c_304,c_36])).

tff(c_316,plain,(
    ! [B_103,A_104] :
      ( r1_tarski(B_103,A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_104)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_311])).

tff(c_334,plain,(
    ! [A_105] : r1_tarski(A_105,A_105) ),
    inference(resolution,[status(thm)],[c_70,c_316])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_338,plain,(
    ! [A_105] : k3_xboole_0(A_105,A_105) = A_105 ),
    inference(resolution,[status(thm)],[c_334,c_14])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_247,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = k1_xboole_0
      | ~ r1_xboole_0(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_256,plain,(
    ! [A_91,B_92] : k3_xboole_0(k4_xboole_0(A_91,B_92),B_92) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_247])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_261,plain,(
    ! [B_92,A_91] : k3_xboole_0(B_92,k4_xboole_0(A_91,B_92)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_2])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1371,plain,(
    ! [A_138,B_139,C_140] : k5_xboole_0(k3_xboole_0(A_138,B_139),k3_xboole_0(C_140,B_139)) = k3_xboole_0(k5_xboole_0(A_138,C_140),B_139) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1388,plain,(
    ! [A_138,B_139] : k3_xboole_0(k5_xboole_0(A_138,k3_xboole_0(A_138,B_139)),B_139) = k4_xboole_0(k3_xboole_0(A_138,B_139),B_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_1371,c_10])).

tff(c_1510,plain,(
    ! [A_141,B_142] : k4_xboole_0(k3_xboole_0(A_141,B_142),B_142) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_2,c_10,c_1388])).

tff(c_1553,plain,(
    ! [A_105] : k4_xboole_0(A_105,A_105) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_1510])).

tff(c_356,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k3_xboole_0(A_107,B_108)) = k4_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_372,plain,(
    ! [A_105] : k5_xboole_0(A_105,A_105) = k4_xboole_0(A_105,A_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_356])).

tff(c_2033,plain,(
    ! [A_158] : k5_xboole_0(A_158,A_158) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1553,c_372])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] : k5_xboole_0(k5_xboole_0(A_17,B_18),C_19) = k5_xboole_0(A_17,k5_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2045,plain,(
    ! [A_158,C_19] : k5_xboole_0(A_158,k5_xboole_0(A_158,C_19)) = k5_xboole_0(k1_xboole_0,C_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_2033,c_20])).

tff(c_2079,plain,(
    ! [A_158,C_19] : k5_xboole_0(A_158,k5_xboole_0(A_158,C_19)) = C_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_2045])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_333,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_316])).

tff(c_342,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_333,c_14])).

tff(c_830,plain,(
    ! [A_128,B_129] : k5_xboole_0(k5_xboole_0(A_128,B_129),k3_xboole_0(A_128,B_129)) = k2_xboole_0(A_128,B_129) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_876,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_4') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_830])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1047,plain,(
    k5_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_3')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_876,c_4])).

tff(c_2214,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2079,c_1047])).

tff(c_2500,plain,(
    ! [A_179,B_180,C_181] :
      ( k4_subset_1(A_179,B_180,C_181) = k2_xboole_0(B_180,C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(A_179))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(A_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12918,plain,(
    ! [A_293,B_294] :
      ( k4_subset_1(A_293,B_294,A_293) = k2_xboole_0(B_294,A_293)
      | ~ m1_subset_1(B_294,k1_zfmisc_1(A_293)) ) ),
    inference(resolution,[status(thm)],[c_70,c_2500])).

tff(c_12927,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_12918])).

tff(c_12933,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2214,c_12927])).

tff(c_12935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_12933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:48:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.59/3.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.59/3.17  
% 8.59/3.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.59/3.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.59/3.17  
% 8.59/3.17  %Foreground sorts:
% 8.59/3.17  
% 8.59/3.17  
% 8.59/3.17  %Background operators:
% 8.59/3.17  
% 8.59/3.17  
% 8.59/3.17  %Foreground operators:
% 8.59/3.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.59/3.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.59/3.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.59/3.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.59/3.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.59/3.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.59/3.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.59/3.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.59/3.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.59/3.17  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.59/3.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.59/3.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.59/3.17  tff('#skF_3', type, '#skF_3': $i).
% 8.59/3.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.59/3.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.59/3.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.59/3.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.59/3.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.59/3.17  tff('#skF_4', type, '#skF_4': $i).
% 8.59/3.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.59/3.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.59/3.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.59/3.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.59/3.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.59/3.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.59/3.17  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.59/3.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.59/3.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.59/3.17  
% 8.79/3.19  tff(f_85, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.79/3.19  tff(f_101, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 8.79/3.19  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.79/3.19  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.79/3.19  tff(f_87, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.79/3.19  tff(f_90, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.79/3.19  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 8.79/3.19  tff(f_68, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 8.79/3.19  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.79/3.19  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 8.79/3.19  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.79/3.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.79/3.19  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.79/3.19  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 8.79/3.19  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.79/3.19  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.79/3.19  tff(f_96, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.79/3.19  tff(c_58, plain, (![A_58]: (k2_subset_1(A_58)=A_58)), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.79/3.19  tff(c_66, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.79/3.19  tff(c_69, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_66])).
% 8.79/3.19  tff(c_125, plain, (![B_72, A_73]: (k5_xboole_0(B_72, A_73)=k5_xboole_0(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.79/3.19  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.79/3.19  tff(c_141, plain, (![A_73]: (k5_xboole_0(k1_xboole_0, A_73)=A_73)), inference(superposition, [status(thm), theory('equality')], [c_125, c_16])).
% 8.79/3.19  tff(c_60, plain, (![A_59]: (m1_subset_1(k2_subset_1(A_59), k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.79/3.19  tff(c_70, plain, (![A_59]: (m1_subset_1(A_59, k1_zfmisc_1(A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60])).
% 8.79/3.19  tff(c_62, plain, (![A_60]: (~v1_xboole_0(k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.79/3.19  tff(c_304, plain, (![B_101, A_102]: (r2_hidden(B_101, A_102) | ~m1_subset_1(B_101, A_102) | v1_xboole_0(A_102))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.79/3.19  tff(c_36, plain, (![C_53, A_49]: (r1_tarski(C_53, A_49) | ~r2_hidden(C_53, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.79/3.19  tff(c_311, plain, (![B_101, A_49]: (r1_tarski(B_101, A_49) | ~m1_subset_1(B_101, k1_zfmisc_1(A_49)) | v1_xboole_0(k1_zfmisc_1(A_49)))), inference(resolution, [status(thm)], [c_304, c_36])).
% 8.79/3.19  tff(c_316, plain, (![B_103, A_104]: (r1_tarski(B_103, A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(A_104)))), inference(negUnitSimplification, [status(thm)], [c_62, c_311])).
% 8.79/3.19  tff(c_334, plain, (![A_105]: (r1_tarski(A_105, A_105))), inference(resolution, [status(thm)], [c_70, c_316])).
% 8.79/3.19  tff(c_14, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.79/3.19  tff(c_338, plain, (![A_105]: (k3_xboole_0(A_105, A_105)=A_105)), inference(resolution, [status(thm)], [c_334, c_14])).
% 8.79/3.19  tff(c_18, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.79/3.19  tff(c_247, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=k1_xboole_0 | ~r1_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.79/3.19  tff(c_256, plain, (![A_91, B_92]: (k3_xboole_0(k4_xboole_0(A_91, B_92), B_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_247])).
% 8.79/3.19  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.79/3.19  tff(c_261, plain, (![B_92, A_91]: (k3_xboole_0(B_92, k4_xboole_0(A_91, B_92))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_256, c_2])).
% 8.79/3.19  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.79/3.19  tff(c_1371, plain, (![A_138, B_139, C_140]: (k5_xboole_0(k3_xboole_0(A_138, B_139), k3_xboole_0(C_140, B_139))=k3_xboole_0(k5_xboole_0(A_138, C_140), B_139))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.79/3.19  tff(c_1388, plain, (![A_138, B_139]: (k3_xboole_0(k5_xboole_0(A_138, k3_xboole_0(A_138, B_139)), B_139)=k4_xboole_0(k3_xboole_0(A_138, B_139), B_139))), inference(superposition, [status(thm), theory('equality')], [c_1371, c_10])).
% 8.79/3.19  tff(c_1510, plain, (![A_141, B_142]: (k4_xboole_0(k3_xboole_0(A_141, B_142), B_142)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_261, c_2, c_10, c_1388])).
% 8.79/3.19  tff(c_1553, plain, (![A_105]: (k4_xboole_0(A_105, A_105)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_338, c_1510])).
% 8.79/3.19  tff(c_356, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k3_xboole_0(A_107, B_108))=k4_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.79/3.19  tff(c_372, plain, (![A_105]: (k5_xboole_0(A_105, A_105)=k4_xboole_0(A_105, A_105))), inference(superposition, [status(thm), theory('equality')], [c_338, c_356])).
% 8.79/3.19  tff(c_2033, plain, (![A_158]: (k5_xboole_0(A_158, A_158)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1553, c_372])).
% 8.79/3.19  tff(c_20, plain, (![A_17, B_18, C_19]: (k5_xboole_0(k5_xboole_0(A_17, B_18), C_19)=k5_xboole_0(A_17, k5_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.79/3.19  tff(c_2045, plain, (![A_158, C_19]: (k5_xboole_0(A_158, k5_xboole_0(A_158, C_19))=k5_xboole_0(k1_xboole_0, C_19))), inference(superposition, [status(thm), theory('equality')], [c_2033, c_20])).
% 8.79/3.19  tff(c_2079, plain, (![A_158, C_19]: (k5_xboole_0(A_158, k5_xboole_0(A_158, C_19))=C_19)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_2045])).
% 8.79/3.19  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.79/3.19  tff(c_333, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_316])).
% 8.79/3.19  tff(c_342, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_333, c_14])).
% 8.79/3.19  tff(c_830, plain, (![A_128, B_129]: (k5_xboole_0(k5_xboole_0(A_128, B_129), k3_xboole_0(A_128, B_129))=k2_xboole_0(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.79/3.19  tff(c_876, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_342, c_830])).
% 8.79/3.19  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.79/3.19  tff(c_1047, plain, (k5_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_3'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_876, c_4])).
% 8.79/3.19  tff(c_2214, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2079, c_1047])).
% 8.79/3.19  tff(c_2500, plain, (![A_179, B_180, C_181]: (k4_subset_1(A_179, B_180, C_181)=k2_xboole_0(B_180, C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(A_179)) | ~m1_subset_1(B_180, k1_zfmisc_1(A_179)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.79/3.19  tff(c_12918, plain, (![A_293, B_294]: (k4_subset_1(A_293, B_294, A_293)=k2_xboole_0(B_294, A_293) | ~m1_subset_1(B_294, k1_zfmisc_1(A_293)))), inference(resolution, [status(thm)], [c_70, c_2500])).
% 8.79/3.19  tff(c_12927, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_12918])).
% 8.79/3.19  tff(c_12933, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2214, c_12927])).
% 8.79/3.19  tff(c_12935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_12933])).
% 8.79/3.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.79/3.19  
% 8.79/3.19  Inference rules
% 8.79/3.19  ----------------------
% 8.79/3.19  #Ref     : 0
% 8.79/3.19  #Sup     : 3227
% 8.79/3.19  #Fact    : 0
% 8.79/3.19  #Define  : 0
% 8.79/3.19  #Split   : 0
% 8.79/3.19  #Chain   : 0
% 8.79/3.19  #Close   : 0
% 8.79/3.19  
% 8.79/3.19  Ordering : KBO
% 8.79/3.19  
% 8.79/3.19  Simplification rules
% 8.79/3.19  ----------------------
% 8.79/3.19  #Subsume      : 81
% 8.79/3.19  #Demod        : 4151
% 8.79/3.19  #Tautology    : 2009
% 8.79/3.19  #SimpNegUnit  : 3
% 8.79/3.19  #BackRed      : 20
% 8.79/3.19  
% 8.79/3.19  #Partial instantiations: 0
% 8.79/3.19  #Strategies tried      : 1
% 8.79/3.19  
% 8.79/3.19  Timing (in seconds)
% 8.79/3.19  ----------------------
% 8.79/3.19  Preprocessing        : 0.37
% 8.79/3.19  Parsing              : 0.20
% 8.79/3.19  CNF conversion       : 0.02
% 8.79/3.19  Main loop            : 2.01
% 8.79/3.19  Inferencing          : 0.47
% 8.79/3.19  Reduction            : 1.11
% 8.79/3.19  Demodulation         : 0.98
% 8.79/3.19  BG Simplification    : 0.06
% 8.79/3.19  Subsumption          : 0.28
% 8.79/3.19  Abstraction          : 0.09
% 8.79/3.19  MUC search           : 0.00
% 8.79/3.19  Cooper               : 0.00
% 8.79/3.19  Total                : 2.42
% 8.79/3.19  Index Insertion      : 0.00
% 8.79/3.19  Index Deletion       : 0.00
% 8.79/3.19  Index Matching       : 0.00
% 8.79/3.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
