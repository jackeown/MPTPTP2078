%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:29 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   72 (  94 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 137 expanded)
%              Number of equality atoms :   34 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_76,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_65,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_394,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(k3_subset_1(A_71,B_72),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_46,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_207,plain,(
    ! [B_54,A_55] :
      ( r2_hidden(B_54,A_55)
      | ~ m1_subset_1(B_54,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_211,plain,(
    ! [B_54,A_13] :
      ( r1_tarski(B_54,A_13)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_207,c_18])).

tff(c_214,plain,(
    ! [B_54,A_13] :
      ( r1_tarski(B_54,A_13)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_13)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_211])).

tff(c_415,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k3_subset_1(A_73,B_74),A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(resolution,[status(thm)],[c_394,c_214])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_452,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(k3_subset_1(A_79,B_80),A_79) = k1_xboole_0
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(resolution,[status(thm)],[c_415,c_6])).

tff(c_465,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_452])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_215,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(B_56,A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_211])).

tff(c_224,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_215])).

tff(c_228,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_224,c_6])).

tff(c_259,plain,(
    ! [A_61,B_62] : k2_xboole_0(A_61,k4_xboole_0(B_62,A_61)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_272,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_259])).

tff(c_283,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_272])).

tff(c_368,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = k3_subset_1(A_69,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_381,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_368])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_385,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_10])).

tff(c_391,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_385])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [C_17,A_13] :
      ( r2_hidden(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_348,plain,(
    ! [B_65,A_66] :
      ( m1_subset_1(B_65,A_66)
      | ~ r2_hidden(B_65,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_354,plain,(
    ! [C_17,A_13] :
      ( m1_subset_1(C_17,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_348])).

tff(c_358,plain,(
    ! [C_17,A_13] :
      ( m1_subset_1(C_17,k1_zfmisc_1(A_13))
      | ~ r1_tarski(C_17,A_13) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_354])).

tff(c_819,plain,(
    ! [A_103,B_104,C_105] :
      ( k4_subset_1(A_103,B_104,C_105) = k2_xboole_0(B_104,C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2331,plain,(
    ! [A_164,B_165,C_166] :
      ( k4_subset_1(A_164,B_165,C_166) = k2_xboole_0(B_165,C_166)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(A_164))
      | ~ r1_tarski(C_166,A_164) ) ),
    inference(resolution,[status(thm)],[c_358,c_819])).

tff(c_2394,plain,(
    ! [C_169] :
      ( k4_subset_1('#skF_3','#skF_4',C_169) = k2_xboole_0('#skF_4',C_169)
      | ~ r1_tarski(C_169,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_2331])).

tff(c_2575,plain,(
    ! [A_174] :
      ( k4_subset_1('#skF_3','#skF_4',A_174) = k2_xboole_0('#skF_4',A_174)
      | k4_xboole_0(A_174,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2394])).

tff(c_40,plain,(
    ! [A_22] : k2_subset_1(A_22) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_53,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_50])).

tff(c_2602,plain,
    ( k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3'
    | k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2575,c_53])).

tff(c_2642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_391,c_2602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:03:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.66  
% 3.87/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.66  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.87/1.66  
% 3.87/1.66  %Foreground sorts:
% 3.87/1.66  
% 3.87/1.66  
% 3.87/1.66  %Background operators:
% 3.87/1.66  
% 3.87/1.66  
% 3.87/1.66  %Foreground operators:
% 3.87/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.87/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.87/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.87/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.87/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.87/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.87/1.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.87/1.66  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.87/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.87/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.87/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.87/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.87/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.87/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.87/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.87/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.87/1.66  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.87/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.87/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.87/1.66  
% 3.87/1.68  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 3.87/1.68  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.87/1.68  tff(f_76, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.87/1.68  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.87/1.68  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.87/1.68  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.87/1.68  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.87/1.68  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.87/1.68  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.87/1.68  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.87/1.68  tff(f_82, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.87/1.68  tff(f_65, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.87/1.68  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.87/1.68  tff(c_394, plain, (![A_71, B_72]: (m1_subset_1(k3_subset_1(A_71, B_72), k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.87/1.68  tff(c_46, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.87/1.68  tff(c_207, plain, (![B_54, A_55]: (r2_hidden(B_54, A_55) | ~m1_subset_1(B_54, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.87/1.68  tff(c_18, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.87/1.68  tff(c_211, plain, (![B_54, A_13]: (r1_tarski(B_54, A_13) | ~m1_subset_1(B_54, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_207, c_18])).
% 3.87/1.68  tff(c_214, plain, (![B_54, A_13]: (r1_tarski(B_54, A_13) | ~m1_subset_1(B_54, k1_zfmisc_1(A_13)))), inference(negUnitSimplification, [status(thm)], [c_46, c_211])).
% 3.87/1.68  tff(c_415, plain, (![A_73, B_74]: (r1_tarski(k3_subset_1(A_73, B_74), A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(resolution, [status(thm)], [c_394, c_214])).
% 3.87/1.68  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.87/1.68  tff(c_452, plain, (![A_79, B_80]: (k4_xboole_0(k3_subset_1(A_79, B_80), A_79)=k1_xboole_0 | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(resolution, [status(thm)], [c_415, c_6])).
% 3.87/1.68  tff(c_465, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_452])).
% 3.87/1.68  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.87/1.68  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.87/1.68  tff(c_215, plain, (![B_56, A_57]: (r1_tarski(B_56, A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)))), inference(negUnitSimplification, [status(thm)], [c_46, c_211])).
% 3.87/1.68  tff(c_224, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_215])).
% 3.87/1.68  tff(c_228, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_224, c_6])).
% 3.87/1.68  tff(c_259, plain, (![A_61, B_62]: (k2_xboole_0(A_61, k4_xboole_0(B_62, A_61))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.87/1.68  tff(c_272, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_228, c_259])).
% 3.87/1.68  tff(c_283, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_272])).
% 3.87/1.68  tff(c_368, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=k3_subset_1(A_69, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.87/1.68  tff(c_381, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_368])).
% 3.87/1.68  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.87/1.68  tff(c_385, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_381, c_10])).
% 3.87/1.68  tff(c_391, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_385])).
% 3.87/1.68  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.87/1.68  tff(c_20, plain, (![C_17, A_13]: (r2_hidden(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.87/1.68  tff(c_348, plain, (![B_65, A_66]: (m1_subset_1(B_65, A_66) | ~r2_hidden(B_65, A_66) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.87/1.68  tff(c_354, plain, (![C_17, A_13]: (m1_subset_1(C_17, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(resolution, [status(thm)], [c_20, c_348])).
% 3.87/1.68  tff(c_358, plain, (![C_17, A_13]: (m1_subset_1(C_17, k1_zfmisc_1(A_13)) | ~r1_tarski(C_17, A_13))), inference(negUnitSimplification, [status(thm)], [c_46, c_354])).
% 3.87/1.68  tff(c_819, plain, (![A_103, B_104, C_105]: (k4_subset_1(A_103, B_104, C_105)=k2_xboole_0(B_104, C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.87/1.68  tff(c_2331, plain, (![A_164, B_165, C_166]: (k4_subset_1(A_164, B_165, C_166)=k2_xboole_0(B_165, C_166) | ~m1_subset_1(B_165, k1_zfmisc_1(A_164)) | ~r1_tarski(C_166, A_164))), inference(resolution, [status(thm)], [c_358, c_819])).
% 3.87/1.68  tff(c_2394, plain, (![C_169]: (k4_subset_1('#skF_3', '#skF_4', C_169)=k2_xboole_0('#skF_4', C_169) | ~r1_tarski(C_169, '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_2331])).
% 3.87/1.68  tff(c_2575, plain, (![A_174]: (k4_subset_1('#skF_3', '#skF_4', A_174)=k2_xboole_0('#skF_4', A_174) | k4_xboole_0(A_174, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2394])).
% 3.87/1.68  tff(c_40, plain, (![A_22]: (k2_subset_1(A_22)=A_22)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.87/1.68  tff(c_50, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.87/1.68  tff(c_53, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_50])).
% 3.87/1.68  tff(c_2602, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3' | k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2575, c_53])).
% 3.87/1.68  tff(c_2642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_465, c_391, c_2602])).
% 3.87/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.68  
% 3.87/1.68  Inference rules
% 3.87/1.68  ----------------------
% 3.87/1.68  #Ref     : 1
% 3.87/1.68  #Sup     : 561
% 3.87/1.68  #Fact    : 0
% 3.87/1.68  #Define  : 0
% 3.87/1.68  #Split   : 3
% 3.87/1.68  #Chain   : 0
% 3.87/1.68  #Close   : 0
% 3.87/1.68  
% 3.87/1.68  Ordering : KBO
% 3.87/1.68  
% 3.87/1.68  Simplification rules
% 3.87/1.68  ----------------------
% 3.87/1.68  #Subsume      : 44
% 3.87/1.68  #Demod        : 405
% 3.87/1.68  #Tautology    : 362
% 3.87/1.68  #SimpNegUnit  : 15
% 3.87/1.68  #BackRed      : 0
% 3.87/1.68  
% 3.87/1.68  #Partial instantiations: 0
% 3.87/1.68  #Strategies tried      : 1
% 3.87/1.68  
% 3.87/1.68  Timing (in seconds)
% 3.87/1.68  ----------------------
% 3.87/1.68  Preprocessing        : 0.33
% 3.87/1.68  Parsing              : 0.17
% 3.87/1.68  CNF conversion       : 0.02
% 3.87/1.68  Main loop            : 0.60
% 3.87/1.68  Inferencing          : 0.22
% 3.87/1.68  Reduction            : 0.21
% 3.87/1.68  Demodulation         : 0.15
% 3.87/1.68  BG Simplification    : 0.03
% 3.87/1.68  Subsumption          : 0.11
% 3.87/1.68  Abstraction          : 0.04
% 3.87/1.68  MUC search           : 0.00
% 3.87/1.68  Cooper               : 0.00
% 3.87/1.68  Total                : 0.95
% 3.87/1.68  Index Insertion      : 0.00
% 3.87/1.68  Index Deletion       : 0.00
% 3.87/1.68  Index Matching       : 0.00
% 3.87/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
