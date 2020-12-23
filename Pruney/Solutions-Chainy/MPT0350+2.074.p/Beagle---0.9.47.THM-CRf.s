%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:35 EST 2020

% Result     : Theorem 16.84s
% Output     : CNFRefutation 16.84s
% Verified   : 
% Statistics : Number of formulae       :   74 (  93 expanded)
%              Number of leaves         :   38 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 123 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_87,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_60,plain,(
    ! [A_34] : k2_subset_1(A_34) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_68,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) != k2_subset_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_71,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_68])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_64,plain,(
    ! [A_37] : ~ v1_xboole_0(k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_162,plain,(
    ! [B_64,A_65] :
      ( r2_hidden(B_64,A_65)
      | ~ m1_subset_1(B_64,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    ! [C_29,A_25] :
      ( r1_tarski(C_29,A_25)
      | ~ r2_hidden(C_29,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_170,plain,(
    ! [B_64,A_25] :
      ( r1_tarski(B_64,A_25)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_25))
      | v1_xboole_0(k1_zfmisc_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_162,c_38])).

tff(c_190,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(B_68,A_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_170])).

tff(c_199,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_190])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_203,plain,(
    k3_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_199,c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_207,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_2])).

tff(c_498,plain,(
    ! [A_96,B_97] :
      ( k4_xboole_0(A_96,B_97) = k3_subset_1(A_96,B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_511,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_498])).

tff(c_277,plain,(
    ! [A_79,B_80] : k2_xboole_0(k3_xboole_0(A_79,B_80),k4_xboole_0(A_79,B_80)) = A_79 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_298,plain,(
    ! [A_1,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_277])).

tff(c_517,plain,(
    k2_xboole_0(k3_xboole_0('#skF_7','#skF_6'),k3_subset_1('#skF_6','#skF_7')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_298])).

tff(c_529,plain,(
    k2_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_2,c_517])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_537,plain,(
    ! [D_98] :
      ( r2_hidden(D_98,'#skF_6')
      | ~ r2_hidden(D_98,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_14])).

tff(c_744,plain,(
    ! [B_117] :
      ( r2_hidden('#skF_1'(k3_subset_1('#skF_6','#skF_7'),B_117),'#skF_6')
      | r1_tarski(k3_subset_1('#skF_6','#skF_7'),B_117) ) ),
    inference(resolution,[status(thm)],[c_8,c_537])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_755,plain,(
    r1_tarski(k3_subset_1('#skF_6','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_744,c_6])).

tff(c_40,plain,(
    ! [C_29,A_25] :
      ( r2_hidden(C_29,k1_zfmisc_1(A_25))
      | ~ r1_tarski(C_29,A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_175,plain,(
    ! [B_66,A_67] :
      ( m1_subset_1(B_66,A_67)
      | ~ r2_hidden(B_66,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_184,plain,(
    ! [C_29,A_25] :
      ( m1_subset_1(C_29,k1_zfmisc_1(A_25))
      | v1_xboole_0(k1_zfmisc_1(A_25))
      | ~ r1_tarski(C_29,A_25) ) ),
    inference(resolution,[status(thm)],[c_40,c_175])).

tff(c_189,plain,(
    ! [C_29,A_25] :
      ( m1_subset_1(C_29,k1_zfmisc_1(A_25))
      | ~ r1_tarski(C_29,A_25) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_184])).

tff(c_1108,plain,(
    ! [A_140,B_141,C_142] :
      ( k4_subset_1(A_140,B_141,C_142) = k2_xboole_0(B_141,C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(A_140))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_44999,plain,(
    ! [A_974,B_975,C_976] :
      ( k4_subset_1(A_974,B_975,C_976) = k2_xboole_0(B_975,C_976)
      | ~ m1_subset_1(B_975,k1_zfmisc_1(A_974))
      | ~ r1_tarski(C_976,A_974) ) ),
    inference(resolution,[status(thm)],[c_189,c_1108])).

tff(c_45061,plain,(
    ! [C_977] :
      ( k4_subset_1('#skF_6','#skF_7',C_977) = k2_xboole_0('#skF_7',C_977)
      | ~ r1_tarski(C_977,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_70,c_44999])).

tff(c_45200,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) = k2_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_755,c_45061])).

tff(c_45247,plain,(
    k4_subset_1('#skF_6','#skF_7',k3_subset_1('#skF_6','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_45200])).

tff(c_45249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_45247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.84/8.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.84/8.58  
% 16.84/8.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.84/8.58  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 16.84/8.58  
% 16.84/8.58  %Foreground sorts:
% 16.84/8.58  
% 16.84/8.58  
% 16.84/8.58  %Background operators:
% 16.84/8.58  
% 16.84/8.58  
% 16.84/8.58  %Foreground operators:
% 16.84/8.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.84/8.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.84/8.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.84/8.58  tff('#skF_7', type, '#skF_7': $i).
% 16.84/8.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.84/8.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.84/8.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.84/8.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.84/8.58  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 16.84/8.58  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 16.84/8.58  tff('#skF_6', type, '#skF_6': $i).
% 16.84/8.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.84/8.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.84/8.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.84/8.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.84/8.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.84/8.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.84/8.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.84/8.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.84/8.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.84/8.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.84/8.58  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 16.84/8.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.84/8.58  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 16.84/8.58  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 16.84/8.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.84/8.58  
% 16.84/8.59  tff(f_80, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 16.84/8.59  tff(f_98, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 16.84/8.59  tff(f_87, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 16.84/8.59  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 16.84/8.59  tff(f_63, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 16.84/8.59  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 16.84/8.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 16.84/8.59  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 16.84/8.59  tff(f_52, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 16.84/8.59  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 16.84/8.59  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 16.84/8.59  tff(f_93, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 16.84/8.59  tff(c_60, plain, (![A_34]: (k2_subset_1(A_34)=A_34)), inference(cnfTransformation, [status(thm)], [f_80])).
% 16.84/8.59  tff(c_68, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))!=k2_subset_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 16.84/8.59  tff(c_71, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_68])).
% 16.84/8.59  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 16.84/8.59  tff(c_64, plain, (![A_37]: (~v1_xboole_0(k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.84/8.59  tff(c_162, plain, (![B_64, A_65]: (r2_hidden(B_64, A_65) | ~m1_subset_1(B_64, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.84/8.59  tff(c_38, plain, (![C_29, A_25]: (r1_tarski(C_29, A_25) | ~r2_hidden(C_29, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.84/8.59  tff(c_170, plain, (![B_64, A_25]: (r1_tarski(B_64, A_25) | ~m1_subset_1(B_64, k1_zfmisc_1(A_25)) | v1_xboole_0(k1_zfmisc_1(A_25)))), inference(resolution, [status(thm)], [c_162, c_38])).
% 16.84/8.59  tff(c_190, plain, (![B_68, A_69]: (r1_tarski(B_68, A_69) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)))), inference(negUnitSimplification, [status(thm)], [c_64, c_170])).
% 16.84/8.59  tff(c_199, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_190])).
% 16.84/8.59  tff(c_30, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.84/8.59  tff(c_203, plain, (k3_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_199, c_30])).
% 16.84/8.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.84/8.59  tff(c_207, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_203, c_2])).
% 16.84/8.59  tff(c_498, plain, (![A_96, B_97]: (k4_xboole_0(A_96, B_97)=k3_subset_1(A_96, B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.84/8.59  tff(c_511, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_498])).
% 16.84/8.59  tff(c_277, plain, (![A_79, B_80]: (k2_xboole_0(k3_xboole_0(A_79, B_80), k4_xboole_0(A_79, B_80))=A_79)), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.84/8.59  tff(c_298, plain, (![A_1, B_2]: (k2_xboole_0(k3_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_277])).
% 16.84/8.59  tff(c_517, plain, (k2_xboole_0(k3_xboole_0('#skF_7', '#skF_6'), k3_subset_1('#skF_6', '#skF_7'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_511, c_298])).
% 16.84/8.59  tff(c_529, plain, (k2_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_207, c_2, c_517])).
% 16.84/8.59  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.84/8.59  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.84/8.59  tff(c_537, plain, (![D_98]: (r2_hidden(D_98, '#skF_6') | ~r2_hidden(D_98, k3_subset_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_511, c_14])).
% 16.84/8.59  tff(c_744, plain, (![B_117]: (r2_hidden('#skF_1'(k3_subset_1('#skF_6', '#skF_7'), B_117), '#skF_6') | r1_tarski(k3_subset_1('#skF_6', '#skF_7'), B_117))), inference(resolution, [status(thm)], [c_8, c_537])).
% 16.84/8.59  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.84/8.59  tff(c_755, plain, (r1_tarski(k3_subset_1('#skF_6', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_744, c_6])).
% 16.84/8.59  tff(c_40, plain, (![C_29, A_25]: (r2_hidden(C_29, k1_zfmisc_1(A_25)) | ~r1_tarski(C_29, A_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.84/8.59  tff(c_175, plain, (![B_66, A_67]: (m1_subset_1(B_66, A_67) | ~r2_hidden(B_66, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.84/8.59  tff(c_184, plain, (![C_29, A_25]: (m1_subset_1(C_29, k1_zfmisc_1(A_25)) | v1_xboole_0(k1_zfmisc_1(A_25)) | ~r1_tarski(C_29, A_25))), inference(resolution, [status(thm)], [c_40, c_175])).
% 16.84/8.59  tff(c_189, plain, (![C_29, A_25]: (m1_subset_1(C_29, k1_zfmisc_1(A_25)) | ~r1_tarski(C_29, A_25))), inference(negUnitSimplification, [status(thm)], [c_64, c_184])).
% 16.84/8.59  tff(c_1108, plain, (![A_140, B_141, C_142]: (k4_subset_1(A_140, B_141, C_142)=k2_xboole_0(B_141, C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(A_140)) | ~m1_subset_1(B_141, k1_zfmisc_1(A_140)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 16.84/8.59  tff(c_44999, plain, (![A_974, B_975, C_976]: (k4_subset_1(A_974, B_975, C_976)=k2_xboole_0(B_975, C_976) | ~m1_subset_1(B_975, k1_zfmisc_1(A_974)) | ~r1_tarski(C_976, A_974))), inference(resolution, [status(thm)], [c_189, c_1108])).
% 16.84/8.59  tff(c_45061, plain, (![C_977]: (k4_subset_1('#skF_6', '#skF_7', C_977)=k2_xboole_0('#skF_7', C_977) | ~r1_tarski(C_977, '#skF_6'))), inference(resolution, [status(thm)], [c_70, c_44999])).
% 16.84/8.59  tff(c_45200, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))=k2_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_755, c_45061])).
% 16.84/8.59  tff(c_45247, plain, (k4_subset_1('#skF_6', '#skF_7', k3_subset_1('#skF_6', '#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_529, c_45200])).
% 16.84/8.59  tff(c_45249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_45247])).
% 16.84/8.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.84/8.59  
% 16.84/8.59  Inference rules
% 16.84/8.59  ----------------------
% 16.84/8.59  #Ref     : 0
% 16.84/8.59  #Sup     : 12361
% 16.84/8.59  #Fact    : 0
% 16.84/8.59  #Define  : 0
% 16.84/8.59  #Split   : 11
% 16.84/8.59  #Chain   : 0
% 16.84/8.59  #Close   : 0
% 16.84/8.59  
% 16.84/8.59  Ordering : KBO
% 16.84/8.59  
% 16.84/8.59  Simplification rules
% 16.84/8.59  ----------------------
% 16.84/8.59  #Subsume      : 2861
% 16.84/8.59  #Demod        : 5766
% 16.84/8.59  #Tautology    : 2755
% 16.84/8.59  #SimpNegUnit  : 133
% 16.84/8.59  #BackRed      : 65
% 16.84/8.59  
% 16.84/8.59  #Partial instantiations: 0
% 16.84/8.59  #Strategies tried      : 1
% 16.84/8.59  
% 16.84/8.59  Timing (in seconds)
% 16.84/8.59  ----------------------
% 16.84/8.60  Preprocessing        : 0.35
% 16.84/8.60  Parsing              : 0.18
% 16.84/8.60  CNF conversion       : 0.03
% 16.84/8.60  Main loop            : 7.43
% 16.84/8.60  Inferencing          : 1.27
% 16.84/8.60  Reduction            : 3.61
% 16.84/8.60  Demodulation         : 3.02
% 16.84/8.60  BG Simplification    : 0.17
% 16.84/8.60  Subsumption          : 1.93
% 16.84/8.60  Abstraction          : 0.23
% 16.84/8.60  MUC search           : 0.00
% 16.84/8.60  Cooper               : 0.00
% 16.84/8.60  Total                : 7.81
% 16.84/8.60  Index Insertion      : 0.00
% 16.84/8.60  Index Deletion       : 0.00
% 16.84/8.60  Index Matching       : 0.00
% 16.84/8.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
