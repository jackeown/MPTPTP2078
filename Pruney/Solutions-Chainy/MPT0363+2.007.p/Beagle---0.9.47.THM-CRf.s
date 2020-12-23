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
% DateTime   : Thu Dec  3 09:56:37 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 117 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :   98 ( 194 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_75,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_55,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_875,plain,(
    ! [B_104,A_105] :
      ( r2_hidden(B_104,A_105)
      | ~ m1_subset_1(B_104,A_105)
      | v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_19] : k3_tarski(k1_zfmisc_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,k3_tarski(B_35))
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_96,plain,(
    ! [A_34,A_19] :
      ( r1_tarski(A_34,A_19)
      | ~ r2_hidden(A_34,k1_zfmisc_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_90])).

tff(c_882,plain,(
    ! [B_104,A_19] :
      ( r1_tarski(B_104,A_19)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_875,c_96])).

tff(c_909,plain,(
    ! [B_108,A_109] :
      ( r1_tarski(B_108,A_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_109)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_882])).

tff(c_922,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_909])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_107,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_133,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_44])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_314,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_326,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_314])).

tff(c_202,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(B_55,A_56)
      | ~ m1_subset_1(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_209,plain,(
    ! [B_55,A_19] :
      ( r1_tarski(B_55,A_19)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_202,c_96])).

tff(c_214,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(B_57,A_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_209])).

tff(c_226,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_214])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_231,plain,(
    k3_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_226,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_177,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_415,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(B_65,A_64)) = k4_xboole_0(A_64,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_177])).

tff(c_443,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_415])).

tff(c_464,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_443])).

tff(c_122,plain,(
    ! [A_42,B_43] : r1_xboole_0(k3_xboole_0(A_42,B_43),k5_xboole_0(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [A_1,B_2] : r1_xboole_0(k3_xboole_0(A_1,B_2),k5_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_122])).

tff(c_242,plain,(
    r1_xboole_0('#skF_3',k5_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_131])).

tff(c_470,plain,(
    r1_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_242])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_491,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_470,c_10])).

tff(c_14,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_xboole_0(A_11,k4_xboole_0(C_13,B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_800,plain,(
    ! [A_86] :
      ( r1_xboole_0(A_86,'#skF_3')
      | ~ r1_tarski(A_86,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_14])).

tff(c_806,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_800])).

tff(c_811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_806])).

tff(c_813,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_981,plain,(
    ! [A_110,B_111] :
      ( k4_xboole_0(A_110,B_111) = k3_subset_1(A_110,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_993,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_981])).

tff(c_1034,plain,(
    ! [A_112,B_113,C_114] :
      ( r1_tarski(A_112,k4_xboole_0(B_113,C_114))
      | ~ r1_xboole_0(A_112,C_114)
      | ~ r1_tarski(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1758,plain,(
    ! [A_153] :
      ( r1_tarski(A_153,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_xboole_0(A_153,'#skF_3')
      | ~ r1_tarski(A_153,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_1034])).

tff(c_812,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1764,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_1758,c_812])).

tff(c_1772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_922,c_813,c_1764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.64  
% 3.62/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.62/1.64  
% 3.62/1.64  %Foreground sorts:
% 3.62/1.64  
% 3.62/1.64  
% 3.62/1.64  %Background operators:
% 3.62/1.64  
% 3.62/1.64  
% 3.62/1.64  %Foreground operators:
% 3.62/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.62/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.62/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.62/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.62/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.62/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.62/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.62/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.62/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.62/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.64  
% 3.62/1.66  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 3.62/1.66  tff(f_75, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.62/1.66  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.62/1.66  tff(f_55, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.62/1.66  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.62/1.66  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.62/1.66  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.62/1.66  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.62/1.66  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.62/1.66  tff(f_29, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.62/1.66  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.62/1.66  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.62/1.66  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.62/1.66  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.62/1.66  tff(c_32, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.62/1.66  tff(c_875, plain, (![B_104, A_105]: (r2_hidden(B_104, A_105) | ~m1_subset_1(B_104, A_105) | v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.62/1.66  tff(c_20, plain, (![A_19]: (k3_tarski(k1_zfmisc_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.62/1.66  tff(c_90, plain, (![A_34, B_35]: (r1_tarski(A_34, k3_tarski(B_35)) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.62/1.66  tff(c_96, plain, (![A_34, A_19]: (r1_tarski(A_34, A_19) | ~r2_hidden(A_34, k1_zfmisc_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_90])).
% 3.62/1.66  tff(c_882, plain, (![B_104, A_19]: (r1_tarski(B_104, A_19) | ~m1_subset_1(B_104, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_875, c_96])).
% 3.62/1.66  tff(c_909, plain, (![B_108, A_109]: (r1_tarski(B_108, A_109) | ~m1_subset_1(B_108, k1_zfmisc_1(A_109)))), inference(negUnitSimplification, [status(thm)], [c_32, c_882])).
% 3.62/1.66  tff(c_922, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_909])).
% 3.62/1.66  tff(c_38, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.62/1.66  tff(c_107, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 3.62/1.66  tff(c_44, plain, (r1_xboole_0('#skF_2', '#skF_3') | r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.62/1.66  tff(c_133, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_107, c_44])).
% 3.62/1.66  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.62/1.66  tff(c_314, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.62/1.66  tff(c_326, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_314])).
% 3.62/1.66  tff(c_202, plain, (![B_55, A_56]: (r2_hidden(B_55, A_56) | ~m1_subset_1(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.62/1.66  tff(c_209, plain, (![B_55, A_19]: (r1_tarski(B_55, A_19) | ~m1_subset_1(B_55, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_202, c_96])).
% 3.62/1.66  tff(c_214, plain, (![B_57, A_58]: (r1_tarski(B_57, A_58) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)))), inference(negUnitSimplification, [status(thm)], [c_32, c_209])).
% 3.62/1.66  tff(c_226, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_214])).
% 3.62/1.66  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.62/1.66  tff(c_231, plain, (k3_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_226, c_8])).
% 3.62/1.66  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.62/1.66  tff(c_177, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.62/1.66  tff(c_415, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(B_65, A_64))=k4_xboole_0(A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_2, c_177])).
% 3.62/1.66  tff(c_443, plain, (k5_xboole_0('#skF_1', '#skF_3')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_231, c_415])).
% 3.62/1.66  tff(c_464, plain, (k5_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_443])).
% 3.62/1.66  tff(c_122, plain, (![A_42, B_43]: (r1_xboole_0(k3_xboole_0(A_42, B_43), k5_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.62/1.66  tff(c_131, plain, (![A_1, B_2]: (r1_xboole_0(k3_xboole_0(A_1, B_2), k5_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_122])).
% 3.62/1.66  tff(c_242, plain, (r1_xboole_0('#skF_3', k5_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_131])).
% 3.62/1.66  tff(c_470, plain, (r1_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_242])).
% 3.62/1.66  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.62/1.66  tff(c_491, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_470, c_10])).
% 3.62/1.66  tff(c_14, plain, (![A_11, C_13, B_12]: (r1_xboole_0(A_11, k4_xboole_0(C_13, B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.62/1.66  tff(c_800, plain, (![A_86]: (r1_xboole_0(A_86, '#skF_3') | ~r1_tarski(A_86, k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_491, c_14])).
% 3.62/1.66  tff(c_806, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_133, c_800])).
% 3.62/1.66  tff(c_811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_806])).
% 3.62/1.66  tff(c_813, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.62/1.66  tff(c_981, plain, (![A_110, B_111]: (k4_xboole_0(A_110, B_111)=k3_subset_1(A_110, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.62/1.66  tff(c_993, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_981])).
% 3.62/1.66  tff(c_1034, plain, (![A_112, B_113, C_114]: (r1_tarski(A_112, k4_xboole_0(B_113, C_114)) | ~r1_xboole_0(A_112, C_114) | ~r1_tarski(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.62/1.66  tff(c_1758, plain, (![A_153]: (r1_tarski(A_153, k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0(A_153, '#skF_3') | ~r1_tarski(A_153, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_993, c_1034])).
% 3.62/1.66  tff(c_812, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_38])).
% 3.62/1.66  tff(c_1764, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_1758, c_812])).
% 3.62/1.66  tff(c_1772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_922, c_813, c_1764])).
% 3.62/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.66  
% 3.62/1.66  Inference rules
% 3.62/1.66  ----------------------
% 3.62/1.66  #Ref     : 0
% 3.62/1.66  #Sup     : 467
% 3.62/1.66  #Fact    : 0
% 3.62/1.66  #Define  : 0
% 3.62/1.66  #Split   : 1
% 3.62/1.66  #Chain   : 0
% 3.62/1.66  #Close   : 0
% 3.62/1.66  
% 3.62/1.66  Ordering : KBO
% 3.62/1.66  
% 3.62/1.66  Simplification rules
% 3.62/1.66  ----------------------
% 3.62/1.66  #Subsume      : 26
% 3.62/1.66  #Demod        : 180
% 3.62/1.66  #Tautology    : 235
% 3.62/1.66  #SimpNegUnit  : 10
% 3.62/1.66  #BackRed      : 5
% 3.62/1.66  
% 3.62/1.66  #Partial instantiations: 0
% 3.62/1.66  #Strategies tried      : 1
% 3.62/1.66  
% 3.62/1.66  Timing (in seconds)
% 3.62/1.66  ----------------------
% 3.62/1.66  Preprocessing        : 0.32
% 3.62/1.66  Parsing              : 0.17
% 3.62/1.66  CNF conversion       : 0.02
% 3.62/1.66  Main loop            : 0.51
% 3.62/1.66  Inferencing          : 0.19
% 3.62/1.66  Reduction            : 0.18
% 3.62/1.66  Demodulation         : 0.13
% 3.62/1.66  BG Simplification    : 0.02
% 3.62/1.66  Subsumption          : 0.08
% 3.62/1.66  Abstraction          : 0.02
% 3.62/1.66  MUC search           : 0.00
% 3.62/1.66  Cooper               : 0.00
% 3.62/1.66  Total                : 0.86
% 3.62/1.66  Index Insertion      : 0.00
% 3.62/1.66  Index Deletion       : 0.00
% 3.62/1.66  Index Matching       : 0.00
% 3.62/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
