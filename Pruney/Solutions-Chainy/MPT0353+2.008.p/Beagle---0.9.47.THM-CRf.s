%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:53 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   71 (  99 expanded)
%              Number of leaves         :   33 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 129 expanded)
%              Number of equality atoms :   35 (  53 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_66,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_61,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_64,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_218,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k3_subset_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_235,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_218])).

tff(c_36,plain,(
    ! [A_22,B_23] : k6_subset_1(A_22,B_23) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [A_19,B_20] : m1_subset_1(k6_subset_1(A_19,B_20),k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_47,plain,(
    ! [A_19,B_20] : m1_subset_1(k4_xboole_0(A_19,B_20),k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32])).

tff(c_256,plain,(
    m1_subset_1(k3_subset_1('#skF_3','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_47])).

tff(c_303,plain,(
    ! [A_60,B_61,C_62] :
      ( k9_subset_1(A_60,B_61,C_62) = k3_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_318,plain,(
    ! [B_61] : k9_subset_1('#skF_3',B_61,k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0(B_61,k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_256,c_303])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_482,plain,(
    ! [A_71,B_72,C_73] :
      ( k7_subset_1(A_71,B_72,C_73) = k4_xboole_0(B_72,C_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_503,plain,(
    ! [C_73] : k7_subset_1('#skF_3','#skF_4',C_73) = k4_xboole_0('#skF_4',C_73) ),
    inference(resolution,[status(thm)],[c_46,c_482])).

tff(c_42,plain,(
    k9_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_5')) != k7_subset_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_505,plain,(
    k9_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_5')) != k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_42])).

tff(c_1640,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) != k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_505])).

tff(c_34,plain,(
    ! [A_21] : ~ v1_xboole_0(k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_132,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,A_51)
      | ~ m1_subset_1(B_50,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_136,plain,(
    ! [B_50,A_10] :
      ( r1_tarski(B_50,A_10)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_132,c_10])).

tff(c_140,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_136])).

tff(c_157,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_140])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_176,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_157,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_190,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_206,plain,(
    k5_xboole_0('#skF_3','#skF_5') = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_4])).

tff(c_298,plain,(
    k5_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_206])).

tff(c_117,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_126,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_156,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_140])).

tff(c_172,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_156,c_8])).

tff(c_561,plain,(
    ! [A_78,B_79,C_80] : k5_xboole_0(k3_xboole_0(A_78,B_79),k3_xboole_0(C_80,B_79)) = k3_xboole_0(k5_xboole_0(A_78,C_80),B_79) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2399,plain,(
    ! [A_137,B_138,C_139] : k5_xboole_0(k3_xboole_0(A_137,B_138),k3_xboole_0(C_139,A_137)) = k3_xboole_0(k5_xboole_0(B_138,C_139),A_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_561])).

tff(c_2516,plain,(
    ! [C_139] : k5_xboole_0('#skF_4',k3_xboole_0(C_139,'#skF_4')) = k3_xboole_0(k5_xboole_0('#skF_3',C_139),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_2399])).

tff(c_2574,plain,(
    ! [C_140] : k3_xboole_0('#skF_4',k5_xboole_0('#skF_3',C_140)) = k4_xboole_0('#skF_4',C_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_2,c_2516])).

tff(c_2630,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_2574])).

tff(c_2641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1640,c_2630])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.74  
% 4.09/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.74  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.09/1.74  
% 4.09/1.74  %Foreground sorts:
% 4.09/1.74  
% 4.09/1.74  
% 4.09/1.74  %Background operators:
% 4.09/1.74  
% 4.09/1.74  
% 4.09/1.74  %Foreground operators:
% 4.09/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.09/1.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.09/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.74  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.09/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.09/1.74  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.09/1.74  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.09/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.09/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.09/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.09/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.09/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.09/1.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.09/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.09/1.74  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.09/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.09/1.74  
% 4.09/1.76  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 4.09/1.76  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.09/1.76  tff(f_66, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.09/1.76  tff(f_61, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 4.09/1.76  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.09/1.76  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.09/1.76  tff(f_64, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.09/1.76  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.09/1.76  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.09/1.76  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.09/1.76  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.09/1.76  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.09/1.76  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 4.09/1.76  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.09/1.76  tff(c_218, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k3_subset_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.09/1.76  tff(c_235, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_218])).
% 4.09/1.76  tff(c_36, plain, (![A_22, B_23]: (k6_subset_1(A_22, B_23)=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.09/1.76  tff(c_32, plain, (![A_19, B_20]: (m1_subset_1(k6_subset_1(A_19, B_20), k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.09/1.76  tff(c_47, plain, (![A_19, B_20]: (m1_subset_1(k4_xboole_0(A_19, B_20), k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32])).
% 4.09/1.76  tff(c_256, plain, (m1_subset_1(k3_subset_1('#skF_3', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_235, c_47])).
% 4.09/1.76  tff(c_303, plain, (![A_60, B_61, C_62]: (k9_subset_1(A_60, B_61, C_62)=k3_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.09/1.76  tff(c_318, plain, (![B_61]: (k9_subset_1('#skF_3', B_61, k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0(B_61, k3_subset_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_256, c_303])).
% 4.09/1.76  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.09/1.76  tff(c_482, plain, (![A_71, B_72, C_73]: (k7_subset_1(A_71, B_72, C_73)=k4_xboole_0(B_72, C_73) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.09/1.76  tff(c_503, plain, (![C_73]: (k7_subset_1('#skF_3', '#skF_4', C_73)=k4_xboole_0('#skF_4', C_73))), inference(resolution, [status(thm)], [c_46, c_482])).
% 4.09/1.76  tff(c_42, plain, (k9_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k7_subset_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.09/1.76  tff(c_505, plain, (k9_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_42])).
% 4.09/1.76  tff(c_1640, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_505])).
% 4.09/1.76  tff(c_34, plain, (![A_21]: (~v1_xboole_0(k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.09/1.76  tff(c_132, plain, (![B_50, A_51]: (r2_hidden(B_50, A_51) | ~m1_subset_1(B_50, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.09/1.76  tff(c_10, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.09/1.76  tff(c_136, plain, (![B_50, A_10]: (r1_tarski(B_50, A_10) | ~m1_subset_1(B_50, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_132, c_10])).
% 4.09/1.76  tff(c_140, plain, (![B_52, A_53]: (r1_tarski(B_52, A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)))), inference(negUnitSimplification, [status(thm)], [c_34, c_136])).
% 4.09/1.76  tff(c_157, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_140])).
% 4.09/1.76  tff(c_8, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.09/1.76  tff(c_176, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_157, c_8])).
% 4.09/1.76  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.09/1.76  tff(c_190, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_176, c_2])).
% 4.09/1.76  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.09/1.76  tff(c_206, plain, (k5_xboole_0('#skF_3', '#skF_5')=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_190, c_4])).
% 4.09/1.76  tff(c_298, plain, (k5_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_206])).
% 4.09/1.76  tff(c_117, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.09/1.76  tff(c_126, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_117])).
% 4.09/1.76  tff(c_156, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_140])).
% 4.09/1.76  tff(c_172, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_156, c_8])).
% 4.09/1.76  tff(c_561, plain, (![A_78, B_79, C_80]: (k5_xboole_0(k3_xboole_0(A_78, B_79), k3_xboole_0(C_80, B_79))=k3_xboole_0(k5_xboole_0(A_78, C_80), B_79))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.09/1.76  tff(c_2399, plain, (![A_137, B_138, C_139]: (k5_xboole_0(k3_xboole_0(A_137, B_138), k3_xboole_0(C_139, A_137))=k3_xboole_0(k5_xboole_0(B_138, C_139), A_137))), inference(superposition, [status(thm), theory('equality')], [c_2, c_561])).
% 4.09/1.76  tff(c_2516, plain, (![C_139]: (k5_xboole_0('#skF_4', k3_xboole_0(C_139, '#skF_4'))=k3_xboole_0(k5_xboole_0('#skF_3', C_139), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_2399])).
% 4.09/1.76  tff(c_2574, plain, (![C_140]: (k3_xboole_0('#skF_4', k5_xboole_0('#skF_3', C_140))=k4_xboole_0('#skF_4', C_140))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_2, c_2516])).
% 4.09/1.76  tff(c_2630, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_298, c_2574])).
% 4.09/1.76  tff(c_2641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1640, c_2630])).
% 4.09/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.76  
% 4.09/1.76  Inference rules
% 4.09/1.76  ----------------------
% 4.09/1.76  #Ref     : 0
% 4.09/1.76  #Sup     : 703
% 4.09/1.76  #Fact    : 0
% 4.09/1.76  #Define  : 0
% 4.09/1.76  #Split   : 0
% 4.09/1.76  #Chain   : 0
% 4.09/1.76  #Close   : 0
% 4.09/1.76  
% 4.09/1.76  Ordering : KBO
% 4.09/1.76  
% 4.09/1.76  Simplification rules
% 4.09/1.76  ----------------------
% 4.09/1.76  #Subsume      : 19
% 4.09/1.76  #Demod        : 361
% 4.09/1.76  #Tautology    : 235
% 4.09/1.76  #SimpNegUnit  : 3
% 4.09/1.76  #BackRed      : 3
% 4.09/1.76  
% 4.09/1.76  #Partial instantiations: 0
% 4.09/1.76  #Strategies tried      : 1
% 4.09/1.76  
% 4.09/1.76  Timing (in seconds)
% 4.09/1.76  ----------------------
% 4.09/1.76  Preprocessing        : 0.32
% 4.09/1.76  Parsing              : 0.17
% 4.09/1.76  CNF conversion       : 0.02
% 4.09/1.76  Main loop            : 0.68
% 4.09/1.76  Inferencing          : 0.21
% 4.09/1.76  Reduction            : 0.28
% 4.09/1.76  Demodulation         : 0.22
% 4.09/1.76  BG Simplification    : 0.03
% 4.09/1.76  Subsumption          : 0.11
% 4.09/1.76  Abstraction          : 0.04
% 4.09/1.76  MUC search           : 0.00
% 4.09/1.76  Cooper               : 0.00
% 4.09/1.76  Total                : 1.03
% 4.09/1.76  Index Insertion      : 0.00
% 4.09/1.76  Index Deletion       : 0.00
% 4.09/1.76  Index Matching       : 0.00
% 4.09/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
