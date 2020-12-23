%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:53 EST 2020

% Result     : Theorem 5.24s
% Output     : CNFRefutation 5.48s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 104 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 149 expanded)
%              Number of equality atoms :   34 (  53 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_64,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_308,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k3_subset_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_325,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_308])).

tff(c_34,plain,(
    ! [A_21] : ~ v1_xboole_0(k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_105,plain,(
    ! [B_44,A_45] :
      ( r2_hidden(B_44,A_45)
      | ~ m1_subset_1(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_109,plain,(
    ! [B_44,A_12] :
      ( r1_tarski(B_44,A_12)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_105,c_12])).

tff(c_113,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(B_46,A_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_109])).

tff(c_126,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_113])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_134,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_126,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_163,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_179,plain,(
    k5_xboole_0('#skF_3','#skF_5') = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_4])).

tff(c_346,plain,(
    k5_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_179])).

tff(c_135,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_147,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_125,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_113])).

tff(c_130,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_125,c_8])).

tff(c_553,plain,(
    ! [A_76,B_77,C_78] : k5_xboole_0(k3_xboole_0(A_76,B_77),k3_xboole_0(C_78,B_77)) = k3_xboole_0(k5_xboole_0(A_76,C_78),B_77) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2338,plain,(
    ! [B_127,A_128,C_129] : k5_xboole_0(k3_xboole_0(B_127,A_128),k3_xboole_0(C_129,B_127)) = k3_xboole_0(k5_xboole_0(A_128,C_129),B_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_553])).

tff(c_2475,plain,(
    ! [C_129] : k5_xboole_0('#skF_4',k3_xboole_0(C_129,'#skF_4')) = k3_xboole_0(k5_xboole_0('#skF_3',C_129),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_2338])).

tff(c_2537,plain,(
    ! [C_130] : k3_xboole_0('#skF_4',k5_xboole_0('#skF_3',C_130)) = k4_xboole_0('#skF_4',C_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2,c_2475])).

tff(c_2598,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_2537])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_356,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_10])).

tff(c_14,plain,(
    ! [C_16,A_12] :
      ( r2_hidden(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_198,plain,(
    ! [B_50,A_51] :
      ( m1_subset_1(B_50,A_51)
      | ~ r2_hidden(B_50,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_204,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_198])).

tff(c_208,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_204])).

tff(c_476,plain,(
    ! [A_67,B_68,C_69] :
      ( k9_subset_1(A_67,B_68,C_69) = k3_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1275,plain,(
    ! [A_96,B_97,C_98] :
      ( k9_subset_1(A_96,B_97,C_98) = k3_xboole_0(B_97,C_98)
      | ~ r1_tarski(C_98,A_96) ) ),
    inference(resolution,[status(thm)],[c_208,c_476])).

tff(c_1301,plain,(
    ! [B_97] : k9_subset_1('#skF_3',B_97,k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0(B_97,k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_356,c_1275])).

tff(c_428,plain,(
    ! [A_62,B_63,C_64] :
      ( k7_subset_1(A_62,B_63,C_64) = k4_xboole_0(B_63,C_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_440,plain,(
    ! [C_64] : k7_subset_1('#skF_3','#skF_4',C_64) = k4_xboole_0('#skF_4',C_64) ),
    inference(resolution,[status(thm)],[c_44,c_428])).

tff(c_40,plain,(
    k9_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_5')) != k7_subset_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_442,plain,(
    k9_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_5')) != k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_40])).

tff(c_3132,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) != k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1301,c_442])).

tff(c_3135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2598,c_3132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:53:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.24/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/2.02  
% 5.24/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/2.02  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.24/2.02  
% 5.24/2.02  %Foreground sorts:
% 5.24/2.02  
% 5.24/2.02  
% 5.24/2.02  %Background operators:
% 5.24/2.02  
% 5.24/2.02  
% 5.24/2.02  %Foreground operators:
% 5.24/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.24/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.24/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.24/2.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.24/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.24/2.02  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.24/2.02  tff('#skF_5', type, '#skF_5': $i).
% 5.24/2.02  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.24/2.02  tff('#skF_3', type, '#skF_3': $i).
% 5.24/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.24/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.24/2.02  tff('#skF_4', type, '#skF_4': $i).
% 5.24/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.24/2.02  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.24/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.24/2.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.24/2.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.24/2.02  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.24/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.24/2.02  
% 5.48/2.03  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 5.48/2.03  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.48/2.03  tff(f_64, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.48/2.03  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.48/2.03  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.48/2.03  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.48/2.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.48/2.03  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.48/2.03  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 5.48/2.03  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.48/2.03  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.48/2.03  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.48/2.03  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.48/2.03  tff(c_308, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k3_subset_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.48/2.03  tff(c_325, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_308])).
% 5.48/2.03  tff(c_34, plain, (![A_21]: (~v1_xboole_0(k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.48/2.03  tff(c_105, plain, (![B_44, A_45]: (r2_hidden(B_44, A_45) | ~m1_subset_1(B_44, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.48/2.03  tff(c_12, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.48/2.03  tff(c_109, plain, (![B_44, A_12]: (r1_tarski(B_44, A_12) | ~m1_subset_1(B_44, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_105, c_12])).
% 5.48/2.03  tff(c_113, plain, (![B_46, A_47]: (r1_tarski(B_46, A_47) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)))), inference(negUnitSimplification, [status(thm)], [c_34, c_109])).
% 5.48/2.03  tff(c_126, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_113])).
% 5.48/2.03  tff(c_8, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.48/2.03  tff(c_134, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_126, c_8])).
% 5.48/2.03  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.48/2.03  tff(c_163, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_134, c_2])).
% 5.48/2.03  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.48/2.03  tff(c_179, plain, (k5_xboole_0('#skF_3', '#skF_5')=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_163, c_4])).
% 5.48/2.03  tff(c_346, plain, (k5_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_325, c_179])).
% 5.48/2.03  tff(c_135, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.48/2.03  tff(c_147, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_135])).
% 5.48/2.03  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.48/2.03  tff(c_125, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_113])).
% 5.48/2.03  tff(c_130, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_125, c_8])).
% 5.48/2.03  tff(c_553, plain, (![A_76, B_77, C_78]: (k5_xboole_0(k3_xboole_0(A_76, B_77), k3_xboole_0(C_78, B_77))=k3_xboole_0(k5_xboole_0(A_76, C_78), B_77))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.48/2.03  tff(c_2338, plain, (![B_127, A_128, C_129]: (k5_xboole_0(k3_xboole_0(B_127, A_128), k3_xboole_0(C_129, B_127))=k3_xboole_0(k5_xboole_0(A_128, C_129), B_127))), inference(superposition, [status(thm), theory('equality')], [c_2, c_553])).
% 5.48/2.03  tff(c_2475, plain, (![C_129]: (k5_xboole_0('#skF_4', k3_xboole_0(C_129, '#skF_4'))=k3_xboole_0(k5_xboole_0('#skF_3', C_129), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_2338])).
% 5.48/2.03  tff(c_2537, plain, (![C_130]: (k3_xboole_0('#skF_4', k5_xboole_0('#skF_3', C_130))=k4_xboole_0('#skF_4', C_130))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2, c_2475])).
% 5.48/2.03  tff(c_2598, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_346, c_2537])).
% 5.48/2.03  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.48/2.03  tff(c_356, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_325, c_10])).
% 5.48/2.03  tff(c_14, plain, (![C_16, A_12]: (r2_hidden(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.48/2.03  tff(c_198, plain, (![B_50, A_51]: (m1_subset_1(B_50, A_51) | ~r2_hidden(B_50, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.48/2.03  tff(c_204, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(resolution, [status(thm)], [c_14, c_198])).
% 5.48/2.03  tff(c_208, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(negUnitSimplification, [status(thm)], [c_34, c_204])).
% 5.48/2.03  tff(c_476, plain, (![A_67, B_68, C_69]: (k9_subset_1(A_67, B_68, C_69)=k3_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.48/2.03  tff(c_1275, plain, (![A_96, B_97, C_98]: (k9_subset_1(A_96, B_97, C_98)=k3_xboole_0(B_97, C_98) | ~r1_tarski(C_98, A_96))), inference(resolution, [status(thm)], [c_208, c_476])).
% 5.48/2.03  tff(c_1301, plain, (![B_97]: (k9_subset_1('#skF_3', B_97, k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0(B_97, k3_subset_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_356, c_1275])).
% 5.48/2.03  tff(c_428, plain, (![A_62, B_63, C_64]: (k7_subset_1(A_62, B_63, C_64)=k4_xboole_0(B_63, C_64) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.48/2.03  tff(c_440, plain, (![C_64]: (k7_subset_1('#skF_3', '#skF_4', C_64)=k4_xboole_0('#skF_4', C_64))), inference(resolution, [status(thm)], [c_44, c_428])).
% 5.48/2.03  tff(c_40, plain, (k9_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k7_subset_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.48/2.03  tff(c_442, plain, (k9_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_440, c_40])).
% 5.48/2.03  tff(c_3132, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1301, c_442])).
% 5.48/2.03  tff(c_3135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2598, c_3132])).
% 5.48/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.48/2.03  
% 5.48/2.03  Inference rules
% 5.48/2.03  ----------------------
% 5.48/2.03  #Ref     : 0
% 5.48/2.03  #Sup     : 837
% 5.48/2.03  #Fact    : 0
% 5.48/2.03  #Define  : 0
% 5.48/2.03  #Split   : 0
% 5.48/2.03  #Chain   : 0
% 5.48/2.03  #Close   : 0
% 5.48/2.03  
% 5.48/2.03  Ordering : KBO
% 5.48/2.03  
% 5.48/2.03  Simplification rules
% 5.48/2.03  ----------------------
% 5.48/2.03  #Subsume      : 22
% 5.48/2.03  #Demod        : 405
% 5.48/2.03  #Tautology    : 269
% 5.48/2.03  #SimpNegUnit  : 2
% 5.48/2.03  #BackRed      : 6
% 5.48/2.03  
% 5.48/2.03  #Partial instantiations: 0
% 5.48/2.03  #Strategies tried      : 1
% 5.48/2.03  
% 5.48/2.03  Timing (in seconds)
% 5.48/2.03  ----------------------
% 5.48/2.04  Preprocessing        : 0.33
% 5.48/2.04  Parsing              : 0.17
% 5.48/2.04  CNF conversion       : 0.02
% 5.48/2.04  Main loop            : 0.92
% 5.48/2.04  Inferencing          : 0.30
% 5.48/2.04  Reduction            : 0.38
% 5.48/2.04  Demodulation         : 0.30
% 5.48/2.04  BG Simplification    : 0.04
% 5.48/2.04  Subsumption          : 0.14
% 5.48/2.04  Abstraction          : 0.05
% 5.48/2.04  MUC search           : 0.00
% 5.48/2.04  Cooper               : 0.00
% 5.48/2.04  Total                : 1.29
% 5.48/2.04  Index Insertion      : 0.00
% 5.48/2.04  Index Deletion       : 0.00
% 5.48/2.04  Index Matching       : 0.00
% 5.48/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
