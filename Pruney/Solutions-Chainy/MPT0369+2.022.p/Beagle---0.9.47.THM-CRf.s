%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:54 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   79 (  99 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :   97 ( 164 expanded)
%              Number of equality atoms :   32 (  44 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_79,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_58,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_111,plain,(
    ! [B_44,A_45] :
      ( v1_xboole_0(B_44)
      | ~ m1_subset_1(B_44,A_45)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_123,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_111])).

tff(c_124,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_44,plain,(
    ! [B_22,A_21] :
      ( r2_hidden(B_22,A_21)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_56,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_92,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    ! [A_11] : k3_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_92])).

tff(c_200,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = k4_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_212,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_200])).

tff(c_217,plain,(
    ! [A_58] : k4_xboole_0(k1_xboole_0,A_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_212])).

tff(c_28,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_222,plain,(
    ! [A_58] : k5_xboole_0(A_58,k1_xboole_0) = k2_xboole_0(A_58,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_28])).

tff(c_226,plain,(
    ! [A_58] : k2_xboole_0(A_58,k1_xboole_0) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_222])).

tff(c_26,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    ! [A_25] : ~ v1_xboole_0(k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_132,plain,(
    ! [B_48,A_49] :
      ( r2_hidden(B_48,A_49)
      | ~ m1_subset_1(B_48,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_139,plain,(
    ! [B_48,A_16] :
      ( r1_tarski(B_48,A_16)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_132,c_30])).

tff(c_172,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(B_54,A_55)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_139])).

tff(c_185,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_172])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_189,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_185,c_20])).

tff(c_209,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_200])).

tff(c_215,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_209])).

tff(c_382,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k3_subset_1(A_65,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_395,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_382])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_401,plain,(
    k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),k4_xboole_0('#skF_4','#skF_3')) = k5_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_2])).

tff(c_410,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_215,c_401])).

tff(c_510,plain,(
    ! [A_76,C_77,B_78] :
      ( r2_hidden(A_76,C_77)
      | ~ r2_hidden(A_76,B_78)
      | r2_hidden(A_76,k5_xboole_0(B_78,C_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_809,plain,(
    ! [A_104] :
      ( r2_hidden(A_104,'#skF_4')
      | ~ r2_hidden(A_104,'#skF_3')
      | r2_hidden(A_104,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_510])).

tff(c_54,plain,(
    ~ r2_hidden('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_827,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_809,c_54])).

tff(c_837,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_827])).

tff(c_840,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_837])).

tff(c_843,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_840])).

tff(c_845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_843])).

tff(c_847,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_861,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_847,c_4])).

tff(c_865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_861])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:36:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.94  
% 3.68/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.94  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.68/1.94  
% 3.68/1.94  %Foreground sorts:
% 3.68/1.94  
% 3.68/1.94  
% 3.68/1.94  %Background operators:
% 3.68/1.94  
% 3.68/1.94  
% 3.68/1.94  %Foreground operators:
% 3.68/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.68/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.68/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.68/1.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.68/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.94  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.68/1.94  tff('#skF_5', type, '#skF_5': $i).
% 3.68/1.94  tff('#skF_3', type, '#skF_3': $i).
% 3.68/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.68/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.94  tff('#skF_4', type, '#skF_4': $i).
% 3.68/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.68/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.68/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.68/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.68/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.68/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.68/1.94  
% 3.68/1.97  tff(f_94, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 3.68/1.97  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.68/1.97  tff(f_48, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.68/1.97  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.68/1.97  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.68/1.97  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.68/1.97  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.68/1.97  tff(f_50, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.68/1.97  tff(f_79, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.68/1.97  tff(f_59, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.68/1.97  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.68/1.97  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 3.68/1.97  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.68/1.97  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.68/1.97  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.68/1.97  tff(c_58, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.68/1.97  tff(c_111, plain, (![B_44, A_45]: (v1_xboole_0(B_44) | ~m1_subset_1(B_44, A_45) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.68/1.97  tff(c_123, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_111])).
% 3.68/1.97  tff(c_124, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_123])).
% 3.68/1.97  tff(c_44, plain, (![B_22, A_21]: (r2_hidden(B_22, A_21) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.68/1.97  tff(c_56, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.68/1.97  tff(c_24, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.68/1.97  tff(c_22, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.68/1.97  tff(c_92, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.68/1.97  tff(c_96, plain, (![A_11]: (k3_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_92])).
% 3.68/1.97  tff(c_200, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k3_xboole_0(A_56, B_57))=k4_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.68/1.97  tff(c_212, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_96, c_200])).
% 3.68/1.97  tff(c_217, plain, (![A_58]: (k4_xboole_0(k1_xboole_0, A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_212])).
% 3.68/1.97  tff(c_28, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.68/1.97  tff(c_222, plain, (![A_58]: (k5_xboole_0(A_58, k1_xboole_0)=k2_xboole_0(A_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_217, c_28])).
% 3.68/1.97  tff(c_226, plain, (![A_58]: (k2_xboole_0(A_58, k1_xboole_0)=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_222])).
% 3.68/1.97  tff(c_26, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.68/1.97  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.68/1.97  tff(c_52, plain, (![A_25]: (~v1_xboole_0(k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.68/1.97  tff(c_132, plain, (![B_48, A_49]: (r2_hidden(B_48, A_49) | ~m1_subset_1(B_48, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.68/1.97  tff(c_30, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.68/1.97  tff(c_139, plain, (![B_48, A_16]: (r1_tarski(B_48, A_16) | ~m1_subset_1(B_48, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_132, c_30])).
% 3.68/1.97  tff(c_172, plain, (![B_54, A_55]: (r1_tarski(B_54, A_55) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)))), inference(negUnitSimplification, [status(thm)], [c_52, c_139])).
% 3.68/1.97  tff(c_185, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_172])).
% 3.68/1.97  tff(c_20, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.68/1.97  tff(c_189, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_185, c_20])).
% 3.68/1.97  tff(c_209, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_189, c_200])).
% 3.68/1.97  tff(c_215, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_209])).
% 3.68/1.97  tff(c_382, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k3_subset_1(A_65, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.68/1.97  tff(c_395, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_382])).
% 3.68/1.97  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.68/1.97  tff(c_401, plain, (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k4_xboole_0('#skF_4', '#skF_3'))=k5_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_395, c_2])).
% 3.68/1.97  tff(c_410, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_215, c_401])).
% 3.68/1.97  tff(c_510, plain, (![A_76, C_77, B_78]: (r2_hidden(A_76, C_77) | ~r2_hidden(A_76, B_78) | r2_hidden(A_76, k5_xboole_0(B_78, C_77)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.68/1.97  tff(c_809, plain, (![A_104]: (r2_hidden(A_104, '#skF_4') | ~r2_hidden(A_104, '#skF_3') | r2_hidden(A_104, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_410, c_510])).
% 3.68/1.97  tff(c_54, plain, (~r2_hidden('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.68/1.97  tff(c_827, plain, (r2_hidden('#skF_5', '#skF_4') | ~r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_809, c_54])).
% 3.68/1.97  tff(c_837, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_827])).
% 3.68/1.97  tff(c_840, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_837])).
% 3.68/1.97  tff(c_843, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_840])).
% 3.68/1.97  tff(c_845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_843])).
% 3.68/1.97  tff(c_847, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_123])).
% 3.68/1.97  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.68/1.97  tff(c_861, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_847, c_4])).
% 3.68/1.97  tff(c_865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_861])).
% 3.68/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.97  
% 3.68/1.97  Inference rules
% 3.68/1.97  ----------------------
% 3.68/1.97  #Ref     : 0
% 3.68/1.97  #Sup     : 188
% 3.68/1.97  #Fact    : 0
% 3.68/1.97  #Define  : 0
% 3.68/1.97  #Split   : 8
% 3.68/1.97  #Chain   : 0
% 3.68/1.97  #Close   : 0
% 3.68/1.97  
% 3.68/1.97  Ordering : KBO
% 3.68/1.97  
% 3.68/1.97  Simplification rules
% 3.68/1.97  ----------------------
% 3.68/1.97  #Subsume      : 11
% 3.68/1.97  #Demod        : 42
% 3.68/1.97  #Tautology    : 90
% 3.68/1.97  #SimpNegUnit  : 17
% 3.68/1.97  #BackRed      : 3
% 3.68/1.97  
% 3.68/1.97  #Partial instantiations: 0
% 3.68/1.97  #Strategies tried      : 1
% 3.68/1.97  
% 3.68/1.97  Timing (in seconds)
% 3.68/1.97  ----------------------
% 3.68/1.97  Preprocessing        : 0.51
% 3.68/1.97  Parsing              : 0.26
% 3.68/1.97  CNF conversion       : 0.04
% 3.68/1.97  Main loop            : 0.60
% 3.68/1.97  Inferencing          : 0.21
% 3.68/1.97  Reduction            : 0.19
% 3.68/1.97  Demodulation         : 0.12
% 3.68/1.97  BG Simplification    : 0.03
% 3.68/1.97  Subsumption          : 0.11
% 3.68/1.97  Abstraction          : 0.03
% 3.68/1.97  MUC search           : 0.00
% 3.68/1.97  Cooper               : 0.00
% 3.68/1.97  Total                : 1.16
% 3.68/1.97  Index Insertion      : 0.00
% 3.68/1.97  Index Deletion       : 0.00
% 3.68/1.97  Index Matching       : 0.00
% 3.68/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
